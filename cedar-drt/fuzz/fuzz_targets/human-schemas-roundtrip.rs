/*
 * Copyright 2022-2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#![no_main]
use cedar_drt::*;
use cedar_drt_inner::*;
use std::collections::HashMap;
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};
use cedar_policy_validator::NamespaceDefinition;
use cedar_policy_validator::ActionType;
use cedar_policy_generators::{settings::ABACSettings, schema::Schema};
use serde::Serialize;
use cedar_policy_core::ast::Name;
use cedar_policy_validator::SchemaFragment;
use smol_str::{SmolStr, ToSmolStr};
use cedar_policy_validator::ApplySpec;


#[derive(Debug,Clone,Serialize)]
struct Input {
    #[serde(skip)]
    pub schema: SchemaFragment,
}

/// settings for this fuzz target
const SETTINGS: ABACSettings = ABACSettings {
    match_types: false,
    enable_extensions: true,
    max_depth: 3,
    max_width: 7,
    enable_additional_attributes: false,
    enable_like: true,
    // ABAC fuzzing restricts the use of action because it is used to generate
    // the corpus tests which will be run on Cedar and CedarCLI.
    // These packages only expose the restricted action behavior.
    enable_action_groups_and_attrs: false,
    enable_arbitrary_func_call: true,
    enable_unknowns: false,
    enable_action_in_constraints: true,
    enable_unspecified_apply_spec: true,
};

impl<'a> Arbitrary<'a> for Input {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let arb_schema = Schema::arbitrary(SETTINGS.clone(), u)?;
        let namespace = arb_schema.schema;
        let name : SmolStr = arb_schema
            .namespace
            .map(|name| name.to_smolstr())
            .unwrap_or_else(|| "".into());
        
        let schema = SchemaFragment(HashMap::from([(name, namespace)]));

        Ok(Self { schema })
    }

    fn size_hint(depth : usize) -> (usize, Option<usize>) {
        Schema::arbitrary_size_hint(depth)
    }
}

fn result_combiner<E>(lhs : Result<(), E>, rhs : Result<(), E>) -> Result<(), E> { 
    match (lhs, rhs) { 
        (Err(e), _) | (_, Err(e)) => Err(e),
        _ => Ok(())
    }
}

fn detailed_equality_check(lhs : SchemaFragment, rhs : SchemaFragment) -> Result<(), String> { 
    if lhs.0.len() == rhs.0.len() { 
        lhs.0.into_iter()
            .map(|(name, lhs_namespace)| { 
                let rhs_namespace = rhs.0
                    .get(&name)
                    .ok_or_else(||format!("`{name}` does not exist in RHS schema"))?;
                detailed_namespace_equality(lhs_namespace, rhs_namespace.clone())
            })
            .fold(Ok(()), result_combiner)
    } else { 
        Err("schema differ in number of namespaces".to_string())
    }
}

fn detailed_namespace_equality(lhs : NamespaceDefinition, rhs : NamespaceDefinition) -> Result<(), String> { 
    if lhs.common_types != rhs.common_types { 
        Err("Common types differ".to_string())
    } else if lhs.entity_types != rhs.entity_types { 
        Err("Entity types differ".to_string())
    } else if lhs.actions.len() != rhs.actions.len() { 
        Err("Different number of actions".to_string())
    } else { 
        lhs.actions.into_iter()
            .map(|(name, lhs_action)| { 
                let rhs_action = rhs.actions
                    .get(&name)
                    .ok_or_else(|| format!("Action `{name}` not present on rhs"))?;
                detailed_action_type_equality(name.as_ref(), lhs_action, rhs_action.clone())
            })
        .fold(Ok(()), result_combiner)
    }
}

fn detailed_action_type_equality(name : &str, lhs : ActionType, rhs : ActionType) -> Result<(), String> { 
    if lhs.attributes != rhs.attributes { 
        Err(format!("Attributes don't match for `{name}`"))
    } else if lhs.member_of != rhs.member_of { 
        Err(format!("Member of don't match for `{name}`"))
    } else { 
        match (lhs.applies_to, rhs.applies_to) { 
            (None, None) => Ok(()), 
            (Some(lhs), Some(rhs)) => if empty_target(&rhs) || empty_target(&lhs) || rhs == lhs { 
                Ok(())
            } else { 
                Err(format!("Mismatched applies to in `{name}`. lhs : `{:?}`,rhs: `{:?}`", lhs, rhs))
            },
            (Some(spec), None) | (None, Some(spec)) if empty_target(&spec) => Ok(()),
            (Some(_), None) => Err(format!("Mismatched applies to in `{name}`, lhs was `Some`, `rhs` was `None`")),
            (None, Some(_)) => Err(format!("Mismatched applies to in `{name}`, lhs was `None`, `rhs` was `Some`")),
        }
    }
}

fn empty_target(spec : &ApplySpec) -> bool { 
    spec.resource_types.as_ref().map(|v| v.is_empty()).unwrap_or(false) || spec.principal_types.as_ref().map(|v| v.is_empty()).unwrap_or(false)
}

fuzz_target!(|i : Input| {
    let src = i.schema.as_natural_schema().unwrap();
    let (parsed, _) = SchemaFragment::from_str_natural(&src).unwrap();
    if i.schema != parsed { 
        if let Err(msg) = detailed_equality_check(i.schema.clone(), parsed) { 
            println!("Schema: {src}");
            println!("LHS:\n{:?}", i.schema);
            println!("RHS:\n{:?}", i.schema);
            panic!("{msg}");
        }
    }
});
