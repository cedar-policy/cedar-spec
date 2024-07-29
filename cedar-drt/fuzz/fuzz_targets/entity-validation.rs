/*
 * Copyright Cedar Contributors
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
 use cedar_policy_core::ast;
 use cedar_policy_core::ast::Entity;
 use cedar_policy_core::extensions::Extensions;
 use cedar_policy_generators::{abac::ABACPolicy, schema::Schema, settings::ABACSettings, hierarchy::Hierarchy, abac::ABACRequest};
 use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};
 use log::{debug, info};
 use serde::Serialize;
 
 /// Input expected by this fuzz target
 #[derive(Debug, Clone, Serialize)]
 pub struct FuzzTargetInput {
     /// generated schema
     #[serde(skip)]
     pub schema: Schema,
    /// generated hierarchy
    #[serde(skip)]
    pub hierarchy: Hierarchy
 }
 
 /// settings for this fuzz target
 const SETTINGS: ABACSettings = ABACSettings {
     match_types: false,
     enable_extensions: true,
     max_depth: 7,
     max_width: 7,
     enable_additional_attributes: true,
     enable_like: true,
     enable_action_groups_and_attrs: true,
     enable_arbitrary_func_call: true,
     enable_unknowns: false,
     enable_action_in_constraints: true,
     enable_unspecified_apply_spec: true,
 };
 
 impl<'a> Arbitrary<'a> for FuzzTargetInput {
     fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
         let schema: Schema = Schema::arbitrary(SETTINGS.clone(), u)?;
         let hierarchy = schema.arbitrary_hierarchy(u)?;
         Ok(Self { schema, hierarchy })
     }
 
     fn size_hint(depth: usize) -> (usize, Option<usize>) {
         arbitrary::size_hint::and_all(&[
             Schema::arbitrary_size_hint(depth),
         ])
     }
 }
 
 // Non-type-directed fuzzing of (strict) validation.
 fuzz_target!(|input: FuzzTargetInput| {
     initialize_log();
     let def_impl = LeanDefinitionalEngine::new();
 
     // generate a schema
     if let Ok(schema) = ValidatorSchema::try_from(input.schema) {
        debug!("Schema: {:?}", schema);
        if let Ok(entities) = Entities::try_from(input.hierarchy) {
            let (_, total_dur) =
            time_function(|| run_ent_val_test(&def_impl, schema, entities, Extensions::all_available()));
        info!("{}{}", TOTAL_MSG, total_dur.as_nanos());
        }
    }
 });
 