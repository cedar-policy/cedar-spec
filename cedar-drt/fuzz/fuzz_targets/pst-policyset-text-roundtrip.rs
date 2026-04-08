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

use cedar_drt::logger::initialize_log;
use cedar_drt_inner::{fuzz_target, pst_equiv, pst_gen::PolicySetFuzzTargetInput};

use cedar_policy::{EntityUid, Policy, PolicySet, SlotId, Template};
use log::debug;
use std::collections::HashMap;

// PST PolicySet -> from_pst -> deconstruct to text -> reconstruct -> to_pst -> compare
// Tests round-tripping through text, with policy/template and link management.
fuzz_target!(|input: PolicySetFuzzTargetInput| {
    initialize_log();
    let pst_set = input.policy_set;

    debug!("Running PST PolicySet roundtrip on: {:?}", pst_set);

    // PST into public PolicySet using from_pst
    let policy_set = PolicySet::from_pst(pst_set.clone())
        .unwrap_or_else(|e| panic!("Failed to create PolicySet from PST.\nError: {:?}", e));

    // Deconstruct and reconstruct via text
    let mut reconstructed = PolicySet::new();

    // Templates: print each to text, parse back with original ID, add to new set
    for template in policy_set.templates() {
        let id = template.id().clone();
        let text = template.to_string();
        let parsed = Template::parse(Some(id), &text).unwrap_or_else(|e| {
            panic!(
                "Failed to parse template from text:\n{}\nError: {:?}",
                text, e
            )
        });
        reconstructed
            .add_template(parsed)
            .unwrap_or_else(|e| panic!("Failed to add template: {:?}", e));
    }

    // Static policies: print each to text, parse back with original ID
    // Linked policies: skip (we'll re-link below)
    for policy in policy_set.policies() {
        if policy.template_id().is_some() {
            continue; // linked policy, will re-link
        }
        let id = policy.id().clone();
        let text = policy.to_string();
        let parsed = Policy::parse(Some(id), &text).unwrap_or_else(|e| {
            panic!(
                "Failed to parse policy from text:\n{}\nError: {:?}",
                text, e
            )
        });
        reconstructed
            .add(parsed)
            .unwrap_or_else(|e| panic!("Failed to add policy: {:?}", e));
    }

    // Re-link templates using original link info
    for link in &pst_set.template_links {
        let vals: HashMap<SlotId, EntityUid> = link
            .values
            .iter()
            .map(|(k, v)| {
                (
                    (*k).into(),
                    cedar_policy_core::ast::EntityUID::from(v.clone()).into(),
                )
            })
            .collect();
        reconstructed
            .link(
                link.template_id.clone().into(),
                link.new_id.clone().into(),
                vals,
            )
            .unwrap_or_else(|e| panic!("Failed to link template: {:?}", e));
    }

    // Reconstructed to PST using to_pst, should maintain ids
    let roundtripped = reconstructed
        .to_pst()
        .unwrap_or_else(|e| panic!("to_pst failed: {:?}", e));

    // Compare policy sets
    pst_equiv::check_policy_set_equivalence(
        &pst_set,
        &roundtripped,
        pst_equiv::CheckingParams { check_ids: true },
    );
});
