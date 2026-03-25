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
use cedar_drt_inner::{fuzz_target, pst_equiv, pst_gen::FuzzTargetInput};

use cedar_policy_core::est;
use cedar_policy_core::pst;
use log::debug;

// PST → EST → PST roundtrip
fuzz_target!(|input: FuzzTargetInput| {
    initialize_log();
    let template = input.template;

    debug!("Running PST→EST→PST roundtrip on: {:?}", template);

    let est_policy: est::Policy = template
        .clone()
        .try_into()
        .unwrap_or_else(|e| panic!("PST → EST failed: {:?}\nTemplate: {:?}", e, template));

    let roundtripped: pst::Template = est_policy
        .try_into()
        .unwrap_or_else(|e| panic!("EST → PST failed: {:?}\nOriginal: {:?}", e, template));

    // IDs are lost in the EST roundtrip
    pst_equiv::check_template_equivalence(
        &template,
        &roundtripped,
        pst_equiv::CheckingParams { check_ids: false },
    );
});
