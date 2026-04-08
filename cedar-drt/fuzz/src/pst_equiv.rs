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

use cedar_policy::pst;

/// Checking parameters for equivalence of PST representations
pub struct CheckingParams {
    pub check_ids: bool,
}

/// Compare two PST policy sets for equivalence
pub fn check_policy_set_equivalence(
    original: &pst::PolicySet,
    roundtripped: &pst::PolicySet,
    params: CheckingParams,
) {
    // Compare templates
    assert_eq!(
        original.templates.len(),
        roundtripped.templates.len(),
        "Template count mismatch"
    );
    for (id, orig) in &original.templates {
        let rt = roundtripped
            .templates
            .get(id)
            .unwrap_or_else(|| panic!("Template {:?} missing after roundtrip", id));
        check_template_equivalence(
            orig,
            rt,
            CheckingParams {
                check_ids: params.check_ids,
            },
        );
    }

    // Compare static policies
    assert_eq!(
        original.policies.len(),
        roundtripped.policies.len(),
        "Static policy count mismatch"
    );
    for (id, orig) in &original.policies {
        let rt = roundtripped
            .policies
            .get(id)
            .unwrap_or_else(|| panic!("Static policy {:?} missing after roundtrip", id));
        check_template_equivalence(
            &orig.body,
            &rt.body,
            CheckingParams {
                check_ids: params.check_ids,
            },
        );
    }

    // Compare template links
    assert_eq!(
        original.template_links.len(),
        roundtripped.template_links.len(),
        "Template link count mismatch"
    );
    for (orig, rt) in original
        .template_links
        .iter()
        .zip(roundtripped.template_links.iter())
    {
        assert_eq!(
            orig.template_id, rt.template_id,
            "Link template_id mismatch"
        );
        assert_eq!(orig.new_id, rt.new_id, "Link new_id mismatch");
        assert_eq!(orig.values, rt.values, "Link values mismatch");
    }
}

/// Compare two PST templates for equivalence
pub fn check_template_equivalence(
    original: &pst::Template,
    roundtripped: &pst::Template,
    params: CheckingParams,
) {
    if params.check_ids {
        assert_eq!(
            original.id, roundtripped.id,
            "Id mismatch.\nOriginal: {:?}\nRoundtripped: {:?}",
            original, roundtripped
        );
    }
    assert_eq!(
        original.effect, roundtripped.effect,
        "Effect mismatch.\nOriginal: {:?}\nRoundtripped: {:?}",
        original, roundtripped
    );
    assert_eq!(
        original.principal, roundtripped.principal,
        "Principal constraint mismatch.\nOriginal: {:?}\nRoundtripped: {:?}",
        original, roundtripped
    );
    assert_eq!(
        original.action, roundtripped.action,
        "Action constraint mismatch.\nOriginal: {:?}\nRoundtripped: {:?}",
        original, roundtripped
    );
    assert_eq!(
        original.resource, roundtripped.resource,
        "Resource constraint mismatch.\nOriginal: {:?}\nRoundtripped: {:?}",
        original, roundtripped
    );
    assert_eq!(
        original.clauses(),
        roundtripped.clauses(),
        "Clauses mismatch.\nOriginal: {:?}\nRoundtripped: {:?}",
        original,
        roundtripped
    );
    assert_eq!(
        original.annotations, roundtripped.annotations,
        "Annotations mismatch.\nOriginal: {:?}\nRoundtripped: {:?}",
        original, roundtripped
    );
}
