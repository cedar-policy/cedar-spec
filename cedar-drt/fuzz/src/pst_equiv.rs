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
