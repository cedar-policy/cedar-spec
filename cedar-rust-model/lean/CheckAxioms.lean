/- Prints the axioms of every exported theorem (checked by `scripts/check_axioms.sh`). -/
import CedarRustModel

#print axioms CedarRustModel.evaluate_correct
#print axioms CedarRustModel.is_authorized_correct
#print axioms CedarRustModel.policy_to_expr_ok
#print axioms CedarRustModel.to_policy_correct
#print axioms CedarRustModel.parse_decimal_correct
#print axioms CedarRustModel.parse_ip_correct
#print axioms CedarRustModel.parse_datetime_correct
#print axioms CedarRustModel.parse_duration_correct
#print axioms CedarRustModel.parse_ip_wf
#print axioms CedarRustModel.call_correct
#print axioms CedarRustModel.ext_eq_correct
#print axioms CedarRustModel.ext_lt_correct
#print axioms CedarRustModel.ext_wf_correct
#print axioms CedarRustModel.Thm.forbid_trumps_permit
#print axioms CedarRustModel.Thm.allowed_only_if_explicitly_permitted
#print axioms CedarRustModel.Thm.default_deny
#print axioms CedarRustModel.Thm.allowed_iff_explicitly_permitted_and_not_denied
#print axioms CedarRustModel.Thm.denied_iff_explicitly_denied_or_not_permitted
#print axioms CedarRustModel.Thm.order_and_dup_independent
#print axioms CedarRustModel.Thm.unchanged_allow_when_add_permit
#print axioms CedarRustModel.Thm.unchanged_deny_when_add_forbid
#print axioms CedarRustModel.Thm.is_authorized_eq_for_sound_policy_slice
#print axioms CedarRustModel.Thm.determining_policies_of
#print axioms CedarRustModel.Thm.erroring_policies_of
#print axioms CedarRustModel.Thm.determining_erroring_disjoint_when_unique_ids
