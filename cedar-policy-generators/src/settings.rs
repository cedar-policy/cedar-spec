/// Maximum length of a pattern string
pub const MAX_PATTERN_LEN: usize = 6;

/// Settings controlling the generation of ABAC hierarchies/policies/requests
#[derive(Debug, Clone)]
pub struct ABACSettings {
    /// If true, generates well-typed hierarchies/policies/requests.
    /// Specifically:
    /// - policies will not throw type errors, ie, we generate subexpressions of the proper type for ops like < or .contains()
    /// - attribute values (in the hierarchy and in the request contexts) will strictly adhere to the types suggested in pool.ty_data
    ///
    /// If false, does not attempt to match types.
    pub match_types: bool,
    /// Allow generation of `Long` types with unspecified bounds. This is
    /// usually harmless but can be a problem if you're using the definitional
    /// validator (which currently doesn't support such types) or expecting that
    /// a policy that passes validation won't raise runtime overflow errors.
    pub enable_long_any: bool,
    /// If true, may generate extension function calls in policies and/or
    /// attribute values.
    pub enable_extensions: bool,
    /// Maximum depth of an expression or type. E.g., maximum nesting of sets.
    ///
    /// This is used in the following places:
    /// - Maximum depth of the expression in a when/unless clause
    ///     - Note that this is only the limit for _each_ `when` and `unless`
    ///     clause.
    ///     Some generated policies will have multiple `when` and `unless`
    ///     clauses, in which case the conjunction of all conditions may exceed
    ///     the `max_depth`. But, the `max_depth` still applies for each clause
    ///     individually.
    /// - Maximum depth of expressions in attribute values in the hierarchy,
    ///     and also of attributes of `context` in each request
    /// - Maximum depth of a type specified in a generated schema
    /// - Maximum number of when/unless clauses in a policy
    pub max_depth: usize,
    /// Maximum width of an expression or type. E.g., maximum number of elements
    /// in a set.
    ///
    /// This is used in the following places:
    /// - Maximum number of elements in a set in an attribute value in the
    ///     hierarchy
    /// - Maximum number of elements in a set literal in a policy
    /// - Maximum number of attributes in a record in an attribute value in the
    ///     hierarchy
    /// - Maximum number of attributes in a record literal in a policy
    /// - Maximum number of UIDs in the hierarchy of any given entity type
    /// - Maximum number of "additional attributes" on any entity in the
    ///     hierarchy
    pub max_width: usize,
    /// Whether to enable the `additional_attributes` flag in generated schemas.
    /// If this option is `false`, `additional_attributes` will always be false
    /// in all generated schemas.
    /// If this option is `true`, `additional_attributes` will be randomly
    /// chosen to be either true or false every time it appears.
    /// Generated attribute data also respects the value of
    /// `additional_attributes` in the schema: it may add additional attributes,
    /// but only if `additional_attributes` is true.
    pub enable_additional_attributes: bool,
    /// Flag to globally enable/disable generation of expressions containing the
    /// `like` operator.
    pub enable_like: bool,
    /// Flag to enable/disable generating actions in groups and declaring
    /// attributes on entity types.
    pub enable_action_groups_and_attrs: bool,
    /// Flag to enable/disable generating arbitrary extension function calls.
    /// Note that this flag is only considered if `enable_extensions` is true.
    /// This flag should only be disabled for target `pp` because the parser now
    /// rejects unknown extension function calls.
    pub enable_arbitrary_func_call: bool,

    /// Flag to enable/disable generating unknowns, exercising partial evaluation
    pub enable_unknowns: bool,

    /// Flag to enable/disable unspecified entities where actions can apply
    /// Enabling it causes `ActionType::applies_to` to match `Some(ApplySpec {resource_types: Some(_), principal_types: Some(_), context: _})`
    pub enable_unspecified_apply_spec: bool,

    /// Flag to enable/disable action constraints in forms of `in` operations
    pub enable_action_in_constraints: bool,
}
