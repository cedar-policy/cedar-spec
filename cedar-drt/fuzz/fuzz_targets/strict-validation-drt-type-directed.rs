#![no_main]
use cedar_drt::*;
use cedar_drt_inner::*;
use cedar_policy_core::ast;
use cedar_policy_validator::{ActionBehavior, ValidatorNamespaceDef, ValidatorSchemaFragment};
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};
use log::{debug, info};

/// Input expected by this fuzz target
#[derive(Debug, Clone)]
struct FuzzTargetInput {
    /// generated schema
    pub schema: Schema,
    /// generated policy
    pub policy: ABACPolicy,
}

/// settings for this fuzz target
const SETTINGS: ABACSettings = ABACSettings {
    match_types: true,
    enable_extensions: true,
    max_depth: 7,
    max_width: 7,
    enable_additional_attributes: true,
    enable_like: true,
    enable_action_groups_and_attrs: true,
    enable_arbitrary_func_call: true,
    enable_unknowns: false,
};

impl<'a> Arbitrary<'a> for FuzzTargetInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let schema: Schema = Schema::arbitrary(SETTINGS.clone(), u)?;
        let hierarchy = schema.arbitrary_hierarchy(u)?;
        let policy = schema.arbitrary_policy(&hierarchy, u)?;
        Ok(Self { schema, policy })
    }

    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        arbitrary::size_hint::and_all(&[
            Schema::arbitrary_size_hint(depth),
            Schema::arbitrary_policy_size_hint(&SETTINGS, depth),
        ])
    }
}

// The main fuzz target
fuzz_target!(|input: FuzzTargetInput| {
    initialize_log();

    // generate a schema
    if let Ok(schema) = ValidatorNamespaceDef::from_namespace_definition(
        input.schema.namespace().clone(),
        input.schema.schemafile().clone(),
        ActionBehavior::ProhibitAttributes,
    )
    .and_then(|f| {
        ValidatorSchema::from_schema_fragments([ValidatorSchemaFragment::from_namespaces([f])])
    }) {
        debug!("Schema: {:?}", schema);

        // generate a policy
        let mut policyset = ast::PolicySet::new();
        let policy: ast::StaticPolicy = input.policy.into();
        policyset.add_static(policy).unwrap();
        debug!("Policies: {policyset}");

        // run the policy through both validators and compare the result
        let diff_tester = DifferentialTester::new();
        let (_, total_dur) = time_function(|| {
            diff_tester.run_validation(schema, &policyset, ValidationMode::Strict)
        });
        info!("{}{}", TOTAL_MSG, total_dur.as_nanos());
    }
});
