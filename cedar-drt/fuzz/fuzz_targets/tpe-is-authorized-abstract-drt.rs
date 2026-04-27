#![no_main]

use std::sync::LazyLock;

use cedar_drt_inner::tpe::test_tpe_is_authorized_equiv;
use cedar_lean_ffi::CedarLeanFfi;
use cedar_policy::{
    PartialEntities, PartialEntityUid, PartialRequest, Policy, PolicyId, PolicySet,
    Schema,
};
use libfuzzer_sys::{
    arbitrary::{self, Arbitrary},
    fuzz_target,
};
use smol_str::format_smolstr;

#[derive(Arbitrary, Debug, PartialEq, Eq, Clone)]
enum AbstractPolicy {
    /// Permit policy that evaluates 'true'
    PermitTrue,
    /// Permit policy that evaluates 'false'
    PermitFalse,
    /// Permit policy that errors
    PermitError,
    /// Permit policy that leaves a residual
    PermitResidual,
    /// Forbid policy that evaluates 'true'
    ForbidTrue,
    /// Forbid policy that evaluates 'false'
    ForbidFalse,
    /// Forbid policy that evaluates 'error'
    ForbidError,
    /// Forbid policy that leaves a residual
    ForbidResidual,
}

mod concrete_policies {
    use cedar_policy::Policy;
    use std::sync::LazyLock;

    pub static PERMIT_TRUE: LazyLock<Policy> = LazyLock::new(|| {
        Policy::parse(None, "permit(principal, action, resource);")
            .expect("should be a valid policy")
    });

    pub static PERMIT_FALSE: LazyLock<Policy> = LazyLock::new(|| {
        Policy::parse(None, "permit(principal, action, resource) when { 1 == 0 };")
            .expect("should be a valid policy")
    });

    pub static PERMIT_ERROR: LazyLock<Policy> = LazyLock::new(|| {
        Policy::parse(
            None,
            &format!(
                "permit(principal, action, resource) when {{ ({} + 1) == 0 }};",
                i64::MAX
            ),
        )
        .expect("should be a valid policy")
    });

    pub static PERMIT_RESIDUAL: LazyLock<Policy> = LazyLock::new(|| {
        Policy::parse(
            None,
            "permit(principal, action, resource) when {{ principal.is_admin };",
        )
        .expect("should be a valid policy")
    });

    pub static FORBID_TRUE: LazyLock<Policy> = LazyLock::new(|| {
        Policy::parse(None, "forbid(principal, action, resource);")
            .expect("should be a valid policy")
    });

    pub static FORBID_FALSE: LazyLock<Policy> = LazyLock::new(|| {
        Policy::parse(None, "forbid(principal, action, resource) when { 1 == 0 };")
            .expect("should be a valid policy")
    });

    pub static FORBID_ERROR: LazyLock<Policy> = LazyLock::new(|| {
        Policy::parse(
            None,
            &format!(
                "forbid(principal, action, resource) when {{ ({} + 1) == 0 }};",
                i64::MAX
            ),
        )
        .expect("should be a valid policy")
    });

    pub static FORBID_RESIDUAL: LazyLock<Policy> = LazyLock::new(|| {
        Policy::parse(
            None,
            "forbid(principal, action, resource) when {{ principal.is_admin };",
        )
        .expect("should be a valid policy")
    });
}

impl AbstractPolicy {
    /// Convert the `AbstractPolicy` into a `Policy` with the given `id`
    fn into_policy(self, id: PolicyId) -> Policy {
        match self {
            AbstractPolicy::PermitTrue => concrete_policies::PERMIT_TRUE.new_id(id),
            AbstractPolicy::PermitFalse => concrete_policies::PERMIT_FALSE.new_id(id),
            AbstractPolicy::PermitError => concrete_policies::PERMIT_ERROR.new_id(id),
            AbstractPolicy::PermitResidual => concrete_policies::PERMIT_RESIDUAL.new_id(id),
            AbstractPolicy::ForbidTrue => concrete_policies::FORBID_TRUE.new_id(id),
            AbstractPolicy::ForbidFalse => concrete_policies::FORBID_FALSE.new_id(id),
            AbstractPolicy::ForbidError => concrete_policies::FORBID_ERROR.new_id(id),
            AbstractPolicy::ForbidResidual => concrete_policies::FORBID_RESIDUAL.new_id(id),
        }
    }
}

#[derive(Arbitrary, Debug)]
pub struct AbstractAuthorizerInput {
    policies: Vec<AbstractPolicy>,
}

static SCHEMA: LazyLock<Schema> = LazyLock::new(|| {
    Schema::from_cedarschema_str("entity E; action A appliesTo {principal: E, resource: E};")
        .unwrap()
        .0
});

static REQUEST: LazyLock<PartialRequest> = LazyLock::new(|| {
    PartialRequest::new(
        PartialEntityUid::from_concrete("E::\"0\"".parse().unwrap()),
        "Action::\"A\"".parse().expect("should be valid"),
        PartialEntityUid::from_concrete("E::\"1\"".parse().unwrap()),
        None,
        &SCHEMA,
    )
    .unwrap()
});

fuzz_target!(|input: AbstractAuthorizerInput| {
    let policyset = PolicySet::from_policies(
        input
            .policies
            .into_iter()
            .enumerate()
            .map(|(idx, p)| p.into_policy(PolicyId::new(format_smolstr!("p{idx}")))),
    )
    .unwrap();
    let ffi = CedarLeanFfi::new();
    test_tpe_is_authorized_equiv(
        &ffi,
        &SCHEMA,
        &policyset,
        &REQUEST,
        &PartialEntities::empty(),
    );
});
