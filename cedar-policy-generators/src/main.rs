use std::str::FromStr;

use arbitrary::Unstructured;
use cedar_policy_core::ast::StaticPolicy;
use cedar_policy_generators::schema_gen::SchemaGen;
use cedar_policy_generators::{schema_gen::ValidatorSchema, settings::ABACSettings};
use rand::rngs::StdRng;
use rand::{RngCore, SeedableRng};

fn get_schema() -> cedar_policy_core::validator::ValidatorSchema {
    cedar_policy_core::validator::ValidatorSchema::from_str(
        r#"
    entity DocumentShare, Drive;
entity Document  = {
  "isPrivate": Bool,
  "manageACL": DocumentShare,
  "modifyACL": DocumentShare,
  "owner": User,
  "publicAccess": String,
  "viewACL": DocumentShare,
};
entity Group in [DocumentShare] = {
  "owner": User,
};
entity Public in [DocumentShare];
entity User in [Group] = {
  "blocked": Set<User>,
  "personalGroup": Group,
};

action DeleteGroup, ModifyGroup appliesTo {
  principal: [User],
  resource: [Group],
  context: {
    "is_authenticated": Bool,
  }
};
action CreateGroup appliesTo {
  principal: [User],
  resource: [Drive],
  context: {
    "is_authenticated": Bool,
  }
};
action ViewDocument appliesTo {
  principal: [User, Public],
  resource: [Document],
  context: {
    "is_authenticated": Bool,
  }
};
action AddToShareACL, DeleteDocument, EditIsPrivate, EditPublicAccess appliesTo {
  principal: [User],
  resource: [Document],
  context: {
    "is_authenticated": Bool,
  }
};
action ModifyDocument appliesTo {
  principal: [User],
  resource: [Document],
  context: {
    "is_authenticated": Bool,
  }
};
action CreateDocument appliesTo {
  principal: [User],
  resource: [Drive],
  context: {
    "is_authenticated": Bool,
  }
};
    "#,
    )
    .expect("should parse")
}

fn main() {
    let settings = ABACSettings {
        match_types: true,
        enable_extensions: true,
        max_depth: 3,
        max_width: 3,
        enable_additional_attributes: false,
        enable_like: true,
        enable_action_groups_and_attrs: true,
        enable_arbitrary_func_call: true,
        enable_unknowns: false,
        enable_action_in_constraints: true,
        per_action_request_env_limit: 128,
        total_action_request_env_limit: 1024,
    };
    let mut rng = StdRng::seed_from_u64(42);
    let mut bytes = [0u8; 4096];
    rng.fill_bytes(&mut bytes);
    let mut u = Unstructured::new(&bytes);
    let core_schema = get_schema();
    let schema = ValidatorSchema::new(&core_schema, &settings, &mut u).expect("should succeed");
    if let Ok(hierarchy) = schema.arbitrary_hierarchy(&mut u) {
        for _ in 0..100 {
            if let Ok(policy) = schema.arbitrary_policy(&hierarchy, &mut u) {
                let policy: StaticPolicy = policy.into();
                println!("{policy}");
            }
        }
    }
}
