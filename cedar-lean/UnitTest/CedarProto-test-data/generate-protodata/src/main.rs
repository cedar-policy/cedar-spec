use cedar_policy_core::{
    ast, entities,
    extensions::Extensions,
    parser::{parse_policy, parse_policy_or_template, parse_policyset, Loc},
};
use cedar_policy_validator::types as validator_types;
use prost::Message;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::str::FromStr;

fn output_dir() -> PathBuf {
    std::env::var("OUTPUT_DIR")
        .map(PathBuf::from)
        .unwrap_or(PathBuf::from_str(".").unwrap())
}

#[track_caller]
fn encode_expr(path: impl AsRef<Path>, e: &str) {
    let expr: ast::Expr = e.parse().unwrap();
    let proto: ast::proto::Expr = (&expr).into();
    let encoded = proto.encode_to_vec();
    std::fs::write(output_dir().join(path.as_ref()), encoded).unwrap();
}

/// Encodes using the protobuf TemplateBody format
#[track_caller]
fn encode_policy_as_template(path: impl AsRef<Path>, p: &str) {
    let policy: ast::Template = parse_policy_or_template(None, p).unwrap().into();
    let proto: ast::proto::TemplateBody = (&policy).into();
    let encoded = proto.encode_to_vec();
    std::fs::write(output_dir().join(path.as_ref()), encoded).unwrap();
}

#[track_caller]
fn encode_policyset(path: impl AsRef<Path>, ps: &ast::PolicySet) {
    let proto: ast::proto::LiteralPolicySet = ps.into();
    let encoded = proto.encode_to_vec();
    std::fs::write(output_dir().join(path.as_ref()), encoded).unwrap();
}

#[track_caller]
fn encode_request(path: impl AsRef<Path>, r: &ast::Request) {
    let proto: ast::proto::Request = r.into();
    let encoded = proto.encode_to_vec();
    std::fs::write(output_dir().join(path.as_ref()), encoded).unwrap();
}

#[track_caller]
fn encode_entity(path: impl AsRef<Path>, e: &ast::Entity) {
    let proto: ast::proto::Entity = e.into();
    let encoded = proto.encode_to_vec();
    std::fs::write(output_dir().join(path.as_ref()), encoded).unwrap();
}

#[track_caller]
fn encode_entities(path: impl AsRef<Path>, es: &entities::Entities) {
    let proto: ast::proto::Entities = es.into();
    let encoded = proto.encode_to_vec();
    std::fs::write(output_dir().join(path.as_ref()), encoded).unwrap();
}

#[track_caller]
fn encode_val_type(path: impl AsRef<Path>, ty: &validator_types::Type) {
    let proto: cedar_policy_validator::proto::Type = ty.into();
    let encoded = proto.encode_to_vec();
    std::fs::write(output_dir().join(path.as_ref()), encoded).unwrap();
}

#[track_caller]
fn encode_schema(path: impl AsRef<Path>, s: &str) {
    let (schema, warnings) = cedar_policy_validator::ValidatorSchema::from_cedarschema_str(
        s,
        &Extensions::all_available(),
    )
    .map_err(|e| format!("{:?}", miette::Report::new(e)))
    .unwrap();
    assert_eq!(warnings.count(), 0);
    let proto: cedar_policy_validator::proto::ValidatorSchema = (&schema).into();
    let encoded = proto.encode_to_vec();
    std::fs::write(output_dir().join(path.as_ref()), encoded).unwrap();
}

fn main() {
    encode_expr("false.protodata", "false");
    encode_expr("true.protodata", "true");
    encode_expr("345.protodata", "345");
    encode_expr("emptystring.protodata", r#""""#);
    encode_expr("thisiscedar.protodata", r#""this is Cedar""#);
    encode_expr("action.protodata", "action");
    encode_expr("user_alice.protodata", r#"User::"alice""#);
    encode_expr("app_widget_123.protodata", r#"App::Widget::"123""#);
    encode_expr("emptyset.protodata", "[]");
    encode_expr("set.protodata", r#"[-2, "minustwo"]"#);
    encode_expr(
        "nested_set.protodata",
        "[ [1, 2], [3, principal.foo], false ]",
    );
    encode_expr("emptyrecord.protodata", "{}");
    encode_expr("record.protodata", "{ ham: 3, eggs: 7 }");
    encode_expr(
        "nested_record.protodata",
        r#"{ ham: { a: 0, b: false }, eggs: ["this is", "a set"] }"#,
    );
    encode_expr(
        "principal_in_resource_owners.protodata",
        "principal in resource.owners",
    );
    encode_expr(
        "has_and_get.protodata",
        r#"principal has department && principal.department == "Sales""#,
    );
    encode_expr(
        "has_and_get_tags.protodata",
        r#"principal.hasTag("department") && principal.getTag("department") == "Sales""#,
    );
    encode_expr(
        "not_and_neg.protodata",
        "!principal.foo || -(principal.bar) != 3",
    );
    encode_expr(
        "plus_and_minus_and_times.protodata",
        "32 + context.count - 7 * 4",
    );
    encode_expr(
        "contains.protodata",
        r#"[2,3,User::"alice"].contains(context.foo)"#,
    );
    encode_expr("like.protodata", r#"context.a.b.c.d like "a*b**cd""#);
    encode_expr(
        "is.protodata",
        r#"App::Widget::"123" is App::Widget && resource.widget is App::Widget in principal.widgets"#,
    );
    encode_expr(
        "complicated.protodata",
        "(if context.foo < 3 then principal.foo else principal.bar).a.b.contains(context.abc)",
    );
    encode_expr(
        "ip.protodata",
        r#"ip("192.168.0.1").isInRange(ip("192.0.0.0/8"))"#,
    );
    encode_expr(
        "decimal.protodata",
        r#"decimal("3.14").lessThan(decimal("3.1416"))"#,
    );

    encode_policy_as_template(
        "rbac.protodata",
        r#"permit(principal == User::"a b c", action, resource is App::Widget);"#,
    );
    encode_policy_as_template(
        "abac.protodata",
        r#"permit(principal, action, resource) when { principal == resource.owner } unless { resource.sensitive };"#,
    );

    let mut policyset: ast::PolicySet = parse_policyset(r#"
        permit(principal, action == Action::"do", resource == Blob::"thing") when { context.foo - 7 == context.bar };
        forbid(principal is UnauthenticatedUser, action, resource) when { resource.requiresAuthentication };
        @foo("bar")
        permit(principal, action in [Action::"1", Action::"2"], resource) when { ["a", "b", "c"].contains(resource.type) };
        permit(principal == ?principal, action, resource) when { resource.eligibility > 2 };
    "#).unwrap();
    policyset
        .link(
            ast::PolicyID::from_string("policy3"),
            ast::PolicyID::from_string("linkedpolicy"),
            HashMap::from_iter([(
                ast::SlotId::principal(),
                ast::EntityUID::with_eid_and_type("User", "alice").unwrap(),
            )]),
        )
        .unwrap();
    encode_policyset("policyset.protodata", &policyset);

    // regression test for #500: a policyset with only templates, no static or linked policies
    let policyset: ast::PolicySet = parse_policyset(r#"
        permit(principal == ?principal, action, resource);
    "#).unwrap();
    encode_policyset("policyset_just_templates.protodata", &policyset);

    // regression test for #505: a policyset with exactly one static policy, with id "" (empty string)
    let policy: ast::StaticPolicy = parse_policy(Some(ast::PolicyID::from_string("")), r#"
        permit(principal, action, resource) when { true };
    "#).unwrap();
    let mut policyset = ast::PolicySet::new();
    policyset.add_static(policy).unwrap();
    encode_policyset("policyset_one_static_policy.protodata", &policyset);

    encode_request(
        "request.protodata",
        &ast::Request::new(
            (
                ast::EntityUID::with_eid_and_type("User", "alice").unwrap(),
                None,
            ),
            (
                ast::EntityUID::with_eid_and_type("Action", "access").unwrap(),
                Some(Loc::new(2..5, "source code".into())),
            ),
            (
                ast::EntityUID::with_eid_and_type("Folder", "data").unwrap(),
                None,
            ),
            ast::Context::from_pairs(
                [("foo".into(), ast::RestrictedExpr::val(true))],
                Extensions::all_available(),
            )
            .unwrap(),
            None::<&ast::RequestSchemaAllPass>,
            Extensions::all_available(),
        )
        .unwrap(),
    );

    encode_entity(
        "entity.protodata",
        &ast::Entity::new(
            ast::EntityUID::from_components(
                ast::EntityType::from_normalized_str("A::B").unwrap(),
                ast::Eid::new("C"),
                None,
            ),
            [
                ("foo".into(), "[1, -1]".parse().unwrap()),
                ("bar".into(), ast::RestrictedExpr::val(false)),
            ],
            HashSet::from_iter([
                ast::EntityUID::with_eid_and_type("Parent", "1").unwrap(),
                ast::EntityUID::with_eid_and_type("Grandparent", "A").unwrap(),
            ]),
            [
                ("tag1".into(), ast::RestrictedExpr::val("val1")),
                ("tag2".into(), ast::RestrictedExpr::val("val2")),
            ],
            Extensions::all_available(),
        )
        .unwrap(),
    );

    encode_entities(
        "entities.protodata",
        &entities::Entities::from_entities(
            [
                ast::Entity::with_uid(ast::EntityUID::with_eid_and_type("ABC", "123").unwrap()),
                ast::Entity::with_uid(ast::EntityUID::with_eid_and_type("DEF", "234").unwrap()),
            ],
            None::<&entities::AllEntitiesNoAttrsSchema>,
            entities::TCComputation::ComputeNow,
            Extensions::all_available(),
        )
        .unwrap(),
    );

    let primitive_bool = validator_types::Type::Primitive {
        primitive_type: validator_types::Primitive::Bool,
    };
    let primitive_long = validator_types::Type::Primitive {
        primitive_type: validator_types::Primitive::Long,
    };
    let primitive_string = validator_types::Type::Primitive {
        primitive_type: validator_types::Primitive::String,
    };

    encode_val_type("type_true.protodata", &validator_types::Type::True);
    encode_val_type("type_false.protodata", &validator_types::Type::False);
    encode_val_type("type_bool.protodata", &primitive_bool);
    encode_val_type("type_long.protodata", &primitive_long.clone());
    encode_val_type("type_string.protodata", &primitive_string.clone());
    encode_val_type(
        "type_set_of_string.protodata",
        &validator_types::Type::Set {
            element_type: Some(Box::new(primitive_string.clone())),
        },
    );
    encode_val_type(
        "type_ip.protodata",
        &validator_types::Type::ExtensionType {
            name: ast::Name::parse_unqualified_name("ipaddr").unwrap(),
        },
    );
    encode_val_type(
        "type_record.protodata",
        &validator_types::Type::EntityOrRecord(validator_types::EntityRecordKind::Record {
            attrs: validator_types::Attributes {
                attrs: BTreeMap::from_iter([
                    (
                        "ham".into(),
                        validator_types::AttributeType::required_attribute(
                            primitive_string.clone(),
                        ),
                    ),
                    (
                        "eggs".into(),
                        validator_types::AttributeType::optional_attribute(primitive_long.clone()),
                    ),
                ]),
            },
            open_attributes: validator_types::OpenTag::ClosedAttributes,
        }),
    );

    encode_schema(
        "schema_basic.protodata",
        r#"
        entity A;
        entity B in A;
        action Read, Write;
        action ReadX in Read appliesTo {
            principal: [A],
            resource: [A, B],
        };
    "#,
    );

    encode_schema(
        "schema_attrs.protodata",
        r#"
        entity A, B;
        entity C {
            a: Bool,
            b: Long,
            c?: String,
            d: A,
            e: Set<B>,
            f: ipaddr,
            g: { ham: String, eggs?: Long, owner: C },
        };
        action Read, Write;
        action ReadX in Read appliesTo {
            principal: [A, B],
            resource: [B, C],
            context: {
                a: String,
                b?: B,
                c: Set<A>,
                d: decimal,
                e: { ham?: Bool, eggs: Long, manager: B },
            },
        };
        "#,
    );

    encode_schema(
        "schema_commontypes.protodata",
        r#"
        entity A, B, C;
        type Z = String;
        type Y = Set<C>;
        entity F in [A, B] { z: Z, y?: Set<Y> };
        action Read appliesTo {
            principal: [A, B],
            resource: [C],
            context: {
                a?: { z?: Z, y: { foo: Y } },
                y: Y,
            },
        };
        "#,
    );

    encode_schema(
        "schema_tags.protodata",
        r#"
        entity A, B;
        entity C tags String;
        entity D in B tags Set<String>;
        entity E tags Set<A>;

        type Z = String;
        entity F in [A, B] { z: Set<Z> } tags Z;
    "#,
    );
}
