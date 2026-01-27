use cedar_policy::{Context, EntityUid, Policy, RestrictedExpression, SlotId};
use cedar_policy::{
    Entities, Entity, Expression, PolicyId, PolicySet, Request, Schema, proto::traits::Protobuf,
};
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::str::FromStr;

fn output_dir() -> PathBuf {
    std::env::var("OUTPUT_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|_| PathBuf::from_str(".").unwrap())
}

#[track_caller]
fn encode_expr(path: impl AsRef<Path>, e: &str) {
    let expr: Expression = e.parse().unwrap();
    let encoded = expr.encode();
    std::fs::write(output_dir().join(path.as_ref()), encoded).unwrap();
}

#[track_caller]
fn encode_policyset(path: impl AsRef<Path>, ps: &PolicySet) {
    let encoded = ps.encode();
    std::fs::write(output_dir().join(path.as_ref()), encoded).unwrap();
}

#[track_caller]
fn encode_request(path: impl AsRef<Path>, r: &Request) {
    let encoded = r.encode();
    std::fs::write(output_dir().join(path.as_ref()), encoded).unwrap();
}

#[track_caller]
fn encode_entity(path: impl AsRef<Path>, e: &Entity) {
    let encoded = e.encode();
    std::fs::write(output_dir().join(path.as_ref()), encoded).unwrap();
}

#[track_caller]
fn encode_entities(path: impl AsRef<Path>, es: &Entities) {
    let encoded = es.encode();
    std::fs::write(output_dir().join(path.as_ref()), encoded).unwrap();
}

#[track_caller]
fn encode_schema(path: impl AsRef<Path>, s: &str) {
    let (schema, warnings) = Schema::from_cedarschema_str(s)
        .map_err(|e| format!("{:?}", miette::Report::new(e)))
        .unwrap();
    assert_eq!(warnings.count(), 0);
    let encoded = schema.encode();
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

    encode_policyset(
        "rbac.protodata",
        &PolicySet::from_str(
            r#"permit(principal == User::"a b c", action, resource is App::Widget);"#,
        )
        .unwrap(),
    );
    encode_policyset(
        "abac.protodata",
        &PolicySet::from_str(r#"permit(principal, action, resource) when { principal == resource.owner } unless { resource.sensitive };"#).unwrap(),
    );

    let mut policyset = PolicySet::from_str(r#"
        permit(principal, action == Action::"do", resource == Blob::"thing") when { context.foo - 7 == context.bar };
        forbid(principal is UnauthenticatedUser, action, resource) when { resource.requiresAuthentication };
        @foo("bar")
        permit(principal, action in [Action::"1", Action::"2"], resource) when { ["a", "b", "c"].contains(resource.type) };
        permit(principal == ?principal, action, resource) when { resource.eligibility > 2 };
    "#).unwrap();
    policyset
        .link(
            PolicyId::from_str("policy3").unwrap(),
            PolicyId::from_str("linkedpolicy").unwrap(),
            HashMap::from_iter([(
                SlotId::principal(),
                EntityUid::from_type_name_and_id("User".parse().unwrap(), "alice".parse().unwrap()),
            )]),
        )
        .unwrap();
    encode_policyset("policyset.protodata", &policyset);

    // regression test for #500: a policyset with only templates, no static or linked policies
    encode_policyset(
        "policyset_just_templates.protodata",
        &PolicySet::from_str(
            r#"
        permit(principal == ?principal, action, resource);
    "#,
        )
        .unwrap(),
    );

    // regression test for #505: a policyset with exactly one static policy, with id "" (empty string)
    let policy = Policy::parse(
        Some(PolicyId::from_str("").unwrap()),
        r#"
        permit(principal, action, resource) when { true };
    "#,
    )
    .unwrap();
    let policyset = PolicySet::from_policies([policy]).unwrap();
    encode_policyset("policyset_one_static_policy.protodata", &policyset);

    encode_request(
        "request.protodata",
        &Request::new(
            EntityUid::from_type_name_and_id("User".parse().unwrap(), "alice".parse().unwrap()),
            EntityUid::from_type_name_and_id("Action".parse().unwrap(), "access".parse().unwrap()),
            EntityUid::from_type_name_and_id("Folder".parse().unwrap(), "data".parse().unwrap()),
            Context::from_pairs([("foo".into(), RestrictedExpression::new_bool(true))]).unwrap(),
            None,
        )
        .unwrap(),
    );

    encode_entity(
        "entity.protodata",
        &Entity::new_with_tags(
            EntityUid::from_type_name_and_id("A::B".parse().unwrap(), "C".parse().unwrap()),
            [
                ("foo".into(), "[1, -1]".parse().unwrap()),
                ("bar".into(), RestrictedExpression::new_bool(false)),
            ],
            [
                EntityUid::from_type_name_and_id("Parent".parse().unwrap(), "1".parse().unwrap()),
                EntityUid::from_type_name_and_id(
                    "Grandparent".parse().unwrap(),
                    "A".parse().unwrap(),
                ),
            ],
            [
                (
                    "tag1".into(),
                    RestrictedExpression::new_string("val1".into()),
                ),
                (
                    "tag2".into(),
                    RestrictedExpression::new_string("val2".into()),
                ),
            ],
        )
        .unwrap(),
    );

    encode_entities(
        "entities.protodata",
        &Entities::from_entities(
            [
                Entity::with_uid(EntityUid::from_type_name_and_id(
                    "ABC".parse().unwrap(),
                    "123".parse().unwrap(),
                )),
                Entity::with_uid(EntityUid::from_type_name_and_id(
                    "DEF".parse().unwrap(),
                    "234".parse().unwrap(),
                )),
            ],
            None,
        )
        .unwrap(),
    );

    encode_schema("type_bool.protodata", "entity E { attr: Bool };");
    encode_schema("type_long.protodata", "entity E { attr: Long };");
    encode_schema("type_string.protodata", "entity E { attr: String };");
    encode_schema(
        "type_set_of_string.protodata",
        "entity E { attr: Set<String> };",
    );
    encode_schema("type_ip.protodata", "entity E { attr: ipaddr };");
    encode_schema(
        "type_record.protodata",
        "entity E { attr: { ham: String, eggs?: Long } };",
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
