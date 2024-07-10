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

use std::collections::HashMap;

use crate::schema_grammar::*;
use crate::settings::ABACSettings;
use crate::size_hint_utils::{size_hint_for_choose, size_hint_for_range, size_hint_for_ratio};
use crate::uniform;
use arbitrary::{self, Arbitrary, Error, Unstructured};
use serde::Serialize;
use serde_json::json;

#[derive(Serialize, Arbitrary, Debug)]
pub struct PolicyJson {
    effect: Effect,
    principal: Principal,
    action: Action,
    resource: Resource,
    conditions: Conditions,
    annotations: Option<Annotations>,
}

#[derive(Serialize, Arbitrary, Debug)]
enum Effect {
    Permit,
    Forbid,
}

#[derive(Serialize, Arbitrary, Debug)]
struct Principal {
    op: PrincipalOp,
    entity: Option<Entity>,
    slot: Option<Slot>,
    entity_type: Option<String>,
    in_entity: Option<InEntity>,
}

#[derive(Serialize, Arbitrary, Debug)]
enum PrincipalOp {
    All,
    Equal,
    In,
    Is,
}

#[derive(Serialize, Arbitrary, Debug)]
struct Entity {
    type_: String,
    id: String,
}

#[derive(Serialize, Arbitrary, Debug)]
struct Slot {
    name: String,
}

#[derive(Serialize, Arbitrary, Debug)]
struct InEntity {
    entity: Option<Entity>,
    slot: Option<Slot>,
}

#[derive(Serialize, Arbitrary, Debug)]
struct Action {
    op: ActionOp,
    entity: Option<Entity>,
    entities: Option<Vec<Entity>>,
}

#[derive(Serialize, Arbitrary, Debug)]
enum ActionOp {
    All,
    Equal,
    In,
}

#[derive(Serialize, Arbitrary, Debug)]
struct Resource {
    op: ResourceOp,
    entity: Option<Entity>,
    slot: Option<Slot>,
    entity_type: Option<String>,
    in_entity: Option<InEntity>,
}

#[derive(Serialize, Arbitrary, Debug)]
enum ResourceOp {
    All,
    Equal,
    In,
    Is,
}

#[derive(Serialize, Arbitrary, Debug)]
struct Conditions {
    kind: ConditionKind,
    body: JsonExpr, // We'll define JsonExpr later
}

#[derive(Serialize, Arbitrary, Debug)]
enum ConditionKind {
    When,
    Unless,
}

#[derive(Serialize, Arbitrary, Debug)]
struct Annotations {
    annotations: HashMap<String, String>,
}

#[derive(Serialize, Arbitrary, Debug)]
enum JsonExpr {
    Value(Value),
    Var(Var),
    Slot(Slot),
    Unknown(String),
    Not(Box<JsonExpr>),
    BinaryOp {
        op: BinaryOp,
        left: Box<JsonExpr>,
        right: Box<JsonExpr>,
    },
    Dot {
        left: Box<JsonExpr>,
        attr: String,
    },
    Has {
        left: Box<JsonExpr>,
        attr: String,
    },
    Is {
        left: Box<JsonExpr>,
        entity_type: String,
        in_expr: Option<Box<JsonExpr>>,
    },
    Like {
        left: Box<JsonExpr>,
        pattern: String,
    },
    IfThenElse {
        if_expr: Box<JsonExpr>,
        then_expr: Box<JsonExpr>,
        else_expr: Box<JsonExpr>,
    },
    Set(Vec<JsonExpr>),
    Record(HashMap<String, JsonExpr>),
    Extension(String, Vec<JsonExpr>),
}

#[derive(Serialize, Arbitrary, Debug)]
enum Value {
    Literal(String),
    Entity(Entity),
    Set(Vec<JsonExpr>),
    Record(HashMap<String, JsonExpr>),
}

#[derive(Serialize, Arbitrary, Debug)]
enum Var {
    Principal,
    Action,
    Resource,
    Context,
}

#[derive(Serialize, Arbitrary, Debug)]
enum BinaryOp {
    Equal,
    NotEqual,
    In,
    LessThan,
    LessThanEqual,
    GreaterThan,
    GreaterThanEqual,
    And,
    Or,
    Add,
    Subtract,
    Multiply,
    Contains,
    ContainsAll,
    ContainsAny,
}

pub fn arbitrary_policy_str(
    settings: &ABACSettings,
    u: &mut Unstructured<'_>,
) -> Result<String, Error> {
    let annotation = arbitrary_annotation_str(settings, u)?;
    let effect = arbitrary_effect_str(settings, u)?;
    let scope = arbitrary_scope_str(settings, u)?;
    // TODO: implement
    let conditions = String::from("true");

    Ok(format!(
        r#"{{{}}}{}({}){};"#,
        annotation, effect, scope, conditions
    ))
}

pub fn arbitrary_annotation_str(
    settings: &ABACSettings,
    u: &mut Unstructured<'_>,
) -> Result<String, Error> {
    Ok(format!(
        r#"@{}({})"#,
        arbitrary_ident_str(settings, u)?,
        arbitrary_str(settings, u)?,
    ))
}

pub fn arbitrary_effect_str(
    settings: &ABACSettings,
    u: &mut Unstructured<'_>,
) -> Result<String, Error> {
    Ok(format!(r#"{}"#, u.choose(&["permit", "forbid"])?,))
}

pub fn arbitrary_scope_str(
    settings: &ABACSettings,
    u: &mut Unstructured<'_>,
) -> Result<String, Error> {
    let principal = arbitrary_principal_str(settings, u)?;
    let action = arbitrary_action_str(settings, u)?;
    let resource = arbitrary_resource_str(settings, u)?;

    Ok(format!(r#"{},{},{}"#, principal, action, resource))
}

pub fn arbitrary_principal_str(
    settings: &ABACSettings,
    u: &mut Unstructured<'_>,
) -> Result<String, Error> {
    let mut output: String = "principal".to_string();
    if u.ratio(1, 2)? {
        if u.ratio(1, 2)? {
            let path = arbitrary_path_str(settings, u)?;
            output.push_str(&format!(r#" {} {}"#, "is", path));
            if u.ratio(1, 2)? {
                let mut entity = String::from("?principal");
                if u.ratio(1, 2)? {
                    entity = arbitrary_entity_str(settings, u)?;
                }
                output.push_str(&format!(r#" {} {}"#, "in", entity));
            }
        } else {
            let mut entity = String::from("?principal");
            if u.ratio(1, 2)? {
                entity = arbitrary_entity_str(settings, u)?;
            }
            output.push_str(&format!(r#" {} {}"#, "==", entity));
        }
    }
    Ok(output)
}

pub fn arbitrary_path_str(
    settings: &ABACSettings,
    u: &mut Unstructured<'_>,
) -> Result<String, Error> {
    let mut parts = Vec::new();
    let num_parts = u.int_in_range(0..=settings.max_width)? as usize;

    for _ in 0..num_parts {
        parts.push(arbitrary_ident_str(settings, u)?);
    }

    if parts.len() == 0 {
        return Ok("".to_string());
    } else if parts.len() == 1 {
        return Ok(format!("{}", parts[0]));
    }
    Ok(format!("{}", parts.join("::")))
}

pub fn arbitrary_entity_str(
    settings: &ABACSettings,
    u: &mut Unstructured<'_>,
) -> Result<String, Error> {
    Ok(format!(
        "{}::{}",
        arbitrary_path_str(settings, u)?,
        arbitrary_str(settings, u)?
    ))
}

pub fn arbitrary_action_str(
    settings: &ABACSettings,
    u: &mut Unstructured<'_>,
) -> Result<String, Error> {
    Ok(format!(
        "{}::{}",
        arbitrary_path_str(settings, u)?,
        arbitrary_str(settings, u)?
    ))
}

pub fn arbitrary_resource_str(
    settings: &ABACSettings,
    u: &mut Unstructured<'_>,
) -> Result<String, Error> {
    let mut output: String = "principal".to_string();
    if u.ratio(1, 2)? {
        if u.ratio(1, 2)? {
            let path = arbitrary_path_str(settings, u)?;
            output.push_str(&format!(r#" {} {}"#, "is", path));
            if u.ratio(1, 2)? {
                let mut entity = String::from("?principal");
                if u.ratio(1, 2)? {
                    entity = arbitrary_entity_str(settings, u)?;
                }
                output.push_str(&format!(r#" {} {}"#, "in", entity));
            }
        } else {
            let mut entity = String::from("?principal");
            if u.ratio(1, 2)? {
                entity = arbitrary_entity_str(settings, u)?;
            }
            output.push_str(&format!(r#" {} {}"#, "==", entity));
        }
    }
    Ok(output)
}
