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

use crate::settings::ABACSettings;
use crate::size_hint_utils::{size_hint_for_choose, size_hint_for_range, size_hint_for_ratio};
use crate::uniform;
use arbitrary::{self, Error, Unstructured};
use serde_json::json;

pub fn arbitrary_str(settings: &ABACSettings, u: &mut Unstructured<'_>) -> Result<String, Error> {
    let width = u.int_in_range(1..=settings.max_width)?;
    let mut s = String::with_capacity(width);
    for _ in 0..width {
        let c = u.arbitrary()?;
        s.push(c);
    }
    Ok(format!("{}", json!(s)))
}

pub fn arbitrary_namespace_str(
    settings: &ABACSettings,
    u: &mut Unstructured,
) -> Result<String, Error> {
    let mut parts = Vec::new();
    let num_parts = u.int_in_range(0..=settings.max_width)? as usize;

    for _ in 0..num_parts {
        parts.push(arbitrary_ident_str(settings, u)?);
    }

    if parts.len() == 0 {
        return Ok("\"\"".to_string());
    } else if parts.len() == 1 {
        return Ok(format!("\"{}\"", parts[0]));
    }
    Ok(format!("\"{}\"", parts.join("::")))
}

pub fn arbitrary_ident_str(
    settings: &ABACSettings,
    u: &mut arbitrary::Unstructured<'_>,
) -> Result<String, Error> {
    // identifier syntax:
    // IDENT     := ['_''a'-'z''A'-'Z']['_''a'-'z''A'-'Z''0'-'9']* - RESERVED
    // BOOL      := 'true' | 'false'
    // RESERVED  := BOOL | 'if' | 'then' | 'else' | 'in' | 'is' | 'like' | 'has'

    let construct_list = |s: &str| s.chars().collect::<Vec<char>>();
    let list_concat = |s1: &[char], s2: &[char]| [s1, s2].concat();
    // the set of the first character of an identifier
    let head_letters = construct_list("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz_");
    // the set of the remaining characters of an identifier
    let tail_letters = list_concat(&construct_list("0123456789"), &head_letters);
    // identifier character count minus 1
    let remaining_length = u.int_in_range(0..=settings.max_width - 1)?;
    let mut cs = vec![*u.choose(&head_letters)?];
    cs.extend(
        (0..remaining_length)
            .map(|_| u.choose(&tail_letters))
            .collect::<Result<Vec<&char>, _>>()
            .unwrap(),
    );
    let mut s: String = cs.into_iter().collect();
    // Should the parsing fails, the string should be reserved word.
    // Append a `_` to create a valid Id.
    if s == "true"
        || s == "false"
        || s == "if"
        || s == "then"
        || s == "else"
        || s == "in"
        || s == "is"
        || s == "like"
        || s == "has"
    {
        s.push('_');
    }
    Ok(s)
}

pub fn arbitrary_primitive(u: &mut Unstructured<'_>) -> Result<String, Error> {
    let primitive_types = &[
        r#""type":"Long""#,
        r#""type":"String""#,
        r#""type":"Boolean""#,
    ];
    let primitive_type = u.choose(primitive_types)?;

    Ok(format!(r#"{}"#, primitive_type))
}

pub fn arbitrary_extension(
    settings: &ABACSettings,
    u: &mut Unstructured<'_>,
) -> Result<String, Error> {
    Ok(format!(
        r#""type":"Extension","name":{}"#,
        arbitrary_str(settings, u)?
    ))
}

pub fn arbitrary_entity_types_str(
    settings: &ABACSettings,
    u: &mut Unstructured<'_>,
    entity_type: &str,
) -> Result<String, Error> {
    let num_idents = u.int_in_range(0..=settings.max_width)?;
    let mut idents = Vec::with_capacity(num_idents);

    if num_idents == 0 {
        return Ok(format!(r#""{}":[]"#, entity_type));
    }
    for _ in 0..num_idents {
        idents.push(arbitrary_ident_str(settings, u)?);
    }

    Ok(format!(r#""{}":["{}"]"#, entity_type, idents.join("\",\"")))
}

pub fn arbitrary_principal_types_str(
    settings: &ABACSettings,
    u: &mut Unstructured<'_>,
) -> Result<String, Error> {
    arbitrary_entity_types_str(settings, u, "principalTypes")
}

pub fn arbitrary_resource_types_str(
    settings: &ABACSettings,
    u: &mut Unstructured<'_>,
) -> Result<String, Error> {
    arbitrary_entity_types_str(settings, u, "resourceTypes")
}

pub fn arbitrary_type(
    settings: &ABACSettings,
    depth: usize,
    u: &mut Unstructured<'_>,
) -> Result<String, Error> {
    if depth == settings.max_depth {
        return arbitrary_primitive(u);
    }
    uniform!(
        u,
        arbitrary_primitive(u),
        arbitrary_set(settings, depth + 1, u),
        arbitrary_entity_ref(settings, u),
        arbitrary_record(settings, depth + 1, u),
        arbitrary_extension(settings, u)
    )
}

pub fn arbitrary_type_json(
    settings: &ABACSettings,
    depth: usize,
    u: &mut Unstructured<'_>,
) -> Result<String, Error> {
    Ok(format!(r#"{{{}}}"#, arbitrary_type(settings, depth, u)?))
}

pub fn arbitrary_context(
    settings: &ABACSettings,
    depth: usize,
    u: &mut Unstructured<'_>,
) -> Result<String, Error> {
    Ok(format!(
        r#""context": {}"#,
        arbitrary_type_json(settings, depth, u)?
    ))
}

pub fn arbitrary_set(
    settings: &ABACSettings,
    depth: usize,
    u: &mut Unstructured<'_>,
) -> Result<String, Error> {
    // Generate a JSON object representing a Set
    Ok(format!(
        r#""type":"Set","element":{}"#,
        arbitrary_type_json(settings, depth, u)?
    ))
}

pub fn arbitrary_entity_ref(
    settings: &ABACSettings,
    u: &mut Unstructured<'_>,
) -> Result<String, Error> {
    // Generate a JSON object representing an EntityRef
    Ok(format!(
        r#""type":"Entity","name":{}"#,
        arbitrary_str(settings, u)?
    ))
}

pub fn arbitrary_record_attr(
    settings: &ABACSettings,
    depth: usize,
    u: &mut Unstructured<'_>,
) -> Result<String, Error> {
    // Generate a JSON object representing a RecordAttr
    let is_required = u.arbitrary().expect("Unable to generate bool");
    Ok(format!(
        r#"{}:{{{}{}}}"#,
        arbitrary_str(settings, u)?,
        arbitrary_type(settings, depth, u)?,
        if is_required {
            r#","required":true"#
        } else {
            r#","required":false"#
        }
    ))
}

pub fn arbitrary_record(
    settings: &ABACSettings,
    depth: usize,
    u: &mut Unstructured<'_>,
) -> Result<String, Error> {
    // Generate a JSON object representing a Record
    let num_attrs = u.int_in_range(0..=settings.max_width)?;
    let mut attrs = Vec::with_capacity(num_attrs);

    for _ in 0..num_attrs {
        attrs.push(arbitrary_record_attr(settings, depth, u)?);
    }

    Ok(format!(
        r#""type":"Record","attributes":{{{}}}"#,
        attrs.join(",")
    ))
}

pub fn arbitrary_action(
    settings: &ABACSettings,
    depth: usize,
    u: &mut Unstructured<'_>,
) -> Result<String, Error> {
    let mut action = format!(r#"{}:{{"#, arbitrary_str(settings, u)?);

    // Generate "memberOf" field
    let num_members = u
        .int_in_range(0..=settings.max_width)
        .expect("Error generating num_members");
    if num_members > 0 {
        let mut members = Vec::with_capacity(num_members as usize);
        for _ in 0..num_members {
            members.push(arbitrary_str(settings, u)?);
        }
        action.push_str(&format!(r#""memberOf":[{}],"#, members.join(",")));
    }

    // Generate "appliesTo" field
    action.push_str(r#""appliesTo":{"#);
    let mut prev_type_exists = false;
    if u.ratio(1, 2)? {
        action.push_str(&arbitrary_principal_types_str(settings, u)?);
        prev_type_exists = true;
    }
    if u.ratio(1, 2)? {
        if prev_type_exists {
            action.push(',');
        }
        prev_type_exists = true;
        action.push_str(&arbitrary_resource_types_str(settings, u)?);
    }
    if u.ratio(1, 2)? {
        if prev_type_exists {
            action.push(',');
        }
        action.push_str(&arbitrary_context(settings, depth, u)?);
    }
    action.push('}');

    action.push('}');
    Ok(action)
}

pub fn arbitrary_actions(
    settings: &ABACSettings,
    depth: usize,
    u: &mut Unstructured<'_>,
) -> Result<String, Error> {
    let num_actions = u
        .int_in_range(0..=settings.max_width)
        .expect("Unable to generate range");
    let mut actions = Vec::with_capacity(num_actions as usize);

    for _ in 0..num_actions {
        actions.push(arbitrary_action(settings, depth, u)?);
    }

    Ok(format!(r#""actions":{{{}}}"#, actions.join(",")))
}

pub fn arbitrary_entity_type(
    settings: &ABACSettings,
    depth: usize,
    u: &mut Unstructured<'_>,
) -> Result<String, Error> {
    let mut entity_type = format!(r#""{}":{{"#, arbitrary_ident_str(settings, u)?);

    // Generate "memberOfTypes" field
    let num_member_types = u
        .int_in_range(0..=settings.max_width)
        .expect("Error generating num_member_types");
    if num_member_types > 0 {
        let mut member_types = Vec::with_capacity(num_member_types as usize);
        for _ in 0..num_member_types {
            member_types.push(arbitrary_ident_str(settings, u)?);
        }
        entity_type.push_str(&format!(
            r#""memberOfTypes":["{}"],"#,
            member_types.join("\",\"")
        ));
    }

    // Generate "shape" field
    entity_type.push_str(&format!(
        r#""shape":{}"#,
        arbitrary_type_json(settings, depth, u)?
    ));

    entity_type.push('}');
    Ok(entity_type)
}

pub fn arbitrary_entity_types(
    settings: &ABACSettings,
    depth: usize,
    u: &mut Unstructured<'_>,
) -> Result<String, Error> {
    let num_entity_types = u.int_in_range(0..=settings.max_width)?;
    let mut entity_types = Vec::with_capacity(num_entity_types as usize);

    for _ in 0..num_entity_types {
        entity_types.push(arbitrary_entity_type(settings, depth, u)?);
    }

    Ok(format!(r#""entityTypes":{{{}}}"#, entity_types.join(",")))
}

pub fn arbitrary_schema_json_str(
    settings: &ABACSettings,
    depth: usize,
    u: &mut Unstructured<'_>,
) -> Result<String, Error> {
    let namespace = arbitrary_namespace_str(settings, u)?;
    let entity_types = arbitrary_entity_types(settings, depth, u)?;
    let actions = arbitrary_actions(settings, depth, u)?;

    Ok(format!(
        r#"{{{}:{{{},{}}}}}"#,
        namespace, entity_types, actions
    ))
}

pub fn arbitrary_schema_human_readable(
    settings: &ABACSettings,
    depth: usize,
    u: &mut Unstructured<'_>,
) -> Result<String, Error> {
    let namespace = arbitrary_namespace_str(settings, u)?;
    let entity_types = arbitrary_entity_types(settings, depth, u)?;
    let actions = arbitrary_actions(settings, depth, u)?;

    Ok(format!(r#"{}:{{{},{}}}"#, namespace, entity_types, actions))
}
