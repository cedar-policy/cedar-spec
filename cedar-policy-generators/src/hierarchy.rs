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

use crate::abac::Type;
use crate::collections::{HashMap, HashSet};
use crate::err::{while_doing, Error, Result};
use crate::schema::{attrs_from_attrs_or_context, Schema};
use crate::size_hint_utils::{size_hint_for_choose, size_hint_for_ratio};
use arbitrary::{Arbitrary, Unstructured};
use cedar_policy_core::ast::{self, Eid, Entity, EntityUID};
use cedar_policy_core::entities::{Entities, NoEntitiesSchema, TCComputation};
use cedar_policy_core::extensions::Extensions;
use cedar_policy_validator::json_schema::{self, EntityTypeKind, StandardEntityType};
use smol_str::SmolStr;

/// EntityUIDs with the mappings to their indices in the container.
/// This is used to generate an entity that is lexicographically smaller/greater than the input entity.
#[derive(Debug, Clone)]
struct EntityUIDs {
    pub indices: HashMap<EntityUID, usize>,
    pub uids: Vec<EntityUID>,
}

impl From<Vec<EntityUID>> for EntityUIDs {
    fn from(value: Vec<EntityUID>) -> Self {
        Self {
            indices: (0..value.len())
                .map(|idx| (value[idx].clone(), idx))
                .collect(),
            uids: value,
        }
    }
}

impl FromIterator<EntityUID> for EntityUIDs {
    fn from_iter<T: IntoIterator<Item = EntityUID>>(iter: T) -> Self {
        let uids: Vec<EntityUID> = iter.into_iter().collect();
        uids.into()
    }
}

impl AsRef<[EntityUID]> for EntityUIDs {
    fn as_ref(&self) -> &[EntityUID] {
        &self.uids
    }
}

impl EntityUIDs {
    // Get a slice of `EntityUID`s whose indices are greater than `uid`'s
    // INVARIANT: `uid` is in `indices`
    fn get_slice_after_uid(&self, uid: &EntityUID) -> &[EntityUID] {
        let idx = self.indices[uid];
        &self.uids[idx + 1..]
    }
}

/// Contains data about an entity hierarchy
#[derive(Debug, Clone)]
pub struct Hierarchy {
    /// maps EntityUID to the corresponding Entity
    entities: HashMap<EntityUID, Entity>,
    /// Vec of UIDs in the hierarchy, which we keep in sync with the `entities`
    /// HashMap.
    /// The reason we have this separately is that is allows us to do
    /// arbitrary_uid() fast.
    uids: Vec<EntityUID>,
    /// Map of entity typename to UID, for all UIDs in the hierarchy.
    /// We keep this in sync with the `entities` HashMap too.
    /// This is to make arbitrary_uid_with_type() fast.
    uids_by_type: HashMap<ast::EntityType, EntityUIDs>,
    /// Vec of all entity types used by entities in the hierarchy, again kept in
    /// sync with the `entities` HashMap. Makes `arbitrary_entity_type()` fast.
    entity_types: Vec<ast::EntityType>,
}

impl Hierarchy {
    /// Create a new `Hierarchy` from the given UIDs, sorted by type (in a
    /// `HashMap` of entity typename to UID). The entities will have no
    /// attributes or parents.
    pub fn from_uids_by_type(uids_by_type: HashMap<ast::EntityType, HashSet<EntityUID>>) -> Self {
        let uids: Vec<EntityUID> = uids_by_type
            .values()
            .flat_map(|uids_inner| uids_inner.iter().cloned())
            .collect();
        let uids_by_type: HashMap<_, _> = uids_by_type
            .into_iter()
            .map(|(n, uids)| (n, EntityUIDs::from_iter(uids)))
            .collect();
        let entity_types: Vec<_> = uids_by_type.keys().cloned().collect();
        Self {
            entities: uids
                .iter()
                .map(|uid| (uid.clone(), Entity::with_uid(uid.clone())))
                .collect(),
            uids,
            uids_by_type,
            entity_types,
        }
    }

    /// Generate an arbitrary uid based on the hierarchy. If `request_field`
    /// is `Some(var)` then the generated uid may be unspecified with eid `var`.
    /// Otherwise, the uid is guaranteed to be specified.
    pub fn arbitrary_uid(
        &self,
        u: &mut Unstructured<'_>,
        request_field: Option<ast::Var>,
    ) -> Result<EntityUID> {
        // UID that exists or doesn't. 90% of the time pick one that exists
        if u.ratio::<u8>(9, 10)? {
            let uid = u
                .choose(&self.uids)
                .map_err(|e| while_doing("getting an arbitrary uid".into(), e))?;
            Ok(uid.clone())
        } else {
            match request_field {
                Some(_) => {
                    let uid: EntityUID = u.arbitrary()?;
                    Ok(uid)
                }
                None => arbitrary_specified_uid(u).map_err(Into::into),
            }
        }
    }
    /// size hint for arbitrary_uid()
    pub fn arbitrary_uid_size_hint(depth: usize) -> (usize, Option<usize>) {
        arbitrary::size_hint::and(
            size_hint_for_ratio(9, 10),
            arbitrary::size_hint::or(
                // exists case
                size_hint_for_choose(None),
                // not-exists case; both branches should lead to a similar cost
                <EntityUID as Arbitrary>::size_hint(depth),
            ),
        )
    }

    /// generate an arbitrary uid based on the hierarchy, with the given typename
    pub fn arbitrary_uid_with_type(
        &self,
        typename: &ast::EntityType,
        u: &mut Unstructured<'_>,
    ) -> Result<EntityUID> {
        // UID that exists or doesn't. 90% of the time pick one that exists
        if u.ratio::<u8>(9, 10)? {
            let uid = u.choose(
                self.uids_by_type
                    .get(typename)
                    .ok_or(Error::EmptyChoose {
                        doing_what: format!("getting an existing uid with type {typename}"),
                    })?
                    .as_ref(),
            )?;
            Ok(uid.clone())
        } else {
            Ok(EntityUID::from_components(
                typename.clone(),
                u.arbitrary()?,
                None,
            ))
        }
    }
    /// size hint for arbitrary_uid_with_type()
    pub fn arbitrary_uid_with_type_size_hint(depth: usize) -> (usize, Option<usize>) {
        arbitrary::size_hint::and(
            size_hint_for_ratio(9, 10),
            arbitrary::size_hint::or(
                size_hint_for_choose(None),
                <Eid as Arbitrary>::size_hint(depth),
            ),
        )
    }

    /// Generate an entity type, usually picking on that's used by some entity in
    /// the hierarchy.
    pub fn arbitrary_entity_type(&self, u: &mut Unstructured<'_>) -> Result<ast::EntityType> {
        // entity type that is used by some entity or isn't. 90% of the time
        // pick one that is used.
        if u.ratio::<u8>(9, 10)? {
            let ety = u.choose(&self.entity_types)?;
            Ok(ety.clone())
        } else {
            Ok(u.arbitrary()?)
        }
    }

    /// Get an Entity object by UID
    pub fn entity(&self, uid: &EntityUID) -> Option<&Entity> {
        self.entities.get(uid)
    }

    /// Get an Entity object by UID, mutable
    pub fn entity_mut(&mut self, uid: &EntityUID) -> Option<&mut Entity> {
        self.entities.get_mut(uid)
    }

    /// How many entities (UIDs) are in the hierarchy
    pub fn num_entities(&self) -> usize {
        self.uids.len()
    }

    /// Iterate over the Hierarchy's `Entity` objects
    pub fn entities(&self) -> impl Iterator<Item = &Entity> {
        self.entities.values()
    }

    /// Iterate over the Hierarchy's `Entity` objects, mutably
    pub fn entities_mut(&mut self) -> impl Iterator<Item = &mut Entity> {
        self.entities.values_mut()
    }

    /// Consume the Hierarchy and create an iterator over its Entity objects
    pub fn into_entities(self) -> impl Iterator<Item = Entity> {
        self.entities.into_values()
    }

    /// Get the list of UIDs in the Hierarchy, as a slice
    pub fn uids(&self) -> &[EntityUID] {
        &self.uids
    }

    /// Consume the Hierarchy and return a new one, which replaces the entities
    /// with a new set of entities.
    ///
    /// IMPORTANT: To avoid violating internal invariants, the new set of
    /// entities must have exactly the same UIDs as the old one, with no
    /// entities added or removed.  All that is allowed to change is the entity
    /// data attached to each UID.
    //
    // The main benefit of offering this method vs making callers use a more
    // generic constructor is that we can move the data structures `uids` and
    // `uids_by_type` rather than cloning or reconstructing them.
    pub fn replace_entities(self, new_entities: HashMap<EntityUID, Entity>) -> Self {
        Self {
            entities: new_entities,
            uids: self.uids,
            uids_by_type: self.uids_by_type,
            entity_types: self.entity_types,
        }
    }

    /// Iterate over the UIDs having the given typename
    /// Also ensure that the returned UIDs is lexicographically larger than the input `EntityUID` if its type is the same as the given typename
    pub fn uids_for_type(
        &self,
        dst_ty: &ast::EntityType,
        entity: &EntityUID,
    ) -> Box<dyn Iterator<Item = &EntityUID> + '_> {
        match self.uids_by_type.get(dst_ty) {
            Some(v) => {
                if entity.entity_type().to_string() == dst_ty.to_string() {
                    Box::new(v.get_slice_after_uid(entity).iter())
                } else {
                    Box::new(v.as_ref().iter())
                }
            }
            None => Box::new(std::iter::empty()),
        }
    }
}

impl TryFrom<Hierarchy> for Entities {
    type Error = String;
    fn try_from(h: Hierarchy) -> std::result::Result<Entities, String> {
        Entities::from_entities(
            h.into_entities().map(Into::into),
            None::<&NoEntitiesSchema>,
            TCComputation::ComputeNow,
            Extensions::all_available(),
        )
        .map_err(|e| e.to_string())
    }
}

impl From<Entities> for Hierarchy {
    fn from(entities: Entities) -> Hierarchy {
        let mut uids = Vec::new();
        let mut uids_by_type: HashMap<ast::EntityType, HashSet<&ast::EntityUID>> = HashMap::new();
        for e in entities.iter() {
            let etype = e.uid().entity_type().clone();
            uids_by_type.entry(etype).or_default().insert(e.uid());
            uids.push(e.uid().clone());
        }
        let entity_types: Vec<_> = uids_by_type.keys().cloned().collect();
        Hierarchy {
            uids,
            uids_by_type: uids_by_type
                .into_iter()
                .map(|(k, v)| (k, EntityUIDs::from_iter(v.into_iter().cloned())))
                .collect(),
            entities: entities.into_iter().map(|e| (e.uid().clone(), e)).collect(),
            entity_types,
        }
    }
}

/// Struct for generating hierarchies; contains options and settings
pub struct HierarchyGenerator<'a, 'u> {
    /// Mode for hierarchy generation, e.g., whether to conform to a schema
    pub mode: HierarchyGeneratorMode<'a>,
    /// How many entities to generate for the hierarchy
    pub num_entities: NumEntities,
    /// `Unstructured` used for making random choices
    pub u: &'a mut Unstructured<'u>,
    /// Extensions active for the attribute values in the hierarchy
    pub extensions: &'a Extensions<'a>,
}

// can't auto-derive `Debug` because of the `Unstructured`
impl<'a, 'u> std::fmt::Debug for HierarchyGenerator<'a, 'u> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        <HierarchyGeneratorMode<'a> as std::fmt::Debug>::fmt(&self.mode, f)?;
        <NumEntities as std::fmt::Debug>::fmt(&self.num_entities, f)?;
        Ok(())
    }
}

/// Modes of hierarchy generation
#[derive(Debug)]
pub enum HierarchyGeneratorMode<'a> {
    /// The generated `Hierarchy` will conform to this `Schema`.
    SchemaBased {
        /// Schema that the generated `Hierarchy` will conform to
        schema: &'a Schema,
    },
    /// The generated `Hierarchy` will be fully arbitrary
    Arbitrary {
        /// Mode for generating attributes (or not)
        attributes_mode: AttributesMode,
    },
}

impl HierarchyGeneratorMode<'_> {
    /// Generate the default arbitrary mode
    pub fn arbitrary_default() -> Self {
        Self::Arbitrary {
            attributes_mode: AttributesMode::NoAttributesOrTags,
        }
    }
}

/// Restrictions (or lack of) on the number of entities in the generated hierarchy
#[derive(Debug)]
pub enum NumEntities {
    /// The hierarchy will contain exactly this many entities, split evenly
    /// across all entity types declared in the schema. If the number here is
    /// not a multiple of the number of entity types, the actual number of
    /// entities may be slightly less than the number here.
    Exactly(usize),
    /// The hierarchy will contain exactly this many entities per entity type.
    ExactlyPerEntityType(usize),
    /// The hierarchy will contain between some min and some max number of
    /// entities (inclusive) per entity type.
    RangePerEntityType(std::ops::RangeInclusive<usize>),
}

/// Settings for generating hierarchy attributes
#[derive(Debug)]
pub enum AttributesMode {
    /// No attributes or tags (RBAC)
    NoAttributesOrTags,
    // For now, we don't support any other modes. Generating attributes is only
    // supported in schema-based mode. If you want arbitrary attributes without
    // a schema, consider first generating an arbitrary schema and then using
    // schema-based mode.
}

/// Helper function to generate an arbitrary UID (but not Unspecified), without
/// regard to an existing schema or hierarchy
pub(crate) fn arbitrary_specified_uid(u: &mut Unstructured<'_>) -> Result<ast::EntityUID> {
    Ok(ast::EntityUID::from_components(
        u.arbitrary::<ast::EntityType>()?,
        u.arbitrary::<ast::Eid>()?,
        None,
    ))
}

/// Helper function that generates a new UID with the given type.
/// Unlike `Hierarchy::arbitrary_uid_with_type()`, this doesn't take a
/// `Hierarchy` parameter and doesn't make any effort to generate a UID that
/// actually exists (yet) in any given hierarchy.
pub(crate) fn generate_uid_with_type(
    ty: ast::EntityType,
    choices: &[SmolStr],
    u: &mut Unstructured<'_>,
) -> Result<ast::EntityUID> {
    let eid = if choices.is_empty() {
        u.arbitrary()?
    } else {
        gen!(u,
         4 => Eid::new(u.choose(choices)?.to_owned()),
         1 => u.arbitrary()?
        )
    };
    Ok(ast::EntityUID::from_components(ty, eid, None))
}

impl<'a, 'u> HierarchyGenerator<'a, 'u> {
    /// Generate a `Hierarchy` according to the specified parameters
    pub fn generate(&mut self) -> Result<Hierarchy> {
        let entity_types = match &self.mode {
            HierarchyGeneratorMode::SchemaBased { schema } => schema.entity_types.clone(),
            HierarchyGeneratorMode::Arbitrary { .. } => {
                // generate a HashSet first to avoid duplicates
                let entity_types: HashSet<ast::EntityType> = self.u.arbitrary()?;
                // Collect into a vector
                entity_types.into_iter().collect()
            }
        };
        // For each entity type, generate entity UIDs of that type
        let uids_by_type: HashMap<ast::EntityType, HashSet<EntityUID>> = entity_types
            .iter()
            .map(|name| {
                let (name, uid_choices) = match &self.mode {
                    HierarchyGeneratorMode::SchemaBased { schema } => (
                        name.qualify_with(schema.namespace()),
                        schema.get_uid_choices(name),
                    ),
                    HierarchyGeneratorMode::Arbitrary { .. } => (name.clone(), vec![]),
                };
                let uids = match &self.num_entities {
                    NumEntities::RangePerEntityType(r) => {
                        let mut uids = HashSet::new();
                        self.u.arbitrary_loop(
                            Some((*r.start()).try_into().unwrap()),
                            Some((*r.end()).try_into().unwrap()),
                            |u| {
                                uids.insert(generate_uid_with_type(name.clone(), &uid_choices, u)?);
                                Ok(std::ops::ControlFlow::Continue(()))
                            },
                        )?;
                        uids
                    }
                    NumEntities::ExactlyPerEntityType(num_entities_per_type) => {
                        // generate `num_entities` entity UIDs of this type
                        (1..=*num_entities_per_type)
                            .map(|_| generate_uid_with_type(name.clone(), &uid_choices, self.u))
                            .collect::<Result<_>>()?
                    }
                    NumEntities::Exactly(num_entities) => {
                        // generate a fixed number of entity UIDs of this type
                        let num_entities_per_type = num_entities / entity_types.len();
                        let mut uids = HashSet::new();
                        while uids.len() < num_entities_per_type {
                            // If we run out of bytes in `u`, then `uid` will be the same on every
                            // subsequent iteration, so the size of `uids` won't increase.
                            if self.u.is_empty() {
                                return Err(Error::NotEnoughData);
                            }
                            let uid = generate_uid_with_type(name.clone(), &uid_choices, self.u)?;
                            uids.insert(uid);
                        }
                        uids
                    }
                };
                Ok((name, uids))
            })
            .collect::<Result<HashMap<ast::EntityType, HashSet<ast::EntityUID>>>>()?;
        let hierarchy_no_attrs = Hierarchy::from_uids_by_type(uids_by_type);
        let entitytypes_by_type: Option<
            HashMap<ast::EntityType, &json_schema::EntityType<ast::InternalName>>,
        > = match &self.mode {
            HierarchyGeneratorMode::SchemaBased { schema } => Some(
                schema
                    .schema
                    .entity_types
                    .iter()
                    .map(|(name, et)| {
                        (
                            ast::EntityType::from(ast::Name::from(name.clone()))
                                .qualify_with(schema.namespace.as_ref()),
                            et,
                        )
                    })
                    .collect(),
            ),
            HierarchyGeneratorMode::Arbitrary { .. } => None,
        };
        // now create an entity hierarchy composed of those entity UIDs
        let entities = hierarchy_no_attrs
            .entities()
            .map(|e| e.uid())
            .map(|uid| {
                let name = uid.entity_type();
                // choose parents for this entity
                let mut parents = HashSet::new();
                match &self.mode {
                    HierarchyGeneratorMode::SchemaBased { schema } => {
                        // we have schema data. Choose parents of appropriate types.
                        let Some(entitytypes_by_type) = &entitytypes_by_type else {
                            unreachable!("in schema-based mode, this should always be Some")
                        };
                        for allowed_parent_typename in match &entitytypes_by_type
                            .get(name)
                            .expect("typename should have an EntityType").kind
                            {
                                json_schema::EntityTypeKind::Standard(StandardEntityType { member_of_types, ..} ) => member_of_types.clone(),
                                json_schema::EntityTypeKind::Enum { .. } => vec![]
                            }
                        {
                            let allowed_parent_typename = ast::Name::try_from(
                                allowed_parent_typename
                                    .qualify_with_name(schema.namespace.as_ref()),
                            )
                            .unwrap()
                            .into();
                            for possible_parent_uid in
                                // `uids_for_type` only prevent cycles resulting from self-loops in the entity types graph
                                // It should be very unlikely where loops involving multiple entity types occur in the schemas
                                hierarchy_no_attrs
                                    .uids_for_type(&allowed_parent_typename, uid)
                            {
                                if self.u.ratio::<u8>(1, 2)? {
                                    parents.insert(possible_parent_uid.clone());
                                }
                            }
                        }
                    }
                    HierarchyGeneratorMode::Arbitrary { .. } => {
                        // no schema data.
                        // for each uid in the pool, flip a weighted coin to decide whether
                        // to add it as a parent. We only consider uids appearing after the
                        // given one in the pool; this ensures we get a DAG (no cycles)
                        // without loss of generality
                        let this_idx = hierarchy_no_attrs
                            .uids()
                            .iter()
                            .position(|x| x == uid)
                            .expect("uid should be in the pool");
                        for pool_uid in &hierarchy_no_attrs.uids()[(this_idx + 1)..] {
                            if self.u.ratio(1, 3)? {
                                parents.insert(pool_uid.clone());
                            }
                        }
                        // assert there is no self-edge
                        assert!(!parents.contains(uid));
                    }
                }
                // generate appropriate attributes for this entity
                let mut attrs = HashMap::new();
                match &self.mode {
                    HierarchyGeneratorMode::Arbitrary {
                        attributes_mode: AttributesMode::NoAttributesOrTags,
                    } => {
                        // don't add any attributes
                    }
                    HierarchyGeneratorMode::SchemaBased { schema } => {
                        // add attributes
                        let Some(entitytypes_by_type) = &entitytypes_by_type else {
                            unreachable!("in schema-based mode, this should always be Some")
                        };
                        let et = entitytypes_by_type
                        .get(name)
                        .expect("typename should have an EntityType");
                        match &et.kind {
                            EntityTypeKind::Enum { .. } => {}
                            EntityTypeKind::Standard(StandardEntityType { shape, .. }) => {
                                let attributes = attrs_from_attrs_or_context(
                                    &schema.schema,shape);
                                if attributes.additional_attrs {
                                    // maybe add some additional attributes with arbitrary types
                                    self.u.arbitrary_loop(
                                        None,
                                        Some(schema.settings.max_width as u32),
                                        |u| {
                                            let attr_type = if schema.settings.enable_extensions {
                                                u.arbitrary()?
                                            } else {
                                                Type::arbitrary_nonextension(u)?
                                            };
                                            let attr_name: String = u.arbitrary()?;
                                            attrs.insert(
                                                attr_name.into(),
                                                schema
                                                    .exprgenerator(Some(&hierarchy_no_attrs))
                                                    .generate_attr_value_for_type(
                                                        &attr_type,
                                                        schema.settings.max_depth,
                                                        u,
                                                    )?
                                                    .into(),
                                            );
                                            Ok(std::ops::ControlFlow::Continue(()))
                                        },
                                    )?;
                                }
                                for (attr, ty) in attributes.attrs {
                                    // now add the actual optional and required attributes, with the
                                    // correct types.
                                    // Doing this second ensures that we overwrite any "additional"
                                    // attributes so that they definitely have the required type, in
                                    // case we got a name collision between an explicitly specified
                                    // attribute and one of the "additional" ones we added.
                                    if ty.required || self.u.ratio::<u8>(1, 2)? {
                                        let attr_val = schema
                                            .exprgenerator(Some(&hierarchy_no_attrs))
                                            .generate_attr_value_for_schematype(
                                                &ty.ty,
                                                schema.settings.max_depth,
                                                self.u,
                                            )?;
                                        attrs.insert(
                                        attr.parse().expect(
                                            "all attribute names in the schema should be valid identifiers",
                                        ),
                                        attr_val.into(),
                                    );
                                    }
                                }
                            }
                            }
                        }
                }
                // generate appropriate tags for the entity
                let mut tags = HashMap::new();
                match &self.mode {
                    HierarchyGeneratorMode::Arbitrary {
                        attributes_mode: AttributesMode::NoAttributesOrTags,
                    } => {
                        // don't add any tags
                    }
                    HierarchyGeneratorMode::SchemaBased { schema } => {
                        // add tags
                        let Some(entitytypes_by_type) = &entitytypes_by_type else {
                            unreachable!("in schema-based mode, this should always be Some")
                        };
                        let et = entitytypes_by_type
                        .get(name)
                        .expect("typename should have an EntityType");
                        match &et.kind {
                            EntityTypeKind::Standard(StandardEntityType { tags: Some(tag_type), .. }) => {
                                // add tags with the type `tag_type`
                                self.u.arbitrary_loop(
                                    None,
                                    Some(schema.settings.max_width as u32),
                                    |u| {
                                        let tag_key: SmolStr = u.arbitrary()?;
                                        tags.insert(
                                            tag_key,
                                            schema
                                                .exprgenerator(Some(&hierarchy_no_attrs))
                                                .generate_attr_value_for_schematype(
                                                    tag_type,
                                                    schema.settings.max_depth,
                                                    u,
                                                )?
                                                .into(),
                                        );
                                        Ok(std::ops::ControlFlow::Continue(()))
                                    },
                                )?;
                            }
                            _ => {}
                        }
                    }
                }
                // create the actual ast::Entity object
                let entity = ast::Entity::new(
                    uid.clone(),
                    attrs,
                    parents.into_iter().collect(),
                    tags,
                    &self.extensions,
                )
                .map_err(|e| Error::EntitiesError(e.to_string()))?;
                Ok((uid.clone(), entity))
            })
            .collect::<Result<_>>()?;
        Ok(hierarchy_no_attrs.replace_entities(entities))
    }
    /// size hint for generate()
    pub fn size_hint(_depth: usize) -> (usize, Option<usize>) {
        (0, None)
    }
}
