use crate::collections::HashMap;
use crate::err::{while_doing, Error, Result};
use crate::size_hint_utils::{size_hint_for_ratio, size_hint_for_choose};
use cedar_policy_core::ast::{Eid, Entity, EntityUID, Name};
use cedar_policy_core::entities::{Entities, TCComputation};
use arbitrary::{Arbitrary, Unstructured};

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
    uids_by_type: HashMap<Name, Vec<EntityUID>>,
}

impl Hierarchy {
    /// generate an arbitrary uid based on the hierarchy
    pub fn arbitrary_uid(&self, u: &mut Unstructured<'_>) -> Result<EntityUID> {
        // UID that exists or doesn't. 90% of the time pick one that exists
        if u.ratio::<u8>(9, 10)? {
            let uid = u
                .choose(&self.uids)
                .map_err(|e| while_doing("getting an arbitrary uid", e))?;
            Ok(uid.clone())
        } else {
            // Note: may generate an unspecified entity
            u.arbitrary().map_err(Into::into)
        }
    }
    /// size hint for arbitrary_uid()
    pub fn arbitrary_uid_size_hint(depth: usize) -> (usize, Option<usize>) {
        arbitrary::size_hint::and(
            size_hint_for_ratio(9, 10),
            arbitrary::size_hint::or(
                // exists case
                size_hint_for_choose(None),
                // not-exists case
                <EntityUID as Arbitrary>::size_hint(depth),
            ),
        )
    }

    /// generate an arbitrary uid based on the hierarchy, with the given typename
    pub fn arbitrary_uid_with_type(
        &self,
        typename: &Name,
        u: &mut Unstructured<'_>,
    ) -> Result<EntityUID> {
        // UID that exists or doesn't. 90% of the time pick one that exists
        if u.ratio::<u8>(9, 10)? {
            let uid = u.choose(self.uids_by_type.get(typename).ok_or(Error::EmptyChoose {
                doing_what: "getting an existing uid with given type",
            })?)?;
            Ok(uid.clone())
        } else {
            Ok(EntityUID::from_components(typename.clone(), u.arbitrary()?))
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
        }
    }

    /// Iterate over the UIDs having the given typename
    pub fn uids_for_type(&self, ty: &Name) -> Box<dyn Iterator<Item = &EntityUID> + '_> {
        match self.uids_by_type.get(ty) {
            Some(v) => Box::new(v.iter()),
            None => Box::new(std::iter::empty()),
        }
    }
}

impl TryFrom<Hierarchy> for Entities {
    type Error = String;
    fn try_from(h: Hierarchy) -> std::result::Result<Entities, String> {
        Entities::from_entities(h.into_entities().map(Into::into), TCComputation::ComputeNow)
            .map_err(|e| e.to_string())
    }
}
