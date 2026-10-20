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

//! Shared infrastructure for fuzz targets that build small entity graphs and
//! compare transitive-closure results. Used by the `tc-repair-equivalence` and
//! `upsert-equivalence` targets, which both generate an arbitrary graph over a
//! bounded set of `Node` entities and check two ways of computing ancestor sets
//! agree.

use cedar_policy_core::ast::{Entity, EntityUID};
use cedar_policy_core::entities::Entities;
use libfuzzer_sys::arbitrary::{self, Unstructured};
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

/// Max number of nodes. Keeps graphs small so fuzzing stays fast and the
/// transitive closure does not blow up.
pub const MAX_NODES: u8 = 24;

/// An edge in the graph, represented as a (child, parent) pair of node indices.
#[derive(Debug, Clone)]
pub struct Edge {
    pub child: u8,
    pub parent: u8,
}

impl Edge {
    /// Generate an arbitrary edge between two of the `num_nodes` nodes.
    pub fn arbitrary_in_range(u: &mut Unstructured<'_>, num_nodes: u8) -> arbitrary::Result<Self> {
        Ok(Edge {
            child: u.int_in_range(0..=(num_nodes - 1))?,
            parent: u.int_in_range(0..=(num_nodes - 1))?,
        })
    }

    /// Generate a `Vec` of `len` arbitrary edges over `num_nodes` nodes.
    pub fn arbitrary_vec(
        u: &mut Unstructured<'_>,
        num_nodes: u8,
        len: usize,
    ) -> arbitrary::Result<Vec<Self>> {
        (0..len)
            .map(|_| Edge::arbitrary_in_range(u, num_nodes))
            .collect()
    }
}

/// Cache of node index -> `EntityUID`, so repeated references to the same node
/// produce the same uid. All uids share the `Node` entity type.
#[derive(Debug, Default)]
pub struct NodeUids(HashMap<u8, EntityUID>);

impl NodeUids {
    pub fn new() -> Self {
        NodeUids(HashMap::new())
    }

    /// Get (or create) the `EntityUID` for node `index`.
    pub fn get(&mut self, index: u8) -> EntityUID {
        self.0
            .entry(index)
            .or_insert_with(|| EntityUID::with_eid_and_type("Node", &index.to_string()).unwrap())
            .clone()
    }

    /// Build a single entity for `node` whose direct parents are `parents`.
    /// The entity has no attributes and no tags; only the parent edges matter
    /// for transitive-closure testing.
    pub fn make_entity(&mut self, node: u8, parents: &[u8]) -> Entity {
        let uid = self.get(node);
        let parent_set: HashSet<EntityUID> = parents.iter().map(|p| self.get(*p)).collect();
        Entity::new_with_attr_partial_value(uid, [], HashSet::new(), parent_set, [])
    }

    /// Build a `HashMap` of all `num_nodes` entities with only direct parent
    /// edges (no transitive closure computed). Every node in `0..num_nodes` gets
    /// an entity, even if it has no edges.
    pub fn build_entities(
        &mut self,
        num_nodes: u8,
        edges: &[Edge],
    ) -> HashMap<EntityUID, Arc<Entity>> {
        let mut parents_map: Vec<HashSet<EntityUID>> = vec![HashSet::new(); num_nodes as usize];
        for edge in edges {
            parents_map[edge.child as usize].insert(self.get(edge.parent));
        }

        parents_map
            .into_iter()
            .enumerate()
            .map(|(i, parents)| {
                let uid = self.get(i as u8);
                let entity = Entity::new_with_attr_partial_value(
                    uid.clone(),
                    [],
                    HashSet::new(),
                    parents,
                    [],
                );
                (uid, Arc::new(entity))
            })
            .collect()
    }
}

/// Collect ancestor (transitive parent) sets from a map of entities, for
/// comparison between two computations.
pub fn ancestor_sets_map(
    entities: &HashMap<EntityUID, Arc<Entity>>,
) -> HashMap<EntityUID, HashSet<EntityUID>> {
    entities
        .iter()
        .map(|(uid, e)| (uid.clone(), e.ancestors().cloned().collect()))
        .collect()
}

/// Collect ancestor (transitive parent) sets from a built `Entities` store, for
/// comparison between two computations.
pub fn ancestor_sets(entities: &Entities) -> HashMap<EntityUID, HashSet<EntityUID>> {
    entities
        .iter()
        .map(|e| (e.uid().clone(), e.ancestors().cloned().collect()))
        .collect()
}
