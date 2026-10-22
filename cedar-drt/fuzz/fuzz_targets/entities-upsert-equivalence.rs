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

#![no_main]

use cedar_drt_inner::entity_graph::{MAX_NODES, NodeUids, ancestor_sets};
use cedar_drt_inner::fuzz_target;

use cedar_policy::entities_errors;
use cedar_policy_core::ast::Entity;
use cedar_policy_core::entities::{Entities, NoEntitiesSchema, TCComputation};
use cedar_policy_core::extensions::Extensions;
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};
use std::collections::HashMap;
use std::sync::Arc;

/// A node together with the full set of parents for one version of it. Unlike
/// the `(child, parent)` edges used by `tc-repair-equivalence`, an upsert
/// replaces a node's entire parent set, so the batch is a sequence of these.
#[derive(Debug, Clone)]
struct NodeParents {
    node: u8,
    parents: Vec<u8>,
}

/// Fuzz input: an initial entity store plus an ordered batch of upserts.
#[derive(Debug, Clone)]
struct FuzzTargetInput {
    initial: Vec<NodeParents>,
    batch: Vec<NodeParents>,
}

impl<'a> Arbitrary<'a> for FuzzTargetInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let num_nodes = u.int_in_range(1..=MAX_NODES)?;
        let arbitrary_node_parents =
            |u: &mut Unstructured<'a>, n: u8| -> arbitrary::Result<NodeParents> {
                let node = u.int_in_range(0..=(n - 1))?;
                let num_parents: usize = u.int_in_range(0..=(n as usize))?;
                let parents = (0..num_parents)
                    .map(|_| u.int_in_range(0..=(n - 1)))
                    .collect::<arbitrary::Result<_>>()?;
                Ok(NodeParents { node, parents })
            };

        let num_initial: usize = u.int_in_range(0..=32)?;
        let num_batch: usize = u.int_in_range(0..=32)?;
        let initial = (0..num_initial)
            .map(|_| arbitrary_node_parents(u, num_nodes))
            .collect::<arbitrary::Result<_>>()?;
        let batch = (0..num_batch)
            .map(|_| arbitrary_node_parents(u, num_nodes))
            .collect::<arbitrary::Result<_>>()?;

        Ok(Self { initial, batch })
    }
}

fn deduped_last(list: &[NodeParents]) -> HashMap<u8, Vec<u8>> {
    let mut map: HashMap<u8, Vec<u8>> = HashMap::new();
    for np in list {
        map.insert(np.node, np.parents.clone());
    }
    map
}

fuzz_target!(|input: FuzzTargetInput| {
    let mut uids = NodeUids::new();

    // Build the initial store. We flatten to the last version per node first,
    // since `from_entities` rejects conflicting duplicates.
    let initial_versions = deduped_last(&input.initial);
    let initial_entities: Vec<Entity> = initial_versions
        .iter()
        .map(|(node, parents)| uids.make_entity(*node, parents))
        .collect();

    let store = match Entities::from_entities(
        initial_entities,
        None::<&NoEntitiesSchema>,
        TCComputation::ComputeNow,
        Extensions::all_available(),
    ) {
        Ok(store) => store,
        // Initial graph is cyclic (not a DAG). `upsert_entities` on the final
        // graph would also fail; this target only checks the acyclic case.
        Err(entities_errors::EntitiesError::TransitiveClosureError { .. }) => return,
        // Other types of errors De/serialization, malformed, dup entities is unexpected
        Err(e) => panic!("from_entities unexpectedly failure: {}", e),
    };

    let batch_entities: Vec<Arc<Entity>> = input
        .batch
        .iter()
        .map(|np| Arc::new(uids.make_entity(np.node, &np.parents)))
        .collect();

    let upserted = store.clone().upsert_entities(
        batch_entities,
        None::<&NoEntitiesSchema>,
        TCComputation::ComputeNow,
        Extensions::all_available(),
    );

    // Oracle: the final intended graph is the initial store overlaid with the
    // last version of each node named in the batch. Build it from scratch with
    // `from_entities` so the transitive closure is recomputed independently of
    // the incremental `upsert_entities` path.
    let batch_versions = deduped_last(&input.batch);
    let mut final_versions = initial_versions;
    for (node, parents) in &batch_versions {
        final_versions.insert(*node, parents.clone());
    }
    let final_entities: Vec<Entity> = final_versions
        .iter()
        .map(|(node, parents)| uids.make_entity(*node, parents))
        .collect();
    let oracle = Entities::from_entities(
        final_entities,
        None::<&NoEntitiesSchema>,
        TCComputation::ComputeNow,
        Extensions::all_available(),
    );

    match (upserted, oracle) {
        (Ok(upserted), Ok(oracle)) => {
            assert_eq!(
                ancestor_sets(&upserted),
                ancestor_sets(&oracle),
                "upsert_entities result differs from from_entities oracle"
            );
        }
        (Err(_), Err(_)) => {
            // Both detect the final graph is cyclic
        }
        (upserted, oracle) => {
            panic!(
                "upsert_entities and from_entities disagree on cycle detection: \
                 upsert ok = {}, oracle ok = {}",
                upserted.is_ok(),
                oracle.is_ok()
            );
        }
    }
});
