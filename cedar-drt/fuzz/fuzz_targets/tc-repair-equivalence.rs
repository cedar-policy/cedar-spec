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

use cedar_drt_inner::entity_graph::{Edge, MAX_NODES, NodeUids, ancestor_sets_map};
use cedar_drt_inner::fuzz_target;

use cedar_policy_core::ast::{Entity, EntityUID};
use cedar_policy_core::transitive_closure::{compute_tc, enforce_tc_and_dag, repair_tc};
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};
use std::collections::HashSet;
use std::sync::Arc;

/// Fuzz input: a set of edges partitioned into pre-existing and new.
#[derive(Debug, Clone)]
struct FuzzTargetInput {
    num_nodes: u8,
    pre_existing_edges: Vec<Edge>,
    new_edges: Vec<Edge>,
}

impl<'a> Arbitrary<'a> for FuzzTargetInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        // A simple arbitrary generating "graphs": sets of nodes and edges, where
        // edges are partitioned into "existing" and "new" for the purposes of
        // comparing incremental addition of edges
        let num_nodes = u.int_in_range(1..=MAX_NODES)?;
        let num_pre: usize = u.int_in_range(0..=32)?;
        let num_new: usize = u.int_in_range(0..=32)?;

        let pre_existing_edges = Edge::arbitrary_vec(u, num_nodes, num_pre)?;
        let new_edges = Edge::arbitrary_vec(u, num_nodes, num_new)?;

        Ok(Self {
            num_nodes,
            pre_existing_edges,
            new_edges,
        })
    }
}

/// Add new parent edges to entities and return the full set of nodes needing
/// TC repair. This mirrors the touched-node logic in `Entities::add_entities`:
/// any node that already has a directly-touched node in its ancestor set also
/// needs its indirect ancestors recomputed.
fn add_new_edges(
    uids: &mut NodeUids,
    entities: &mut std::collections::HashMap<EntityUID, Arc<Entity>>,
    new_edges: &[Edge],
) -> HashSet<EntityUID> {
    let mut directly_touched: HashSet<EntityUID> = HashSet::new();
    for edge in new_edges {
        let child_uid = uids.get(edge.child);
        let parent_uid = uids.get(edge.parent);
        let entity = Arc::make_mut(entities.get_mut(&child_uid).unwrap());
        entity.add_parent(parent_uid);
        entity.remove_all_indirect_ancestors();
        directly_touched.insert(child_uid);
    }
    // The logic in add_entities. This fuzz target focuses on the low-level implementations and
    // wants to test them directly, but we have to make sure the arguments to repair_tc are correct.
    let mut touched = directly_touched.clone();
    for (uid, entity) in entities.iter() {
        if !directly_touched
            .is_disjoint(&entity.ancestors().cloned().collect::<HashSet<EntityUID>>())
        {
            touched.insert(uid.clone());
        }
    }
    for uid in &touched {
        if !directly_touched.contains(uid) {
            Arc::make_mut(entities.get_mut(uid).unwrap()).remove_all_indirect_ancestors();
        }
    }
    touched
}

fuzz_target!(|input: FuzzTargetInput| {
    // This tests that, given a graph partition of old and new edges:
    // - if old + new is cyclic, then compute_tc and repair_tc agree that it is cyclic when enforce_dag=true,
    // - if old + new is not cyclic,
    //.   - compute_tc and repair_tc agree that it is not cyclic when enforce_dag=true
    //.   - compute_tc and repair_tc with enforce_dag=true and enforce_dag=false agree on the TC.
    // compute_tc and repair_tc paths will disagree on cyclic graphs with enforce_dag = false
    // I.e. repair_tc should not be used without enforce_dag=false when the graph is not known to
    // be a dag.
    let all_edges: Vec<Edge> = input
        .pre_existing_edges
        .iter()
        .chain(input.new_edges.iter())
        .cloned()
        .collect();
    let mut uids = NodeUids::new();
    // --- Test with enforce_dag=true: cycle detection must agree ---
    let mut expected_entities = uids.build_entities(input.num_nodes, &all_edges);
    let expected_result = compute_tc(&mut expected_entities, true);

    let mut incremental_entities = uids.build_entities(input.num_nodes, &input.pre_existing_edges);
    if compute_tc(&mut incremental_entities, true).is_err() {
        // Pre-existing edges alone form a cycle. Full graph must also be cyclic.
        assert!(
            expected_result.is_err(),
            "pre-existing edges cyclic but full graph is not?"
        );
        return;
    }

    let touched = add_new_edges(&mut uids, &mut incremental_entities, &input.new_edges);
    let repair_result = repair_tc(&touched, &mut incremental_entities, true);

    // Both must agree on whether the graph is a DAG.
    assert_eq!(
        expected_result.is_ok(),
        repair_result.is_ok(),
        "compute_tc and repair_tc disagree on cycle detection"
    );

    if expected_result.is_ok() {
        // On DAGs, ancestor sets must match exactly.
        let expected = ancestor_sets_map(&expected_entities);
        let actual = ancestor_sets_map(&incremental_entities);
        assert_eq!(
            expected, actual,
            "repair_tc result differs from compute_tc (DAG path)"
        );
        // Independent verification: enforce_tc_and_dag must pass on repair_tc output.
        enforce_tc_and_dag(&incremental_entities)
            .expect("enforce_tc_and_dag failed on repair_tc output");
    }

    // --- Test with enforce_dag=false: TC equivalence on acyclic graphs ---
    // Only run this if the graph is actually a DAG (already confirmed above).
    if expected_result.is_ok() {
        let mut expected_no_dag = uids.build_entities(input.num_nodes, &all_edges);
        let _ = compute_tc(&mut expected_no_dag, false);

        let mut incremental_no_dag =
            uids.build_entities(input.num_nodes, &input.pre_existing_edges);
        let _ = compute_tc(&mut incremental_no_dag, false);
        let touched = add_new_edges(&mut uids, &mut incremental_no_dag, &input.new_edges);
        let _ = repair_tc(&touched, &mut incremental_no_dag, false);

        let expected = ancestor_sets_map(&expected_no_dag);
        let actual = ancestor_sets_map(&incremental_no_dag);
        assert_eq!(
            expected, actual,
            "repair_tc result differs from compute_tc (no-DAG path)"
        );
    }
});
