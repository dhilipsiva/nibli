//! The indexed graph kernel shared by stratification and materialization.
//!
//! Predicate spelling and map iteration belong to the adapter in `rules`.
//! Keeping the traversal over owned indices makes its state explicit to the
//! Rust-to-Lean extractor without changing Tarjan's linear-time algorithm.

#[derive(Clone, Copy)]
struct NodeState {
    index: Option<usize>,
    lowlink: usize,
    on_stack: bool,
}

#[derive(Clone, Copy)]
struct Frame {
    node: usize,
    cursor: usize,
}

/// Finish the active component at `root`. Its root is present in the live
/// stack prefix, and every member is a valid state index. Moving the state
/// buffer into and out of this helper does not copy it.
fn pop_component(
    mut state: Vec<NodeState>,
    stack: &[usize],
    mut stack_len: usize,
    root: usize,
) -> (Vec<NodeState>, usize, Vec<usize>) {
    let mut component = Vec::new();
    let mut complete = false;
    while !complete {
        stack_len -= 1;
        let member = stack[stack_len];
        state[member].on_stack = false;
        component.push(member);
        complete = member == root;
    }
    (state, stack_len, component)
}

/// Return SCCs in DFS completion order. Within each SCC, nodes are in stack
/// pop order; the public name adapter sorts the members for stable reports.
///
/// Every edge target must be less than `graph.len()`. The adapter constructs
/// exactly this closed node set, including predicates used only as targets.
/// Traversal uses explicit stacks so a long chain cannot overflow the call stack.
pub(crate) fn compute_sccs(graph: &[Vec<usize>]) -> Vec<Vec<usize>> {
    let mut state = vec![
        NodeState {
            index: None,
            lowlink: 0,
            on_stack: false,
        };
        graph.len()
    ];
    // At most one live stack entry and DFS frame exist per vertex. Fixed
    // buffers expose those bounds directly; the cursors are the live lengths.
    let mut stack = vec![0; graph.len()];
    let mut stack_len = 0;
    let mut work = vec![Frame { node: 0, cursor: 0 }; graph.len()];
    let mut depth = 0;
    let mut components = Vec::new();
    let mut next_index = 0;
    let mut start = 0;

    while start < graph.len() {
        if state[start].index.is_none() {
            state[start] = NodeState {
                index: Some(next_index),
                lowlink: next_index,
                on_stack: true,
            };
            next_index += 1;
            stack[stack_len] = start;
            stack_len += 1;
            work[depth] = Frame {
                node: start,
                cursor: 0,
            };
            depth += 1;

            while depth > 0 {
                let top = depth - 1;
                let node = work[top].node;
                let cursor = work[top].cursor;
                if cursor < graph[node].len() {
                    let target = graph[node][cursor];
                    work[top].cursor += 1;
                    if let Some(index) = state[target].index {
                        if state[target].on_stack {
                            state[node].lowlink = state[node].lowlink.min(index);
                        }
                    } else {
                        state[target] = NodeState {
                            index: Some(next_index),
                            lowlink: next_index,
                            on_stack: true,
                        };
                        next_index += 1;
                        stack[stack_len] = target;
                        stack_len += 1;
                        work[depth] = Frame {
                            node: target,
                            cursor: 0,
                        };
                        depth += 1;
                    }
                } else {
                    let is_root = match state[node].index {
                        Some(index) => index == state[node].lowlink,
                        None => false,
                    };
                    if is_root {
                        let (updated, remaining, component) =
                            pop_component(state, &stack, stack_len, node);
                        state = updated;
                        stack_len = remaining;
                        components.push(component);
                    }
                    depth -= 1;
                    if depth > 0 {
                        let parent = work[depth - 1].node;
                        state[parent].lowlink = state[parent].lowlink.min(state[node].lowlink);
                    }
                }
            }
        }
        start += 1;
    }
    components
}

#[cfg(test)]
mod tests {
    use super::compute_sccs;

    // An independent transitive-closure oracle checks every directed graph on
    // three vertices, including self-edges, isolated vertices and all cycles.
    #[test]
    fn every_three_vertex_graph_matches_mutual_reachability() {
        for bits in 0..1_u16 << 9 {
            let mut graph = vec![Vec::new(); 3];
            let mut reach = [[false; 3]; 3];
            for source in 0..3 {
                reach[source][source] = true;
                for (target, reachable) in reach[source].iter_mut().enumerate() {
                    if bits & (1 << (3 * source + target)) != 0 {
                        graph[source].push(target);
                        *reachable = true;
                    }
                }
            }
            for via in 0..3 {
                for source in 0..3 {
                    for target in 0..3 {
                        reach[source][target] |= reach[source][via] && reach[via][target];
                    }
                }
            }
            let mut label = [None; 3];
            for (index, component) in compute_sccs(&graph).iter().enumerate() {
                assert!(!component.is_empty());
                for &node in component {
                    assert!(
                        label[node].replace(index).is_none(),
                        "duplicate node: {bits}"
                    );
                }
            }
            assert!(label.iter().all(Option::is_some));
            for source in 0..3 {
                for target in 0..3 {
                    assert_eq!(
                        label[source] == label[target],
                        reach[source][target] && reach[target][source],
                        "graph {bits}: {source}, {target}",
                    );
                }
            }
        }
    }

    #[test]
    fn handles_empty_graph_duplicates_and_completed_targets() {
        assert!(compute_sccs(&[]).is_empty());
        assert_eq!(
            compute_sccs(&[vec![1, 1], vec![], vec![0, 1, 3], vec![2]]),
            vec![vec![1], vec![0], vec![3, 2]],
        );
    }

    #[test]
    fn long_chain_and_cycle_use_explicit_stacks() {
        let length = 20_000;
        let mut graph: Vec<Vec<usize>> = (1..=length)
            .map(|next| if next < length { vec![next] } else { vec![] })
            .collect();
        let chain = compute_sccs(&graph);
        assert_eq!(chain.len(), length);
        assert!(
            chain
                .iter()
                .enumerate()
                .all(|(i, c)| c == &[length - i - 1])
        );
        graph[length - 1].push(0);
        assert_eq!(
            compute_sccs(&graph),
            vec![(0..length).rev().collect::<Vec<_>>()]
        );
    }
}
