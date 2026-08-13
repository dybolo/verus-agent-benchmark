use std::fs;

use lynette::check_allowed_additions_only;
use tempfile::tempdir;

const ORIGINAL: &str = r#"
verus! {
    #[inductive(reader_finish)]
    fn reader_finish_inductive(pre: int, post: int, node_id: int) {
    }
}
"#;

fn check_changed(source: &str) -> bool {
    check_pair(ORIGINAL, source)
}

fn check_pair(original_source: &str, changed_source: &str) -> bool {
    let directory = tempdir().unwrap();
    let original = directory.path().join("original.rs");
    let changed = directory.path().join("changed.rs");
    fs::write(&original, original_source).unwrap();
    fs::write(&changed, changed_source).unwrap();
    check_allowed_additions_only(original, changed).unwrap()
}

#[test]
fn allows_completion_of_an_inductive_transition_proof() {
    assert!(check_changed(r#"
verus! {
    #[inductive(reader_finish)]
    fn reader_finish_inductive(pre: int, post: int, node_id: int) {
        let proof_value = pre + node_id;
        if proof_value <= post {
            assert(proof_value <= post);
        }
    }
}
"#));
}

#[test]
fn rejects_inductive_transition_declaration_changes() {
    assert!(!check_changed(r#"
verus! {
    #[inductive(reader_finish)]
    fn reader_finish_inductive(pre: int, post: int, node_id: nat) {
    }
}
"#));

    assert!(!check_changed(r#"
verus! {
    #[inductive(reader_abort)]
    fn reader_finish_inductive(pre: int, post: int, node_id: int) {
    }
}
"#));
}

#[test]
fn allows_only_empty_inductive_bodies_inside_state_machine_macros() {
    let original = r#"
verus! {
    tokenized_state_machine! { Machine {
        #[inductive(reader_finish)]
        fn reader_finish_inductive(pre: Self, post: Self, node_id: NodeId) { }

        #[inductive(reader_start)]
        fn reader_start_inductive(pre: Self, post: Self, node_id: NodeId) { assert(true); }
    } }
}
"#;
    let changed = r#"
verus! {
    tokenized_state_machine! { Machine {
        #[inductive(reader_finish)]
        fn reader_finish_inductive(pre: Self, post: Self, node_id: NodeId) {
            let proof_value = node_id;
            assert(proof_value == node_id);
        }

        #[inductive(reader_start)]
        fn reader_start_inductive(pre: Self, post: Self, node_id: NodeId) { assert(true); }
    } }
}
"#;
    assert!(check_pair(original, changed));

    let changed_non_target = changed.replace("assert(true);", "assert(false);");
    assert!(!check_pair(original, &changed_non_target));
}
