use std::fs;
use lynette::check_allowed_additions_only;
use tempfile::tempdir;

const ORIGINAL: &str = r#"
fn protected() {
    let _value = atomic_with_ghost!(atom => fetch_add(1); update old -> new; ghost g => {
        assert(g == old);
    });
    unimplemented!()
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
fn supports_impl_and_trait_default_methods() {
    let original = r#"
struct S;
impl S {
    fn protected(&self) {
        atomic_with_ghost!(atom => load(); ghost g => { assert(g == g); });
        unimplemented!()
    }
}
trait T {
    fn protected(&self) {
        atomic_with_ghost!(atom => load(); ghost g => { assert(g == g); });
        unimplemented!()
    }
}
"#;
    let changed = r#"
struct S;
impl S {
    fn protected(&self) {
        atomic_with_ghost!(atom => load(); ghost g => { assert(g == g); assert(true); });
        unimplemented!()
    }
}
trait T {
    fn protected(&self) {
        atomic_with_ghost!(atom => load(); ghost g => { assert(g == g); assert(true); });
        unimplemented!()
    }
}
"#;
    assert!(check_pair(original, changed));
}

#[test]
fn allows_ghost_body_changes_in_non_target_exec_functions() {
    assert!(check_changed(r#"
fn protected() {
    let _value = atomic_with_ghost!(atom => fetch_add(1); update old -> new; ghost g => {
        assert(g == old);
        assert(new == old + 1);
    });
    unimplemented!()
}
"#));
}

#[test]
fn rejects_changes_to_atomic_operation_or_clauses() {
    assert!(!check_changed(r#"
fn protected() {
    let _value = atomic_with_ghost!(atom => fetch_sub(1); update old -> new; ghost g => {
        assert(g == old);
    });
    unimplemented!()
}
"#));

    assert!(!check_changed(r#"
fn protected() {
    let _value = atomic_with_ghost!(atom => fetch_add(1); update before -> after; ghost g => {
        assert(g == before);
    });
    unimplemented!()
}
"#));
}

#[test]
fn rejects_missing_or_malformed_ghost_structure() {
    assert!(!check_changed(r#"
fn protected() {
    let _value = atomic_with_ghost!(atom => fetch_add(1); update old -> new; ghost g => ());
    unimplemented!()
}
"#));
}

#[test]
fn rejects_unrelated_macro_changes() {
    assert!(!check_changed(r#"
fn protected() {
    let _value = atomic_with_ghost!(atom => fetch_add(1); update old -> new; ghost g => {
        assert(g == old);
    });
    different_macro!(value);
    unimplemented!()
}
"#));
}

const TRY_OPEN_ORIGINAL: &str = r#"
fn protected() {
    let _value = try_open_atomic_update!(au, mut token => {
        let result = atom.compare_exchange(token, 0, 1);
        proof {
            assert(token == token);
        }
        Tracked(Commit(token))
    });
    unimplemented!()
}
"#;

#[test]
fn allows_try_open_atomic_update_proof_completion() {
    assert!(check_pair(TRY_OPEN_ORIGINAL, r#"
fn protected() {
    let _value = try_open_atomic_update!(au, mut token => {
        let result = atom.compare_exchange(token, 0, 1);
        proof {
            assert(token == token);
            assert(result == result);
        }
        Tracked(Commit(token))
    });
    unimplemented!()
}
"#));
}

#[test]
fn allows_try_open_atomic_update_match_proof_completion() {
    assert!(check_pair(r#"
fn protected() {
    let outcome;
    let result = try_open_atomic_update!(au, mut token => {
        let res = atom.compare_exchange(token, 0, 1);
        proof { }
        Tracked(outcome)
    });
}
"#, r#"
fn protected() {
    let outcome;
    let result = try_open_atomic_update!(au, mut token => {
        let res = atom.compare_exchange(token, 0, 1);
        proof {
            outcome = match res {
                Ok(_) => Ok(token),
                Err(_) => Err(token),
            };
        }
        Tracked(outcome)
    });
}
"#));
}

#[test]
fn rejects_try_open_atomic_update_non_proof_changes() {
    assert!(!check_pair(TRY_OPEN_ORIGINAL, r#"
fn protected() {
    let _value = try_open_atomic_update!(au, mut replacement => {
        let result = atom.compare_exchange(replacement, 0, 1);
        proof {
            assert(replacement == replacement);
        }
        Tracked(Commit(replacement))
    });
    unimplemented!()
}
"#));

    assert!(!check_pair(TRY_OPEN_ORIGINAL, r#"
fn protected() {
    let _value = try_open_atomic_update!(au, mut token => {
        let result = atom.compare_exchange(token, 0, 2);
        proof {
            assert(token == token);
        }
        Tracked(Commit(token))
    });
    unimplemented!()
}
"#));

    assert!(!check_pair(TRY_OPEN_ORIGINAL, r#"
fn protected() {
    let _value = try_open_atomic_update!(au, mut token => {
        let result = atom.compare_exchange(token, 0, 1);
        proof {
            assert(token == token);
        }
        Tracked(Abort(token))
    });
    unimplemented!()
}
"#));
}
