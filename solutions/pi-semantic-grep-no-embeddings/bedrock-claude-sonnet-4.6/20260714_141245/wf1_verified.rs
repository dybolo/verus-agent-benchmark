use vstd::prelude::*;

fn main() {}

verus!{

pub type StatePred<T> = spec_fn(T) -> bool;

pub type ActionPred<T> = spec_fn(T, T) -> bool;


// File: defs.rs
pub struct Execution<T> {
    pub nat_to_state: spec_fn(nat) -> T,
}

impl<T> Execution<T> {

    pub open spec fn head(self) -> T {
        (self.nat_to_state)(0)
    }

    pub open spec fn head_next(self) -> T {
        (self.nat_to_state)(1)
    }

    pub open spec fn suffix(self, pos: nat) -> Self {
        Execution {
            nat_to_state: |i: nat| (self.nat_to_state)(i + pos),
        }
    }

}


#[verifier(reject_recursive_types(T))]
pub struct TempPred<T> {
    pub pred: spec_fn(Execution<T>) -> bool,
}

impl<T> TempPred<T> {

    pub open spec fn new(pred: spec_fn(Execution<T>) -> bool) -> Self {
        TempPred {
            pred: pred,
        }
    }

    pub open spec fn satisfied_by(self, execution: Execution<T>) -> bool {
        (self.pred)(execution)
    }

    pub open spec fn and(self, other: Self) -> Self {
        TempPred::new(|ex: Execution<T>| self.satisfied_by(ex) && other.satisfied_by(ex))
    }

    pub open spec fn or(self, other: Self) -> Self {
        TempPred::new(|ex: Execution<T>| self.satisfied_by(ex) || other.satisfied_by(ex))
    }

    pub open spec fn implies(self, other: Self) -> Self {
        TempPred::new(|ex: Execution<T>| self.satisfied_by(ex) ==> other.satisfied_by(ex))
    }

    pub open spec fn leads_to(self, other: Self) -> Self {
        always(self.implies(eventually(other)))
    }

    pub open spec fn entails(self, other: Self) -> bool {
        valid(self.implies(other))
    }

}


pub open spec fn lift_state<T>(state_pred: StatePred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| state_pred(ex.head()))
}

pub open spec fn lift_action<T>(action_pred: ActionPred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| action_pred(ex.head(), ex.head_next()))
}

pub open spec fn always<T>(temp_pred: TempPred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| forall |i: nat| #[trigger] temp_pred.satisfied_by(ex.suffix(i)))
}

pub open spec fn eventually<T>(temp_pred: TempPred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| exists |i: nat| #[trigger] temp_pred.satisfied_by(ex.suffix(i)))
}

pub open spec fn later<T>(temp_pred: TempPred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| temp_pred.satisfied_by(ex.suffix(1)))
}

pub open spec fn enabled<T>(action_pred: ActionPred<T>) -> StatePred<T> {
    |s: T| exists |s_prime: T| #[trigger] action_pred(s, s_prime)
}

pub open spec fn weak_fairness<T>(action_pred: ActionPred<T>) -> TempPred<T> {
    always(lift_state(enabled(action_pred))).leads_to(lift_action(action_pred))
}

pub open spec fn valid<T>(temp_pred: TempPred<T>) -> bool {
    forall |ex: Execution<T>| temp_pred.satisfied_by(ex)
}


// File: rules.rs
	#[verifier::external_body]
proof fn weak_fairness_unfold<T>(ex: Execution<T>, p: ActionPred<T>)
    requires weak_fairness(p).satisfied_by(ex),
    ensures forall |i| always(lift_state(enabled(p))).implies(eventually(lift_action(p))).satisfied_by(#[trigger] ex.suffix(i)),
	{
		unimplemented!()
	}

	#[verifier::external_body]
proof fn implies_apply<T>(ex: Execution<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        p.implies(q).satisfied_by(ex),
        p.satisfied_by(ex),
    ensures q.satisfied_by(ex),
	{
		unimplemented!()
	}

	#[verifier::external_body]
proof fn implies_apply_with_always<T>(ex: Execution<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        always(p.implies(q)).satisfied_by(ex),
        always(p).satisfied_by(ex),
    ensures always(q).satisfied_by(ex),
	{
		unimplemented!()
	}

	#[verifier::external_body]
pub proof fn execution_equality<T>(ex1: Execution<T>, ex2: Execution<T>)
    requires forall |i: nat| #[trigger] (ex1.nat_to_state)(i) == (ex2.nat_to_state)(i),
    ensures ex1 == ex2,
	{
		unimplemented!()
	}

	#[verifier::external_body]
pub proof fn wf1_variant_temp<T>(spec: TempPred<T>, next: TempPred<T>, forward: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        spec.entails(always(p.and(next).implies(later(p).or(later(q))))),
        spec.entails(always(p.and(next).and(forward).implies(later(q)))),
        spec.entails(always(next)),
        spec.entails(always(p).leads_to(forward)),
    ensures spec.entails(p.leads_to(q)),
	{
		unimplemented!()
	}

// Helper lemma: suffix of suffix equals a single suffix
proof fn suffix_suffix_eq<T>(ex: Execution<T>, i: nat, j: nat)
    ensures ex.suffix(i).suffix(j) == ex.suffix((i + j) as nat),
{
    execution_equality::<T>(ex.suffix(i).suffix(j), ex.suffix((i + j) as nat));
}

pub proof fn wf1<T>(spec: TempPred<T>, next: ActionPred<T>, forward: ActionPred<T>, p: StatePred<T>, q: StatePred<T>)
    requires
        forall |s, s_prime: T| p(s) && #[trigger] next(s, s_prime) ==> p(s_prime) || q(s_prime),
        forall |s, s_prime: T| p(s) && #[trigger] next(s, s_prime) && forward(s, s_prime) ==> q(s_prime),
        forall |s: T| #[trigger] p(s) ==> enabled(forward)(s),
        spec.entails(always(lift_action(next))),
        spec.entails(weak_fairness(forward)),
    ensures spec.entails(lift_state(p).leads_to(lift_state(q))),
{
    let p_pred = lift_state(p);
    let q_pred = lift_state(q);
    let next_pred = lift_action(next);
    let forward_pred = lift_action(forward);

    // Condition 1: spec |= always(p /\ next => later(p) \/ later(q))
    assert(spec.entails(always(p_pred.and(next_pred).implies(later(p_pred).or(later(q_pred)))))) by {
        assert forall |ex: Execution<T>| #[trigger] spec.satisfied_by(ex) implies
            always(p_pred.and(next_pred).implies(later(p_pred).or(later(q_pred)))).satisfied_by(ex) by {
            assert forall |i: nat| #[trigger] (p_pred.and(next_pred).implies(later(p_pred).or(later(q_pred)))).satisfied_by(ex.suffix(i)) by {
                if p_pred.and(next_pred).satisfied_by(ex.suffix(i)) {
                    let s = ex.suffix(i).head();
                    let s_prime = ex.suffix(i).head_next();
                    // p(s) holds
                    assert(p(s));
                    // next(s, s_prime) holds
                    assert(next(s, s_prime));
                    // By precondition 1: p(s_prime) || q(s_prime)
                    assert(p(s_prime) || q(s_prime));
                    // Connect s_prime to the later predicate
                    // ex.suffix(i).suffix(1).head() = ex.suffix(i).head_next() = s_prime
                    assert(ex.suffix(i).suffix(1).head() == s_prime) by {
                        assert((ex.suffix(i).nat_to_state)(0 + 1) == (ex.nat_to_state)(0 + 1 + i));
                    };
                    if p(s_prime) {
                        assert(later(p_pred).satisfied_by(ex.suffix(i)));
                    } else {
                        assert(later(q_pred).satisfied_by(ex.suffix(i)));
                    }
                }
            };
        };
    };

    // Condition 2: spec |= always(p /\ next /\ forward => later(q))
    assert(spec.entails(always(p_pred.and(next_pred).and(forward_pred).implies(later(q_pred))))) by {
        assert forall |ex: Execution<T>| #[trigger] spec.satisfied_by(ex) implies
            always(p_pred.and(next_pred).and(forward_pred).implies(later(q_pred))).satisfied_by(ex) by {
            assert forall |i: nat| #[trigger] (p_pred.and(next_pred).and(forward_pred).implies(later(q_pred))).satisfied_by(ex.suffix(i)) by {
                if p_pred.and(next_pred).and(forward_pred).satisfied_by(ex.suffix(i)) {
                    let s = ex.suffix(i).head();
                    let s_prime = ex.suffix(i).head_next();
                    assert(p(s));
                    assert(next(s, s_prime));
                    assert(forward(s, s_prime));
                    // By precondition 2: q(s_prime)
                    assert(q(s_prime));
                    // Connect s_prime to later(q_pred)
                    assert(ex.suffix(i).suffix(1).head() == s_prime) by {
                        assert((ex.suffix(i).nat_to_state)(0 + 1) == (ex.nat_to_state)(0 + 1 + i));
                    };
                    assert(later(q_pred).satisfied_by(ex.suffix(i)));
                }
            };
        };
    };

    // Condition 3: spec |= always(next_pred) -- directly from spec.entails(always(lift_action(next)))
    // (already given as precondition)

    // Condition 4: spec |= always(p_pred) ~> forward_pred
    // i.e., always(always(p_pred).implies(eventually(forward_pred)))
    assert(spec.entails(always(p_pred).leads_to(forward_pred))) by {
        assert forall |ex: Execution<T>| #[trigger] spec.satisfied_by(ex) implies
            always(p_pred).leads_to(forward_pred).satisfied_by(ex) by {
            // leads_to = always(self.implies(eventually(other)))
            assert forall |i: nat| #[trigger] (always(p_pred).implies(eventually(forward_pred))).satisfied_by(ex.suffix(i)) by {
                if always(p_pred).satisfied_by(ex.suffix(i)) {
                    // For all j, p_pred holds at ex.suffix(i).suffix(j)
                    // We need: always(lift_state(enabled(forward))).satisfied_by(ex.suffix(i))
                    assert(always(lift_state(enabled(forward))).satisfied_by(ex.suffix(i))) by {
                        assert forall |j: nat| #[trigger] lift_state(enabled(forward)).satisfied_by(ex.suffix(i).suffix(j)) by {
                            // p_pred holds at ex.suffix(i).suffix(j)
                            assert(p_pred.satisfied_by(ex.suffix(i).suffix(j)));
                            let s = ex.suffix(i).suffix(j).head();
                            assert(p(s));
                            // By precondition 3: p(s) ==> enabled(forward)(s)
                            assert(enabled(forward)(s));
                        };
                    };
                    // Use weak_fairness_unfold at index i
                    assert(weak_fairness(forward).satisfied_by(ex)) by {
                        // spec.entails(weak_fairness(forward)) means forall ex2, spec(ex2) ==> wf(ex2)
                        assert(spec.entails(weak_fairness(forward)));
                        // spec.entails is valid(spec.implies(wf))
                        // i.e., forall ex2, spec.satisfied_by(ex2) ==> wf.satisfied_by(ex2)
                        assert(valid(spec.implies(weak_fairness(forward))));
                        assert(spec.implies(weak_fairness(forward)).satisfied_by(ex));
                    };
                    weak_fairness_unfold::<T>(ex, forward);
                    // always(lift_state(enabled(forward))).implies(eventually(lift_action(forward))).satisfied_by(ex.suffix(i))
                    assert(always(lift_state(enabled(forward))).implies(eventually(lift_action(forward))).satisfied_by(ex.suffix(i)));
                    implies_apply::<T>(
                        ex.suffix(i),
                        always(lift_state(enabled(forward))),
                        eventually(lift_action(forward))
                    );
                    assert(eventually(forward_pred).satisfied_by(ex.suffix(i)));
                }
            };
        };
    };

    // Now apply wf1_variant_temp
    wf1_variant_temp::<T>(spec, next_pred, forward_pred, p_pred, q_pred);
}


}
