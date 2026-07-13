use vstd::prelude::*;

fn main() {}

verus!{

// File: defs.rs
pub struct Execution<T> {
    pub nat_to_state: spec_fn(nat) -> T,
}

impl<T> Execution<T> {

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


pub open spec fn always<T>(temp_pred: TempPred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| forall |i: nat| #[trigger] temp_pred.satisfied_by(ex.suffix(i)))
}

pub open spec fn eventually<T>(temp_pred: TempPred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| exists |i: nat| #[trigger] temp_pred.satisfied_by(ex.suffix(i)))
}

pub open spec fn later<T>(temp_pred: TempPred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| temp_pred.satisfied_by(ex.suffix(1)))
}

pub open spec fn valid<T>(temp_pred: TempPred<T>) -> bool {
    forall |ex: Execution<T>| temp_pred.satisfied_by(ex)
}


// File: rules.rs
	#[verifier::external_body]
proof fn leads_to_unfold<T>(ex: Execution<T>, p: TempPred<T>, q: TempPred<T>)
    requires p.leads_to(q).satisfied_by(ex),
    ensures forall |i: nat| p.implies(eventually(q)).satisfied_by(#[trigger] ex.suffix(i)),
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
proof fn always_propagate_forwards<T>(ex: Execution<T>, p: TempPred<T>, i: nat)
    requires always(p).satisfied_by(ex),
    ensures always(p).satisfied_by(ex.suffix(i)),
	{
		unimplemented!()
	}

	#[verifier::external_body]
proof fn eventually_proved_by_witness<T>(ex: Execution<T>, p: TempPred<T>, witness_idx: nat)
    requires p.satisfied_by(ex.suffix(witness_idx)),
    ensures eventually(p).satisfied_by(ex)
	{
		unimplemented!()
	}

spec fn eventually_choose_witness<T>(ex: Execution<T>, p: TempPred<T>) -> nat
    recommends exists |i| p.satisfied_by(#[trigger] ex.suffix(i)),
{
    let witness = choose |i| p.satisfied_by(#[trigger] ex.suffix(i));
    witness
}

	#[verifier::external_body]
proof fn next_preserves_inv_rec<T>(ex: Execution<T>, next: TempPred<T>, inv: TempPred<T>, i: nat)
    requires
        inv.satisfied_by(ex),
        forall |idx| next.satisfied_by(#[trigger] ex.suffix(idx)),
        forall |idx| inv.satisfied_by(#[trigger] ex.suffix(idx)) && next.satisfied_by(ex.suffix(idx))
            ==> inv.satisfied_by(ex.suffix(idx + 1)),
    ensures inv.satisfied_by(ex.suffix(i)),
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

/// Helper: ex.suffix(i).suffix(j) == ex.suffix(i + j)
proof fn suffix_add<T>(ex: Execution<T>, i: nat, j: nat)
    ensures ex.suffix(i).suffix(j) == ex.suffix((i + j) as nat)
{
    assert forall |k: nat| #[trigger] (ex.suffix(i).suffix(j).nat_to_state)(k)
                                   == (ex.suffix((i + j) as nat).nat_to_state)(k)
    by {
        // (ex.suffix(i).suffix(j).nat_to_state)(k)
        //   = (ex.nat_to_state)(k + j + i)   [by double-unfolding suffix]
        // (ex.suffix(i+j).nat_to_state)(k)
        //   = (ex.nat_to_state)(k + (i+j))
        // k + j + i == k + (i + j)  by arithmetic
        assert((ex.suffix(i).suffix(j).nat_to_state)(k)
            == (ex.nat_to_state)(k + j + i));
        assert((ex.suffix((i + j) as nat).nat_to_state)(k)
            == (ex.nat_to_state)(k + (i + j)));
        assert(k + j + i == k + (i + j)) by (nonlinear_arith);
    };
    execution_equality(ex.suffix(i).suffix(j), ex.suffix((i + j) as nat));
}

pub proof fn leads_to_stable<T>(spec: TempPred<T>, next: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        spec.entails(always(q.and(next).implies(later(q)))),
        spec.entails(always(next)),
        spec.entails(p.leads_to(q)),
    ensures spec.entails(p.leads_to(always(q))),
{
    assert forall |ex: Execution<T>| spec.satisfied_by(ex)
        implies p.leads_to(always(q)).satisfied_by(ex)
    by {
        // ---- Extract three hypotheses for this execution ----
        // 1. q is stable: q.and(next) => later(q) always
        assert(spec.implies(always(q.and(next).implies(later(q)))).satisfied_by(ex));
        implies_apply(ex, spec, always(q.and(next).implies(later(q))));
        // 2. next always holds
        assert(spec.implies(always(next)).satisfied_by(ex));
        implies_apply(ex, spec, always(next));
        // 3. p leads_to q
        assert(spec.implies(p.leads_to(q)).satisfied_by(ex));
        implies_apply(ex, spec, p.leads_to(q));

        // Unfold p.leads_to(q) on ex
        leads_to_unfold(ex, p, q);
        // => forall i, p.implies(eventually(q)).satisfied_by(ex.suffix(i))

        // Now show p.leads_to(always(q)).satisfied_by(ex)
        // = always(p.implies(eventually(always(q)))).satisfied_by(ex)
        // = forall i, p.implies(eventually(always(q))).satisfied_by(ex.suffix(i))
        assert forall |i: nat| p.implies(eventually(always(q))).satisfied_by(#[trigger] ex.suffix(i)) by {
            // Assume p holds at ex.suffix(i); need to show eventually(always(q)) holds there.
            if p.satisfied_by(ex.suffix(i)) {
                // p.implies(eventually(q)) holds at ex.suffix(i) (from leads_to_unfold)
                assert(p.implies(eventually(q)).satisfied_by(ex.suffix(i)));
                // Since p holds, eventually(q) holds
                implies_apply(ex.suffix(i), p, eventually(q));
                assert(eventually(q).satisfied_by(ex.suffix(i)));

                // Choose witness j where q holds at ex.suffix(i).suffix(j)
                let j = eventually_choose_witness(ex.suffix(i), q);
                assert(q.satisfied_by(ex.suffix(i).suffix(j)));

                // Convert: ex.suffix(i).suffix(j) == ex.suffix(i+j)
                suffix_add(ex, i, j);
                assert(ex.suffix(i).suffix(j) == ex.suffix((i + j) as nat));
                assert(q.satisfied_by(ex.suffix((i + j) as nat)));

                // Propagate always(next) and stability to ex.suffix(i+j)
                always_propagate_forwards(ex, next, (i + j) as nat);
                assert(always(next).satisfied_by(ex.suffix((i + j) as nat)));

                always_propagate_forwards(ex, q.and(next).implies(later(q)), (i + j) as nat);
                assert(always(q.and(next).implies(later(q))).satisfied_by(ex.suffix((i + j) as nat)));

                // Establish: next holds at every suffix of ex.suffix(i+j)
                assert forall |idx: nat| next.satisfied_by(#[trigger] ex.suffix((i + j) as nat).suffix(idx)) by {
                    // From always(next) on ex.suffix(i+j)
                    assert(always(next).satisfied_by(ex.suffix((i + j) as nat)));
                };

                // Establish stability: q preserved one step at every position of ex.suffix(i+j)
                assert forall |idx: nat|
                    q.satisfied_by(#[trigger] ex.suffix((i + j) as nat).suffix(idx)) &&
                    next.satisfied_by(ex.suffix((i + j) as nat).suffix(idx))
                    ==> q.satisfied_by(ex.suffix((i + j) as nat).suffix(idx + 1))
                by {
                    if q.satisfied_by(ex.suffix((i + j) as nat).suffix(idx)) &&
                       next.satisfied_by(ex.suffix((i + j) as nat).suffix(idx))
                    {
                        let e = ex.suffix((i + j) as nat).suffix(idx);
                        // From always stability, q.and(next).implies(later(q)) holds at e
                        assert(q.and(next).implies(later(q)).satisfied_by(e));
                        // q.and(next) holds at e
                        assert(q.and(next).satisfied_by(e));
                        // Apply: later(q) holds at e
                        implies_apply(e, q.and(next), later(q));
                        assert(later(q).satisfied_by(e));
                        // later(q) at e means q at e.suffix(1)
                        assert(q.satisfied_by(e.suffix(1)));
                        // e.suffix(1) == ex.suffix(i+j).suffix(idx).suffix(1)
                        // == ex.suffix(i+j).suffix(idx+1)  [by suffix_add]
                        suffix_add(ex.suffix((i + j) as nat), idx, 1);
                        assert(ex.suffix((i + j) as nat).suffix(idx).suffix(1)
                            == ex.suffix((i + j) as nat).suffix((idx + 1) as nat));
                        assert(q.satisfied_by(ex.suffix((i + j) as nat).suffix((idx + 1) as nat)));
                        assert(q.satisfied_by(ex.suffix((i + j) as nat).suffix(idx + 1)));
                    }
                };

                // By induction (next_preserves_inv_rec), q holds at every suffix of ex.suffix(i+j)
                assert forall |k: nat| q.satisfied_by(#[trigger] ex.suffix((i + j) as nat).suffix(k)) by {
                    next_preserves_inv_rec(ex.suffix((i + j) as nat), next, q, k);
                };

                // So always(q) holds at ex.suffix(i+j)
                assert(always(q).satisfied_by(ex.suffix((i + j) as nat)));
                // Which equals always(q) at ex.suffix(i).suffix(j)
                assert(always(q).satisfied_by(ex.suffix(i).suffix(j)));

                // Conclude: eventually(always(q)) holds at ex.suffix(i)
                eventually_proved_by_witness(ex.suffix(i), always(q), j);
                assert(eventually(always(q)).satisfied_by(ex.suffix(i)));
            }
        };
        // From the forall, p.leads_to(always(q)) holds on ex
        assert(p.leads_to(always(q)).satisfied_by(ex));
    };
    // Conclude spec.entails(p.leads_to(always(q)))
    assert(spec.entails(p.leads_to(always(q))));
}


}
