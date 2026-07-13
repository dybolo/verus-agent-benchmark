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

pub open spec fn valid<T>(temp_pred: TempPred<T>) -> bool {
    forall |ex: Execution<T>| temp_pred.satisfied_by(ex)
}


// File: rules.rs
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
pub proof fn execution_equality<T>(ex1: Execution<T>, ex2: Execution<T>)
    requires forall |i: nat| #[trigger] (ex1.nat_to_state)(i) == (ex2.nat_to_state)(i),
    ensures ex1 == ex2,
	{
		unimplemented!()
	}

	#[verifier::external_body]
pub proof fn always_and_equality<T>(p: TempPred<T>, q: TempPred<T>)
    ensures always(p.and(q)) == always(p).and(always(q)),
	{
		unimplemented!()
	}

// Helper: suffix of suffix is suffix at sum
proof fn suffix_suffix_eq<T>(ex: Execution<T>, i: nat, j: nat)
    ensures ex.suffix(i).suffix(j) == ex.suffix((i + j) as nat)
{
    assert forall |k: nat| #[trigger] (ex.suffix(i).suffix(j).nat_to_state)(k) == (ex.suffix((i + j) as nat).nat_to_state)(k) by {
        // ex.suffix(i).suffix(j).nat_to_state(k) = ex.nat_to_state(k + j + i)
        // ex.suffix(i+j).nat_to_state(k) = ex.nat_to_state(k + (i+j))
        // These are equal
    };
    execution_equality(ex.suffix(i).suffix(j), ex.suffix((i + j) as nat));
}

// Helper: always(p) at ex.suffix(i) and j more steps means always(p) holds at ex.suffix(i+j)
proof fn always_propagate_twice<T>(ex: Execution<T>, p: TempPred<T>, i: nat, j: nat)
    requires always(p).satisfied_by(ex.suffix(i)),
    ensures always(p).satisfied_by(ex.suffix((i + j) as nat))
{
    always_propagate_forwards(ex.suffix(i), p, j);
    suffix_suffix_eq(ex, i, j);
}

// Helper: if always(q) and always(r) hold at ex, then always(q.and(r)) holds at ex
proof fn always_and_intro<T>(ex: Execution<T>, q: TempPred<T>, r: TempPred<T>)
    requires
        always(q).satisfied_by(ex),
        always(r).satisfied_by(ex),
    ensures
        always(q.and(r)).satisfied_by(ex),
        always(q).and(always(r)).satisfied_by(ex),
{
    assert forall |i: nat| #[trigger] q.and(r).satisfied_by(ex.suffix(i)) by {
        assert(q.satisfied_by(ex.suffix(i)));
        assert(r.satisfied_by(ex.suffix(i)));
        assert(q.and(r).satisfied_by(ex.suffix(i)));
    };
}

// Helper: given spec entails phi, and spec holds on ex, conclude phi holds on ex
proof fn entails_apply<T>(ex: Execution<T>, spec: TempPred<T>, phi: TempPred<T>)
    requires
        spec.entails(phi),
        spec.satisfied_by(ex),
    ensures phi.satisfied_by(ex),
{
    // spec.entails(phi) = valid(spec.implies(phi)) = forall ex, spec.satisfied_by(ex) ==> phi.satisfied_by(ex)
    // We need to instantiate the forall on ex
    assert(spec.entails(phi) == valid(spec.implies(phi)));
    assert(valid(spec.implies(phi)));
    assert(spec.implies(phi).satisfied_by(ex));
    implies_apply(ex, spec, phi);
}

pub proof fn leads_to_always_combine<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>, r: TempPred<T>)
    requires
        spec.entails(p.leads_to(always(q))),
        spec.entails(p.leads_to(always(r))),
    ensures
        spec.entails(p.leads_to(always(q.and(r)))),
        spec.entails(p.leads_to(always(q).and(always(r)))),
{
    assert forall |ex: Execution<T>| spec.satisfied_by(ex) implies p.leads_to(always(q.and(r))).satisfied_by(ex) by {
        entails_apply(ex, spec, p.leads_to(always(q)));
        entails_apply(ex, spec, p.leads_to(always(r)));
        assert(p.leads_to(always(q)).satisfied_by(ex));
        assert(p.leads_to(always(r)).satisfied_by(ex));
        assert forall |i: nat| #[trigger] p.implies(eventually(always(q.and(r)))).satisfied_by(ex.suffix(i)) by {
            if p.satisfied_by(ex.suffix(i)) {
                assert(p.implies(eventually(always(q))).satisfied_by(ex.suffix(i)));
                assert(eventually(always(q)).satisfied_by(ex.suffix(i)));
                let j1 = eventually_choose_witness(ex.suffix(i), always(q));
                assert(always(q).satisfied_by(ex.suffix(i).suffix(j1)));

                assert(p.implies(eventually(always(r))).satisfied_by(ex.suffix(i)));
                assert(eventually(always(r)).satisfied_by(ex.suffix(i)));
                let j2 = eventually_choose_witness(ex.suffix(i), always(r));
                assert(always(r).satisfied_by(ex.suffix(i).suffix(j2)));

                let j = if j1 >= j2 { j1 } else { j2 };

                if j1 >= j2 {
                    let diff: nat = (j1 - j2) as nat;
                    assert((j2 + diff) as nat == j1);
                    always_propagate_forwards(ex.suffix(i).suffix(j2), r, diff);
                    suffix_suffix_eq(ex.suffix(i), j2, diff);
                    assert(always(r).satisfied_by(ex.suffix(i).suffix((j2 + diff) as nat)));
                    assert(always(r).satisfied_by(ex.suffix(i).suffix(j1)));
                    assert(always(q).satisfied_by(ex.suffix(i).suffix(j)));
                    assert(always(r).satisfied_by(ex.suffix(i).suffix(j)));
                } else {
                    let diff: nat = (j2 - j1) as nat;
                    assert((j1 + diff) as nat == j2);
                    always_propagate_forwards(ex.suffix(i).suffix(j1), q, diff);
                    suffix_suffix_eq(ex.suffix(i), j1, diff);
                    assert(always(q).satisfied_by(ex.suffix(i).suffix((j1 + diff) as nat)));
                    assert(always(q).satisfied_by(ex.suffix(i).suffix(j2)));
                    assert(always(q).satisfied_by(ex.suffix(i).suffix(j)));
                    assert(always(r).satisfied_by(ex.suffix(i).suffix(j)));
                }

                always_and_intro(ex.suffix(i).suffix(j), q, r);
                assert(always(q.and(r)).satisfied_by(ex.suffix(i).suffix(j)));
                eventually_proved_by_witness(ex.suffix(i), always(q.and(r)), j);
                assert(eventually(always(q.and(r))).satisfied_by(ex.suffix(i)));
            }
        };
    };

    assert forall |ex: Execution<T>| spec.satisfied_by(ex) implies p.leads_to(always(q).and(always(r))).satisfied_by(ex) by {
        entails_apply(ex, spec, p.leads_to(always(q)));
        entails_apply(ex, spec, p.leads_to(always(r)));
        assert(p.leads_to(always(q)).satisfied_by(ex));
        assert(p.leads_to(always(r)).satisfied_by(ex));
        assert forall |i: nat| #[trigger] p.implies(eventually(always(q).and(always(r)))).satisfied_by(ex.suffix(i)) by {
            if p.satisfied_by(ex.suffix(i)) {
                assert(p.implies(eventually(always(q))).satisfied_by(ex.suffix(i)));
                assert(eventually(always(q)).satisfied_by(ex.suffix(i)));
                let j1 = eventually_choose_witness(ex.suffix(i), always(q));
                assert(always(q).satisfied_by(ex.suffix(i).suffix(j1)));

                assert(p.implies(eventually(always(r))).satisfied_by(ex.suffix(i)));
                assert(eventually(always(r)).satisfied_by(ex.suffix(i)));
                let j2 = eventually_choose_witness(ex.suffix(i), always(r));
                assert(always(r).satisfied_by(ex.suffix(i).suffix(j2)));

                let j = if j1 >= j2 { j1 } else { j2 };

                if j1 >= j2 {
                    let diff: nat = (j1 - j2) as nat;
                    assert((j2 + diff) as nat == j1);
                    always_propagate_forwards(ex.suffix(i).suffix(j2), r, diff);
                    suffix_suffix_eq(ex.suffix(i), j2, diff);
                    assert(always(r).satisfied_by(ex.suffix(i).suffix((j2 + diff) as nat)));
                    assert(always(r).satisfied_by(ex.suffix(i).suffix(j)));
                    assert(always(q).satisfied_by(ex.suffix(i).suffix(j)));
                } else {
                    let diff: nat = (j2 - j1) as nat;
                    assert((j1 + diff) as nat == j2);
                    always_propagate_forwards(ex.suffix(i).suffix(j1), q, diff);
                    suffix_suffix_eq(ex.suffix(i), j1, diff);
                    assert(always(q).satisfied_by(ex.suffix(i).suffix((j1 + diff) as nat)));
                    assert(always(q).satisfied_by(ex.suffix(i).suffix(j)));
                    assert(always(r).satisfied_by(ex.suffix(i).suffix(j)));
                }

                assert(always(q).and(always(r)).satisfied_by(ex.suffix(i).suffix(j)));
                eventually_proved_by_witness(ex.suffix(i), always(q).and(always(r)), j);
            }
        };
    };
}


}
