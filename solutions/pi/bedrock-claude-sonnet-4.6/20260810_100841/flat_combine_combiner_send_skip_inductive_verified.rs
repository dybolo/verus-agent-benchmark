// rust_verify/tests/example.rs expect-warnings
#[allow(unused_imports)]
use verus_builtin::*;
use verus_builtin_macros::*;
use vstd::map::*;
use vstd::multiset::*;
use vstd::prelude::*;
use vstd::seq::*;
use vstd::{pervasive::*, *};

use verus_state_machines_macros::tokenized_state_machine;

// Based off of the FlatCombine system from Seagull-NR.
// A major difference is that one didn't make any use of storage, because storage was
// rather complicated to use, and it wasn't necessary.
// Now, I expect storage to be a lot easier to use, easier than the alternative.

verus! {

pub struct Request {
    pub rid: int,
    pub req: int,
}

pub struct Response {
    pub rid: int,
    pub resp: int,
}

#[is_variant]
pub enum Client {
    Idle,
    Waiting { rid: int },
}

#[is_variant]
pub enum Combiner {
    Collecting { elems: Seq<Option<int>> },
    Responding { elems: Seq<Option<int>>, idx: nat },
}

} // verus!
tokenized_state_machine! {
    FlatCombiner {
        fields {
            #[sharding(constant)]
            pub num_clients: nat,

            #[sharding(imap)]
            pub clients: IMap<nat, Client>,

            #[sharding(imap)]
            pub slots: IMap<nat, bool>,

            #[sharding(variable)]
            pub combiner: Combiner,

            #[sharding(storage_imap)]
            pub requests: IMap<nat, Request>,

            #[sharding(storage_imap)]
            pub responses: IMap<nat, Response>,
        }

        pub open spec fn valid_idx(self, i: nat) -> bool {
            0 <= i && i < self.num_clients
        }

        #[invariant]
        pub fn clients_complete(self) -> bool {
            forall |i: nat| (0 <= i && i < self.num_clients) ==
                self.clients.dom().contains(i)
        }

        #[invariant]
        pub fn slots_complete(self) -> bool {
            forall |i: nat| (0 <= i && i < self.num_clients) ==
                self.slots.dom().contains(i)
        }

        #[invariant]
        pub fn clients_size(self) -> bool {
            match self.combiner {
                Combiner::Collecting{elems} => elems.len() <= self.num_clients,
                Combiner::Responding{elems, idx} => elems.len() == self.num_clients &&
                    0 <= idx && idx <= self.num_clients,
            }
        }

        /*
        #[verifier::spec]
        fn should_have_req_stored(self, i: nat) -> bool {
            0 <= i
            && i < self.slots
            && self.slots.index(i)
            && match self.combiner {
                Combiner::Collecting{elems} => elems.len() < i || elems.index(i).is_None()
                Combiner::Responding{elems, idx} => idx >= i || elems.index(i).is_None()
            }
        }
        */

        pub open spec fn client_waiting(self, i: nat) -> bool {
            self.valid_idx(i)
            && self.clients.index(i).is_Waiting()
        }

        pub open spec fn combiner_has(self, i: nat) -> bool {
            self.valid_idx(i)
            && match self.combiner {
                Combiner::Collecting{elems} => i < elems.len() && elems.index(i as int).is_Some(),
                Combiner::Responding{elems, idx} => i >= idx && elems.index(i as int).is_Some(),
            }
        }

        pub open spec fn combiner_rid(self, i: nat) -> int {
            match self.combiner {
                Combiner::Collecting{elems} => elems.index(i as int).get_Some_0(),
                Combiner::Responding{elems, idx} => elems.index(i as int).get_Some_0(),
            }
        }

        pub open spec fn request_stored(self, i: nat) -> bool {
            self.requests.dom().contains(i)
        }

        pub open spec fn response_stored(self, i: nat) -> bool {
            self.responses.dom().contains(i)
        }

        #[invariant]
        pub fn not_waiting_inv(self) -> bool {
            forall |i: nat| #[trigger] self.valid_idx(i) && self.clients.index(i).is_Idle() ==>
                !self.slots.index(i)
        }

        #[invariant]
        pub fn waiting_inv(self) -> bool {
            forall |i: nat| #[trigger] self.client_waiting(i) ==>
                self.request_stored(i) || self.response_stored(i) || self.combiner_has(i)
        }

        #[invariant]
        pub fn request_stored_inv(self) -> bool {
            forall |i: nat| #[trigger] self.request_stored(i) ==>
                self.client_waiting(i)
                && self.requests.index(i).rid == self.clients.index(i).get_Waiting_rid()
                && self.slots.index(i)
        }

        #[invariant]
        pub fn response_stored_inv(self) -> bool {
            forall |i: nat| #[trigger] self.response_stored(i) ==>
                self.client_waiting(i)
                && self.responses.index(i).rid == self.clients.index(i).get_Waiting_rid()
                && !self.slots.index(i)
        }


        #[invariant]
        pub fn combiner_has_inv(self) -> bool {
            forall |i: nat| #[trigger] self.combiner_has(i) ==>
                self.client_waiting(i)
                && self.slots.index(i)
                && self.combiner_rid(i) == self.clients.index(i).get_Waiting_rid()
                && !self.request_stored(i)
        }

        init!{
            initialize(num_clients: nat) {
                init num_clients = num_clients;
                init clients = IMap::new(
                    |i: nat| 0 <= i && i < num_clients,
                    |i: nat| Client::Idle);
                init slots = IMap::new(
                    |i: nat| 0 <= i && i < num_clients,
                    |i: nat| false);
                init combiner = Combiner::Collecting { elems: Seq::empty() };
                init requests = IMap::empty();
                init responses = IMap::empty();
            }
        }

        #[inductive(initialize)]
        fn init_inductive(post: Self, num_clients: nat) {
            // clients_complete: IMap::new domain is {i | 0 <= i < num_clients}
            assert forall |i: nat| (0 <= i && i < num_clients) == post.clients.dom().contains(i) by {
                broadcast use vstd::iset::group_iset_lemmas;
            };
            // slots_complete: same
            assert forall |i: nat| (0 <= i && i < num_clients) == post.slots.dom().contains(i) by {
                broadcast use vstd::iset::group_iset_lemmas;
            };
            // clients_size: combiner is Collecting{empty}, len = 0 <= num_clients
            // not_waiting_inv: all clients are Idle, slots are all false
            assert forall |i: nat| #[trigger] post.valid_idx(i) && post.clients.index(i).is_Idle()
                implies !post.slots.index(i) by {
                broadcast use vstd::iset::group_iset_lemmas;
                // clients[i] = Idle (from IMap::new), slots[i] = false
                assert(post.clients.index(i) == Client::Idle);
                assert(post.slots.index(i) == false);
            };
            // waiting_inv: no client is waiting (all Idle), vacuously true
            assert forall |i: nat| #[trigger] post.client_waiting(i)
                implies post.request_stored(i) || post.response_stored(i) || post.combiner_has(i) by {
                broadcast use vstd::iset::group_iset_lemmas;
                // client_waiting(i) requires clients[i].is_Waiting(), but all are Idle
                assert(post.clients.index(i) == Client::Idle);
                // contradiction: is_Waiting() is false
            };
            // request_stored_inv: requests is empty
            assert forall |i: nat| #[trigger] post.request_stored(i)
                implies post.client_waiting(i)
                    && post.requests.index(i).rid == post.clients.index(i).get_Waiting_rid()
                    && post.slots.index(i) by {
                // requests.dom() is empty
                broadcast use vstd::imap::group_imap_lemmas;
                assert(post.requests.dom() =~= ISet::<nat>::empty());
            };
            // response_stored_inv: responses is empty
            assert forall |i: nat| #[trigger] post.response_stored(i)
                implies post.client_waiting(i)
                    && post.responses.index(i).rid == post.clients.index(i).get_Waiting_rid()
                    && !post.slots.index(i) by {
                broadcast use vstd::imap::group_imap_lemmas;
                assert(post.responses.dom() =~= ISet::<nat>::empty());
            };
            // combiner_has_inv: combiner is Collecting{empty}, combiner_has(i) = (i < 0) = false
            assert forall |i: nat| #[trigger] post.combiner_has(i)
                implies post.client_waiting(i)
                    && post.slots.index(i)
                    && post.combiner_rid(i) == post.clients.index(i).get_Waiting_rid()
                    && !post.request_stored(i) by {
                // combiner is Collecting{empty}, so combiner_has(i) requires i < 0, which is false
                assert(post.combiner == Combiner::Collecting { elems: Seq::empty() });
                assert(!post.combiner_has(i));
            };
        }

        ///// Client transitions

        transition!{
            client_send(j: nat, request: Request, cur_slot: bool) {
                require(0 <= j && j < pre.num_clients);

                // Move client to 'waiting' state
                remove clients -= [j => Client::Idle];
                add    clients += [j => Client::Waiting{rid: request.rid}];

                // Set the slot
                remove slots -= [j => cur_slot];
                add    slots += [j => true];

                // deposit the request
                deposit requests += [j => request] by {
                    assert(!pre.request_stored(j));
                };
            }
        }

        #[inductive(client_send)]
        fn client_send_inductive(pre: Self,
            post: Self, j: nat, request: Request, cur_slot: bool)
        {
            // clients changes at j: Idle -> Waiting{rid: request.rid}
            // slots changes at j: cur_slot -> true
            // requests gets j => request deposited

            // not_waiting_inv: for i != j, same as pre. For i = j, now Waiting (not Idle), so vacuous.
            assert forall |i: nat| #[trigger] post.valid_idx(i) && post.clients.index(i).is_Idle()
                implies !post.slots.index(i) by {
                if i == j {
                    // post.clients[j] = Waiting, not Idle -> vacuously true
                    assert(post.clients.index(j).is_Waiting());
                } else {
                    // clients[i] and slots[i] unchanged for i != j
                    assert(pre.not_waiting_inv());
                    assert(pre.valid_idx(i));
                    assert(pre.clients.index(i).is_Idle());
                    assert(!pre.slots.index(i));
                }
            };

            // waiting_inv
            assert forall |i: nat| #[trigger] post.client_waiting(i)
                implies post.request_stored(i) || post.response_stored(i) || post.combiner_has(i) by {
                if i == j {
                    // post.clients[j] = Waiting{rid: request.rid}, post.requests[j] = request
                    assert(post.request_stored(j));
                } else {
                    // unchanged for i != j
                    assert(pre.waiting_inv());
                    assert(pre.client_waiting(i));
                    // request_stored, response_stored unchanged for i != j (j was not already in requests
                    // by the deposit's by-block showing !pre.request_stored(j))
                    if pre.combiner_has(i) {
                        assert(post.combiner_has(i));
                    }
                }
            };

            // request_stored_inv
            assert forall |i: nat| #[trigger] post.request_stored(i)
                implies post.client_waiting(i)
                    && post.requests.index(i).rid == post.clients.index(i).get_Waiting_rid()
                    && post.slots.index(i) by {
                if i == j {
                    // post.requests[j] = request, post.clients[j] = Waiting{rid: request.rid}
                    // post.slots[j] = true
                    assert(post.clients.index(j) == Client::Waiting{rid: request.rid});
                    assert(post.requests.index(j) == request);
                    assert(post.slots.index(j) == true);
                } else {
                    assert(pre.request_stored_inv());
                    assert(pre.request_stored(i));
                    // clients[i] unchanged, slots[i] unchanged for i != j
                }
            };

            // response_stored_inv: responses unchanged, for i = j: was not response_stored in pre
            // because pre.clients[j] = Idle (not Waiting), so response_stored_inv requires client_waiting
            assert forall |i: nat| #[trigger] post.response_stored(i)
                implies post.client_waiting(i)
                    && post.responses.index(i).rid == post.clients.index(i).get_Waiting_rid()
                    && !post.slots.index(i) by {
                if i == j {
                    // Was response stored for j in pre? pre.clients[j] = Idle.
                    // response_stored_inv says response_stored(j) => client_waiting(j)
                    // But pre.client_waiting(j) = false (was Idle). Contradiction.
                    assert(!pre.response_stored(j)) by {
                        assert(pre.response_stored_inv());
                        if pre.response_stored(j) {
                            assert(pre.client_waiting(j)); // impossible
                        }
                    };
                    // So post.response_stored(j) = pre.response_stored(j) = false -> vacuous
                } else {
                    assert(pre.response_stored_inv());
                    assert(pre.response_stored(i));
                    // clients[i] unchanged, slots[i] unchanged for i != j
                }
            };

            // combiner_has_inv: combiner unchanged.
            // For i = j: pre.combiner_has(j) was false (pre.clients[j] = Idle, so combiner_has_inv 
            // would require client_waiting(j) which is false). So still false in post.
            assert forall |i: nat| #[trigger] post.combiner_has(i)
                implies post.client_waiting(i)
                    && post.slots.index(i)
                    && post.combiner_rid(i) == post.clients.index(i).get_Waiting_rid()
                    && !post.request_stored(i) by {
                if i == j {
                    // pre.combiner_has(j) was false (pre.client_waiting(j) = false)
                    assert(!pre.combiner_has(j)) by {
                        assert(pre.combiner_has_inv());
                        if pre.combiner_has(j) {
                            assert(pre.client_waiting(j)); // impossible: j was Idle
                        }
                    };
                    // post.combiner_has(j) = pre.combiner_has(j) = false -> vacuous
                    assert(!post.combiner_has(j));
                } else {
                    assert(pre.combiner_has_inv());
                    assert(pre.combiner_has(i));
                    // client_waiting(i): clients[i] unchanged for i != j
                    assert(pre.client_waiting(i));
                    // slots[i] unchanged for i != j
                    assert(pre.slots.index(i));
                    // combiner_rid unchanged (combiner unchanged)
                    // request_stored(i): for i != j, requests same except at j
                    // but we need !post.request_stored(i)
                    // pre.request_stored(i) was false (from combiner_has_inv)
                    assert(!pre.request_stored(i));
                }
            };
        }

        transition!{
            client_recv(j: nat) {
                require(0 <= j && j < pre.num_clients);

                // Move client to 'idle' state
                remove clients -= [j => let Client::Waiting{rid}];
                add    clients += [j => Client::Idle];

                // Check that the slot has been set back to 'false'
                have slots >= [j => false];

                // withdraw the response
                withdraw responses -= [j => let response] by {
                    assert(pre.client_waiting(j));
                    //assert(!pre.request_stored(j));
                    //assert(!pre.combiner_has(j));
                    //assert(pre.response_stored(j));
                };

                // make sure we get back the response for the correct request id:
                assert(response.rid == rid) by {
                    assert(pre.client_waiting(j));
                };
            }
        }

        #[inductive(client_recv)]
        fn client_recv_inductive(pre: Self, post: Self, j: nat) {
            // clients changes at j: Waiting{rid} -> Idle
            // slots[j] = false (unchanged, from have)
            // responses: j removed

            // not_waiting_inv: for i != j, same. For i = j, now Idle and slots[j] = false.
            assert forall |i: nat| #[trigger] post.valid_idx(i) && post.clients.index(i).is_Idle()
                implies !post.slots.index(i) by {
                if i == j {
                    // post.clients[j] = Idle, post.slots[j] = false (from have slots >= [j => false])
                    assert(!post.slots.index(j));
                } else {
                    assert(pre.not_waiting_inv());
                    assert(pre.valid_idx(i));
                    assert(pre.clients.index(i).is_Idle());
                    assert(!pre.slots.index(i));
                }
            };

            // waiting_inv: for i != j, same. For i = j, now Idle -> vacuous.
            assert forall |i: nat| #[trigger] post.client_waiting(i)
                implies post.request_stored(i) || post.response_stored(i) || post.combiner_has(i) by {
                if i == j {
                    // post.client_waiting(j) = false (j is now Idle) -> vacuous
                    assert(!post.client_waiting(j));
                } else {
                    assert(pre.waiting_inv());
                    assert(pre.client_waiting(i));
                    if pre.combiner_has(i) {
                        assert(post.combiner_has(i));
                    }
                    // response_stored: for i != j, responses same
                }
            };

            // request_stored_inv: requests unchanged.
            // For i = j: was pre.request_stored(j)? From pre.waiting_inv + slots[j]=false:
            // combiner_has_inv says combiner_has(j) => slots[j]=true. But slots[j]=false. So !combiner_has(j).
            // Then from pre.waiting_inv: request_stored(j) || response_stored(j).
            // From pre.request_stored_inv: request_stored(j) => slots[j]=true. But slots[j]=false. So !request_stored(j).
            // So response_stored(j).
            assert forall |i: nat| #[trigger] post.request_stored(i)
                implies post.client_waiting(i)
                    && post.requests.index(i).rid == post.clients.index(i).get_Waiting_rid()
                    && post.slots.index(i) by {
                if i == j {
                    // request_stored(j) was false (slots[j] = false but request_stored requires slots[j] = true)
                    assert(!pre.request_stored(j)) by {
                        assert(pre.request_stored_inv());
                        if pre.request_stored(j) {
                            assert(pre.slots.index(j)); // but slots[j] = false
                        }
                    };
                    // So post.request_stored(j) = false -> vacuous
                } else {
                    assert(pre.request_stored_inv());
                    assert(pre.request_stored(i));
                    // client_waiting(i): clients[i] unchanged for i != j
                    assert(pre.client_waiting(i));
                    // slots[i] unchanged for i != j
                }
            };

            // response_stored_inv: for i = j, response removed -> !post.response_stored(j).
            // For i != j, same as pre.
            assert forall |i: nat| #[trigger] post.response_stored(i)
                implies post.client_waiting(i)
                    && post.responses.index(i).rid == post.clients.index(i).get_Waiting_rid()
                    && !post.slots.index(i) by {
                if i == j {
                    // response[j] was withdrawn, so post.response_stored(j) = false -> vacuous
                    assert(!post.response_stored(j));
                } else {
                    assert(pre.response_stored_inv());
                    assert(pre.response_stored(i));
                    // client_waiting(i): clients[i] unchanged for i != j
                    assert(pre.client_waiting(i));
                }
            };

            // combiner_has_inv: combiner unchanged.
            // For i = j: post.combiner_has(j)? If true, then slots[j] = true (from combiner_has_inv on pre).
            // But slots[j] = false. Contradiction. So post.combiner_has(j) = false.
            assert forall |i: nat| #[trigger] post.combiner_has(i)
                implies post.client_waiting(i)
                    && post.slots.index(i)
                    && post.combiner_rid(i) == post.clients.index(i).get_Waiting_rid()
                    && !post.request_stored(i) by {
                if i == j {
                    // pre.combiner_has(j) would require pre.slots.index(j) = true (from combiner_has_inv)
                    // But slots[j] = false
                    assert(!pre.combiner_has(j)) by {
                        assert(pre.combiner_has_inv());
                        if pre.combiner_has(j) {
                            assert(pre.slots.index(j)); // but slots[j] = false
                        }
                    };
                    assert(!post.combiner_has(j));
                } else {
                    assert(pre.combiner_has_inv());
                    assert(pre.combiner_has(i));
                    // client_waiting(i): clients[i] unchanged for i != j
                    assert(pre.client_waiting(i));
                    // slots[i] unchanged for i != j
                    assert(pre.slots.index(i));
                    // request_stored(i): unchanged for i != j
                    assert(!pre.request_stored(i));
                }
            };
        }

        ///// Combiner transitions

        transition!{
            combiner_recv() {
                require(pre.combiner.is_Collecting());
                let j = pre.combiner.get_Collecting_elems().len();
                require(0 <= j && j < pre.num_clients);

                // Observe that the slot has been set to 'true'
                have slots >= [j => true];

                // Withdraw a request
                withdraw requests -= [j => let request] by {
                    assert(pre.valid_idx(j));
                    assert(pre.client_waiting(j));
                    assert(pre.request_stored(j));
                };

                // Update combiner's local state to remember we withdrew a request with this ID
                update combiner = Combiner::Collecting{
                    elems: pre.combiner.get_Collecting_elems().push(Option::Some(request.rid)),
                };
            }
        }

        #[inductive(combiner_recv)]
        fn combiner_recv_inductive(pre: Self, post: Self) {
            // j = pre.combiner.get_Collecting_elems().len()
            // Combiner: Collecting{elems} -> Collecting{elems.push(Some(request.rid))}
            // requests: j removed
            // slots unchanged (just have'd)
            // clients unchanged

            let j = pre.combiner.get_Collecting_elems().len();
            let elems = pre.combiner.get_Collecting_elems();
            let new_elems = elems.push(Option::Some(pre.requests.index(j).rid));

            // The request's rid
            let req_rid = pre.requests.index(j).rid;

            // post.combiner = Collecting{elems.push(Some(req_rid))}
            assert(post.combiner == Combiner::Collecting { elems: new_elems });

            // clients_size: new elems.len() = old len + 1 = j + 1 <= num_clients (since j < num_clients)
            assert(new_elems.len() == j + 1);

            // not_waiting_inv: clients and slots unchanged
            assert forall |i: nat| #[trigger] post.valid_idx(i) && post.clients.index(i).is_Idle()
                implies !post.slots.index(i) by {
                assert(pre.not_waiting_inv());
            };

            // waiting_inv
            assert forall |i: nat| #[trigger] post.client_waiting(i)
                implies post.request_stored(i) || post.response_stored(i) || post.combiner_has(i) by {
                assert(pre.waiting_inv());
                assert(pre.client_waiting(i));
                if i == j {
                    // post.combiner_has(j): new_elems[j] = Some(req_rid), j < new_elems.len() = j+1
                    assert(post.combiner_has(j)) by {
                        assert(new_elems.index(j as int) == Option::Some(req_rid));
                        assert(j < new_elems.len());
                    };
                } else if pre.request_stored(i) {
                    // request_stored(i) unchanged for i != j
                    assert(post.request_stored(i));
                } else if pre.response_stored(i) {
                    // response_stored(i) unchanged
                    assert(post.response_stored(i));
                } else {
                    // pre.combiner_has(i) must be true
                    assert(pre.combiner_has(i));
                    // For i != j: combiner_has(i) in pre means i < j (collecting, i < elems.len() = j)
                    // In post: i < new_elems.len() = j+1 and new_elems[i] = elems[i].is_Some()
                    assert(i < j);
                    assert(elems.index(i as int).is_Some());
                    assert(new_elems.index(i as int) == elems.index(i as int));
                    assert(post.combiner_has(i));
                }
            };

            // request_stored_inv: for i = j, request withdrawn. For i != j, same as pre.
            assert forall |i: nat| #[trigger] post.request_stored(i)
                implies post.client_waiting(i)
                    && post.requests.index(i).rid == post.clients.index(i).get_Waiting_rid()
                    && post.slots.index(i) by {
                if i == j {
                    // request[j] was withdrawn -> !post.request_stored(j) -> vacuous
                    assert(!post.request_stored(j));
                } else {
                    assert(pre.request_stored_inv());
                    assert(pre.request_stored(i));
                    // client_waiting(i): clients unchanged
                    assert(pre.client_waiting(i));
                    // slots[i]: unchanged
                    assert(pre.slots.index(i));
                }
            };

            // combiner_has_inv: post.combiner = Collecting{new_elems}
            // combiner_has(i) in post = i < new_elems.len() && new_elems[i].is_Some()
            assert forall |i: nat| #[trigger] post.combiner_has(i)
                implies post.client_waiting(i)
                    && post.slots.index(i)
                    && post.combiner_rid(i) == post.clients.index(i).get_Waiting_rid()
                    && !post.request_stored(i) by {
                // post.combiner_has(i) means: valid_idx(i) && i < new_elems.len() && new_elems[i].is_Some()
                // = valid_idx(i) && i < j+1 && new_elems[i].is_Some()
                assert(i < new_elems.len());
                assert(new_elems.index(i as int).is_Some());
                if i == j {
                    // new_elems[j] = Some(req_rid)
                    assert(new_elems.index(j as int) == Option::Some(req_rid));
                    // client_waiting(j): from pre.request_stored_inv
                    assert(pre.request_stored_inv());
                    assert(pre.request_stored(j));
                    assert(pre.client_waiting(j));
                    // slots[j] = true: from pre.request_stored_inv
                    assert(pre.slots.index(j));
                    // combiner_rid in post: new_elems[j].get_Some_0() = req_rid
                    assert(post.combiner_rid(j) == req_rid);
                    // client[j].get_Waiting_rid() = req_rid (from pre.request_stored_inv)
                    assert(pre.requests.index(j).rid == pre.clients.index(j).get_Waiting_rid());
                    assert(post.clients.index(j).get_Waiting_rid() == req_rid);
                    // !post.request_stored(j): request[j] was withdrawn
                    assert(!post.request_stored(j));
                } else {
                    // i < j, so i < elems.len() = j and new_elems[i] = elems[i]
                    assert(i < j);
                    assert(new_elems.index(i as int) == elems.index(i as int));
                    assert(pre.combiner_has(i));
                    assert(pre.combiner_has_inv());
                    // client_waiting(i): unchanged
                    assert(pre.client_waiting(i));
                    // slots[i]: unchanged
                    assert(pre.slots.index(i));
                    // combiner_rid: pre.combiner_rid(i) = elems[i].get_Some_0()
                    // post.combiner_rid(i) = new_elems[i].get_Some_0() = elems[i].get_Some_0()
                    // !request_stored(i): request[j] removed, i != j, so same
                    assert(!pre.request_stored(i));
                }
            };
        }

        transition!{
            combiner_skip() {
                require(pre.combiner.is_Collecting());
                let j = pre.combiner.get_Collecting_elems().len();
                require(0 <= j && j < pre.num_clients);

                // In practice, this happens when slot j is set to false, so we could add this:
                //    have slots >= [j => false];
                // but it's not necessary

                // Update combiner's local state to remember that we didn't withdraw
                // anything here.
                update combiner = Combiner::Collecting{
                    elems: pre.combiner.get_Collecting_elems().push(Option::None),
                };
            }
        }

        #[inductive(combiner_skip)]
        fn combiner_skip_inductive(pre: Self, post: Self) {
            // j = pre.combiner.get_Collecting_elems().len()
            // Combiner: Collecting{elems} -> Collecting{elems.push(None)}
            // clients, slots, requests, responses unchanged

            let j = pre.combiner.get_Collecting_elems().len();
            let elems = pre.combiner.get_Collecting_elems();
            let new_elems = elems.push(Option::<int>::None);

            assert(post.combiner == Combiner::Collecting { elems: new_elems });

            // not_waiting_inv: clients and slots unchanged
            assert forall |i: nat| #[trigger] post.valid_idx(i) && post.clients.index(i).is_Idle()
                implies !post.slots.index(i) by {
                assert(pre.not_waiting_inv());
            };

            // waiting_inv
            assert forall |i: nat| #[trigger] post.client_waiting(i)
                implies post.request_stored(i) || post.response_stored(i) || post.combiner_has(i) by {
                assert(pre.waiting_inv());
                assert(pre.client_waiting(i));
                if pre.request_stored(i) {
                    assert(post.request_stored(i));
                } else if pre.response_stored(i) {
                    assert(post.response_stored(i));
                } else {
                    // pre.combiner_has(i) must be true
                    assert(pre.combiner_has(i));
                    // combiner_has(i) in pre means i < j (since pre.combiner is Collecting{elems, len=j})
                    // and elems[i].is_Some()
                    assert(i < j);
                    assert(elems.index(i as int).is_Some());
                    // In post, i < j < j+1 = new_elems.len(), and new_elems[i] = elems[i].is_Some()
                    assert(i < new_elems.len());
                    assert(new_elems.index(i as int) == elems.index(i as int));
                    assert(post.combiner_has(i));
                }
            };

            // combiner_has_inv: for i = j (new slot): new_elems[j] = None -> combiner_has(j) = false
            // For i < j: same as pre (combiner_has preserved)
            assert forall |i: nat| #[trigger] post.combiner_has(i)
                implies post.client_waiting(i)
                    && post.slots.index(i)
                    && post.combiner_rid(i) == post.clients.index(i).get_Waiting_rid()
                    && !post.request_stored(i) by {
                // post.combiner_has(i): valid_idx(i) && i < new_elems.len() && new_elems[i].is_Some()
                assert(i < new_elems.len());
                assert(new_elems.index(i as int).is_Some());
                // i < j+1 = new_elems.len() and new_elems[j] = None, so if i = j then new_elems[i] = None -> contradiction
                assert(i != j) by {
                    assert(new_elems.index(j as int) == Option::<int>::None);
                };
                // So i < j, which means i < elems.len() = j
                assert(i < j);
                // new_elems[i] = elems[i] for i < j
                assert(new_elems.index(i as int) == elems.index(i as int));
                // pre.combiner_has(i): same condition
                assert(pre.combiner_has(i));
                assert(pre.combiner_has_inv());
                // client_waiting(i): unchanged
                assert(pre.client_waiting(i));
                // slots[i]: unchanged
                assert(pre.slots.index(i));
                // !request_stored(i): unchanged
                assert(!pre.request_stored(i));
            };
        }

        transition!{
            combiner_go_to_responding() {
                require(pre.combiner.is_Collecting());
                require(pre.combiner.get_Collecting_elems().len() == pre.num_clients);
                update combiner = Combiner::Responding{
                    elems: pre.combiner.get_Collecting_elems(),
                    idx: 0,
                };
            }
        }

        transition!{
            combiner_send(response: Response, cur_slot: bool) {
                require(pre.combiner.is_Responding());
                let j = pre.combiner.get_Responding_idx();
                require(0 <= j && j < pre.num_clients);
                let response_opt = pre.combiner.get_Responding_elems().index(j as int);

                // The response we return has to have the right request ID
                require(response_opt == Option::Some(response.rid));

                // Set the slot back to false
                remove slots -= [j => cur_slot];
                add    slots += [j => false];

                // Update the combiner's local state
                update combiner = Combiner::Responding{
                    elems: pre.combiner.get_Responding_elems(),
                    idx: j + 1,
                };

                deposit responses += [j => response] by {
                    assert(pre.valid_idx(j));
                    assert(pre.combiner_has(j));
                    assert(!pre.response_stored(j));
                };
            }
        }

        #[inductive(combiner_send)]
        fn combiner_send_inductive(pre: Self, post: Self, response: Response, cur_slot: bool) {
            // Combiner: Responding{elems, j} -> Responding{elems, j+1}
            // slots[j] -> false
            // responses: deposit j => response
            // clients unchanged, requests unchanged

            let j = pre.combiner.get_Responding_idx();
            let elems = pre.combiner.get_Responding_elems();

            // Key fact: elems[j] = Some(response.rid) (from transition precondition)
            assert(elems.index(j as int) == Option::Some(response.rid));

            // not_waiting_inv: for i != j, slots and clients unchanged.
            // For i = j: combiner_has(j) was true in pre, so client_waiting(j) was true,
            // so clients[j] is Waiting, not Idle. Vacuous.
            assert forall |i: nat| #[trigger] post.valid_idx(i) && post.clients.index(i).is_Idle()
                implies !post.slots.index(i) by {
                if i == j {
                    // post.clients[j] = pre.clients[j] (clients unchanged)
                    // pre.combiner_has(j) => pre.client_waiting(j) => pre.clients[j].is_Waiting()
                    assert(pre.combiner_has(j));
                    assert(pre.combiner_has_inv());
                    assert(pre.client_waiting(j));
                    assert(pre.clients.index(j).is_Waiting());
                    // So post.clients[j].is_Idle() = false -> vacuous
                } else {
                    assert(pre.not_waiting_inv());
                    assert(pre.valid_idx(i));
                    assert(pre.clients.index(i).is_Idle());
                    assert(!pre.slots.index(i));
                }
            };

            // waiting_inv
            assert forall |i: nat| #[trigger] post.client_waiting(i)
                implies post.request_stored(i) || post.response_stored(i) || post.combiner_has(i) by {
                assert(pre.waiting_inv());
                assert(pre.client_waiting(i));
                if i == j {
                    // post.response_stored(j) = true (we deposited response[j])
                    assert(post.response_stored(j));
                } else {
                    if pre.combiner_has(i) {
                        // pre.combiner_has(i) in Responding{elems, j}: i >= j && elems[i].is_Some()
                        // Since i != j, i > j, so i >= j+1
                        // post.combiner_has(i) in Responding{elems, j+1}: i >= j+1 && elems[i].is_Some()
                        assert(i >= j);
                        assert(i != j);
                        assert(i > j);
                        assert(i >= j + 1);
                        assert(post.combiner_has(i));
                    } else if pre.request_stored(i) {
                        assert(post.request_stored(i));
                    } else {
                        assert(pre.response_stored(i));
                        assert(post.response_stored(i));
                    }
                }
            };

            // request_stored_inv: requests unchanged
            assert forall |i: nat| #[trigger] post.request_stored(i)
                implies post.client_waiting(i)
                    && post.requests.index(i).rid == post.clients.index(i).get_Waiting_rid()
                    && post.slots.index(i) by {
                assert(pre.request_stored_inv());
                assert(pre.request_stored(i));
                // client_waiting(i): clients unchanged
                assert(pre.client_waiting(i));
                // slots[i] = true from pre:
                if i == j {
                    // pre.slots[j] was whatever (cur_slot). But post.slots[j] = false.
                    // Was pre.request_stored(j)? From pre.combiner_has_inv, !pre.request_stored(j).
                    assert(!pre.request_stored(j)) by {
                        assert(pre.combiner_has(j));
                        assert(pre.combiner_has_inv());
                    };
                    // So this case is vacuous
                } else {
                    assert(pre.slots.index(i));
                    // post.slots[i] = pre.slots[i] for i != j
                }
            };

            // response_stored_inv: for i != j same as pre. For i = j: response deposited.
            assert forall |i: nat| #[trigger] post.response_stored(i)
                implies post.client_waiting(i)
                    && post.responses.index(i).rid == post.clients.index(i).get_Waiting_rid()
                    && !post.slots.index(i) by {
                if i == j {
                    // post.responses[j] = response, post.clients[j] = pre.clients[j] (unchanged)
                    // pre.combiner_has(j) => pre.client_waiting(j) and clients[j].get_Waiting_rid() = elems[j].get_Some_0()
                    // post.slots[j] = false
                    assert(pre.combiner_has(j));
                    assert(pre.combiner_has_inv());
                    assert(pre.client_waiting(j));
                    // pre.combiner_rid(j) = elems[j].get_Some_0() = response.rid (since elems[j] = Some(response.rid))
                    assert(pre.combiner_rid(j) == pre.clients.index(j).get_Waiting_rid());
                    assert(pre.combiner_rid(j) == response.rid);
                    assert(post.responses.index(j) == response);
                    assert(post.responses.index(j).rid == response.rid);
                    assert(!post.slots.index(j));
                } else {
                    assert(pre.response_stored_inv());
                    assert(pre.response_stored(i));
                    assert(pre.client_waiting(i));
                    // slots[i] unchanged for i != j
                    assert(!pre.slots.index(i));
                }
            };

            // combiner_has_inv: 
            assert forall |i: nat| #[trigger] post.combiner_has(i)
                implies post.client_waiting(i)
                    && post.slots.index(i)
                    && post.combiner_rid(i) == post.clients.index(i).get_Waiting_rid()
                    && !post.request_stored(i) by {
                // post.combiner_has(i): i >= j+1 && elems[i].is_Some()
                assert(i >= j + 1);
                assert(elems.index(i as int).is_Some());
                // So i > j, and pre.combiner_has(i) also holds (i >= j && elems[i].is_Some())
                assert(i > j);
                assert(i >= j);
                assert(pre.combiner_has(i));
                assert(pre.combiner_has_inv());
                // client_waiting(i): unchanged
                assert(pre.client_waiting(i));
                // slots[i]: unchanged for i != j (since i != j because i > j)
                assert(i != j);
                assert(pre.slots.index(i));
                // request_stored(i): unchanged, was false
                assert(!pre.request_stored(i));
            };
        }

        transition!{
            combiner_send_skip() {
                require(pre.combiner.is_Responding());
                let j = pre.combiner.get_Responding_idx();
                require(0 <= j && j < pre.num_clients);
                let response_opt = pre.combiner.get_Responding_elems().index(j as int);

                // The response we return has to have the right request ID
                require(equal(response_opt, Option::None));

                // Update the combiner's local state
                update combiner = Combiner::Responding{
                    elems: pre.combiner.get_Responding_elems(),
                    idx: j + 1,
                };
            }
        }

        #[inductive(combiner_send_skip)]
        fn combiner_send_skip_inductive(pre: Self, post: Self) {
            // Only combiner changes: Responding{elems, j} -> Responding{elems, j+1}
            // elems[j] = None (from transition precondition)
            // clients, slots, requests, responses unchanged

            let j = pre.combiner.get_Responding_idx();
            let elems = pre.combiner.get_Responding_elems();

            // Key fact: elems[j] = None
            assert(elems.index(j as int) == Option::<int>::None);

            // not_waiting_inv: clients and slots unchanged
            assert forall |i: nat| #[trigger] post.valid_idx(i) && post.clients.index(i).is_Idle()
                implies !post.slots.index(i) by {
                assert(pre.not_waiting_inv());
            };

            // waiting_inv
            assert forall |i: nat| #[trigger] post.client_waiting(i)
                implies post.request_stored(i) || post.response_stored(i) || post.combiner_has(i) by {
                assert(pre.waiting_inv());
                // client_waiting unchanged (clients unchanged)
                assert(pre.client_waiting(i));
                if pre.combiner_has(i) {
                    // pre.combiner_has(i): i >= j && elems[i].is_Some()
                    // Since elems[j] = None and elems[i].is_Some(), i != j
                    // So i > j, hence i >= j+1
                    // post.combiner_has(i): valid_idx(i) && i >= j+1 && elems[i].is_Some()
                    assert(i >= j);
                    assert(elems.index(i as int).is_Some());
                    assert(i != j);
                    assert(i > j);
                    assert(i >= j + 1);
                    assert(post.combiner_has(i));
                } else if pre.request_stored(i) {
                    assert(post.request_stored(i));
                } else {
                    assert(pre.response_stored(i));
                    assert(post.response_stored(i));
                }
            };
        }

        #[inductive(combiner_go_to_responding)]
        fn combiner_go_to_responding_inductive(pre: Self, post: Self) {
            // Combiner: Collecting{elems, len=num_clients} -> Responding{elems, idx=0}
            // All other fields unchanged

            let elems = pre.combiner.get_Collecting_elems();

            // post.combiner = Responding{elems, 0}
            assert(post.combiner == Combiner::Responding { elems: elems, idx: 0nat });

            // clients_size: elems.len() = num_clients, 0 <= 0 <= num_clients ✓

            // not_waiting_inv: clients and slots unchanged
            assert forall |i: nat| #[trigger] post.valid_idx(i) && post.clients.index(i).is_Idle()
                implies !post.slots.index(i) by {
                assert(pre.not_waiting_inv());
            };

            // waiting_inv:
            // pre.combiner_has(i) in Collecting{elems, num_clients}: i < num_clients && elems[i].is_Some()
            //   = valid_idx(i) && elems[i].is_Some()
            // post.combiner_has(i) in Responding{elems, 0}: i >= 0 && elems[i].is_Some()
            //   = valid_idx(i) && elems[i].is_Some() (since i >= 0 always for nat)
            // So pre.combiner_has(i) == post.combiner_has(i) for all i
            assert forall |i: nat| #[trigger] post.client_waiting(i)
                implies post.request_stored(i) || post.response_stored(i) || post.combiner_has(i) by {
                assert(pre.waiting_inv());
                assert(pre.client_waiting(i));
                if pre.combiner_has(i) {
                    // pre.combiner_has(i): valid_idx(i) && i < num_clients && elems[i].is_Some()
                    // (since elems.len() = num_clients)
                    assert(elems.index(i as int).is_Some());
                    // post.combiner_has(i): valid_idx(i) && i >= 0 && elems[i].is_Some() = true
                    assert(post.combiner_has(i));
                } else if pre.request_stored(i) {
                    assert(post.request_stored(i));
                } else {
                    assert(pre.response_stored(i));
                    assert(post.response_stored(i));
                }
            };

            // combiner_has_inv:
            // post.combiner_has(i): valid_idx(i) && i >= 0 && elems[i].is_Some()
            // = valid_idx(i) && elems[i].is_Some()
            // pre.combiner_has(i): valid_idx(i) && i < num_clients && elems[i].is_Some()
            // = valid_idx(i) && elems[i].is_Some() (since num_clients = elems.len())
            // So post.combiner_has(i) => pre.combiner_has(i)
            assert forall |i: nat| #[trigger] post.combiner_has(i)
                implies post.client_waiting(i)
                    && post.slots.index(i)
                    && post.combiner_rid(i) == post.clients.index(i).get_Waiting_rid()
                    && !post.request_stored(i) by {
                // post.combiner_has(i): i >= 0 && elems[i].is_Some()
                assert(elems.index(i as int).is_Some());
                // pre.combiner_has(i): i < elems.len() = num_clients && elems[i].is_Some()
                // valid_idx(i) is needed: post.valid_idx(i) = pre.valid_idx(i) (num_clients unchanged)
                assert(pre.combiner_has(i));
                assert(pre.combiner_has_inv());
                assert(pre.client_waiting(i));
                assert(pre.slots.index(i));
                assert(!pre.request_stored(i));
                // combiner_rid: same in pre and post (both use elems)
                assert(pre.combiner_rid(i) == post.combiner_rid(i));
            };
        }

        transition!{
            combiner_go_to_collecting() {
                require(pre.combiner.is_Responding());
                require(pre.combiner.get_Responding_idx() == pre.num_clients);
                update combiner = Combiner::Collecting{ elems: Seq::empty() };
            }
        }

        #[inductive(combiner_go_to_collecting)]
        fn combiner_go_to_collecting_inductive(pre: Self, post: Self) {
            // Combiner: Responding{elems, idx=num_clients} -> Collecting{empty}
            // All other fields unchanged

            let idx = pre.combiner.get_Responding_idx();
            // idx = num_clients

            // post.combiner = Collecting{empty}
            assert(post.combiner == Combiner::Collecting { elems: Seq::empty() });

            // clients_size: Collecting{empty}, len = 0 <= num_clients ✓

            // not_waiting_inv: clients and slots unchanged
            assert forall |i: nat| #[trigger] post.valid_idx(i) && post.clients.index(i).is_Idle()
                implies !post.slots.index(i) by {
                assert(pre.not_waiting_inv());
            };

            // Key observation: pre.combiner_has(i) = false for all i
            // Because combiner_has in Responding{elems, num_clients}: i >= num_clients && ...
            // But valid_idx(i) requires i < num_clients. Contradiction.
            assert forall |i: nat| !pre.combiner_has(i) by {
                if pre.combiner_has(i) {
                    // pre.combiner_has(i) requires valid_idx(i) && i >= num_clients
                    // valid_idx(i) requires i < num_clients
                    // i >= num_clients && i < num_clients is impossible
                    assert(pre.valid_idx(i));
                    assert(i >= idx);  // idx = num_clients
                    assert(i < pre.num_clients);  // from valid_idx
                }
            };

            // waiting_inv: pre.combiner_has(i) = false, so from pre.waiting_inv:
            // client_waiting(i) => request_stored(i) || response_stored(i)
            // These are unchanged in post, and post.combiner_has(i) = false (Collecting{empty})
            assert forall |i: nat| #[trigger] post.client_waiting(i)
                implies post.request_stored(i) || post.response_stored(i) || post.combiner_has(i) by {
                assert(pre.waiting_inv());
                assert(pre.client_waiting(i));
                assert(!pre.combiner_has(i));
                // From pre.waiting_inv: request_stored(i) || response_stored(i)
                assert(pre.request_stored(i) || pre.response_stored(i));
                if pre.request_stored(i) {
                    assert(post.request_stored(i));
                } else {
                    assert(pre.response_stored(i));
                    assert(post.response_stored(i));
                }
            };

            // combiner_has_inv: post.combiner = Collecting{empty}
            // post.combiner_has(i) = i < 0 = false -> vacuously true
            assert forall |i: nat| #[trigger] post.combiner_has(i)
                implies post.client_waiting(i)
                    && post.slots.index(i)
                    && post.combiner_rid(i) == post.clients.index(i).get_Waiting_rid()
                    && !post.request_stored(i) by {
                // post.combiner_has(i) = i < empty.len() = i < 0 = false -> vacuous
                assert(!post.combiner_has(i));
            };
        }

    }
}

fn main() {}
