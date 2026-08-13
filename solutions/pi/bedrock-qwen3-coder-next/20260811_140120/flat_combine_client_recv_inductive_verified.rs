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
        fn init_inductive(post: Self, num_clients: nat) { }

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
            admit()
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
        fn client_recv_inductive(pre: Self, post: Self, j: nat)
        {
            broadcast use imap::group_imap_lemmas;
            broadcast use map::group_map_lemmas;
            broadcast use set::group_set_lemmas;
            broadcast use iset::group_iset_lemmas;
            broadcast use seq::group_seq_lemmas;

            // For not_waiting_inv in post-state
            // We need to show: post.clients[j] is Idle ==> !post.slots[j]
            // Since post.clients[j] is Idle (from add clients += [j => Client::Idle]),
            // we need to show !post.slots[j]
            // From have slots >= [j => false], we have post.slots.dom().contains(j) && post.slots[j] == false
            // So !post.slots[j] holds.

            // For waiting_inv in post-state
            // We need to show: post.client_waiting(j) ==> post.request_stored(j) || post.response_stored(j) || post.combiner_has(j)
            // Since post.clients[j] is Idle, post.client_waiting(j) is false, so the implication is vacuously true.

            // For request_stored_inv in post-state
            // We need to show: post.request_stored(j) ==> post.client_waiting(j) && ... 
            // For post.requests[j] to be stored, pre.requests[j] must be stored (we don't modify requests).
            // But from pre.client_waiting(j) and the pre-state invariants, if pre.request_stored(j),
            // then pre.slots[j] == true.
            // But from have slots >= [j => false], post.slots[j] == false.
            // And since we don't modify slots, post.slots = pre.slots, so pre.slots[j] == false.
            // Contradiction! So pre.requests[j] is not stored, and post.requests[j] is not stored.
            // So post.request_stored(j) is false, and the implication is vacuously true.

            // For response_stored_inv in post-state
            // We need to show: post.response_stored(j) ==> ...
            // We withdraw responses[j], so post.responses.dom().contains(j) == false
            // So post.response_stored(j) is false, and the implication is vacuously true.

            // For combiner_has_inv in post-state
            // We need to show: post.combiner_has(j) ==> ...
            // post.combiner = pre.combiner (we don't modify combiner in client_recv).
            // If pre.combiner_has(j), then from combiner_has_inv in pre-state:
            //     pre.slots[j] == true
            // But from have slots >= [j => false], post.slots[j] == false.
            // Since we don't modify slots, pre.slots[j] == false.
            // Contradiction! So pre.combiner_has(j) is false, and post.combiner_has(j) is false.
            // So the implication is vacuously true.

            // Now, let's use the pre-state invariants to prove the above.
            
            // From waiting_inv in pre-state and pre.client_waiting(j):
            assert(pre.request_stored(j) || pre.response_stored(j) || pre.combiner_has(j)) by {
                assert(pre.client_waiting(j));
                assert(pre.waiting_inv());
            };

            // From not_waiting_inv in pre-state, we know that if clients[j] is waiting, slots[j] could be true or false.
            // But from have slots >= [j => false], we have post.slots[j] == false.
            // Since we don't modify slots, post.slots = pre.slots, so pre.slots[j] == false.

            // From request_stored_inv in pre-state:
            //     pre.request_stored(j) ==> pre.slots[j]
            // But pre.slots[j] == false, so !pre.request_stored(j).
            assert(!pre.request_stored(j)) by {
                assert(pre.request_stored_inv());
                if pre.request_stored(j) {
                    assert(pre.slots.index(j));
                }
            };

            // From combiner_has_inv in pre-state:
            //     pre.combiner_has(j) ==> pre.slots[j]
            // But pre.slots[j] == false, so !pre.combiner_has(j).
            assert(!pre.combiner_has(j)) by {
                assert(pre.combiner_has_inv());
                if pre.combiner_has(j) {
                    assert(pre.slots.index(j));
                }
            };

            // Since pre.request_stored(j) == false and pre.combiner_has(j) == false,
            // and from waiting_inv we have pre.request_stored(j) || pre.response_stored(j) || pre.combiner_has(j),
            // we must have pre.response_stored(j).
            assert(pre.response_stored(j)) by {
                if !pre.response_stored(j) {
                    assert(false); // contradiction!
                }
            };

            // From response_stored_inv in pre-state:
            //     pre.response_stored(j) ==> !pre.slots[j]
            // So !pre.slots[j], which we already knew.
            assert(!pre.slots.index(j)) by {
                assert(pre.response_stored_inv());
            };

            // After withdrawing responses[j], post.responses[j] is removed.
            // So post.responses.dom().contains(j) == false.
            assert(!post.response_stored(j)) by {
                // withdraw responses -= [j => response] means post.responses = pre.responses.remove(j)
            };

            // We need to show !post.slots[j].
            // From have slots >= [j => false], we have post.slots.dom().contains(j) && post.slots[j] == false.
            assert(post.slots.dom().contains(j)) by {
                // have slots >= [j => false] means [j => false].submap_of(post.slots)
                // which means post.slots.dom().contains(j) && post.slots[j] == false
            };
            assert(!post.slots.index(j)) by {
                // From the above, post.slots[j] == false
            };

            // post.clients[j] == Idle is from the add operation.
            // After add clients += [j => Client::Idle], post.clients[j] == Client::Idle
            assert(post.clients.dom().contains(j)) by {
                // add clients += [j => Client::Idle]
            };
            assert(post.clients.index(j).is_Idle()) by {
                // add clients += [j => Client::Idle]
            };
            assert(post.valid_idx(j)) by {
                // From require(0 <= j && j < pre.num_clients) and pre.num_clients = post.num_clients
            };
            assert(!post.slots.index(j)) by {
                // As shown above
            };

            // Now we can prove the invariants for client j:
            // For not_waiting_inv:
            // post.clients[j] is Idle and !post.slots[j], so the invariant holds for j.
            assert(post.clients.dom().contains(j) && post.clients.index(j).is_Idle() ==> !post.slots.index(j)) by {
                assert(post.clients.dom().contains(j));
                assert(post.clients.index(j).is_Idle());
                assert(!post.slots.index(j));
            };

            // For waiting_inv:
            // post.clients[j] is Idle, so post.client_waiting(j) is false.
            assert(!post.client_waiting(j)) by {
                assert(post.clients.dom().contains(j));
                assert(post.clients.index(j).is_Idle());
            };
            // The implication is vacuously true.

            // For request_stored_inv:
            // We need to show: post.request_stored(j) ==> ...
            // But post.clients[j] is Idle, so if post.request_stored(j), the invariant would require post.clients[j] to be Waiting.
            // Contradiction! So post.request_stored(j) must be false.
            assert(!post.request_stored(j)) by {
                // post.requests = pre.requests, and we've shown !pre.request_stored(j)
            };
            // The implication is vacuously true.

            // For response_stored_inv:
            // post.responses[j] is not stored (we withdrew it), so the implication is vacuously true.

            // For combiner_has_inv:
            // post.combiner = pre.combiner, and we've shown !pre.combiner_has(j), so the implication is vacuously true.
            assert(!post.combiner_has(j)) by {
                // post.combiner = pre.combiner (no update to combiner in client_recv)
                // And we've shown !pre.combiner_has(j)
            };
            // The implication is vacuously true.
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
        fn combiner_recv_inductive(pre: Self, post: Self)
        {
            admit()
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
            admit()
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
            admit()
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
            admit()
        }

        #[inductive(combiner_go_to_responding)]
        fn combiner_go_to_responding_inductive(pre: Self, post: Self) {
            admit()
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
            admit()
        }

    }
}

fn main() {}
