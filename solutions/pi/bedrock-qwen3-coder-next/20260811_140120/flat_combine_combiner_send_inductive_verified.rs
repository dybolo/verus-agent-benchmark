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
                Combiner::Collecting{elems} => i < elems.len() && i < elems.len() as int && elems.index(i as int).is_Some(),
                Combiner::Responding{elems, idx} => i >= idx && i < elems.len() as int && elems.index(i as int).is_Some(),
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
        fn client_recv_inductive(pre: Self, post: Self, j: nat) {
            admit()
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
        fn combiner_send_inductive(pre: Self, post: Self, response: Response, cur_slot: bool)
        {
            // The transition: combiner_send(j, response, cur_slot) where j = pre.combiner.get_Responding_idx()
            // modifies: slots[j], responses[j], and combiner.idx (from j to j+1)

            // Extract j from pre.combiner for use in the proof
            let j_val = pre.combiner.get_Responding_idx();

            // From the transition precondition, we know:
            // response_opt = pre.combiner.get_Responding_elems().index(j_val as int)
            // response_opt = Option::Some(response.rid)
            // So: pre.combiner.get_Responding_elems().index(j_val as int) = Option::Some(response.rid)

            // This means j_val < pre.combiner.get_Responding_elems().len()
            // And pre.combiner.get_Responding_elems().index(j_val as int).is_Some()

            // From pre invariant combiner_has_inv and pre.combiner_has(j_val):
            pre.combiner_has_inv();
            assert(pre.combiner_has(j_val));
            assert(pre.client_waiting(j_val));
            assert(pre.slots.index(j_val));
            assert(pre.combiner_rid(j_val) == pre.clients.index(j_val).get_Waiting_rid());
            assert(!pre.request_stored(j_val));

            // Broadcast the necessary lemmas
            broadcast use vstd::iset::group_iset_lemmas;
            broadcast use vstd::imap::group_imap_lemmas;
            broadcast use vstd::seq::group_seq_lemmas;

            // Analyze what changed:
            // 1. slots[j_val] changed from cur_slot to false
            // 2. responses[j_val] is now Some(response)
            // 3. combiner changed from Responding{elems, idx=j_val} to Responding{elems, idx=j_val+1}

            // For all other indices i != j_val, the state is unchanged.

            // Key facts about the transition (from the state machine semantics):
            // post.clients = pre.clients
            // post.slots = pre.slots.remove(j_val).insert(j_val, false)
            // post.responses = pre.responses.insert(j_val, response)
            // post.requests = pre.requests
            // post.combiner = Combiner::Responding { elems: pre.combiner.get_Responding_elems(), idx: j_val + 1 }

            // 2. waiting_inv in post:
            // forall |i: nat| post.client_waiting(i) ==> post.request_stored(i) || post.response_stored(i) || post.combiner_has(i)
            assert(forall |i: nat| post.client_waiting(i) ==>
                post.request_stored(i) || post.response_stored(i) || post.combiner_has(i)) by {
                assert(pre.clients == post.clients);
                assert(post.responses.dom().contains(j_val) && post.responses.index(j_val) == response);
                assert(post.requests == pre.requests);
                assert(post.slots == pre.slots.remove(j_val).insert(j_val, false));
                assert(post.combiner.is_Responding());
                // For i != j_val: All fields unchanged, use pre.waiting_inv
                // For i == j_val: post.response_stored(j_val) is true
                assert(post.waiting_inv());
            };
            assert(post.waiting_inv());

            // 3. request_stored_inv in post:
            // forall |i: nat| post.request_stored(i) ==> post.client_waiting(i) && post.requests[i].rid == post.clients[i].rid && post.slots[i]
            assert(forall |i: nat| post.request_stored(i) ==>
                post.client_waiting(i) && post.requests.index(i).rid == post.clients.index(i).get_Waiting_rid() && post.slots.index(i)) by {
                assert(post.requests == pre.requests);
                assert(post.clients == pre.clients);
                assert(post.slots == pre.slots.remove(j_val).insert(j_val, false));
                assert(!pre.request_stored(j_val));
                // For i != j_val: All fields unchanged, use pre.request_stored_inv
                // For i == j_val: !post.request_stored(j_val), vacuously true
                assert(post.request_stored_inv());
            };
            assert(post.request_stored_inv());

            // 4. response_stored_inv in post:
            // forall |i: nat| post.response_stored(i) ==> post.client_waiting(i) && post.responses[i].rid == post.clients[i].rid && !post.slots[i]
            assert(forall |i: nat| post.response_stored(i) ==>
                post.client_waiting(i) && post.responses.index(i).rid == post.clients.index(i).get_Waiting_rid() && !post.slots.index(i)) by {
                assert(post.responses.dom().contains(j_val) && post.responses.index(j_val) == response);
                assert(post.clients == pre.clients);
                assert(post.slots == pre.slots.remove(j_val).insert(j_val, false));
                assert(!post.slots.index(j_val));
                assert(pre.combiner_rid(j_val) == pre.clients.index(j_val).get_Waiting_rid());
                // From pre.combiner_rid definition (for Responding state):
                // pre.combiner_rid(j_val) = pre.combiner.get_Responding_elems().index(j_val as int).get_Some_0()
                // And from transition: pre.combiner.get_Responding_elems().index(j_val as int) = Option::Some(response.rid)
                // So: pre.combiner.get_Responding_elems().index(j_val as int).get_Some_0() = response.rid
                assert(response.rid == pre.combiner.get_Responding_elems().index(j_val as int).get_Some_0());
                assert(response.rid == pre.clients.index(j_val).get_Waiting_rid());
                // For i != j_val: All fields unchanged, use pre.response_stored_inv
                // For i == j_val: response.rid == pre.clients[j_val].get_Waiting_rid() == post.clients[j_val].get_Waiting_rid()
                assert(post.response_stored_inv());
            };
            assert(post.response_stored_inv());

            // 5. combiner_has_inv in post:
            // forall |i: nat| post.combiner_has(i) ==> post.client_waiting(i) && post.slots[i] && post.combiner_rid(i) == post.clients[i].rid && !post.request_stored(i)
            assert(forall |i: nat| post.combiner_has(i) ==>
                post.client_waiting(i) && post.slots.index(i) && post.combiner_rid(i) == post.clients.index(i).get_Waiting_rid() && !post.request_stored(i)) by {
                assert(post.combiner.is_Responding());
                // For i < j_val or i == j_val: post.combiner_has(i) is false (because i < j_val+1 = post.combiner.idx)
                // For i > j_val: post.combiner_has(i) = pre.combiner_has(i)
                assert(post.combiner_has_inv());
            };
            assert(post.combiner_has_inv());

            // 6. slots_complete in post:
            // post.slots.dom() = pre.slots.dom()
            assert(forall |i: nat| (0 <= i && i < post.num_clients) == post.slots.dom().contains(i)) by {
                assert(post.num_clients == pre.num_clients);
                assert(post.slots == pre.slots.remove(j_val).insert(j_val, false));
                assert(post.slots.dom() == pre.slots.dom());
                assert(post.slots_complete());
            };
            assert(post.slots_complete());

            // 7. clients_complete in post:
            // post.clients.dom() = pre.clients.dom()
            assert(forall |i: nat| (0 <= i && i < post.num_clients) == post.clients.dom().contains(i)) by {
                assert(post.num_clients == pre.num_clients);
                assert(post.clients == pre.clients);
                assert(post.clients_complete());
            };
            assert(post.clients_complete());

            // 8. clients_size in post:
            // post.combiner = Responding{elems, idx=j_val+1}
            assert(match post.combiner {
                Combiner::Collecting{elems} => elems.len() <= post.num_clients,
                Combiner::Responding{elems, idx} => elems.len() == post.num_clients && 0 <= idx && idx <= post.num_clients,
            }) by {
                assert(post.combiner.is_Responding());
                let post_combiner = post.combiner;
                let pre_combiner = pre.combiner;
                assert(pre_combiner.is_Responding());
                assert(pre.clients_size());
                let pre_elems = pre_combiner.get_Responding_elems();
                let pre_idx = pre_combiner.get_Responding_idx();
                let post_elems = post_combiner.get_Responding_elems();
                let post_idx = post_combiner.get_Responding_idx();
                assert(post_elems.len() == pre_elems.len());
                assert(post_idx == j_val + 1);
                assert(0 <= j_val);
                assert(j_val < pre.num_clients);
                assert(j_val + 1 <= pre.num_clients);
                assert(post.num_clients == pre.num_clients);
            };
            assert(post.clients_size());

            // All invariants hold!
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
