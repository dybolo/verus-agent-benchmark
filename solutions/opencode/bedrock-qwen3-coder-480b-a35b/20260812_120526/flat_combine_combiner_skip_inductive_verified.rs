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
            let j = pre.combiner.get_Collecting_elems().len();
            assert(j < pre.num_clients);
            
            // Proof that not_waiting_inv holds
            assert forall |i: nat| #[trigger] post.valid_idx(i) && post.clients.index(i).is_Idle() 
            implies !post.slots.index(i) by {
                // The combiner_skip transition does not modify clients or slots
                assert(post.clients === pre.clients);
                assert(post.slots === pre.slots);
                
                // Since states are identical, the invariant holds by induction hypothesis
                assert(pre.valid_idx(i));
                assert(pre.clients.index(i).is_Idle() ==> !pre.slots.index(i)); // by pre.not_waiting_inv
                assert(post.clients.index(i).is_Idle() ==> !post.slots.index(i));
            }
            
            // Proof that waiting_inv holds
            assert forall |i: nat| #[trigger] post.client_waiting(i) 
            implies post.request_stored(i) || post.response_stored(i) || post.combiner_has(i) by {
                // The combiner_skip transition does not modify clients, requests, or responses
                assert(post.clients === pre.clients);
                assert(post.requests === pre.requests);
                assert(post.responses === pre.responses);
                
                assert(pre.valid_idx(i));
                assert(post.client_waiting(i) == pre.client_waiting(i));
                
                if post.client_waiting(i) {
                    assert(pre.client_waiting(i));
                    // By the inductive hypothesis, the invariant holds for pre
                    assert(pre.request_stored(i) || pre.response_stored(i) || pre.combiner_has(i));
                    
                    // Now we need to check how the combiner state changed affects this
                    // post.combiner = Combiner::Collecting{elems: pre.combiner.get_Collecting_elems().push(Option::None)}
                    
                    if pre.request_stored(i) {
                        // requests unchanged, so post.request_stored(i)
                        assert(post.request_stored(i));
                    }
                    if pre.response_stored(i) {
                        // responses unchanged, so post.response_stored(i)
                        assert(post.response_stored(i));
                    }
                    if pre.combiner_has(i) {
                        // Need to check if post.combiner_has(i) still holds
                        // pre.combiner_has(i) means:
                        //   i < pre.combiner.get_Collecting_elems().len() && pre.combiner.get_Collecting_elems().index(i as int).is_Some()
                        //
                        // post.combiner_has(i) means:
                        //   i < post.combiner.get_Collecting_elems().len() && post.combiner.get_Collecting_elems().index(i as int).is_Some()
                        //   i < pre.combiner.get_Collecting_elems().len() + 1 && post.combiner.get_Collecting_elems().index(i as int).is_Some()
                        
                        if i < pre.combiner.get_Collecting_elems().len() {
                            // The element at index i is unchanged
                            assert(post.combiner.get_Collecting_elems().index(i as int) === pre.combiner.get_Collecting_elems().index(i as int));
                            assert(post.combiner_has(i));
                        } else {
                            // i >= pre.combiner.get_Collecting_elems().len() = j
                            // Since we appended Option::None, post.combiner.get_Collecting_elems().len() = j + 1
                            // If i > j, then i >= j+1, so i < j+1 is false, so post.combiner_has(i) is false
                            // If i = j, then post.combiner.get_Collecting_elems().index(j) = Option::None, so post.combiner_has(j) is false
                            
                            // But we assumed pre.combiner_has(i), which means i < pre.combiner.get_Collecting_elems().len() = j
                            // This contradicts i >= j, so this case is impossible
                            assert(false);
                        }
                    }
                }
            }
            
            // Proof that request_stored_inv holds
            assert forall |i: nat| #[trigger] post.request_stored(i) 
            implies post.client_waiting(i)
                && post.requests.index(i).rid == post.clients.index(i).get_Waiting_rid()
                && post.slots.index(i) by {
                // The combiner_skip transition does not modify requests, clients, or slots
                assert(post.requests === pre.requests);
                assert(post.clients === pre.clients);
                assert(post.slots === pre.slots);
                
                // Since post.request_stored(i), and requests are unchanged, pre.request_stored(i)
                assert(pre.request_stored(i));
                
                // From pre's invariant (which we assume holds)
                assert(pre.valid_idx(i));
                assert(pre.client_waiting(i)
                    && pre.requests.index(i).rid == pre.clients.index(i).get_Waiting_rid()
                    && pre.slots.index(i));
                
                // Since all components are unchanged:
                assert(post.client_waiting(i)
                    && post.requests.index(i).rid == post.clients.index(i).get_Waiting_rid()
                    && post.slots.index(i));
            }
            
            // Proof that response_stored_inv holds
            assert forall |i: nat| #[trigger] post.response_stored(i) 
            implies post.client_waiting(i)
                && post.responses.index(i).rid == post.clients.index(i).get_Waiting_rid()
                && !post.slots.index(i) by {
                // The combiner_skip transition does not modify responses, clients, or slots
                assert(post.responses === pre.responses);
                assert(post.clients === pre.clients);
                assert(post.slots === pre.slots);
                
                // Since post.response_stored(i), and responses are unchanged, pre.response_stored(i)
                assert(pre.response_stored(i));
                
                // From pre's invariant (which we assume holds)
                assert(pre.valid_idx(i));
                assert(pre.client_waiting(i)
                    && pre.responses.index(i).rid == pre.clients.index(i).get_Waiting_rid()
                    && !pre.slots.index(i));
                
                // Since all components are unchanged:
                assert(post.client_waiting(i)
                    && post.responses.index(i).rid == post.clients.index(i).get_Waiting_rid()
                    && !post.slots.index(i));
            }
            
            // Proof that combiner_has_inv holds
            assert forall |i: nat| #[trigger] post.combiner_has(i) 
            implies post.client_waiting(i)
                && post.slots.index(i)
                && post.combiner_rid(i) == post.clients.index(i).get_Waiting_rid()
                && !post.request_stored(i) by {
                let j = pre.combiner.get_Collecting_elems().len();
                
                // post.combiner_has(i) means i is a valid index and the combiner has a request at position i
                assert(post.valid_idx(i));
                
                // post.combiner = Combiner::Collecting{elems: pre.combiner.get_Collecting_elems().push(Option::None)}
                // So post.combiner.get_Collecting_elems() = pre.combiner.get_Collecting_elems().push(Option::None)
                
                // post.combiner_has(i) is true, which means:
                // i < post.combiner.get_Collecting_elems().len() && post.combiner.get_Collecting_elems().index(i as int).is_Some()
                // i < pre.combiner.get_Collecting_elems().len() + 1 && post.combiner.get_Collecting_elems().index(i as int).is_Some()
                
                if i < j {
                    // i < j, so the element at index i is unchanged from pre to post
                    assert(post.combiner.get_Collecting_elems().index(i as int) === pre.combiner.get_Collecting_elems().index(i as int));
                    assert(pre.combiner_has(i));
                    
                    // By inductive hypothesis on pre
                    assert(pre.client_waiting(i)
                        && pre.slots.index(i)
                        && pre.combiner_rid(i) == pre.clients.index(i).get_Waiting_rid()
                        && !pre.request_stored(i));
                    
                    // Since clients, slots, and requests are unchanged:
                    assert(post.client_waiting(i)
                        && post.slots.index(i)
                        && post.combiner_rid(i) == post.clients.index(i).get_Waiting_rid()
                        && !post.request_stored(i));
                } else {
                    // i >= j
                    // Since post.combiner.get_Collecting_elems().len() = j + 1, we have i < j + 1, so i <= j
                    // Combined with i >= j, we have i = j
                    assert(i == j);
                    
                    // At index j, we appended Option::None, so:
                    assert(post.combiner.get_Collecting_elems().index(j as int) === Option::None);
                    
                    // But this contradicts post.combiner_has(j), which requires the element to be Some
                    // This is impossible, so we have a contradiction
                    assert(false);
                }
            }
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