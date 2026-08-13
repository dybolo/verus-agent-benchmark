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
            // This transition only changes the combiner state from Collecting to Responding
            // with idx=0. All other fields remain unchanged.
            
            // Show that not_waiting_inv still holds
            assert forall |i: nat| #[trigger] post.valid_idx(i) && post.clients.index(i).is_Idle() 
            implies !post.slots.index(i) by {
                // All fields except combiner are unchanged
                assert(post.clients.index(i) == pre.clients.index(i));
                assert(post.slots.index(i) == pre.slots.index(i));
                assert(pre.valid_idx(i) == post.valid_idx(i));
                
                // Since the invariant held for pre, and clients/slots unchanged:
                assert(pre.clients.index(i).is_Idle() ==> !pre.slots.index(i));
                assert(post.clients.index(i).is_Idle() ==> !post.slots.index(i));
            }
            
            // Show that waiting_inv still holds
            assert forall |i: nat| #[trigger] post.client_waiting(i) 
            implies post.request_stored(i) || post.response_stored(i) || post.combiner_has(i) by {
                // All fields except combiner are unchanged
                assert(post.clients.index(i) == pre.clients.index(i));
                assert(post.requests.dom() == pre.requests.dom());
                assert(post.responses.dom() == pre.responses.dom());
                assert(post.requests.dom().contains(i) == pre.requests.dom().contains(i));
                assert(post.responses.dom().contains(i) == pre.responses.dom().contains(i));
                assert(post.client_waiting(i) == pre.client_waiting(i));
                assert(post.request_stored(i) == pre.request_stored(i));
                assert(post.response_stored(i) == pre.response_stored(i));
                
                // The combiner state changed from Collecting to Responding with idx=0
                assert(post.combiner.is_Responding());
                assert(post.combiner.get_Responding_elems() == pre.combiner.get_Collecting_elems());
                assert(post.combiner.get_Responding_idx() == 0);
                
                // Since pre satisfied the invariant:
                assert(pre.client_waiting(i) ==> pre.request_stored(i) || pre.response_stored(i) || pre.combiner_has(i));
                
                // For post, we need to check if combiner_has(i) holds
                // In the new state, combiner_has(i) means:
                // i >= idx (which is 0) && elems.index(i).is_Some()
                // Since idx=0, this simplifies to: i >= 0 && elems.index(i).is_Some()
                // Which further simplifies to: elems.index(i).is_Some() (since i is nat)
                
                // The elems array is the same as pre.combiner.get_Collecting_elems()
                // By the transition precondition, this has length num_clients
                // So for any valid i, elems.index(i) exists
                
                if post.client_waiting(i) {
                    assert(pre.client_waiting(i));
                    if pre.request_stored(i) {
                        assert(post.request_stored(i)); // unchanged
                    } else if pre.response_stored(i) {
                        assert(post.response_stored(i)); // unchanged
                    } else {
                        assert(pre.combiner_has(i));
                        // In pre: i < elems.len() && elems.index(i).is_Some()
                        // In post: i >= 0 && elems.index(i).is_Some() (since idx=0)
                        // Since i is nat, i >= 0 is true
                        // Since elems is unchanged and i < elems.len() was true in pre,
                        // elems.index(i).is_Some() is still true in post
                        assert(post.combiner_has(i));
                    }
                }
            }
            
            // Show that request_stored_inv still holds
            assert forall |i: nat| #[trigger] post.request_stored(i) 
            implies post.client_waiting(i)
                && post.requests.index(i).rid == post.clients.index(i).get_Waiting_rid()
                && post.slots.index(i) by {
                // All relevant fields are unchanged
                assert(post.requests.dom() == pre.requests.dom());
                assert(post.clients.dom() == pre.clients.dom());
                assert(post.slots.dom() == pre.slots.dom());
                assert(post.requests.index(i) == pre.requests.index(i));
                assert(post.clients.index(i) == pre.clients.index(i));
                assert(post.slots.index(i) == pre.slots.index(i));
                
                // Since the invariant held for pre:
                assert(pre.request_stored(i) ==> pre.client_waiting(i)
                    && pre.requests.index(i).rid == pre.clients.index(i).get_Waiting_rid()
                    && pre.slots.index(i));
                    
                // And all conditions are unchanged in post:
                assert(post.request_stored(i) ==> post.client_waiting(i)
                    && post.requests.index(i).rid == post.clients.index(i).get_Waiting_rid()
                    && post.slots.index(i));
            }
            
            // Show that response_stored_inv still holds
            assert forall |i: nat| #[trigger] post.response_stored(i) 
            implies post.client_waiting(i)
                && post.responses.index(i).rid == post.clients.index(i).get_Waiting_rid()
                && !post.slots.index(i) by {
                // All relevant fields are unchanged
                assert(post.responses.dom() == pre.responses.dom());
                assert(post.clients.dom() == pre.clients.dom());
                assert(post.slots.dom() == pre.slots.dom());
                assert(post.responses.index(i) == pre.responses.index(i));
                assert(post.clients.index(i) == pre.clients.index(i));
                assert(post.slots.index(i) == pre.slots.index(i));
                
                // Since the invariant held for pre:
                assert(pre.response_stored(i) ==> pre.client_waiting(i)
                    && pre.responses.index(i).rid == pre.clients.index(i).get_Waiting_rid()
                    && !pre.slots.index(i));
                    
                // And all conditions are unchanged in post:
                assert(post.response_stored(i) ==> post.client_waiting(i)
                    && post.responses.index(i).rid == post.clients.index(i).get_Waiting_rid()
                    && !post.slots.index(i));
            }
            
            // Show that combiner_has_inv still holds
            assert forall |i: nat| #[trigger] post.combiner_has(i) 
            implies post.client_waiting(i)
                && post.slots.index(i)
                && post.combiner_rid(i) == post.clients.index(i).get_Waiting_rid()
                && !post.request_stored(i) by {
                // In post, combiner_has(i) means:
                // valid_idx(i) && i >= post.combiner.get_Responding_idx() && post.combiner.get_Responding_elems().index(i).is_Some()
                // Since idx=0, this becomes:
                // valid_idx(i) && post.combiner.get_Responding_elems().index(i).is_Some()
                
                assert(post.combiner.get_Responding_elems() == pre.combiner.get_Collecting_elems());
                
                // If post.combiner_has(i), then:
                // 1. post.valid_idx(i) (given)
                // 2. post.combiner.get_Responding_elems().index(i).is_Some() (given)
                
                // Since the elems array is unchanged:
                assert(pre.combiner.get_Collecting_elems().index(i as int).is_Some());
                
                // In pre, combiner_has(i) meant:
                // pre.valid_idx(i) && i < pre.combiner.get_Collecting_elems().len() && pre.combiner.get_Collecting_elems().index(i).is_Some()
                
                // Since pre satisfied combiner_has_inv:
                if pre.combiner_has(i) {
                    assert(pre.client_waiting(i));
                    assert(pre.slots.index(i));
                    assert(pre.combiner_rid(i) == pre.clients.index(i).get_Waiting_rid());
                    assert(!pre.request_stored(i));
                }
                
                // All relevant fields are unchanged:
                assert(post.client_waiting(i) == pre.client_waiting(i));
                assert(post.slots.index(i) == pre.slots.index(i));
                assert(post.clients.index(i) == pre.clients.index(i));
                assert(post.requests.dom() == pre.requests.dom());
                assert(post.request_stored(i) == pre.request_stored(i));
                
                // The RID is determined by the elems array which is unchanged:
                assert(post.combiner_rid(i) == pre.combiner_rid(i));
                assert(pre.combiner_rid(i) == pre.clients.index(i).get_Waiting_rid());
                assert(post.clients.index(i).get_Waiting_rid() == pre.clients.index(i).get_Waiting_rid());
                assert(post.combiner_rid(i) == post.clients.index(i).get_Waiting_rid());
                
                // Therefore:
                assert(post.client_waiting(i));
                assert(post.slots.index(i));
                assert(post.combiner_rid(i) == post.clients.index(i).get_Waiting_rid());
                assert(!post.request_stored(i));
            }
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
