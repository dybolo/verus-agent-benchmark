#[allow(unused_imports)]
use verus_builtin::*;
use verus_builtin_macros::*;
use vstd::map::*;
use vstd::multiset::*;
use vstd::prelude::*;
use vstd::seq::*;
use vstd::{pervasive::*, *};

use verus_state_machines_macros::tokenized_state_machine;


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

} 
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


        transition!{
            client_send(j: nat, request: Request, cur_slot: bool) {
                require(0 <= j && j < pre.num_clients);

                remove clients -= [j => Client::Idle];
                add    clients += [j => Client::Waiting{rid: request.rid}];

                remove slots -= [j => cur_slot];
                add    slots += [j => true];

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

                remove clients -= [j => let Client::Waiting{rid}];
                add    clients += [j => Client::Idle];

                have slots >= [j => false];

                withdraw responses -= [j => let response] by {
                    assert(pre.client_waiting(j));
                };

                assert(response.rid == rid) by {
                    assert(pre.client_waiting(j));
                };
            }
        }

        #[inductive(client_recv)]
        fn client_recv_inductive(pre: Self, post: Self, j: nat) {
            admit()
        }


        transition!{
            combiner_recv() {
                require(pre.combiner.is_Collecting());
                let j = pre.combiner.get_Collecting_elems().len();
                require(0 <= j && j < pre.num_clients);

                have slots >= [j => true];

                withdraw requests -= [j => let request] by {
                    assert(pre.valid_idx(j));
                    assert(pre.client_waiting(j));
                    assert(pre.request_stored(j));
                };

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

                require(response_opt == Option::Some(response.rid));

                remove slots -= [j => cur_slot];
                add    slots += [j => false];

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

                require(equal(response_opt, Option::None));

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
            assert(post.clients == pre.clients);
            assert(post.slots == pre.slots);
            assert(post.requests == pre.requests);
            assert(post.responses == pre.responses);

            assert(post.not_waiting_inv()) by {
                assert forall |i: nat| #[trigger] post.valid_idx(i)
                    && post.clients.index(i).is_Idle() ==> !post.slots.index(i) by {
                    if post.valid_idx(i) && post.clients.index(i).is_Idle() {
                        assert(pre.valid_idx(i));
                        assert(pre.clients.index(i).is_Idle());
                        assert(pre.not_waiting_inv());
                        assert(!pre.slots.index(i));
                    }
                }
            };

            assert(post.waiting_inv()) by {
                assert forall |i: nat| #[trigger] post.client_waiting(i) ==>
                    post.request_stored(i) || post.response_stored(i) || post.combiner_has(i) by {
                    if post.client_waiting(i) {
                        assert(pre.client_waiting(i));
                        assert(pre.waiting_inv());
                        assert(pre.request_stored(i) || pre.response_stored(i) || pre.combiner_has(i));
                        if pre.request_stored(i) {
                            assert(post.request_stored(i));
                        } else if pre.response_stored(i) {
                            assert(post.response_stored(i));
                        } else {
                            assert(post.combiner_has(i));
                        }
                    }
                }
            };

            assert(post.request_stored_inv()) by {
                assert forall |i: nat| #[trigger] post.request_stored(i) ==>
                    post.client_waiting(i)
                    && post.requests.index(i).rid == post.clients.index(i).get_Waiting_rid()
                    && post.slots.index(i) by {
                    if post.request_stored(i) {
                        assert(pre.request_stored(i));
                        assert(pre.request_stored_inv());
                        assert(pre.client_waiting(i));
                        assert(pre.requests.index(i).rid == pre.clients.index(i).get_Waiting_rid());
                        assert(pre.slots.index(i));
                    }
                }
            };

            assert(post.response_stored_inv()) by {
                assert forall |i: nat| #[trigger] post.response_stored(i) ==>
                    post.client_waiting(i)
                    && post.responses.index(i).rid == post.clients.index(i).get_Waiting_rid()
                    && !post.slots.index(i) by {
                    if post.response_stored(i) {
                        assert(pre.response_stored(i));
                        assert(pre.response_stored_inv());
                        assert(pre.client_waiting(i));
                        assert(pre.responses.index(i).rid == pre.clients.index(i).get_Waiting_rid());
                        assert(!pre.slots.index(i));
                    }
                }
            };
        }

    }
}

fn main() {}
