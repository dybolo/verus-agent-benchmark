#![cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause)]
#![allow(unused_imports)]

use verus_builtin::*;
use verus_builtin_macros::*;
use vstd::atomic_ghost::*;
use vstd::cell::pcell_maybe_uninit::*;
use vstd::prelude::*;
use vstd::*;
use vstd::raw_ptr::MemContents;

use std::sync::atomic::*;

verus! {

// A simple counter, albeit with nothing verified about it.
exec static GLOBAL_COUNTER: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

fn increment_counter() {
    GLOBAL_COUNTER.fetch_add(1, Ordering::Relaxed);
}

// Thread-safe lazy initialization
pub tracked enum GhostState<T: 'static> {
    Uninitialized(PointsTo<Option<T>>),
    Initializing,
    Initialized(&'static PointsTo<Option<T>>),
}

struct_with_invariants!{
    struct Lazy<T: 'static> {
        pub cell: PCell<Option<T>>,
        pub state: vstd::atomic_ghost::AtomicU64<_, GhostState<T>, _>
    }

    spec fn wf(&self) -> bool {
        invariant on state with (cell) is (v: u64, g: GhostState<T>) {
            // State = 0: Uninitialized
            // State = 1: currently initializing
            // State = 2: is initialized
            match g {
                GhostState::Uninitialized(points_to) => {
                    v == 0
                      && points_to.id() == cell.id()
                      && (points_to.mem_contents() == MemContents::Init(None))
                }
                GhostState::Initializing => {
                    v == 1
                }
                GhostState::Initialized(points_to) => {
                    v == 2
                      && points_to.id() == cell.id()
                      && (points_to.mem_contents() matches MemContents::Init(Some(_)))
                }
            }
        }
    }
}

trait Initializable: Sized {
    fn initialize() -> Self;
}

impl<T: Initializable> Lazy<T> {
    const fn new() -> (s: Self)
        ensures
            s.wf(),
    {
        let (pcell, Tracked(points_to)) = PCell::new(None);
        Lazy {
            cell: pcell,
            state: vstd::atomic_ghost::AtomicU64::new(
                Ghost(pcell),
                0,
                Tracked(GhostState::Uninitialized(points_to)),
            ),
        }
    }

    fn get<'a>(&'a self) -> &'a T
        requires
            self.wf(),
    {
        loop
            invariant
                self.wf(),
        {
            let tracked mut readonly_points_to: Option<&'static PointsTo<Option<T>>> = None;
            let cur_state =
                atomic_with_ghost!(&self.state => load(); ghost g => {
                    // Populate readonly_points_to when we find an initialized state
                    match g {
                        GhostState::Initialized(points_to) => {
                            readonly_points_to = Some(points_to);
                        }
                        _ => {}
                    }
                });
            if cur_state == 2 {
                // Already initialized.
                // Proof: readonly_points_to is definitely Some now  
                proof {
                    assert(readonly_points_to matches Some(_));
                }
                return self.cell.borrow(
                    Tracked(readonly_points_to.tracked_take()),
                ).as_ref().unwrap();
            } else {
                // Initialization is required. Try to take the lock if initialization
                // isn't already in progress.
                let mut do_initialization = (cur_state == 0);
                let tracked mut points_to_option: Option<PointsTo<Option<T>>> = None;
                if do_initialization {
                    let res =
                        atomic_with_ghost!(&self.state => compare_exchange(0, 1);
                        returning res; ghost g =>
                    {
                        match g {
                             GhostState::Uninitialized(points_to) => {
                                // Extract the PointsTo for later use
                                // We must leave the ghost invariant valid:
                                // Switch to Initializing state, PointsTo goes to our local variable
                                points_to_option = Some(points_to);
                                g = GhostState::Initializing;
                            }
                            GhostState::Initializing => {
                                // Someone else started initialization
                            }
                            GhostState::Initialized(_) => {
                                // This case should be impossible:
                                // If cur_state == 0, then g cannot be Initialized (which requires v == 2)
                                // This contradiction proves this arm is unreachable
                            }
                        }
                    });
                    if res matches Err(_) {
                        // don't initialize after all
                        do_initialization = false;
                    }
                }
                if do_initialization {
                    // Do initialization
                    proof {
                        assert(points_to_option matches Some(_));
                    }
                    let t = T::initialize();
                    let tracked mut points_to = points_to_option.tracked_unwrap();
                    proof {
                        // Prove that the PCell and PointsTo ids match
                        assert(self.cell.id() == points_to.id());
                    }
                    self.cell.replace(Tracked(&mut points_to), Some(t));
                    let tracked static_points_to = vstd::modes::tracked_static_ref(points_to);
                    atomic_with_ghost!(&self.state => store(2); ghost g => {
                        // Set up final ghost state: initialized with static reference
                        g = GhostState::Initialized(static_points_to);
                    });
                    return self.cell.borrow(Tracked(static_points_to)).as_ref().unwrap();
                } else {
                    // Wait for initialization to complete by a different thread
                    // (Try again in the next iteration of the loop.)
                }
            }
        }
    }
}

// Example usage
struct X {}

impl Initializable for X {
    fn initialize() -> Self {
        X {  }
    }
}

exec static LAZY_X: Lazy<X>
    ensures
        LAZY_X.wf(),
{
    Lazy::<X>::new()
}

fn get_lazy_x() -> &'static X {
    LAZY_X.get()
}

fn main() {
}

} // verus!