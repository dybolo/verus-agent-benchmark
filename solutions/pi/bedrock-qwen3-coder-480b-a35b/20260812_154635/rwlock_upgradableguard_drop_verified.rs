impl<T  /*: ?Sized*/ , G: SpinGuardian> RwLockUpgradeableGuard<'_, T, G> {
    /// VERUS LIMITATION: We implement `drop` and call it manually because Verus's support for `Drop` is incomplete for now.
    pub fn drop(self) {
        proof! {
            use_type_invariant(&self);
            use_type_invariant(self.inner);
            lemma_consts_properties();
        }
        proof_decl!{
            let tracked guard_token = self.tracked_token.get();
        }
        //self.inner.lock.fetch_sub(UPGRADEABLE_READER, Release);
        atomic_with_ghost!(
            self.inner.lock => fetch_sub(UPGRADEABLE_READER);
            update prev -> next;
            ghost g => {
                g.upreader_guard_token = Some(guard_token);
                g.core_token.join_one_left_owner(guard_token);
            }
        );
    }
}