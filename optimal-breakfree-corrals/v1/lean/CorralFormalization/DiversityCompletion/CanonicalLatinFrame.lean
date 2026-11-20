import CorralFormalization.DiversityCompletion.LatinPrefixFrame

namespace CorralFormalization.LatinCompletion.LatinPrefix

open LatinTransfer TerraceLift PhaseTiling

noncomputable def phaseOwner {h m k : ℕ} [NeZero h] (htotal : h=3*m+2*k)
    (q : ZMod h) : TileIndex m k := Classical.choose (phaseBlock_exactly_once htotal q)

theorem phaseOwner_mem {h m k : ℕ} [NeZero h] (htotal : h=3*m+2*k) (q : ZMod h) :
    q ∈ phaseBlock h (phaseOwner htotal q) := (Classical.choose_spec (phaseBlock_exactly_once htotal q)).1

theorem phaseOwner_eq {h m k : ℕ} [NeZero h] (htotal : h=3*m+2*k)
    (i : TileIndex m k) (q : ZMod h) (hq : q ∈ phaseBlock h i) : phaseOwner htotal q=i := by
  obtain ⟨a,_,huniq⟩ := phaseBlock_exactly_once htotal q
  exact (huniq _ (phaseOwner_mem htotal q)).trans (huniq _ hq).symm

noncomputable def roles {h m k : ℕ} [NeZero h] (htotal : h=3*m+2*k) (q : ZMod h) : RowRole :=
  match phaseOwner htotal q with
  | .inl i => if q=top h (.inl i : TileIndex m k) then .first else
      if q=top h (.inl i : TileIndex m k)-1 then .secondThree else .third
  | .inr j => if q=top h (.inr j : TileIndex m k) then .first else .secondTwo

theorem roles_first_three {h m k : ℕ} [NeZero h] (htotal : h=3*m+2*k) (i : Fin m) :
    roles htotal (top h (.inl i : TileIndex m k)) = .first := by
  have ho := phaseOwner_eq htotal (.inl i : TileIndex m k) (top h (.inl i : TileIndex m k))
    (by rw [phaseBlock_three]; simp)
  simp [roles,ho]

theorem roles_second_three {h n m k : ℕ} [NeZero h] [NeZero n] [NeZero (h*n)] (htotal : h=3*m+2*k)
    (hn : n=2*h-1) (hsmall : 15 ≤ n) (i : Fin m) :
    roles htotal (top h (.inl i : TileIndex m k)-1) = .secondThree := by
  let q := top h (.inl i : TileIndex m k)
  have ho := phaseOwner_eq htotal (.inl i : TileIndex m k) (q-1)
    (by rw [phaseBlock_three]; simp [q])
  have hne : q-1 ≠ q := (CompletedTerrace.phase_ne_pred hn hsmall q).symm
  dsimp [q] at ho hne
  simp [roles,ho,hne]

theorem roles_third {h n m k : ℕ} [NeZero h] [NeZero n] [NeZero (h*n)] (htotal : h=3*m+2*k)
    (hn : n=2*h-1) (hsmall : 15 ≤ n) (i : Fin m) :
    roles htotal (top h (.inl i : TileIndex m k)-2) = .third := by
  let q := top h (.inl i : TileIndex m k)
  have ho := phaseOwner_eq htotal (.inl i : TileIndex m k) (q-2)
    (by rw [phaseBlock_three]; simp [q])
  have hne : q-2 ≠ q := (CompletedTerrace.phase_ne_two_pred hn hsmall q).symm
  have hne₁ : q-2 ≠ q-1 := by
    have he : (q-1)-1=q-2 := by ring
    have hp := CompletedTerrace.phase_ne_pred hn hsmall (q-1)
    rw [he] at hp
    exact hp.symm
  dsimp [q] at ho hne hne₁
  simp [roles,ho,hne,hne₁]

theorem roles_first_two {h m k : ℕ} [NeZero h] (htotal : h=3*m+2*k) (j : Fin k) :
    roles htotal (top h (.inr j : TileIndex m k)) = .first := by
  have ho := phaseOwner_eq htotal (.inr j : TileIndex m k) (top h (.inr j : TileIndex m k))
    (by rw [phaseBlock_two]; simp)
  simp [roles,ho]

theorem roles_second_two {h n m k : ℕ} [NeZero h] [NeZero n] [NeZero (h*n)] (htotal : h=3*m+2*k)
    (hn : n=2*h-1) (hsmall : 15 ≤ n) (j : Fin k) :
    roles htotal (top h (.inr j : TileIndex m k)-1) = .secondTwo := by
  let q := top h (.inr j : TileIndex m k)
  have ho := phaseOwner_eq htotal (.inr j : TileIndex m k) (q-1)
    (by rw [phaseBlock_two]; simp [q])
  have hne : q-1 ≠ q := (CompletedTerrace.phase_ne_pred hn hsmall q).symm
  dsimp [q] at ho hne
  simp [roles,ho,hne]

section Physical

variable {h n r : ℕ} [NeZero h] [NeZero n] [NeZero r] [NeZero (h*n)]
variable {T : CompletedTerrace n}

theorem frame_baseline_word (P : BodyInput T r) (hr : 2 ≤ r) (hn : n=2*h-1)
    (hlarge : 100*r*r ≤ n) (rs : ZMod h → RowRole) (q : ZMod h) :
    (physicalFrame P hr hn hlarge rs).row (cyclicLatinFamily h r) q =
      TileGapWords.row (((q.val*n+startOffset n (rs q) : ℕ) : ZMod (h*n))) (roleWord T (rs q)) := by
  have hc : choice (cyclicLatinFamily h r) q = canonicalSymbol := by funext i; rfl
  change physicalOffsets (h*n) (q.val*n+startOffset n (rs q))
    (properPrefixSites (word cellA cellB (choice (cyclicLatinFamily h r) q) (assembled P (rs q)))) = _
  rw [hc,assembled_word P]
  exact (CompletedTerrace.physicalOffsets_origin _ _ rfl _).symm

def roleRow (T : CompletedTerrace n) (q : ZMod h) : RowRole → Finset (ZMod (h*n))
  | .first => T.tileFirst q
  | .secondTwo => T.tileTwoSecond (q+1)
  | .secondThree => T.tileThreeSecond (q+1)
  | .third => T.tileThreeThird (q+2)

theorem zeroSite_next (q : ZMod h) : zeroSite h n (q+1) = zeroSite h n q+(n : ZMod (h*n)) := by
  rw [zeroSite_add]
  have h1 : zeroSite h n (1 : ZMod h) = (n : ZMod (h*n)) := by simpa using zeroSite_natCast h n 1
  rw [h1]

theorem frame_baseline_role (P : BodyInput T r) (hr : 2 ≤ r) (hn : n=2*h-1)
    (hlarge : 100*r*r ≤ n) (rs : ZMod h → RowRole) (q : ZMod h) :
    (physicalFrame P hr hn hlarge rs).row (cyclicLatinFamily h r) q = roleRow T q (rs q) := by
  rw [frame_baseline_word P hr hn hlarge]
  have ho : (((q.val*n+startOffset n (rs q) : ℕ) : ZMod (h*n))) =
      zeroSite h n q+(startOffset n (rs q) : ZMod (h*n)) := by simp only [zeroSite,Nat.cast_add]
  rw [ho]
  have hphase : (q+2)-1=q+1 := by ring
  cases hrole : rs q <;> simp only [roleWord,roleRow,startOffset,CompletedTerrace.tileFirst,
    CompletedTerrace.tileTwoSecond,CompletedTerrace.tileThreeSecond,CompletedTerrace.tileThreeThird,
    Nat.cast_add,Nat.cast_ofNat,zeroSite_next,hphase,add_assoc]

noncomputable def scheduleFrame (P : BodyInput T r) (hr : 2 ≤ r) (hn : n=2*h-1)
    (hlarge : 100*r*r ≤ n) {m k : ℕ} (htotal : h=3*m+2*k) : PhysicalFrame h n r :=
  physicalFrame P hr hn hlarge (roles htotal)

theorem schedule_first_three (P : BodyInput T r) (hr : 2 ≤ r) (hn : n=2*h-1)
    (hlarge : 100*r*r ≤ n) {m k : ℕ} (htotal : h=3*m+2*k) (i : Fin m) :
    (scheduleFrame P hr hn hlarge htotal).row (cyclicLatinFamily h r) (top h (.inl i : TileIndex m k)) =
      T.tileFirst (top h (.inl i : TileIndex m k)) := by
  rw [scheduleFrame,frame_baseline_role P hr hn hlarge,roles_first_three htotal i]
  rfl

theorem schedule_second_three (P : BodyInput T r) (hr : 2 ≤ r) (hn : n=2*h-1)
    (hlarge : 100*r*r ≤ n) {m k : ℕ} (htotal : h=3*m+2*k) (i : Fin m) :
    (scheduleFrame P hr hn hlarge htotal).row (cyclicLatinFamily h r) (top h (.inl i : TileIndex m k)-1) =
      T.tileThreeSecond (top h (.inl i : TileIndex m k)) := by
  rw [scheduleFrame,frame_baseline_role P hr hn hlarge,roles_second_three htotal hn (by nlinarith) i]
  simp only [roleRow,sub_add_cancel]

theorem schedule_third (P : BodyInput T r) (hr : 2 ≤ r) (hn : n=2*h-1)
    (hlarge : 100*r*r ≤ n) {m k : ℕ} (htotal : h=3*m+2*k) (i : Fin m) :
    (scheduleFrame P hr hn hlarge htotal).row (cyclicLatinFamily h r) (top h (.inl i : TileIndex m k)-2) =
      T.tileThreeThird (top h (.inl i : TileIndex m k)) := by
  rw [scheduleFrame,frame_baseline_role P hr hn hlarge,roles_third htotal hn (by nlinarith) i]
  simp only [roleRow,sub_add_cancel]

theorem schedule_first_two (P : BodyInput T r) (hr : 2 ≤ r) (hn : n=2*h-1)
    (hlarge : 100*r*r ≤ n) {m k : ℕ} (htotal : h=3*m+2*k) (j : Fin k) :
    (scheduleFrame P hr hn hlarge htotal).row (cyclicLatinFamily h r) (top h (.inr j : TileIndex m k)) =
      T.tileFirst (top h (.inr j : TileIndex m k)) := by
  rw [scheduleFrame,frame_baseline_role P hr hn hlarge,roles_first_two htotal j]
  rfl

theorem schedule_second_two (P : BodyInput T r) (hr : 2 ≤ r) (hn : n=2*h-1)
    (hlarge : 100*r*r ≤ n) {m k : ℕ} (htotal : h=3*m+2*k) (j : Fin k) :
    (scheduleFrame P hr hn hlarge htotal).row (cyclicLatinFamily h r) (top h (.inr j : TileIndex m k)-1) =
      T.tileTwoSecond (top h (.inr j : TileIndex m k)) := by
  rw [scheduleFrame,frame_baseline_role P hr hn hlarge,roles_second_two htotal hn (by nlinarith) j]
  simp only [roleRow,sub_add_cancel]

/-- Exact equality of the constructed connectorPrefixCenterSite frame's baseline physical family
and the actual globally assembled tile family. -/
theorem schedule_family_eq (P : BodyInput T r) (hr : 2 ≤ r) (hn : n=2*h-1)
    (hlarge : 100*r*r ≤ n) {m k : ℕ} (htotal : h=3*m+2*k) :
    (scheduleFrame P hr hn hlarge htotal).unlabelled (cyclicLatinFamily h r) = T.globalFamily (h := h) m k := by
  simp only [PhysicalFrame.unlabelled,CompletedTerrace.globalFamily]
  ext R
  constructor
  · intro hx
    obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨i,hi,_⟩ := phaseBlock_exactly_once htotal q
    refine Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,?_⟩
    cases i with
    | inl i =>
      rw [phaseBlock_three] at hi
      simp only [Finset.mem_insert,Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl
      · rw [schedule_first_three P hr hn hlarge htotal]
        simp [CompletedTerrace.tileRows]
      · rw [schedule_second_three P hr hn hlarge htotal]
        simp [CompletedTerrace.tileRows]
      · rw [schedule_third P hr hn hlarge htotal]
        simp [CompletedTerrace.tileRows]
    | inr j =>
      rw [phaseBlock_two] at hi
      simp only [Finset.mem_insert,Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · rw [schedule_first_two P hr hn hlarge htotal]
        simp [CompletedTerrace.tileRows]
      · rw [schedule_second_two P hr hn hlarge htotal]
        simp [CompletedTerrace.tileRows]
  · intro hx
    obtain ⟨i,_,hR⟩ := Finset.mem_biUnion.mp hx
    cases i with
    | inl i =>
      simp only [CompletedTerrace.tileRows,Finset.mem_insert,Finset.mem_singleton] at hR
      rcases hR with rfl | rfl | rfl
      · exact Finset.mem_image.mpr ⟨top h (.inl i : TileIndex m k),Finset.mem_univ _,schedule_first_three P hr hn hlarge htotal i⟩
      · exact Finset.mem_image.mpr ⟨top h (.inl i : TileIndex m k)-1,Finset.mem_univ _,schedule_second_three P hr hn hlarge htotal i⟩
      · exact Finset.mem_image.mpr ⟨top h (.inl i : TileIndex m k)-2,Finset.mem_univ _,schedule_third P hr hn hlarge htotal i⟩
    | inr j =>
      simp only [CompletedTerrace.tileRows,Finset.mem_insert,Finset.mem_singleton] at hR
      rcases hR with rfl | rfl
      · exact Finset.mem_image.mpr ⟨top h (.inr j : TileIndex m k),Finset.mem_univ _,schedule_first_two P hr hn hlarge htotal j⟩
      · exact Finset.mem_image.mpr ⟨top h (.inr j : TileIndex m k)-1,Finset.mem_univ _,schedule_second_two P hr hn hlarge htotal j⟩

noncomputable def scheduleBaseline (P : BodyInput T r) (hr : 2 ≤ r) (hn : n=2*h-1)
    (hlarge : 100*r*r ≤ n) {m k : ℕ} (htotal : h=3*m+2*k) :
    PhysicalFrame.FullBaseline (scheduleFrame P hr hn hlarge htotal) := by
  let G := scheduleFrame P hr hn hlarge htotal
  let L₀ := cyclicLatinFamily h r
  have hF : G.unlabelled L₀ = T.globalFamily (h := h) m k := schedule_family_eq P hr hn hlarge htotal
  have hsmall : 15 ≤ n := by nlinarith
  have hmem (q : ZMod h) : G.row L₀ q ∈ T.globalFamily (h := h) m k := by
    rw [← hF]
    exact Finset.mem_image.mpr ⟨q,Finset.mem_univ _,rfl⟩
  have hc : (Finset.univ.image (G.row L₀)).card = (Finset.univ : Finset (ZMod h)).card := by
    change (G.unlabelled L₀).card = _
    rw [hF,T.global_card hn hsmall htotal]
    simp [ZMod.card]
  have hinj : Function.Injective (G.row L₀) := by
    have hi := Finset.card_image_iff.mp hc
    intro q p he
    exact hi (Finset.mem_univ q) (Finset.mem_univ p) he
  refine { latin := L₀, partition := ?_, palette := ?_ }
  · intro x
    have hx : x ∈ (T.globalFamily (h := h) m k).biUnion id := by
      rw [T.global_full hn hsmall htotal]
      exact Finset.mem_univ _
    obtain ⟨R,hR,hxR⟩ := Finset.mem_biUnion.mp hx
    rw [← hF] at hR
    obtain ⟨q,_,he⟩ := Finset.mem_image.mp hR
    rw [← he] at hxR
    refine ⟨q,hxR,?_⟩
    intro p hp
    by_contra hne
    have hset : G.row L₀ p ≠ G.row L₀ q := fun he => hne (hinj he)
    exact Finset.disjoint_left.mp (T.global_disjoint hn hsmall htotal _ _ (hmem p) (hmem q) hset) hp hxR
  · intro q
    exact T.global_inventory hn hsmall m k _ (hmem q)

theorem height_large (hr : 2 ≤ r) (hn : n=2*h-1) (hlarge : 100*r*r ≤ n) : 8 ≤ h := by
  have hsmall : 15 ≤ n := by nlinarith
  omega

noncomputable def canonicalFrame (P : BodyInput T r) (hr : 2 ≤ r) (hn : n=2*h-1)
    (hlarge : 100*r*r ≤ n) : PhysicalFrame h n r :=
  scheduleFrame P hr hn hlarge (canonical_total (height_large hr hn hlarge))

noncomputable def canonicalBaseline (P : BodyInput T r) (hr : 2 ≤ r) (hn : n=2*h-1)
    (hlarge : 100*r*r ≤ n) : PhysicalFrame.FullBaseline (canonicalFrame P hr hn hlarge) :=
  scheduleBaseline P hr hn hlarge (canonical_total (height_large hr hn hlarge))

/-- The actual prescribed-terrace body data now produce genuine corrals for
all Latin parameters, with full occupancy and physical unlabelled decoding.
No baseline corral, skeleton, cyclic-edge certificate or full frame is input. -/
theorem canonical_latin_corrals (P : BodyInput T r) (hr : 2 ≤ r) (hn : n=2*h-1)
    (hlarge : 100*r*r ≤ n) :
    ∃ C : Family h r → CorralRows h n,
      (∀ L q,(C L).sites q = naturalRows ((canonicalFrame P hr hn hlarge).row L) q) ∧
      (∀ L x,x < width n → ∃! q,x ∈ (C L).sites q) ∧
      Function.Injective (canonicalFrame P hr hn hlarge).unlabelled := by
  let G := canonicalFrame P hr hn hlarge
  let B := canonicalBaseline P hr hn hlarge
  obtain ⟨hres,hh⟩ := connectorPrefix_numeric_bounds hr hn hlarge
  exact ⟨G.completed hr hlarge hres B hn,G.completed_sites hr hlarge hres B hn,
    G.completed_full_occupancy hr hlarge hres B hn,G.unlabelled_injective hr hlarge hres B hh⟩

end Physical

end CorralFormalization.LatinCompletion.LatinPrefix
