import CorralFormalization.Results.ConnectorFreePrefix.PhysicalTransfer.Frame
import CorralFormalization.DiversityCompletion.CanonicalLatinFrame

/-!
# The connector-free source-body interface and its physical tiled frame

The input is a *residue-terrace body*, decomposed into fixed edges and the
actual adjacent two-edge Latin cells.  Its position field is the raw L14
predecessor formula.  A physical partition, a skeleton, and a completed
physical frame are all constructed below rather than assumed.
-/

namespace CorralFormalization.LatinCompletion.ConnectorFreePhysical

open LatinTransfer TerraceLift LatinPrefix PhaseTiling

/-- Narrow interface from the actual L7 prefix plus its chosen terrace
completion.  In contrast to the old `LatinPrefix.BodyInput`, the bases are
`m*j`, the columns are normalized translated Walecki coordinates, and the
lift level is `2+r*j+t`.

The calendar is an exact equality of lists, not just a palette claim.  The
position equation concerns the predecessor of the actual adjacent cell.
-/
structure BodyInput {n r : ℕ} [NeZero r] (T : CompletedTerrace n) (D : Coordinates r) where
  pieces : List (Piece (Cell r))
  fixed_positive : ∀ d, Piece.fixed d ∈ pieces → 0 < d
  cells_complete : (cells pieces).Perm (Finset.univ : Finset (Cell r)).toList
  calendar : T.body=word D.cellA D.cellB canonicalSymbol pieces
  position : ∀ i p, (i,p) ∈ locatedCells D.cellA D.cellB pieces →
    2*n+10+p=D.predecessor i.1 i.2+(2+r*i.1.val+i.2.val)*n

namespace BodyInput

variable {n r : ℕ} [NeZero r] {T : CompletedTerrace n} {D : Coordinates r}
variable (P : BodyInput T D)

def assembled (role : RowRole) : List (Piece (Cell r)) :=
  fixedPieces (before n role)++P.pieces++fixedPieces (after n role)

theorem assembled_word (role : RowRole) :
    word D.cellA D.cellB canonicalSymbol (P.assembled role)=roleWord T role := by
  rw [assembled,word_append,word_append,word_fixedPieces,word_fixedPieces,← P.calendar]
  cases role <;> simp [before,after,roleWord,TileGapWords.first,TileGapWords.cycle,
    TileGapWords.middle,TileGapWords.twoSecond,TileGapWords.threeSecond,
    TileGapWords.threeThird,TileGapWords.thirdPrefix,List.append_assoc]

theorem assembled_cells (role : RowRole) :
    (cells (P.assembled role)).Perm (Finset.univ : Finset (Cell r)).toList := by
  simpa only [assembled,cells_append,cells_fixedPieces,List.nil_append,List.append_nil]
    using P.cells_complete

theorem assembled_locations (role : RowRole) :
    locatedCells D.cellA D.cellB (P.assembled role)=
      (locatedCells D.cellA D.cellB P.pieces).map (fun p => (p.1,(before n role).sum+p.2)) := by
  simp [assembled,locatedCells_append,locatedCells_fixedPieces,weights_fixedPieces]

theorem assembled_fixed_positive (hn : 15 ≤ n) (role : RowRole) (d : ℕ)
    (hd : Piece.fixed d ∈ P.assembled role) : 0 < d := by
  have hmem : Piece.fixed d ∈ fixedPieces (I := Cell r) (before n role) ∨
      Piece.fixed d ∈ P.pieces ∨ Piece.fixed d ∈ fixedPieces (I := Cell r) (after n role) := by
    simpa [assembled,List.mem_append,or_assoc] using hd
  rcases hmem with hp | hp | hp
  · cases role <;> simp [fixedPieces,before] at hp <;> omega
  · exact P.fixed_positive d hp
  · cases role <;> simp [fixedPieces,after] at hp <;> omega

theorem canonical_lt (hr : 3 ≤ r) (i : Cell r) : canonicalSymbol i < D.cellB i := by
  have hs : canonicalSymbol i < r := ((cyclicLatinSquare r).entry i.1 i.2).isLt
  dsimp [Coordinates.cellB,Coordinates.b]
  nlinarith

theorem assembled_winding {h : ℕ} [NeZero h] (hr : 3 ≤ r) (hn : n=2*h-1)
    (hlarge : 200*r*r ≤ n) (role : RowRole) :
    ((P.assembled role).map (Piece.weight D.cellA D.cellB)).sum=h*n := by
  rw [← word_sum D.cellA D.cellB canonicalSymbol _ (fun i => (canonical_lt hr i).le),
    P.assembled_word role,(roleWord_perm T (by nlinarith) role).sum_eq,fullGapList_sum,
    optimal_width (NeZero.pos h) hn]

/-- This is the key change from L14 to H4; it derives the frame's physical
location equation from a raw integer predecessor position. -/
theorem assembled_site {h : ℕ} [NeZero h] (hr : 3 ≤ r) (hlarge : 200*r*r ≤ n)
    (hnsmall : 15 ≤ n) (q : ZMod h) (role : RowRole) (i : Cell r) (p : ℕ)
    (hp : (i,p) ∈ locatedCells D.cellA D.cellB (P.assembled role)) (s : Fin r) :
    ((q.val*n+startOffset n role+(p+D.cellA i+s.val) : ℕ) : ZMod (h*n))=
      D.site h n (q+D.offset h i.1,i.2,s) := by
  rw [P.assembled_locations role] at hp
  obtain ⟨⟨a,b⟩,hab,he⟩ := List.mem_map.mp hp
  have hai : a=i := congrArg Prod.fst he
  subst a
  have hbp : (before n role).sum+b=p := congrArg Prod.snd he
  have hstart := common_body_start hnsmall role
  have hL14 := P.position i b hab
  have hPA := (D.local_gap_geometry hr hlarge i.1 i.2 s).2.2.1
  have hcoord : q.val*n+startOffset n role+(p+D.cellA i+s.val)=
      q.val*n+D.residue i.2 s+(2+r*i.1.val+i.2.val)*n := by
    dsimp [Coordinates.residue,Coordinates.cellA] at *
    omega
  rw [hcoord]
  exact D.lift_eq_site q i.1 i.2 s

/-- A full physical frame is constructed for any supplied assignment of the
four *unchanged* tile roles.  No physical partition is an input. -/
def physicalFrame {h : ℕ} [NeZero h] (hr : 3 ≤ r) (hn : n=2*h-1)
    (hlarge : 200*r*r ≤ n) (rs : ZMod h → RowRole) : Frame h n D where
  pieces q := P.assembled (rs q)
  origin q := q.val*n+startOffset n (rs q)
  fixed_positive q := P.assembled_fixed_positive (by nlinarith) (rs q)
  cells_complete q := P.assembled_cells (rs q)
  winding q := P.assembled_winding hr hn hlarge (rs q)
  location q i p hp s := P.assembled_site hr hlarge (by nlinarith) q (rs q) i p hp s

section Physical

variable {h : ℕ} [NeZero h] [NeZero n] [NeZero (h*n)]

theorem frame_baseline_word (hr : 3 ≤ r) (hn : n=2*h-1) (hlarge : 200*r*r ≤ n)
    (rs : ZMod h → RowRole) (q : ZMod h) :
    (P.physicalFrame hr hn hlarge rs).row (cyclicLatinFamily h r) q =
      TileGapWords.row (((q.val*n+startOffset n (rs q) : ℕ) : ZMod (h*n))) (roleWord T (rs q)) := by
  have hc : D.choice (cyclicLatinFamily h r) q=canonicalSymbol := by funext i; rfl
  change physicalOffsets (h*n) (q.val*n+startOffset n (rs q))
    (properPrefixSites (word D.cellA D.cellB (D.choice (cyclicLatinFamily h r) q) (P.assembled (rs q))))=_
  rw [hc,P.assembled_word]
  exact (CompletedTerrace.physicalOffsets_origin _ _ rfl _).symm

theorem frame_baseline_role (hr : 3 ≤ r) (hn : n=2*h-1) (hlarge : 200*r*r ≤ n)
    (rs : ZMod h → RowRole) (q : ZMod h) :
    (P.physicalFrame hr hn hlarge rs).row (cyclicLatinFamily h r) q=roleRow T q (rs q) := by
  rw [P.frame_baseline_word hr hn hlarge]
  have ho : (((q.val*n+startOffset n (rs q) : ℕ) : ZMod (h*n)))=
      zeroSite h n q+(startOffset n (rs q) : ZMod (h*n)) := by simp only [zeroSite,Nat.cast_add]
  rw [ho]
  have hphase : (q+2)-1=q+1 := by ring
  cases hrole : rs q <;> simp only [roleWord,roleRow,startOffset,CompletedTerrace.tileFirst,
    CompletedTerrace.tileTwoSecond,CompletedTerrace.tileThreeSecond,CompletedTerrace.tileThreeThird,
    Nat.cast_add,Nat.cast_ofNat,zeroSite_next,hphase,add_assoc]

noncomputable def scheduleFrame (hr : 3 ≤ r) (hn : n=2*h-1) (hlarge : 200*r*r ≤ n)
    {m k : ℕ} (htotal : h=3*m+2*k) : Frame h n D :=
  P.physicalFrame hr hn hlarge (roles htotal)

theorem schedule_first_three (hr : 3 ≤ r) (hn : n=2*h-1) (hlarge : 200*r*r ≤ n)
    {m k : ℕ} (htotal : h=3*m+2*k) (i : Fin m) :
    (P.scheduleFrame hr hn hlarge htotal).row (cyclicLatinFamily h r) (top h (.inl i : TileIndex m k))=
      T.tileFirst (top h (.inl i : TileIndex m k)) := by
  rw [scheduleFrame,P.frame_baseline_role hr hn hlarge,roles_first_three htotal i]
  rfl

theorem schedule_second_three (hr : 3 ≤ r) (hn : n=2*h-1) (hlarge : 200*r*r ≤ n)
    {m k : ℕ} (htotal : h=3*m+2*k) (i : Fin m) :
    (P.scheduleFrame hr hn hlarge htotal).row (cyclicLatinFamily h r) (top h (.inl i : TileIndex m k)-1)=
      T.tileThreeSecond (top h (.inl i : TileIndex m k)) := by
  rw [scheduleFrame,P.frame_baseline_role hr hn hlarge,roles_second_three htotal hn (by nlinarith) i]
  simp only [roleRow,sub_add_cancel]

theorem schedule_third (hr : 3 ≤ r) (hn : n=2*h-1) (hlarge : 200*r*r ≤ n)
    {m k : ℕ} (htotal : h=3*m+2*k) (i : Fin m) :
    (P.scheduleFrame hr hn hlarge htotal).row (cyclicLatinFamily h r) (top h (.inl i : TileIndex m k)-2)=
      T.tileThreeThird (top h (.inl i : TileIndex m k)) := by
  rw [scheduleFrame,P.frame_baseline_role hr hn hlarge,roles_third htotal hn (by nlinarith) i]
  simp only [roleRow,sub_add_cancel]

theorem schedule_first_two (hr : 3 ≤ r) (hn : n=2*h-1) (hlarge : 200*r*r ≤ n)
    {m k : ℕ} (htotal : h=3*m+2*k) (j : Fin k) :
    (P.scheduleFrame hr hn hlarge htotal).row (cyclicLatinFamily h r) (top h (.inr j : TileIndex m k))=
      T.tileFirst (top h (.inr j : TileIndex m k)) := by
  rw [scheduleFrame,P.frame_baseline_role hr hn hlarge,roles_first_two htotal j]
  rfl

theorem schedule_second_two (hr : 3 ≤ r) (hn : n=2*h-1) (hlarge : 200*r*r ≤ n)
    {m k : ℕ} (htotal : h=3*m+2*k) (j : Fin k) :
    (P.scheduleFrame hr hn hlarge htotal).row (cyclicLatinFamily h r) (top h (.inr j : TileIndex m k)-1)=
      T.tileTwoSecond (top h (.inr j : TileIndex m k)) := by
  rw [scheduleFrame,P.frame_baseline_role hr hn hlarge,roles_second_two htotal hn (by nlinarith) j]
  simp only [roleRow,sub_add_cancel]

/-- The baseline family is literally the independently constructed physical
tile partition of Lemma 11, so it imports no Latin replacement conclusion. -/
theorem schedule_family_eq (hr : 3 ≤ r) (hn : n=2*h-1) (hlarge : 200*r*r ≤ n)
    {m k : ℕ} (htotal : h=3*m+2*k) :
    (P.scheduleFrame hr hn hlarge htotal).unlabelled (cyclicLatinFamily h r)=
      T.globalFamily (h := h) m k := by
  simp only [Frame.unlabelled,CompletedTerrace.globalFamily]
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
      · rw [P.schedule_first_three hr hn hlarge htotal]; simp [CompletedTerrace.tileRows]
      · rw [P.schedule_second_three hr hn hlarge htotal]; simp [CompletedTerrace.tileRows]
      · rw [P.schedule_third hr hn hlarge htotal]; simp [CompletedTerrace.tileRows]
    | inr j =>
      rw [phaseBlock_two] at hi
      simp only [Finset.mem_insert,Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · rw [P.schedule_first_two hr hn hlarge htotal]; simp [CompletedTerrace.tileRows]
      · rw [P.schedule_second_two hr hn hlarge htotal]; simp [CompletedTerrace.tileRows]
  · intro hx
    obtain ⟨i,_,hR⟩ := Finset.mem_biUnion.mp hx
    cases i with
    | inl i =>
      simp only [CompletedTerrace.tileRows,Finset.mem_insert,Finset.mem_singleton] at hR
      rcases hR with rfl | rfl | rfl
      · exact Finset.mem_image.mpr ⟨top h (.inl i : TileIndex m k),Finset.mem_univ _,P.schedule_first_three hr hn hlarge htotal i⟩
      · exact Finset.mem_image.mpr ⟨top h (.inl i : TileIndex m k)-1,Finset.mem_univ _,P.schedule_second_three hr hn hlarge htotal i⟩
      · exact Finset.mem_image.mpr ⟨top h (.inl i : TileIndex m k)-2,Finset.mem_univ _,P.schedule_third hr hn hlarge htotal i⟩
    | inr j =>
      simp only [CompletedTerrace.tileRows,Finset.mem_insert,Finset.mem_singleton] at hR
      rcases hR with rfl | rfl
      · exact Finset.mem_image.mpr ⟨top h (.inr j : TileIndex m k),Finset.mem_univ _,P.schedule_first_two hr hn hlarge htotal j⟩
      · exact Finset.mem_image.mpr ⟨top h (.inr j : TileIndex m k)-1,Finset.mem_univ _,P.schedule_second_two hr hn hlarge htotal j⟩

/-- The unique physical occupancy and all actual baseline palettes are
proved from the terrace tiling.  They are not parameters to this definition. -/
noncomputable def scheduleBaseline (hr : 3 ≤ r) (hn : n=2*h-1) (hlarge : 200*r*r ≤ n)
    {m k : ℕ} (htotal : h=3*m+2*k) :
    Frame.FullBaseline (P.scheduleFrame hr hn hlarge htotal) := by
  let G := P.scheduleFrame hr hn hlarge htotal
  let L₀ := cyclicLatinFamily h r
  have hF : G.unlabelled L₀=T.globalFamily (h := h) m k := P.schedule_family_eq hr hn hlarge htotal
  have hsmall : 15 ≤ n := by nlinarith
  have hmem (q : ZMod h) : G.row L₀ q ∈ T.globalFamily (h := h) m k := by
    rw [← hF]; exact Finset.mem_image.mpr ⟨q,Finset.mem_univ _,rfl⟩
  have hc : (Finset.univ.image (G.row L₀)).card=(Finset.univ : Finset (ZMod h)).card := by
    change (G.unlabelled L₀).card=_
    rw [hF,T.global_card hn hsmall htotal]
    simp [ZMod.card]
  have hinj : Function.Injective (G.row L₀) := by
    have hi := Finset.card_image_iff.mp hc
    intro q p he
    exact hi (Finset.mem_univ q) (Finset.mem_univ p) he
  refine { latin := L₀, partition := ?_, palette := ?_ }
  · intro x
    have hx : x ∈ (T.globalFamily (h := h) m k).biUnion id := by
      rw [T.global_full hn hsmall htotal]; exact Finset.mem_univ _
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

theorem height_large (hr : 3 ≤ r) (hn : n=2*h-1) (hlarge : 200*r*r ≤ n) : 8 ≤ h := by
  have hsmall : 15 ≤ n := by nlinarith
  omega

noncomputable def canonicalFrame (hr : 3 ≤ r) (hn : n=2*h-1) (hlarge : 200*r*r ≤ n) :
    Frame h n D := P.scheduleFrame hr hn hlarge (canonical_total (height_large hr hn hlarge))

noncomputable def canonicalBaseline (hr : 3 ≤ r) (hn : n=2*h-1) (hlarge : 200*r*r ≤ n) :
    Frame.FullBaseline (P.canonicalFrame hr hn hlarge) :=
  P.scheduleBaseline hr hn hlarge (canonical_total (height_large hr hn hlarge))

/-- A constructive downstream theorem conditional solely on the exact
source-body calendar and L14 positions.  It supplies actual CorralRows,
unique full physical occupancy, and an absolute unlabelled decoder. -/
theorem canonical_latin_corrals (hr : 3 ≤ r) (hn : n=2*h-1) (hlarge : 200*r*r ≤ n) :
    ∃ C : Family h r → CorralRows h n,
      (∀ L q, (C L).sites q=naturalRows ((P.canonicalFrame hr hn hlarge).row L) q) ∧
      (∀ L x, x < width n → ∃! q, x ∈ (C L).sites q) ∧
      Function.Injective (P.canonicalFrame hr hn hlarge).unlabelled := by
  let G := P.canonicalFrame hr hn hlarge
  let B := P.canonicalBaseline hr hn hlarge
  have hn' : n+1=2*h := by have := NeZero.pos h; omega
  have hh : r*r ≤ h := by nlinarith
  exact ⟨G.completed hr hlarge B hn,G.completed_sites hr hlarge B hn,
    G.completed_full_occupancy hr hlarge B hn,G.unlabelled_injective hr hlarge hh B⟩

end Physical
end BodyInput
end CorralFormalization.LatinCompletion.ConnectorFreePhysical
