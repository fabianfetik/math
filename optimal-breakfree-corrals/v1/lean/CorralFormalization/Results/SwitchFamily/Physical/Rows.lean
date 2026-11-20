import CorralFormalization.Results.SwitchFamily.Physical.Locations

/-! Actual word frames indexed by the original, unlabelled tile rows. -/

namespace CorralFormalization.Results.SwitchFamily.Physical

open CorralFormalization CorralFormalization.LatinCompletion
open LatinTransfer PhysicalCorral DiversitySymmetry TerraceLift GeneralTiles LatinPrefix
open scoped Classical
noncomputable section

variable {h n m : ℕ} [NeZero h] [NeZero n] [NeZero (h*n)]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

structure RowRepresentation (T : CompletedTerrace n) (R : Finset (ZMod (h*n))) where
  phase : ZMod h
  role : RowRole
  row_eq : R=TileGapWords.row (tileOrigin n (zeroSite h n phase) role) (roleWord T role)

theorem rowRepresentation_nonempty (L : CyclicTiling h ι) (T : CompletedTerrace n)
    (hn : n=2*h-1) (hsmall : 65≤n) (rest : List ℕ)
    (hbody : T.body=[7,1]++((List.range m).flatMap (Prefix.blockColors n)++rest))
    (R : {R : Finset (ZMod (h*n)) // R∈L.family T}) : Nonempty (RowRepresentation T R.val) := by
  obtain ⟨p,role,he,_⟩ := L.every_row_unchanged_segment T hn hsmall
    ((List.range m).flatMap (Prefix.blockColors n)++rest) hbody R.val R.property
  exact ⟨⟨p,role,he⟩⟩

def rowRepresentation (L : CyclicTiling h ι) (T : CompletedTerrace n)
    (hn : n=2*h-1) (hsmall : 65≤n) (rest : List ℕ)
    (hbody : T.body=[7,1]++((List.range m).flatMap (Prefix.blockColors n)++rest))
    (R : {R : Finset (ZMod (h*n)) // R∈L.family T}) : RowRepresentation T R.val :=
  Classical.choice (rowRepresentation_nonempty L T hn hsmall rest hbody R)

def rowFrame (L : CyclicTiling h ι) (T : CompletedTerrace n)
    (hn : n=2*h-1) (hsmall : 65≤n) (rest : List ℕ)
    (hbody : T.body=[7,1]++((List.range m).flatMap (Prefix.blockColors n)++rest))
    (R : {R : Finset (ZMod (h*n)) // R∈L.family T}) : BinaryWordFrame (h*n) (Cell m) :=
  let d := rowRepresentation L T hn hsmall rest hbody R
  tileWordFrame T hn hsmall rest hbody (zeroSite h n d.phase) d.role

theorem rowFrame_original (L : CyclicTiling h ι) (T : CompletedTerrace n)
    (hn : n=2*h-1) (hsmall : 65≤n) (rest : List ℕ)
    (hbody : T.body=[7,1]++((List.range m).flatMap (Prefix.blockColors n)++rest))
    (R : {R : Finset (ZMod (h*n)) // R∈L.family T}) :
    (rowFrame L T hn hsmall rest hbody R).row originalSetting=R.val := by
  rw [rowFrame,tileWordFrame_original]
  exact (rowRepresentation L T hn hsmall rest hbody R).row_eq.symm

theorem rowFrame_movingRow (L : CyclicTiling h ι) (T : CompletedTerrace n)
    (hn : n=2*h-1) (hsmall : 65≤n) (hsize : (5*m+8)^2≤n) (rest : List ℕ)
    (hbody : T.body=[7,1]++((List.range m).flatMap (Prefix.blockColors n)++rest))
    (R : {R : Finset (ZMod (h*n)) // R∈L.family T}) :
    (rowFrame L T hn hsmall rest hbody R).movingRow originalSetting=
      (Finset.univ : Finset (Cell m)).image
        (cellEndpoint (n:=n) (rowRepresentation L T hn hsmall rest hbody R).phase
          (rowRepresentation L T hn hsmall rest hbody R).role) :=
  tileWordFrame_movingRow T hn hsmall hsize rest hbody _ _

/-- Arbitrary per-cell settings produce rows with the original full
palette and all old 1/2/n edges. Compatibility with a common site
permutation, hence physical full occupancy, is established separately. -/
def wordModification (L : CyclicTiling h ι) (T : CompletedTerrace n)
    (hn : n=2*h-1) (hsmall : 65≤n) (hsize : (5*m+8)^2≤n) (rest : List ℕ)
    (hbody : T.body=[7,1]++((List.range m).flatMap (Prefix.blockColors n)++rest))
    (b : {R : Finset (ZMod (h*n)) // R∈L.family T} → Cell m → Bool) :
    RowModification n (L.family T) where
  row R := (rowFrame L T hn hsmall rest hbody R).row (b R)
  palette R := tileWordFrame_inventory T hn hsmall rest hbody _ _ (b R)
  preserves R d hd := by
    have he := tileWordFrame_tails T hn hsmall hsize rest hbody
      (zeroSite h n (rowRepresentation L T hn hsmall rest hbody R).phase)
      (rowRepresentation L T hn hsmall rest hbody R).role (b R) d hd
    rw [← (rowRepresentation L T hn hsmall rest hbody R).row_eq] at he
    exact he.symm.subset

theorem moving_subset_original (L : CyclicTiling h ι) (T : CompletedTerrace n)
    (hn : n=2*h-1) (hsmall : 65≤n) (rest : List ℕ)
    (hbody : T.body=[7,1]++((List.range m).flatMap (Prefix.blockColors n)++rest))
    (R : {R : Finset (ZMod (h*n)) // R∈L.family T}) :
    (rowFrame L T hn hsmall rest hbody R).movingRow originalSetting⊆R.val := by
  rw [← rowFrame_original L T hn hsmall rest hbody R,
    BinaryWordFrame.row_split]
  exact Finset.subset_union_right

theorem fixed_subset_original (L : CyclicTiling h ι) (T : CompletedTerrace n)
    (hn : n=2*h-1) (hsmall : 65≤n) (rest : List ℕ)
    (hbody : T.body=[7,1]++((List.range m).flatMap (Prefix.blockColors n)++rest))
    (R : {R : Finset (ZMod (h*n)) // R∈L.family T}) :
    (rowFrame L T hn hsmall rest hbody R).fixedRow⊆R.val := by
  rw [← rowFrame_original L T hn hsmall rest hbody R,
    BinaryWordFrame.row_split]
  exact Finset.subset_union_left

def allEndpoints (h n m : ℕ) [NeZero h] : Finset (ZMod (h*n)) :=
  (Finset.univ : Finset (Bit m h × Bool)).image (fun c => endpoint (n:=n) c.1 c.2)

def allMoving (L : CyclicTiling h ι) (T : CompletedTerrace n)
    (hn : n=2*h-1) (hsmall : 65≤n) (rest : List ℕ)
    (hbody : T.body=[7,1]++((List.range m).flatMap (Prefix.blockColors n)++rest)) :
    Finset (ZMod (h*n)) :=
  (L.family T).attach.biUnion
    (fun R => (rowFrame L T hn hsmall rest hbody R).movingRow originalSetting)

theorem allMoving_eq_endpoints (L : CyclicTiling h ι) (T : CompletedTerrace n)
    (hn : n=2*h-1) (hsmall : 65≤n) (hsize : (5*m+8)^2≤n) (rest : List ℕ)
    (hbody : T.body=[7,1]++((List.range m).flatMap (Prefix.blockColors n)++rest)) :
    allMoving L T hn hsmall rest hbody=allEndpoints h n m := by
  have hsub : allMoving L T hn hsmall rest hbody⊆allEndpoints h n m := by
    intro x hx
    obtain ⟨R,_,hxR⟩ := Finset.mem_biUnion.mp hx
    rw [rowFrame_movingRow L T hn hsmall hsize rest hbody R] at hxR
    obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp hxR
    exact Finset.mem_image.mpr ⟨((c.1,cellPhase
      (rowRepresentation L T hn hsmall rest hbody R).phase
      (rowRepresentation L T hn hsmall rest hbody R).role c),c.2),by simp,rfl⟩
  have hc : (allMoving L T hn hsmall rest hbody).card=h*(2*m) := by
    rw [allMoving,Finset.card_biUnion]
    · have he (R : {R : Finset (ZMod (h*n)) // R∈L.family T}) :
          ((rowFrame L T hn hsmall rest hbody R).movingRow originalSetting).card=2*m :=
        tileWordFrame_movingRow_card T hn hsmall hsize rest hbody _ _
      simp_rw [he]
      simp [L.card T hn (by omega : 15≤n)]
    · intro R _ S _ hRS
      have hne : R.val≠S.val := fun he => hRS (Subtype.ext he)
      exact (L.disjoint T hn (by omega : 15≤n) _ _ R.property S.property hne).mono
        (moving_subset_original L T hn hsmall rest hbody R)
        (moving_subset_original L T hn hsmall rest hbody S)
  have he : (allEndpoints h n m).card=h*(2*m) := by
    rw [allEndpoints,Finset.card_image_of_injective _ (endpoint_injective hsize)]
    simp [Fintype.card_prod,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc]
  apply Finset.eq_of_subset_of_card_le hsub
  omega

/-- Every fixed word boundary is isolated from every switch pair. This
follows from actual baseline partitioning and the derived moving-site
census, rather than an assumed noninterference certificate. -/
theorem fixedRow_isolated (L : CyclicTiling h ι) (T : CompletedTerrace n)
    (hn : n=2*h-1) (hsmall : 65≤n) (hsize : (5*m+8)^2≤n) (rest : List ℕ)
    (hbody : T.body=[7,1]++((List.range m).flatMap (Prefix.blockColors n)++rest))
    (R : {R : Finset (ZMod (h*n)) // R∈L.family T})
    (x : ZMod (h*n)) (hx : x∈(rowFrame L T hn hsmall rest hbody R).fixedRow) :
    (switchLayer hsize).Isolated x := by
  rw [switchLayer_isolated_iff]
  intro k s he
  have hxe : x∈allEndpoints h n m := Finset.mem_image.mpr ⟨(k,s),by simp,he⟩
  rw [← allMoving_eq_endpoints L T hn hsmall hsize rest hbody] at hxe
  obtain ⟨S,_,hxS⟩ := Finset.mem_biUnion.mp hxe
  have hRS : R=S := by
    by_contra hne
    have hne' : R.val≠S.val := fun he => hne (Subtype.ext he)
    exact Finset.disjoint_left.mp
      (L.disjoint T hn (by omega : 15≤n) _ _ R.property S.property hne')
      (fixed_subset_original L T hn hsmall rest hbody R hx)
      (moving_subset_original L T hn hsmall rest hbody S hxS)
  subst S
  exact Finset.disjoint_left.mp
    ((rowFrame L T hn hsmall rest hbody R).fixed_moving_disjoint originalSetting) hx hxS

end
end CorralFormalization.Results.SwitchFamily.Physical
