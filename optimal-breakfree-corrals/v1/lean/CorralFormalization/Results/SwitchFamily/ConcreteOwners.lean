import CorralFormalization.Results.SwitchFamily.ConcreteMarkers

/-!
# The two actual switch sites have different row owners

If two consecutive physical sites were in the same row, they would form an
actual gap-one edge. The proven gap-one marker pattern puts all such tails
at residue 17, while the prescribed switch centers have residue at least 38.
This pays the owner distinction directly from the existing general tile
geometry; no moving-site coverage or selected-row premise is used.
-/

open EndpointRouter
open CorralFormalization.PhysicalCorral CorralFormalization.DiversitySymmetry
open CorralFormalization.LatinCompletion
open CorralFormalization.LatinCompletion.TerraceLift
open CorralFormalization.LatinCompletion.TerraceCompletion
open CorralFormalization.LatinCompletion.GeneralTiles
open CorralFormalization.Results.SwitchFamily.Physical

namespace CorralFormalization.Results.SwitchFamily.ConcreteOwners

noncomputable section

theorem gapLength_succ {M : ℕ} [NeZero M] (hM : 2 ≤ M) (x : ZMod M) :
    gapLength x (x+1) = 1 := by
  unfold gapLength
  have he : x+1-x = (1 : ZMod M) := by ring
  rw [he]
  have : Fact (1<M) := ⟨by omega⟩
  exact ZMod.val_one M

/-- If consecutive sites both belong to a row, their actual clockwise edge
has length one, including across the physical clock's zero. -/
theorem adjacent_succ {M : ℕ} [NeZero M] (hM : 2 ≤ M)
    (R : Finset (ZMod M)) (x : ZMod M) (hx : x ∈ R) (hy : x+1 ∈ R) :
    Adjacent R x (x+1) := by
  have hg := gapLength_succ hM x
  refine ⟨hx,hy,?_,?_⟩
  · intro he
    have hh := congrArg (gapLength x) he
    simp only [gapLength,sub_self,ZMod.val_zero] at hh
    have hg' : ((x+1-x : ZMod M)).val = 1 := hg
    omega
  · intro z hz hi
    have hl : gapLength x z < 1 := by simpa [hg] using hi.2
    exact (by omega : ¬(0 < gapLength x z ∧ gapLength x z < 1)) ⟨hi.1,hl⟩

variable {h n m : ℕ} [NeZero h] [NeZero n] [NeZero (h*n)]

omit [NeZero h] [NeZero n] [NeZero (h*n)] in
theorem left_endpoint_residue_ne_seventeen (hsmall : 65 ≤ n)
    (hsize : (5*m+8)^2 ≤ n) (k : Bit m h) :
    residueMap h n (endpoint (n:=n) k false) ≠ 17 := by
  rw [endpoint_residue]
  simp only [Bool.toNat_false,Nat.add_zero]
  have hval := center_value_bounds hsize k.1 false
  simp only [Bool.toNat_false,Nat.add_zero] at hval
  have hlarge : 17 < Prefix.center k.1.val := by simp [Prefix.center]; omega
  intro he
  have hv := congrArg ZMod.val he
  change ((Prefix.center k.1.val : ℕ) : ZMod n).val = (((17 : ℕ) : ZMod n)).val at hv
  rw [ZMod.val_natCast_of_lt hval.2,ZMod.val_natCast_of_lt (by omega : 17<n)] at hv
  omega

/-- Both endpoints of every concrete switch are in different rows of the
arbitrary baseline tiling. The required first owner is an actual row. -/
theorem concrete_switch_owners {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : DirectedTerrace n) (hn : n=2*h-1) (hsmall : 65 ≤ n)
    (hp : HasSpecifiedPrefix D) (tiles : CyclicTiling h ι)
    (hsize : (5*m+8)^2 ≤ n) :
    ∀ e ∈ (switchLayer (h:=h) hsize).edges,
      ∃ R ∈ tiles.family (completedOfSpecifiedPrefix D hsmall hp), e.1 ∈ R ∧ e.2 ∉ R := by
  intro e he
  change e ∈ (Finset.univ : Finset (Bit m h)).toList.map (sitePair (n:=n)) at he
  obtain ⟨k,_,rfl⟩ := List.mem_map.mp he
  let T := completedOfSpecifiedPrefix D hsmall hp
  let base := tiles.family T
  let x := endpoint (n:=n) k false
  have hx : x ∈ base.biUnion id := by
    rw [tiles.full T hn (by omega)]
    simp
  obtain ⟨R,hR,hxR⟩ := Finset.mem_biUnion.mp hx
  refine ⟨R,hR,hxR,?_⟩
  intro hyR
  have hy : x+1 ∈ R := by simpa [x,sitePair,endpoint_right] using hyR
  have hM : 2 ≤ h*n := by
    have hh := NeZero.pos h
    nlinarith
  have ha := adjacent_succ hM R x hxR hy
  have hgap : gapLength x (x+1)=1 := gapLength_succ hM x
  have htail : x ∈ gapTails R 1 := (mem_gapTails R 1 x).mpr ⟨x+1,ha,hgap⟩
  have hglobal : x ∈ familyTails base 1 := Finset.mem_biUnion.mpr ⟨R,hR,htail⟩
  have hpattern := (explicit_distinguished_tails D hn hsmall hp tiles).1
  change familyTails base 1 = oneTailPattern h n at hpattern
  rw [hpattern] at hglobal
  have hres := (mem_oneTailPattern x).mp hglobal
  exact left_endpoint_residue_ne_seventeen hsmall hsize k hres

end
end CorralFormalization.Results.SwitchFamily.ConcreteOwners
