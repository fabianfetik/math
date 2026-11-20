import CorralFormalization.EndpointProof.AbsorberInputs.CandidatePacking.CompleteCollision

namespace AbsorberInputs.CandidatePacking

open Finset EndpointRouter EndpointOriginalReservoir
open scoped BigOperators Classical

noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
variable {e r s : ℕ} (D : Data e r s G)

namespace Data

theorem mem_support (t : Fin e → G) (x : G) :
    x ∈ D.support t ↔ ∃ j, x = D.value t j ∨ x = -D.value t j := by
  constructor
  · intro hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hx
      exact ⟨j,Or.inl hj.symm⟩
    · obtain ⟨y,hy,hyx⟩ := Finset.mem_image.mp hx
      obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hy
      exact ⟨j,Or.inr (hyx.symm.trans (congrArg Neg.neg hj).symm)⟩
  · rintro ⟨j,hx | hx⟩
    · apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,hx.symm⟩
    · apply Finset.mem_union_right
      exact Finset.mem_image.mpr
        ⟨D.value t j,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩,hx.symm⟩

theorem value_mem_support (t : Fin e → G) (j : Fin r) : D.value t j ∈ D.support t :=
  (D.mem_support t _).mpr ⟨j,Or.inl rfl⟩

theorem support_nonempty (hr : 0 < r) (t : Fin e → G) : (D.support t).Nonempty :=
  ⟨D.value t ⟨0,hr⟩,D.value_mem_support t ⟨0,hr⟩⟩

end Data

/-- All validity and disjointness fields of this output are supplied below
from affine coefficients and the canonical collision specification. -/
structure Packed (D : Data e r s G) (M : ℕ) where
  parameter : Fin M ↪ (Fin e → G)
  valid : ∀ i, D.Valid (parameter i)
  disjoint : Pairwise fun i j => Disjoint (D.support (parameter i)) (D.support (parameter j))

/-- Exact greedy criterion, without a packing or orbit injection premise. -/
theorem exists_packed (hodd : Odd (Fintype.card G)) (hr : 0 < r)
    (hreg : D.Regular) (hp : D.IndividualPivots) (M : ℕ)
    (hsize : D.collisionCount + 2*r*r*M < Fintype.card G) :
    Nonempty (Packed D M) := by
  let k : Fin r → Fin e := fun j => Classical.choose (hp j)
  have hk (j : Fin r) : Switch.SmallCoefficient (D.coefficient j (k j)) :=
    Classical.choose_spec (hp j)
  have he := D.positive_parameters hr hp
  have hpw : 0 < (Fintype.card G)^(e-1) := pow_pos Fintype.card_pos _
  have hpow : (Fintype.card G)^e = (Fintype.card G)^(e-1)*Fintype.card G := by
    conv_lhs => rw [← Nat.sub_add_cancel he]
    rw [pow_succ]
  have hsize' : D.collisionCount*(Fintype.card G)^(e-1) +
      (2*r*r*M)*(Fintype.card G)^(e-1) < (Fintype.card G)^e := by
    rw [hpow]
    simpa only [Nat.mul_add,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using
      Nat.mul_lt_mul_of_pos_left hsize hpw
  obtain ⟨U,hU,hvalid,hdisj⟩ := GenericAffine.exists_affine_orbit_packing hodd hr
    D.collisionConstant D.collisionCoefficient (fun _ => 0) D.collisionPivot D.collisionPivot_spec
    D.constant D.coefficient k hk M hsize'
  let eqv : U ≃ Fin M := Fintype.equivFinOfCardEq (by simpa using hU)
  let f : Fin M ↪ (Fin e → G) :=
    ⟨fun i => (eqv.symm i).val,Subtype.val_injective.comp eqv.symm.injective⟩
  refine ⟨⟨f,?_,?_⟩⟩
  · intro i
    exact (D.not_excluded_iff_valid hreg (f i)).mp (hvalid (f i) (eqv.symm i).property)
  · intro i j hij
    exact hdisj (eqv.symm i).property (eqv.symm j).property
      (fun heq => hij (f.injective heq))

/-- The upper bound `m` and collision bound `C` are uniform quantitative
parameters. The actual nonempty form count is `r ≤ m`. -/
theorem exists_linear_packed (hodd : Odd (Fintype.card G)) (hr : 0 < r)
    (hreg : D.Regular) (hp : D.IndividualPivots) (m C : ℕ)
    (hrm : r ≤ m) (hC : D.collisionCount ≤ C) (hn : 2*C < Fintype.card G) :
    Nonempty (Packed D (Fintype.card G/(4*m*m))) := by
  let n := Fintype.card G
  let M := n/(4*m*m)
  have hdiv : (4*m*m)*M ≤ n := Nat.mul_div_le n (4*m*m)
  have hhalf : 2*(2*m*m*M) ≤ n := by
    calc
      _ = (4*m*m)*M := by ring
      _ ≤ n := hdiv
  have hcost : 2*r*r*M ≤ 2*m*m*M := by gcongr
  apply exists_packed D hodd hr hreg hp M
  change 2*C < n at hn
  change D.collisionCount + 2*r*r*M < n
  omega

/-- The chosen canonical orbit and the orientation of an actual nonzero form. -/
def locate (hodd : Odd (Fintype.card G)) (x : G) (hx : x ≠ 0) : OddOrbit G × Bool :=
  Classical.choose (orbitPlace_covers_nonzero hodd hx)

theorem locate_spec (hodd : Odd (Fintype.card G)) (x : G) (hx : x ≠ 0) :
    orbitPlace (locate hodd x hx) = x :=
  Classical.choose_spec (orbitPlace_covers_nonzero hodd hx)

def actualOrbit (hodd : Odd (Fintype.card G)) (x : G) (hx : x ≠ 0) : OddOrbit G :=
  (locate hodd x hx).1

theorem actualOrbit_signed (hodd : Odd (Fintype.card G)) (x : G) (hx : x ≠ 0) :
    x = (actualOrbit hodd x hx).val ∨ x = -(actualOrbit hodd x hx).val := by
  have h := locate_spec hodd x hx
  change (if (locate hodd x hx).2 then -(actualOrbit hodd x hx).val
    else (actualOrbit hodd x hx).val) = x at h
  cases ht : (locate hodd x hx).2 <;> simp only [ht,Bool.false_eq_true,↓reduceIte] at h
  · exact Or.inl h.symm
  · exact Or.inr h.symm

theorem signed_of_actualOrbit_eq (hodd : Odd (Fintype.card G)) (x y : G)
    (hx : x ≠ 0) (hy : y ≠ 0) (he : actualOrbit hodd x hx = actualOrbit hodd y hy) :
    x = y ∨ x = -y := by
  have hxs := actualOrbit_signed hodd x hx
  have hys := actualOrbit_signed hodd y hy
  rw [he] at hxs
  rcases hxs with hxs | hxs
  · rcases hys with hys | hys
    · exact Or.inl (hxs.trans hys.symm)
    · right; rw [hys,neg_neg]; exact hxs
  · rcases hys with hys | hys
    · right; rw [hys]; exact hxs
    · exact Or.inl (hxs.trans hys.symm)

namespace Packed

variable {D} {M : ℕ} (P : Packed D M)

/-- This desired injection is proved from the constructed packing and the
complete internal signed collision tests. -/
def orbitEmbedding (hodd : Odd (Fintype.card G)) : Fin M × Fin r ↪ OddOrbit G where
  toFun ij := actualOrbit hodd (D.value (P.parameter ij.1) ij.2) ((P.valid ij.1).1 ij.2)
  inj' := by
    rintro ⟨i,j⟩ ⟨k,l⟩ he
    have hs := signed_of_actualOrbit_eq hodd
      (D.value (P.parameter i) j) (D.value (P.parameter k) l)
      ((P.valid i).1 j) ((P.valid k).1 l) he
    have hik : i = k := by
      by_contra hik
      have hj := D.value_mem_support (P.parameter i) j
      have hl := (D.mem_support (P.parameter k) _).mpr ⟨l,hs⟩
      exact Finset.disjoint_left.mp (P.disjoint hik) hj hl
    subst k
    have hjl : j = l := by
      by_contra hjl
      have hd := (P.valid i).2.1 j l hjl
      exact hs.elim hd.1 hd.2
    exact Prod.ext rfl hjl

theorem orbitEmbedding_coordinate (hodd : Odd (Fintype.card G)) (i : Fin M) (j : Fin r) :
    ∃ b, orbitPlace (P.orbitEmbedding hodd (i,j),b) = D.value (P.parameter i) j :=
  ⟨(locate hodd _ ((P.valid i).1 j)).2,locate_spec hodd _ ((P.valid i).1 j)⟩

def sigmaOrbitEmbedding (hodd : Odd (Fintype.card G)) : (Σ _i : Fin M, Fin r) ↪ OddOrbit G where
  toFun ij := P.orbitEmbedding hodd (ij.1,ij.2)
  inj' := by
    rintro ⟨i,j⟩ ⟨k,l⟩ he
    have h := (P.orbitEmbedding hodd).injective he
    rcases Prod.mk.inj h with ⟨hi,hj⟩
    dsimp at hi hj
    subst k l
    rfl

theorem orbitEmbedding_place_iff (hodd : Odd (Fintype.card G)) (i : Fin M) (j : Fin r) (x : G) :
    (∃ b, orbitPlace (P.orbitEmbedding hodd (i,j),b) = x) ↔
      x = D.value (P.parameter i) j ∨ x = -D.value (P.parameter i) j := by
  obtain ⟨b,hb⟩ := P.orbitEmbedding_coordinate hodd i j
  constructor
  · rintro ⟨c,hc⟩
    have hbc : c = b ∨ c = !b := by cases b <;> cases c <;> simp
    rcases hbc with rfl | rfl
    · exact Or.inl (hc.symm.trans hb)
    · rw [orbitPlace_neg,hb] at hc
      exact Or.inr hc.symm
  · rintro (hx | hx)
    · exact ⟨b,hb.trans hx.symm⟩
    · exact ⟨!b,by rw [orbitPlace_neg,hb,hx]⟩

def numericalSupport (hodd : Odd (Fintype.card G)) (i : Fin M) : Finset G :=
  Finset.univ.image fun jb : Fin r × Bool => orbitPlace (P.orbitEmbedding hodd (i,jb.1),jb.2)

theorem numericalSupport_eq (hodd : Odd (Fintype.card G)) (i : Fin M) :
    P.numericalSupport hodd i = D.support (P.parameter i) := by
  ext x
  simp only [numericalSupport,Finset.mem_image,Finset.mem_univ,true_and,Data.mem_support]
  constructor
  · rintro ⟨⟨j,b⟩,h⟩
    exact ⟨j,(P.orbitEmbedding_place_iff hodd i j x).mp ⟨b,h⟩⟩
  · rintro ⟨j,h⟩
    obtain ⟨b,hb⟩ := (P.orbitEmbedding_place_iff hodd i j x).mpr h
    exact ⟨(j,b),hb⟩

theorem support_card (hodd : Odd (Fintype.card G)) (i : Fin M) :
    (D.support (P.parameter i)).card = 2*r := by
  rw [← P.numericalSupport_eq hodd i,numericalSupport,Finset.card_image_of_injective]
  · simp [Nat.mul_comm]
  · rintro ⟨j,b⟩ ⟨k,c⟩ he
    have h := orbitPlace.injective he
    have hjk := (P.orbitEmbedding hodd).injective (Prod.mk.inj h).1
    exact Prod.ext (Prod.mk.inj hjk).2 (Prod.mk.inj h).2

/-- The actual physical signed supports, not just parameter assignments,
are distinct when the actual orbit list is nonempty. -/
theorem physical_support_injective (hr : 0 < r) :
    Function.Injective (fun i => D.support (P.parameter i)) := by
  intro i j hij
  change D.support (P.parameter i) = D.support (P.parameter j) at hij
  by_contra hne
  obtain ⟨x,hx⟩ := D.support_nonempty hr (P.parameter i)
  have hxj : x ∈ D.support (P.parameter j) := by rw [← hij]; exact hx
  exact Finset.disjoint_left.mp (P.disjoint hne) hx hxj

end Packed

end
end AbsorberInputs.CandidatePacking
