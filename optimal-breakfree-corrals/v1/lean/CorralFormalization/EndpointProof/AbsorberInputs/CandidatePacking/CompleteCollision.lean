import CorralFormalization.EndpointProof.AbsorberInputs.GenericAffineFibers
import CorralFormalization.EndpointProof.Sampling.InverseOrbits
import Mathlib.Data.Fintype.Prod

/-!
# Actual affine orbit gadgets from a complete collision specification

The hypotheses below concern the actual affine coefficients and the complete
canonical list of zero, signed-pair and signed-root equations. Neither internal
orbit injectivity nor a valid packing is an input. The number `r` is the number
of actual representatives, whereas `m` in the quantitative theorem is only an
upper bound. A positive `r`, together with an individual pivot, implies `e > 0`.
-/

namespace AbsorberInputs.CandidatePacking

open Finset EndpointRouter EndpointOriginalReservoir
open scoped BigOperators Classical

noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

structure Data (e r s : ℕ) (G : Type*) where
  root : Fin s → G
  constant : Fin r → G
  coefficient : Fin r → Fin e → ℤ

namespace Data

variable {e r s : ℕ} (D : Data e r s G)

def value (t : Fin e → G) (j : Fin r) : G :=
  GenericAffine.value (D.constant j) (D.coefficient j) t

def support (t : Fin e → G) : Finset G :=
  GenericAffine.signedClosure (GenericAffine.representatives D.constant D.coefficient t)

def rootSupport : Finset G :=
  GenericAffine.signedClosure (Finset.univ.image D.root)

def Valid (t : Fin e → G) : Prop :=
  (∀ j, D.value t j ≠ 0) ∧
  (∀ i j, i ≠ j → D.value t i ≠ D.value t j ∧ D.value t i ≠ -D.value t j) ∧
  (∀ i j, D.value t i ≠ D.root j ∧ D.value t i ≠ -D.root j)

def IndividualPivots : Prop :=
  ∀ j, ∃ k, Switch.SmallCoefficient (D.coefficient j k)

/-- The tests contain each unordered pair once and both signs. -/
abbrev Test (_D : Data e r s G) := Fin r ⊕
  (({ij : Fin r × Fin r // ij.1 < ij.2} × Bool) ⊕ (Fin r × Fin s × Bool))

def signed {α : Type*} [Neg α] (b : Bool) (x : α) : α := if b then -x else x

def testConstant : D.Test → G
  | .inl i => D.constant i
  | .inr (.inl (ij,b)) => D.constant ij.val.1 - signed b (D.constant ij.val.2)
  | .inr (.inr (i,j,b)) => D.constant i - signed b (D.root j)

def testCoefficient : D.Test → Fin e → ℤ
  | .inl i => D.coefficient i
  | .inr (.inl (ij,b)) => fun k => D.coefficient ij.val.1 k - signed b (D.coefficient ij.val.2 k)
  | .inr (.inr (i,_,_)) => D.coefficient i

def testValue (q : D.Test) (t : Fin e → G) : G :=
  GenericAffine.value (D.testConstant q) (D.testCoefficient q) t

theorem value_neg (a : G) (p : Fin e → ℤ) (t : Fin e → G) :
    GenericAffine.value (-a) (fun k => -p k) t = -GenericAffine.value a p t := by
  simp only [GenericAffine.value, neg_zsmul, Finset.sum_neg_distrib, neg_add_rev]
  abel

@[simp] theorem testValue_zero (i : Fin r) (t : Fin e → G) :
    D.testValue (.inl i) t = D.value t i := rfl

@[simp] theorem testValue_pair (ij : {ij : Fin r × Fin r // ij.1 < ij.2})
    (b : Bool) (t : Fin e → G) :
    D.testValue (.inr (.inl (ij,b))) t =
      D.value t ij.val.1 - signed b (D.value t ij.val.2) := by
  cases b
  · exact (GenericAffine.value_sub _ _ _ _ _).symm
  · simpa only [testValue,testConstant,testCoefficient,signed, Bool.true_eq, ↓reduceIte,
      value_neg,value] using
      (GenericAffine.value_sub (D.constant ij.val.1) (-D.constant ij.val.2)
        (D.coefficient ij.val.1) (fun k => -D.coefficient ij.val.2 k) t).symm

@[simp] theorem testValue_root (i : Fin r) (j : Fin s) (b : Bool) (t : Fin e → G) :
    D.testValue (.inr (.inr (i,j,b))) t = D.value t i - signed b (D.root j) := by
  dsimp only [testValue,testConstant,testCoefficient,value,GenericAffine.value]
  abel

/-- Exact completeness of the canonical collision list. -/
theorem valid_iff_all_tests (t : Fin e → G) :
    D.Valid t ↔ ∀ q, D.testValue q t ≠ 0 := by
  constructor
  · rintro ⟨hz,hpair,hr⟩ (i | (⟨ij,b⟩ | ⟨i,j,b⟩))
    · exact hz i
    · rw [testValue_pair,sub_ne_zero]
      have hp := hpair ij.val.1 ij.val.2 (ne_of_lt ij.property)
      cases b
      · simpa [signed] using hp.1
      · simpa [signed] using hp.2
    · rw [testValue_root,sub_ne_zero]
      cases b
      · simpa [signed] using (hr i j).1
      · simpa [signed] using (hr i j).2
  · intro ht
    refine ⟨fun i => ht (.inl i), ?_, ?_⟩
    · intro i j hij
      by_cases hlt : i < j
      · have hp := ht (.inr (.inl (⟨(i,j),hlt⟩,false)))
        have hm := ht (.inr (.inl (⟨(i,j),hlt⟩,true)))
        simpa only [testValue_pair,signed,Bool.false_eq_true,↓reduceIte,sub_ne_zero]
          using And.intro hp hm
      · have hji : j < i := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hij)
        have hp := ht (.inr (.inl (⟨(j,i),hji⟩,false)))
        have hm := ht (.inr (.inl (⟨(j,i),hji⟩,true)))
        simp only [testValue_pair,signed,Bool.false_eq_true,↓reduceIte,
          Bool.true_eq,sub_ne_zero] at hp hm
        refine ⟨Ne.symm hp, ?_⟩
        intro h
        apply hm
        simpa using (congrArg Neg.neg h).symm
    · intro i j
      have hp := ht (.inr (.inr (i,j,false)))
      have hm := ht (.inr (.inr (i,j,true)))
      simpa only [testValue_root,signed,Bool.false_eq_true,↓reduceIte,sub_ne_zero]
        using And.intro hp hm

def HasPivot (q : D.Test) : Prop :=
  ∃ k, Switch.SmallCoefficient (D.testCoefficient q k)

/-- Root-excluded equations are explicitly impossible for every assignment.
Every remaining actual collision equation has a genuine small pivot. -/
def Regular : Prop :=
  ∀ q, (∀ t, D.testValue q t ≠ 0) ∨ D.HasPivot q

abbrev LiveTest := {q : D.Test // D.HasPivot q}

def collisionCount : ℕ := Fintype.card D.LiveTest

def liveTest (j : Fin D.collisionCount) : D.LiveTest :=
  (Fintype.equivFin D.LiveTest).symm j

def collisionConstant (j : Fin D.collisionCount) : G := D.testConstant (D.liveTest j).val
def collisionCoefficient (j : Fin D.collisionCount) : Fin e → ℤ :=
  D.testCoefficient (D.liveTest j).val
def collisionPivot (j : Fin D.collisionCount) : Fin e := Classical.choose (D.liveTest j).property

theorem collisionPivot_spec (j : Fin D.collisionCount) :
    Switch.SmallCoefficient (D.collisionCoefficient j (D.collisionPivot j)) :=
  Classical.choose_spec (D.liveTest j).property

def excluded : Finset (Fin e → G) :=
  GenericAffine.collisionAssignments D.collisionConstant D.collisionCoefficient (fun _ => 0)

theorem not_excluded_iff_valid (hreg : D.Regular) (t : Fin e → G) :
    t ∉ D.excluded ↔ D.Valid t := by
  rw [valid_iff_all_tests]
  constructor
  · intro ht q
    rcases hreg q with hq | hq
    · exact hq t
    · intro he
      apply ht
      let j := Fintype.equivFin D.LiveTest ⟨q,hq⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨j,Finset.mem_univ _,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
      simpa [collisionConstant,collisionCoefficient,liveTest,j,testValue] using he
  · intro ht hbad
    obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp hbad
    exact ht (D.liveTest j).val (Finset.mem_filter.mp hj).2

theorem positive_parameters (hr : 0 < r) (hp : D.IndividualPivots) : 1 ≤ e := by
  obtain ⟨k,_⟩ := hp ⟨0,hr⟩
  exact Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le k.val) k.isLt)

theorem canonical_test_count : Fintype.card D.Test = r + 2*(r.choose 2) + 2*r*s := by
  have hpair : Fintype.card {ij : Fin r × Fin r // ij.1 < ij.2} = r.choose 2 := by
    rw [Fintype.card_subtype]
    simpa using (Fintype.card_product_filter_lt (α := Fin r))
  simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,hpair]
  ring

theorem collisionCount_le_canonical : D.collisionCount ≤ r + 2*(r.choose 2) + 2*r*s := by
  rw [← D.canonical_test_count]
  exact Fintype.card_le_of_injective (fun q : D.LiveTest => q.val) Subtype.val_injective

/-- Full collision validity is concluded, not supplied as a premise. -/
theorem validAssignments_card_lower (hodd : Odd (Fintype.card G)) (hreg : D.Regular)
    (C : ℕ) (hC : D.collisionCount ≤ C) :
    (Fintype.card G)^e - C*(Fintype.card G)^(e-1) ≤
      ((Finset.univ : Finset (Fin e → G)).filter D.Valid).card := by
  have h := GenericAffine.validAssignments_card_lower hodd D.collisionConstant
    D.collisionCoefficient (fun _ => 0) D.collisionPivot D.collisionPivot_spec
  have heq : (Finset.univ : Finset (Fin e → G)) \ D.excluded =
      Finset.univ.filter D.Valid := by
    ext t
    simp only [Finset.mem_sdiff,Finset.mem_univ,true_and,Finset.mem_filter]
    exact D.not_excluded_iff_valid hreg t
  change _ ≤ ((Finset.univ : Finset (Fin e → G)) \ D.excluded).card at h
  rw [heq] at h
  exact (Nat.sub_le_sub_left (Nat.mul_le_mul_right _ hC) _).trans h

end Data

end
end AbsorberInputs.CandidatePacking
