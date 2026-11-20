import CorralFormalization.EndpointProof.Transitions.Weights

/-!
# The complete nine-convolution exceptional-set and weighted-formula bounds

This file derives the explicit core/root weighted degree *formulas* from
the literal raw Fourier and one-sided later-target hypotheses of the ordinary transition lemma.
Converting these formulas to finite hypergraph incidence sums is a separate
combinatorial step; no equality of that kind is assumed here.
-/

open scoped Classical BigOperators

namespace EndpointTransitions

noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G]

def partner₁ (i : Fin 3) : Fin 3 := if i=0 then 1 else 0
def partner₂ (i : Fin 3) : Fin 3 := if i=2 then 1 else 2

def badLabels (R T : Fin 3 → Finset G) (a : Fin 3 → ℝ) (η : ℝ) (i : Fin 3) : Finset G :=
  exceptional (R (partner₁ i)) (R (partner₂ i)) (a (partner₁ i)) η ∪
  exceptional (R (partner₂ i)) (additions (R (partner₁ i)) (T (partner₁ i))) (a (partner₂ i)) η ∪
  exceptional (R (partner₁ i)) (additions (R (partner₂ i)) (T (partner₂ i))) (a (partner₁ i)) η

def coreDegreeFormula (R T : Fin 3 → Finset G) (a : Fin 3 → ℝ)
    (q : ℝ) (i : Fin 3) (x : G) : ℝ :=
  coreWeight q (a i) (a (partner₁ i)) (a (partner₂ i)) *
    pairCount (core (R (partner₁ i)) (T (partner₁ i)))
      (core (R (partner₂ i)) (T (partner₂ i))) (-x) +
  rootWeight q (a i) (a (partner₂ i)) *
    pairCount (additions (R (partner₁ i)) (T (partner₁ i)))
      (core (R (partner₂ i)) (T (partner₂ i))) (-x) +
  rootWeight q (a i) (a (partner₁ i)) *
    pairCount (core (R (partner₁ i)) (T (partner₁ i)))
      (additions (R (partner₂ i)) (T (partner₂ i))) (-x)

def rootDegreeFormula (R T : Fin 3 → Finset G) (a : Fin 3 → ℝ)
    (q : ℝ) (i : Fin 3) (x : G) : ℝ :=
  rootWeight q (a (partner₁ i)) (a (partner₂ i)) *
    pairCount (core (R (partner₁ i)) (T (partner₁ i)))
      (core (R (partner₂ i)) (T (partner₂ i))) (-x)

theorem badLabels_card {R : Fin 3 → Finset G} {a : Fin 3 → ℝ} {η : ℝ}
    (hraw : ∀ i, FourierGood (R i) (a i) η) (hη : 0 < η)
    (T : Fin 3 → Finset G) (i : Fin 3) :
    ((badLabels R T a η i).card : ℝ) ≤ 3*η^2*(Fintype.card G : ℝ) := by
  have h₀ := (hraw (partner₁ i)).exceptional_card hη (R (partner₂ i))
  have h₁ := (hraw (partner₂ i)).exceptional_card hη
    (additions (R (partner₁ i)) (T (partner₁ i)))
  have h₂ := (hraw (partner₁ i)).exceptional_card hη
    (additions (R (partner₂ i)) (T (partner₂ i)))
  have hcard : (badLabels R T a η i).card ≤
      (exceptional (R (partner₁ i)) (R (partner₂ i)) (a (partner₁ i)) η).card+
      (exceptional (R (partner₂ i)) (additions (R (partner₁ i)) (T (partner₁ i)))
        (a (partner₂ i)) η).card+
      (exceptional (R (partner₁ i)) (additions (R (partner₂ i)) (T (partner₂ i)))
        (a (partner₁ i)) η).card := by
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)
  have hcard' : ((badLabels R T a η i).card : ℝ) ≤
      ((exceptional (R (partner₁ i)) (R (partner₂ i)) (a (partner₁ i)) η).card : ℝ)+
      ((exceptional (R (partner₂ i)) (additions (R (partner₁ i)) (T (partner₁ i)))
        (a (partner₂ i)) η).card : ℝ)+
      ((exceptional (R (partner₁ i)) (additions (R (partner₂ i)) (T (partner₂ i)))
        (a (partner₁ i)) η).card : ℝ) := by exact_mod_cast hcard
  linarith

/-- The actual target vertices deleted for exceptional labels, using the
negative label because the edge equation is `x+y+z=0`. -/
def badVertices (R T : Fin 3 → Finset G) (a : Fin 3 → ℝ) (η : ℝ) :
    Finset (Fin 3 × G) :=
  Finset.univ.biUnion (fun i => ((T i).filter (fun x => -x ∈ badLabels R T a η i)).image
    (fun x => (i,x)))

theorem mem_badVertices (R T : Fin 3 → Finset G) (a : Fin 3 → ℝ) (η : ℝ)
    (i : Fin 3) (x : G) :
    (i,x) ∈ badVertices R T a η ↔ x ∈ T i ∧ -x ∈ badLabels R T a η i := by
  simp [badVertices]

/-- At most nine `η²n` tagged vertices are deleted in total.  Coincident
numerical labels in different roles are counted with their actual tags. -/
theorem badVertices_card {R : Fin 3 → Finset G} {a : Fin 3 → ℝ} {η : ℝ}
    (hraw : ∀ i, FourierGood (R i) (a i) η) (hη : 0 < η) (T : Fin 3 → Finset G) :
    ((badVertices R T a η).card : ℝ) ≤ 9*η^2*(Fintype.card G : ℝ) := by
  have hc (i : Fin 3) :
      (((T i).filter (fun x => -x ∈ badLabels R T a η i)).card : ℝ) ≤
        3*η^2*(Fintype.card G : ℝ) := by
    have hinj : ((T i).filter (fun x => -x ∈ badLabels R T a η i)).card ≤
        (badLabels R T a η i).card := by
      apply Finset.card_le_card_of_injOn (fun x : G => -x)
      · intro x hx
        exact (Finset.mem_filter.mp hx).2
      · exact fun x _ y _ hxy => neg_injective hxy
    have hinj' : (((T i).filter (fun x => -x ∈ badLabels R T a η i)).card : ℝ) ≤
        (badLabels R T a η i).card := by exact_mod_cast hinj
    exact hinj'.trans (badLabels_card hraw hη T i)
  have hcard : (badVertices R T a η).card ≤
      ∑ i : Fin 3, ((T i).filter (fun x => -x ∈ badLabels R T a η i)).card := by
    apply (Finset.card_biUnion_le).trans
    apply Finset.sum_le_sum
    intro i _
    exact Finset.card_image_le
  have hcard' : ((badVertices R T a η).card : ℝ) ≤
      ∑ i : Fin 3, (((T i).filter (fun x => -x ∈ badLabels R T a η i)).card : ℝ) := by
    exact_mod_cast hcard
  calc
    _ ≤ ∑ i : Fin 3, (((T i).filter (fun x => -x ∈ badLabels R T a η i)).card : ℝ) := hcard'
    _ ≤ ∑ _i : Fin 3, 3*η^2*(Fintype.card G : ℝ) := Finset.sum_le_sum (fun i _ => hc i)
    _ = _ := by simp; ring

/-- The displayed core/root formulas have the correct common ideal degree
and the stated `14ηn`/`4ηn` errors.  All target quantifiers are deterministic
and follow the raw Fourier hypotheses. -/
theorem convolution_degree_errors {R T : Fin 3 → Finset G} {a : Fin 3 → ℝ}
    {q η : ℝ} (hq : 0 < q) (hqone : q ≤ 1)
    (ha : ∀ i, DensityWindow q (a i)) (hraw : ∀ i, FourierGood (R i) (a i) η)
    (hη : 0 ≤ η) (hηone : η ≤ 1)
    (htarget : ∀ i, |((T i).card : ℝ)-q*(Fintype.card G : ℝ)| ≤ η*(Fintype.card G : ℝ))
    (hloss : ∀ i, (((R i) \ (T i)).card : ℝ) ≤ η*(Fintype.card G : ℝ))
    (i : Fin 3) (x : G) (hx : -x ∉ badLabels R T a η i) :
    |coreDegreeFormula R T a q i x-q^2*(Fintype.card G : ℝ)/2| ≤
      14*η*(Fintype.card G : ℝ) ∧
    |rootDegreeFormula R T a q i x-q^2*(Fintype.card G : ℝ)/2| ≤
      4*η*(Fintype.card G : ℝ) := by
  have h₀ : -x ∉ exceptional (R (partner₁ i)) (R (partner₂ i)) (a (partner₁ i)) η := by
    intro h
    exact hx (Finset.mem_union_left _ (Finset.mem_union_left _ h))
  have h₁ : -x ∉ exceptional (R (partner₂ i))
      (additions (R (partner₁ i)) (T (partner₁ i))) (a (partner₂ i)) η := by
    intro h
    exact hx (Finset.mem_union_left _ (Finset.mem_union_right _ h))
  have h₂ : -x ∉ exceptional (R (partner₁ i))
      (additions (R (partner₂ i)) (T (partner₂ i))) (a (partner₁ i)) η := by
    intro h
    exact hx (Finset.mem_union_right _ h)
  have hc := core_pair_error (hraw (partner₁ i)) (hraw (partner₂ i)) hη hηone
    ((ha (partner₁ i)).pos hq).le ((ha (partner₁ i)).2.trans hqone)
    (hloss (partner₁ i)) (hloss (partner₂ i)) h₀
  have hj₁ := additions_core_error (hraw (partner₂ i)) (hraw (partner₁ i)) hη hηone
    ((ha (partner₂ i)).pos hq).le ((ha (partner₂ i)).2.trans hqone)
    (htarget (partner₁ i)) (hloss (partner₂ i)) (hloss (partner₁ i)) h₁
  rw [pairCount_comm] at hj₁
  have hj₂ := additions_core_error (hraw (partner₁ i)) (hraw (partner₂ i)) hη hηone
    ((ha (partner₁ i)).pos hq).le ((ha (partner₁ i)).2.trans hqone)
    (htarget (partner₂ i)) (hloss (partner₁ i)) (hloss (partner₂ i)) h₂
  constructor
  · apply core_degree_error hq (ha i) (ha (partner₁ i)) (ha (partner₂ i)) hc
    · convert hj₁ using 1 <;> ring
    · convert hj₂ using 1 <;> ring
  · have hw := rootWeight_bounds hq (ha (partner₁ i)) (ha (partner₂ i))
    rw [rootDegreeFormula, ← ideal_root_degree q (a (partner₁ i)) (a (partner₂ i))
      (Fintype.card G) (ne_of_gt ((ha (partner₁ i)).pos hq))
      (ne_of_gt ((ha (partner₂ i)).pos hq)), ← mul_sub, abs_mul, abs_of_nonneg hw.1.le]
    exact (mul_le_mul_of_nonneg_left hc hw.1.le).trans
      (by nlinarith [mul_nonneg hη (Nat.cast_nonneg (α := ℝ) (Fintype.card G))])

end
end EndpointTransitions
