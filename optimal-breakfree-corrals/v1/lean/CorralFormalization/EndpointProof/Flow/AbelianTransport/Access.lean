import CorralFormalization.EndpointProof.Flow.AbelianTransport.Theorem

/-!
Purely additive access to the written real budgets and original signed
sample. The six-root output-sum law is derived from its actual matching.
-/

open scoped Classical BigOperators

namespace EndpointFlow.AbelianTransport

open EndpointFullProduct
open CorralFormalization.EndpointProof.RateBudget
open CorralFormalization.EndpointProof.RateBudget.SamplingConstants

noncomputable section

variable {G : Type*} [Fintype G] [AddCommGroup G]

theorem ReservoirVertex.originalSigned (ω : FullSample G) (isQ : Bool) (v : Vertex G)
    (hv : ReservoirVertex ω isQ v) : originalSigned v.1 (originalProcess ω) v.2 := by
  obtain ⟨o,side,hcoord,hchild⟩ := hv
  apply signedMinus_subset_originalSigned
  rw [← hcoord]
  exact child_signed_containment v.1 isQ side ω o hchild

theorem Matching.coordinate_sum_zero {S : Finset (Vertex G)} (M : Matching S) :
    ∑ v ∈ S, v.2 = 0 := by
  rw [← M.cover]
  change (∑ v ∈ M.edges.biUnion (fun E ↦ E), v.2) = 0
  rw [Finset.sum_biUnion M.disjoint]
  apply Finset.sum_eq_zero
  intro E hE
  obtain ⟨a,b,c,hzero,rfl⟩ := M.valid E hE
  simpa [add_assoc] using hzero

theorem ne_neg_of_odd (hodd : Odd (Fintype.card G)) {x : G} (hx : x ≠ 0) : x ≠ -x := by
  have hc : (Nat.card G).Coprime 2 := by
    rw [Nat.card_eq_fintype_card]
    exact hodd.coprime_two_right
  have hi : Function.Injective (fun x : G ↦ x+x) := by
    simpa only [two_nsmul] using hc.nsmul_right_bijective.injective
  intro he
  apply hx
  apply hi
  calc
    x+x = x+(-x) := congrArg (fun y ↦ x+y) he
    _ = 0+0 := by simp

theorem paired_coordinate_sum_zero (hodd : Odd (Fintype.card G))
    (T : Finset (Vertex G)) (hpair : ∀ v ∈ T, (v.1,-v.2) ∈ T) :
    ∑ v ∈ T, v.2 = 0 := by
  exact Finset.sum_involution (fun v _ ↦ (v.1,-v.2))
    (fun v _ ↦ by simp)
    (fun v _ hne heq ↦ (ne_neg_of_odd hodd hne) (congrArg Prod.snd heq).symm)
    hpair (fun v _ ↦ by simp)

/-- paired cover construction's output sum is a consequence of the native finite matching and
pairing. No ring structure or extra sum hypothesis is supplied. -/
theorem SixRootOutput.output_coordinate_sum (hodd : Odd (Fintype.card G))
    {Q : Vertex G → Prop} {O X : Finset (Vertex G)} {F : Finset G}
    (A : SixRootOutput Q O X F) :
    (∑ v ∈ A.output, v.2) = ∑ v ∈ O ∪ X, v.2 := by
  have hdis : Disjoint (O ∪ X) A.added := by
    apply Finset.disjoint_left.mpr
    intro v hvRoots hvAdded
    exact Finset.disjoint_left.mp A.roots_fresh
      (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v,hvAdded,rfl⟩))
      (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v,hvRoots,rfl⟩))
  have hmatch := A.matching.coordinate_sum_zero
  have hadded := paired_coordinate_sum_zero hodd A.added A.added_paired
  have hOut : A.output ⊆ (O ∪ X) ∪ A.added :=
    A.output_subset.trans Finset.subset_union_right
  have hsplit := Finset.sum_sdiff (f := fun v : Vertex G ↦ v.2) hOut
  have hunion := Finset.sum_union (f := fun v : Vertex G ↦ v.2) hdis
  rw [hmatch,zero_add] at hsplit
  rw [hadded,add_zero] at hunion
  exact hsplit.trans hunion

/-- The written real C_Q controls every later six-root query, and every
added vertex is in the original signed sample carried by the same ω. -/
theorem sixRoot_of_real_budget
    (q : ℝ) (ω : FullSample G)
    (hsupply : SixRootSupplier (ReservoirVertex ω true) (flowBudget (tau q) (Fintype.card G)))
    (O X : Finset (Vertex G)) (F : Finset G)
    (hO : OnePerPart O) (hX : OnePerPart X) (hdis : Disjoint O X)
    (hOn : ∀ v ∈ O, v.2 ≠ 0) (hXn : ∀ v ∈ X, v.2 ≠ 0)
    (hF : (F.card : ℝ) ≤ (tau q)^9*(Fintype.card G : ℝ)/10^6) :
    ∃ A : SixRootOutput (ReservoirVertex ω true) O X F,
      ∀ v ∈ A.added, originalSigned v.1 (originalProcess ω) v.2 := by
  have htau : 0 ≤ tau q := by unfold tau p rho eta; positivity
  have hint : F.card ≤ flowBudget (tau q) (Fintype.card G) :=
    (le_flowBudget_iff (tau q) (Fintype.card G) F.card htau).2 hF
  obtain ⟨A⟩ := hsupply O X F hO hX hdis hOn hXn hint
  exact ⟨A,fun v hv ↦ ReservoirVertex.originalSigned ω true v (A.added_Q v hv)⟩

/-- One original-model augmentation gives the literal real-budget selector
and paired-cover interfaces. Every occupied P/Q vertex belongs to the same
original signed sample. The entire statement is purely additive. -/
theorem original_selectors_sixRoots_and_covers_witness_real
    (q : ℝ) (s : OriginalSample G)
    (hgood : OriginalAdmitsSelectorsSixRootsAndCovers
      (selectorExternalBudget (p q) (Fintype.card G))
      (flowBudget (tau q) (Fintype.card G)) s) :
    ∃ ω : FullSample G, originalProcess ω = s ∧
      (∀ (part : Fin 3) (R : Finset (Finset (Vertex G))),
        R.Nonempty → R.card ≤ 100 → (∀ T ∈ R, LegalPair part T) →
        ∀ F : Finset G, (F.card : ℝ) ≤ (p q)^4*(Fintype.card G : ℝ)/10^12 →
          ∃ T : Selector (ReservoirVertex ω false) R,
            T.interior.card ≤ 18*R.card-2 ∧ Disjoint (support T.interior) F ∧
            (support (T.interior ∪ R.biUnion id)).card ≤ 3996 ∧
            (∀ v ∈ T.interior, originalSigned v.1 s v.2)) ∧
      SixRootSupplier (ReservoirVertex ω true) (flowBudget (tau q) (Fintype.card G)) ∧
      (∀ S : Finset (Vertex G), Balanced S → (∀ v ∈ S, v.2 ≠ 0) →
        (∑ v ∈ S, v.2=0) → ∀ U : Finset G,
        2*(U.card : ℝ)+20*(S.card : ℝ) ≤ (tau q)^9*(Fintype.card G : ℝ)/10^6 →
        ∃ C : PairedCover (ReservoirVertex ω true) S U,
          ∀ v ∈ C.added, originalSigned v.1 s v.2) := by
  obtain ⟨ω,hω,hselectors,hflow,hcovers⟩ := hgood
  refine ⟨ω,hω,?_,hflow,?_⟩
  · intro part R hne hk hlegal F hF
    have hint : F.card ≤ selectorExternalBudget (p q) (Fintype.card G) :=
      (le_selectorExternalBudget_iff (p q) (Fintype.card G) F.card).2 hF
    obtain ⟨T,hsize,havoid,hsupport⟩ := hselectors part R hne hk hlegal F hint
    refine ⟨T,hsize,havoid,hsupport,?_⟩
    intro v hv
    rw [← hω]
    exact ReservoirVertex.originalSigned ω false v (T.inside v hv)
  · intro S hb hnz hsum U hbudget
    have htau : 0 ≤ tau q := by unfold tau p rho eta; positivity
    have hint : 2*U.card+20*S.card ≤ flowBudget (tau q) (Fintype.card G) := by
      apply (le_flowBudget_iff (tau q) (Fintype.card G) _ htau).2
      simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hbudget
    obtain ⟨C⟩ := hcovers S hb hnz hsum U hint
    refine ⟨C,?_⟩
    intro v hv
    rw [← hω]
    exact ReservoirVertex.originalSigned ω true v (C.added_Q v hv)

end
end EndpointFlow.AbelianTransport
