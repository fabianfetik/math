import CorralFormalization.EndpointProof.Factor.OrdinaryFragments.Counts
import CorralFormalization.EndpointProof.Probability.LayeredSample.PairSupply

/-!
# Actual endpoint and colour choices for fragment donors

The supply hypotheses count the actual pair candidates from the raw last
layer and the original special colour bank. The proof removes the actual
bad endpoints and colours, then greedily chooses distinct original donors
and distinct joining colours. It does not identify list length with the
number of distinct choices.
-/

open scoped Classical
namespace EndpointFactor.OrdinaryFragments
noncomputable section
universe u v
variable {G : Type u} [AddCommGroup G] [DecidableEq G]

/-- Original physical pair candidates for the edge `a → g`. -/
def rawDonors (g : G) (R C : Finset G) : Finset G := R.filter (fun a => g-a ∈ C)

/-- Actual original primary ends outside prescribed terminals, whose
joining colour belongs to the original bank. -/
def availableDonors (g : G) (R C Z Y H : Finset G) : Finset G :=
  (rawDonors g R C).filter (fun a => a ∈ Z ∧ a ∉ Y ∧ g-a ∈ H)

@[simp] theorem mem_availableDonors (g a : G) (R C Z Y H : Finset G) :
    a ∈ availableDonors g R C Z Y H ↔
      a ∈ R ∧ g-a ∈ C ∧ a ∈ Z ∧ a ∉ Y ∧ g-a ∈ H := by
  simp [availableDonors, rawDonors, and_assoc]

/-- Exact static losses before any donors have been selected.  Removing
missing colours costs at most their actual cardinality because `a ↦ g-a`
is injective. -/
theorem availableDonors_card (g : G) (R C Z Y H : Finset G) :
    (rawDonors g R C).card ≤ (availableDonors g R C Z Y H).card +
      (R \ Z).card + Y.card + (C \ H).card := by
  let raw := rawDonors g R C
  let available := availableDonors g R C Z Y H
  let badColor := raw.filter (fun a => g-a ∉ H)
  have hinj : Function.Injective (fun a : G => g-a) := by
    intro a b hab
    exact sub_right_inj.mp hab
  have hcol : badColor.image (fun a => g-a) ⊆ C \ H := by
    intro c hc
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hc
    have har := (Finset.mem_filter.mp ha).1
    have haC : g-a ∈ C := (Finset.mem_filter.mp har).2
    exact Finset.mem_sdiff.mpr ⟨haC, (Finset.mem_filter.mp ha).2⟩
  have hcolcard : badColor.card ≤ (C \ H).card := by
    have h := Finset.card_le_card hcol
    rw [Finset.card_image_of_injective _ hinj] at h
    exact h
  have hbad : raw \ available ⊆ ((R \ Z) ∪ Y) ∪ badColor := by
    intro a ha
    have har := (Finset.mem_sdiff.mp ha).1
    have hav := (Finset.mem_sdiff.mp ha).2
    have haR : a ∈ R := (Finset.mem_filter.mp har).1
    by_cases haZ : a ∈ Z
    · by_cases haY : a ∈ Y
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ haY)
      · apply Finset.mem_union_right
        apply Finset.mem_filter.mpr
        refine ⟨har, ?_⟩
        intro haH
        exact hav (Finset.mem_filter.mpr ⟨har, haZ, haY, haH⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨haR, haZ⟩))
  have hb : (raw \ available).card ≤ (R \ Z).card + Y.card + (C \ H).card := by
    calc
      (raw \ available).card ≤ (((R \ Z) ∪ Y) ∪ badColor).card := Finset.card_le_card hbad
      _ ≤ ((R \ Z) ∪ Y).card + badColor.card := Finset.card_union_le _ _
      _ ≤ ((R \ Z).card + Y.card) + (C \ H).card :=
        Nat.add_le_add (Finset.card_union_le _ _) hcolcard
  have hsub : available ⊆ raw := Finset.filter_subset _ _
  have hpart := Finset.card_sdiff_add_card_eq_card hsub
  change raw.card ≤ available.card + (R \ Z).card + Y.card + (C \ H).card
  omega

private theorem injOn_update {I : Type v} [DecidableEq I]
    (s : Finset I) (e : I) (he : e ∉ s) (f : I → G)
    (hf : Set.InjOn f (s : Set I)) (a : G) (ha : a ∉ s.image f) :
    Set.InjOn (Function.update f e a) (↑(insert e s) : Set I) := by
  intro i hi j hj hij
  by_cases hie : i = e
  · subst i
    by_cases hje : j = e
    · exact hje.symm
    · have hjs : j ∈ s := (Finset.mem_insert.mp hj).resolve_left hje
      have hval : a = f j := by simpa [Function.update_of_ne hje] using hij
      exact False.elim (ha (Finset.mem_image.mpr ⟨j, hjs, hval.symm⟩))
  · have his : i ∈ s := (Finset.mem_insert.mp hi).resolve_left hie
    by_cases hje : j = e
    · subst j
      have hval : f i = a := by simpa [Function.update_of_ne hie] using hij
      exact False.elim (ha (Finset.mem_image.mpr ⟨i, his, hval⟩))
    · have hjs : j ∈ s := (Finset.mem_insert.mp hj).resolve_left hje
      exact hf his hjs (by simpa [Function.update_of_ne hie, Function.update_of_ne hje] using hij)

/-- Finite greedy choice with two independently protected actual
inventories: donor endpoints and directed joining colours. -/
theorem choose_distinct_donors {I : Type v} [DecidableEq I]
    (s : Finset I) (g : I → G) (candidate : I → Finset G)
    (hsupply : ∀ i ∈ s, 2*s.card < (candidate i).card) :
    ∃ a : I → G, (∀ i ∈ s, a i ∈ candidate i) ∧
      Set.InjOn a (s : Set I) ∧
      Set.InjOn (fun i => g i-a i) (s : Set I) := by
  revert hsupply
  induction s using Finset.induction with
  | empty =>
    intro _
    exact ⟨fun _ => 0, by simp, by simp, by simp⟩
  | @insert e s he ih =>
    intro hsupply
    have hs : ∀ i ∈ s, 2*s.card < (candidate i).card := by
      intro i hi
      have h := hsupply i (Finset.mem_insert_of_mem hi)
      rw [Finset.card_insert_of_notMem he] at h
      omega
    obtain ⟨f, hf, hfi, hfci⟩ := ih hs
    let usedD := s.image f
    let usedC := s.image (fun i => g i-f i)
    let blocked := usedD ∪ usedC.image (fun c => g e-c)
    have hb : blocked.card ≤ 2*s.card := by
      calc
        blocked.card ≤ usedD.card + (usedC.image (fun c => g e-c)).card := Finset.card_union_le _ _
        _ ≤ s.card + usedC.card := Nat.add_le_add Finset.card_image_le Finset.card_image_le
        _ ≤ s.card+s.card := Nat.add_le_add_left Finset.card_image_le _
        _ = 2*s.card := by omega
    have hlt : blocked.card < (candidate e).card := by
      have h := hsupply e (Finset.mem_insert_self _ _)
      rw [Finset.card_insert_of_notMem he] at h
      omega
    obtain ⟨a, ha, hanot⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    have haD : a ∉ usedD := fun h => hanot (Finset.mem_union_left _ h)
    have haC : g e-a ∉ usedC := by
      intro h
      apply hanot
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨g e-a, h, ?_⟩
      abel
    refine ⟨Function.update f e a, ?_, injOn_update s e he f hfi a haD, ?_⟩
    · intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · simpa using ha
      · have hine : i ≠ e := by intro h; exact he (h ▸ hi)
        simpa [Function.update_of_ne hine] using hf i hi
    · have heq : (fun i => g i-Function.update f e a i) =
          Function.update (fun i => g i-f i) e (g e-a) := by
        funext i
        by_cases hi : i = e
        · subst i; simp
        · simp [Function.update_of_ne hi]
      rw [heq]
      exact injOn_update s e he _ hfci _ haC

/-- Paper-shaped donor selection.  The hypothesis uses the original pair
candidate count and the actual current losses.  All chosen donors lie in
`Z`, avoid `Y`, and use distinct actual colours of `H`. -/
theorem choose_original_donors {I : Type v} [Fintype I] [DecidableEq I]
    (g : I → G) (R C Z Y H : Finset G)
    (hsupply : ∀ i, (R \ Z).card + Y.card + (C \ H).card +
      2*Fintype.card I < (rawDonors (g i) R C).card) :
    ∃ a : I → G, (∀ i, a i ∈ Z ∧ a i ∉ Y ∧ g i-a i ∈ H) ∧
      Function.Injective a ∧ Function.Injective (fun i => g i-a i) := by
  have havail : ∀ i, 2*Fintype.card I < (availableDonors (g i) R C Z Y H).card := by
    intro i
    have h := availableDonors_card (g i) R C Z Y H
    have hs := hsupply i
    omega
  obtain ⟨a, ha, hinj, hcinj⟩ := choose_distinct_donors Finset.univ g
    (fun i => availableDonors (g i) R C Z Y H) (by simpa using havail)
  refine ⟨a, ?_, ?_, ?_⟩
  · intro i
    have h := (mem_availableDonors _ _ _ _ _ _ _).mp (ha i (Finset.mem_univ _))
    exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  · intro i j h
    exact hinj (Finset.mem_univ _) (Finset.mem_univ _) h
  · intro i j h
    exact hcinj (Finset.mem_univ _) (Finset.mem_univ _) h

/-- The original last layer can lose only its actual discrepancy from the
new last layer and the new last-layer points outside `Z₀`. -/
theorem raw_endpoint_loss (R E Z : Finset G) :
    (R \ Z).card ≤ (R \ E).card + (E \ Z).card := by
  have hsub : R \ Z ⊆ (R \ E) ∪ (E \ Z) := by
    intro a ha
    by_cases he : a ∈ E
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨he, (Finset.mem_sdiff.mp ha).2⟩)
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp ha).1, he⟩)
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

/-- The exact coefficient `3(h+w)` in §6.7 pays the static loss `h`
and both previously chosen inventories. -/
theorem choose_original_donors_of_explicit_losses {I : Type v} [Fintype I] [DecidableEq I]
    (g : I → G) (R C Z Y H₀ : Finset G) (B d s K h H : ℕ)
    (hI : Fintype.card I = H) (hhH : h ≤ H)
    (hR : (R \ Z).card ≤ B+h) (hY : Y.card ≤ K)
    (hC : (C \ H₀).card ≤ d+s+K)
    (hsupply : ∀ i, B+d+s+2*K+3*H < (rawDonors (g i) R C).card) :
    ∃ a : I → G, (∀ i, a i ∈ Z ∧ a i ∉ Y ∧ g i-a i ∈ H₀) ∧
      Function.Injective a ∧ Function.Injective (fun i => g i-a i) := by
  apply choose_original_donors g R C Z Y H₀
  intro i
  have hi := hsupply i
  rw [hI]
  omega

section CommonSample
open EndpointLayeredSample
variable [Fintype G]

/-- The already-proved common pair event really supplies the donor sets
used above. Its exclusion of colour zero only strengthens this bound. -/
theorem pairSupply_rawDonors_lower {m : ℕ} {d : Densities m} {s : Sample G m}
    (hpair : PairSupplyEvent d s) (g : G) :
    d.q^2*(Fintype.card G : ℝ)/2 ≤
      ((rawDonors g (vertexSet s (lastVertex m)) (colourSet s (specialColour m))).card : ℝ) := by
  classical
  have hsub : pairSupplySet s g ⊆
      rawDonors g (vertexSet s (lastVertex m)) (colourSet s (specialColour m)) := by
    intro a ha
    simp only [pairSupplySet, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    rcases ha with ⟨hv, hc, _⟩
    simp [rawDonors, vertexSet, colourSet, hv, hc]
  exact (hpair g).trans (by exact_mod_cast Finset.card_le_card hsub)

/-- An actual same-sample pair event and its actual loss budget choose all
donors and joining colours. No new reservoir or probabilistic event is
assumed here. -/
theorem choose_original_donors_of_pairSupply {m : ℕ} {d : Densities m}
    {s : Sample G m} (hpair : PairSupplyEvent d s)
    {I : Type v} [Fintype I] [DecidableEq I] (g : I → G) (Z Y H : Finset G)
    (hbudget : (((vertexSet s (lastVertex m) \ Z).card + Y.card +
      (colourSet s (specialColour m) \ H).card + 2*Fintype.card I : ℕ) : ℝ) <
        d.q^2*(Fintype.card G : ℝ)/2) :
    ∃ a : I → G, (∀ i, a i ∈ Z ∧ a i ∉ Y ∧ g i-a i ∈ H) ∧
      Function.Injective a ∧ Function.Injective (fun i => g i-a i) := by
  apply choose_original_donors g (vertexSet s (lastVertex m))
    (colourSet s (specialColour m)) Z Y H
  intro i
  have hi := hbudget.trans_le (pairSupply_rawDonors_lower hpair (g i))
  exact_mod_cast hi

end CommonSample
end
end EndpointFactor.OrdinaryFragments
