import CorralFormalization.EndpointProof.Matching.Fractional.RoundingAKSSource

/-!
# A source-visible Pippenger input and the proved local rounding reduction

The external proposition below is the three-uniform specialization of
Alon--Yuster, *On a hypergraph matching problem*, Theorem 1.1, printed p. 2:
https://web.math.princeton.edu/~nalon/PDFS/ayhyper2.pdf

The source defines hypergraphs as families of distinct finite vertex sets.
`maximumDegree` is the actual maximum, and the codegree inequality is strict.
The source's strict maximum-codegree condition excludes a zero maximum
degree.  For the empty vertex type the desired conclusion is trivial, so we
allow that case separately.  This prevents the pairwise formulation from
being vacuous for an isolated singleton.
No matching assertion is registered as an axiom.  The source proposition is
an explicit argument of theorems using it.

The ordinary-transition edge-retention argument can be replaced by the existing proved
three-column rounding theorem.  Its error is less than three at each vertex,
and it works separately on each realised later target.  It needs neither
independent raw roles nor an additional uniform probability event.
-/

open scoped Classical BigOperators

namespace EndpointTransitions

noncomputable section

open EndpointMatching.Fractional.Rounding

universe u v

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E]

def maximumDegree (H : Finset (Finset V)) : ℕ :=
  Finset.univ.sup (degree id H)

def codegree (H : Finset (Finset V)) (v w : V) : ℕ :=
  (H.filter (fun e => v ∈ e ∧ w ∈ e)).card

/-- Literal three-uniform instance of the external Theorem 1.1, for one
chosen accuracy and one chosen source constant. -/
def PippengerInput (V : Type u) [Fintype V] (μ ε : ℝ) : Prop :=
  ∀ H : Finset (Finset V), (∀ e ∈ H, e.card = 3) →
    (0 < maximumDegree H ∨ IsEmpty V) →
    (∀ v, (1-μ)*(maximumDegree H : ℝ) ≤ degree id H v) →
    (∀ v w, v ≠ w → (codegree H v w : ℝ) < μ*(maximumDegree H : ℝ)) →
    ∃ M : Finset (Finset V), M ⊆ H ∧ IsMatching id M ∧
      (uncovered id M).card ≤ ε*(Fintype.card V : ℝ)

/-- Uniform external theorem, specialized only to uniformity three. -/
def PippengerTheorem : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ μ : ℝ, 0 < μ ∧
    ∀ (V : Type u) [Fintype V], PippengerInput V μ ε

theorem degree_le_maximumDegree (H : Finset (Finset V)) (v : V) :
    degree id H v ≤ maximumDegree H := Finset.le_sup (Finset.mem_univ v)

theorem maximumDegree_le {H : Finset (Finset V)} {d : ℕ}
    (h : ∀ v, degree id H v ≤ d) : maximumDegree H ≤ d :=
  Finset.sup_le (fun v _ => h v)

/-- Linearity of an actual set family gives codegree at most one. -/
theorem codegree_le_one (H : Finset (Finset V))
    (hlinear : (H : Set (Finset V)).Pairwise (fun e f => (e ∩ f).card ≤ 1))
    (v w : V) (hvw : v ≠ w) : codegree H v w ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro e he f hf
  by_contra hef
  obtain ⟨heH, hev, hew⟩ := Finset.mem_filter.mp he
  obtain ⟨hfH, hfv, hfw⟩ := Finset.mem_filter.mp hf
  exact hvw (Finset.card_le_one.mp (hlinear heH hfH hef)
    v (Finset.mem_inter.mpr ⟨hev,hfv⟩) w (Finset.mem_inter.mpr ⟨hew,hfw⟩))

/-- A smaller positive `μ` has stronger degree and codegree hypotheses.
This proves the freedom to choose `μ_t ≤ 1/2` used in the ordinary transition lemma. -/
theorem PippengerInput.mono_mu {μ μ' ε : ℝ} (h : PippengerInput V μ ε)
    (hμ : 0 < μ') (hsmall : μ' ≤ μ) : PippengerInput V μ' ε := by
  intro H hu hnondeg hd hc
  apply h H hu hnondeg
  · intro v
    apply le_trans _ (hd v)
    exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
  · intro v w hvw
    exact (hc v w hvw).trans_le
      (mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg _))

theorem PippengerTheorem.choose_mu (h : PippengerTheorem.{u}) (ε : ℝ) (hε : 0 < ε) :
    ∃ μ : ℝ, 0 < μ ∧ μ ≤ 1/2 ∧
      ∀ (V : Type u) [Fintype V], PippengerInput V μ ε := by
  obtain ⟨μ, hμ, hs⟩ := h ε hε
  refine ⟨min μ (1/2), lt_min hμ (by norm_num), min_le_right _ _, ?_⟩
  intro V _
  exact (hs V).mono_mu (lt_min hμ (by norm_num)) (min_le_left _ _)

/-- Reindex the literal finite-set source theorem to arbitrary indexed
linear three-edges. Distinct indexed edges are proved to have distinct images. -/
theorem matching_of_degree_window (edges : E → Finset V)
    (S : Finset E) (huniform : ∀ e ∈ S, (edges e).card = 3)
    (hlinear : (S : Set E).Pairwise (fun e f => ((edges e) ∩ (edges f)).card ≤ 1))
    (μ ε D δ : ℝ) (hμ : 0 < μ) (hμone : μ ≤ 1)
    (hδ : 0 ≤ δ) (hwindow : 2*δ ≤ μ*(D-δ)) (hcodegree : 1 < μ*(D-δ))
    (hdegree : ∀ v, D-δ ≤ (degree edges S v : ℝ) ∧ (degree edges S v : ℝ) ≤ D+δ)
    (hsource : PippengerInput V μ ε) :
    ∃ M : Finset E, M ⊆ S ∧ IsMatching edges M ∧
      (uncovered edges M).card ≤ ε*(Fintype.card V : ℝ) := by
  let H : Finset (Finset V) := S.image edges
  have hinj := linear_three_uniform_injOn edges S huniform hlinear
  have huH : ∀ a ∈ H, a.card = 3 := by
    intro a ha
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
    exact huniform e he
  have hlH : (H : Set (Finset V)).Pairwise (fun a b => (a ∩ b).card ≤ 1) := by
    intro a ha b hb hab
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hb
    exact hlinear he hf (fun hef => hab (congrArg edges hef))
  have hdH (v : V) : degree id H v = degree edges S v := by
    unfold degree H
    rw [Finset.filter_image]
    exact Finset.card_image_of_injOn (hinj.mono (Finset.filter_subset _ _))
  have hmax_upper : (maximumDegree H : ℝ) ≤ D+δ := by
    by_cases hV : Nonempty V
    · letI := hV
      obtain ⟨w, hw, hmax⟩ := Finset.exists_mem_eq_sup Finset.univ
        (Finset.univ_nonempty (α := V)) (degree id H)
      rw [maximumDegree, hmax, hdH]
      exact (hdegree w).2
    · haveI : IsEmpty V := not_nonempty_iff.mp hV
      have hz : maximumDegree H = 0 := by simp [maximumDegree]
      rw [hz, Nat.cast_zero]
      have hp : 0 < D-δ := by nlinarith
      linarith
  have hregular : ∀ v, (1-μ)*(maximumDegree H : ℝ) ≤ degree id H v := by
    intro v
    have hmax_lower : D-δ ≤ (maximumDegree H : ℝ) := by
      calc
        D-δ ≤ degree edges S v := (hdegree v).1
        _ = degree id H v := by rw [hdH]
        _ ≤ maximumDegree H := by exact_mod_cast degree_le_maximumDegree H v
    have hgap : (maximumDegree H : ℝ) - (degree id H v : ℝ) ≤ 2*δ := by
      rw [hdH]
      linarith [(hdegree v).1]
    have hmul : μ*(D-δ) ≤ μ*(maximumDegree H : ℝ) :=
      mul_le_mul_of_nonneg_left hmax_lower hμ.le
    nlinarith
  have hcH : ∀ v w, v ≠ w → (codegree H v w : ℝ) < μ*(maximumDegree H : ℝ) := by
    intro v w hvw
    have hmax_lower : D-δ ≤ (maximumDegree H : ℝ) := by
      calc
        D-δ ≤ degree edges S v := (hdegree v).1
        _ = degree id H v := by rw [hdH]
        _ ≤ maximumDegree H := by exact_mod_cast degree_le_maximumDegree H v
    calc
      (codegree H v w : ℝ) ≤ 1 := by exact_mod_cast codegree_le_one H hlH v w hvw
      _ < μ*(D-δ) := hcodegree
      _ ≤ μ*(maximumDegree H : ℝ) := mul_le_mul_of_nonneg_left hmax_lower hμ.le
  have hnondeg : 0 < maximumDegree H ∨ IsEmpty V := by
    by_cases hV : Nonempty V
    · obtain ⟨v⟩ := hV
      have hD : 0 < D-δ := by nlinarith
      have hmax : (0 : ℝ) < (maximumDegree H : ℝ) := by
        have hv : D-δ ≤ (degree id H v : ℝ) := by simpa only [hdH] using (hdegree v).1
        have hvmax : (degree id H v : ℝ) ≤ (maximumDegree H : ℝ) := by
          exact_mod_cast degree_le_maximumDegree H v
        linarith
      exact Or.inl (by exact_mod_cast hmax)
    · exact Or.inr (not_nonempty_iff.mp hV)
  obtain ⟨P, hPH, hP, hrest⟩ := hsource H huH hnondeg hregular hcH
  let M : Finset E := S.filter (fun e => edges e ∈ P)
  have hMS : M ⊆ S := Finset.filter_subset _ _
  have himage : M.image edges = P := by
    ext a
    constructor
    · intro ha
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
      exact (Finset.mem_filter.mp he).2
    · intro ha
      obtain ⟨e, he, hef⟩ := Finset.mem_image.mp (hPH ha)
      exact Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨he, by simpa [hef] using ha⟩, hef⟩
  have hM : IsMatching edges M := by
    intro e he f hf hne
    exact hP (Finset.mem_filter.mp he).2 (Finset.mem_filter.mp hf).2
      (fun hef => hne (hinj (hMS he) (hMS hf) hef))
  have hcover : M.biUnion edges = P.biUnion id := by
    rw [← himage, Finset.image_biUnion]
    rfl
  refine ⟨M, hMS, hM, ?_⟩
  simpa only [uncovered, hcover] using hrest

/-- The local replacement for probabilistic edge thinning.  The weighted
degree is allowed an error `b`; rounding adds less than three. -/
theorem weighted_near_perfect_matching (edges : E → Finset V)
    (huniform : ∀ e, (edges e).card = 3) (hlinear : IsLinear edges)
    (w : E → ℝ) (hw : ∀ e, 0 ≤ w e ∧ w e ≤ 1)
    (μ ε D b : ℝ) (hμ : 0 < μ) (hμone : μ ≤ 1)
    (hb : 0 ≤ b) (hwindow : 2*(b+3) ≤ μ*(D-(b+3)))
    (hcodegree : 1 < μ*(D-(b+3)))
    (hload : ∀ v, |(∑ e, if v ∈ edges e then w e else 0)-D| ≤ b)
    (hsource : PippengerInput V μ ε) :
    ∃ M : Finset E, IsMatching edges M ∧ (∀ e ∈ M, 0 < w e) ∧
      (uncovered edges M).card ≤ ε*(Fintype.card V : ℝ) := by
  let A : V → E → Prop := fun v e => v ∈ edges e
  have hcol : ∀ e, (columnSupport A e).card ≤ 3 := by
    intro e
    simpa [A, columnSupport] using (huniform e).le
  obtain ⟨S, hsupp, herr⟩ := exists_selection A 3 (by decide) hcol w hw
  have hdegrees : ∀ v, D-(b+3) ≤ (degree edges S v : ℝ) ∧
      (degree edges S v : ℝ) ≤ D+(b+3) := by
    intro v
    have he' : |(degree edges S v : ℝ)-(∑ e, if v ∈ edges e then w e else 0)| < 3 := by
      have hd : (rowSupport A S v).card = degree edges S v := by
        congr 1
        ext e
        simp [rowSupport, degree, A]
      have hs : rowSum A w v = ∑ e, if v ∈ edges e then w e else 0 := by
        unfold rowSum
        apply Finset.sum_congr rfl
        intro e _
        by_cases hv : v ∈ edges e <;> simp [A, hv]
      simpa only [hd, hs, Nat.cast_ofNat] using herr v
    have he := abs_lt.mp he'
    have hl := abs_le.mp (hload v)
    constructor <;> linarith
  obtain ⟨M, hMS, hM, hrest⟩ := matching_of_degree_window edges S
    (fun e _ => huniform e) (fun e _ f _ hne => hlinear e f hne)
    μ ε D (b+3) hμ hμone (by linarith) hwindow hcodegree hdegrees hsource
  exact ⟨M, hM, fun e he => hsupp e (hMS he), hrest⟩

/-- Restricting to actual surviving vertices may leave shorter zero-weight
edges.  Only positive-weight edges need to be three-uniform; rounding never
selects the other indices. -/
theorem weighted_supported_near_perfect_matching (edges : E → Finset V)
    (hcard : ∀ e, (edges e).card ≤ 3)
    (w : E → ℝ) (hw : ∀ e, 0 ≤ w e ∧ w e ≤ 1)
    (huniform : ∀ e, 0 < w e → (edges e).card = 3) (hlinear : IsLinear edges)
    (μ ε D b : ℝ) (hμ : 0 < μ) (hμone : μ ≤ 1)
    (hb : 0 ≤ b) (hwindow : 2*(b+3) ≤ μ*(D-(b+3)))
    (hcodegree : 1 < μ*(D-(b+3)))
    (hload : ∀ v, |(∑ e, if v ∈ edges e then w e else 0)-D| ≤ b)
    (hsource : PippengerInput V μ ε) :
    ∃ M : Finset E, IsMatching edges M ∧ (∀ e ∈ M, 0 < w e) ∧
      (uncovered edges M).card ≤ ε*(Fintype.card V : ℝ) := by
  let A : V → E → Prop := fun v e => v ∈ edges e
  have hcol : ∀ e, (columnSupport A e).card ≤ 3 := by
    intro e
    simpa [A, columnSupport] using hcard e
  obtain ⟨S, hsupp, herr⟩ := exists_selection A 3 (by decide) hcol w hw
  have hdegrees : ∀ v, D-(b+3) ≤ (degree edges S v : ℝ) ∧
      (degree edges S v : ℝ) ≤ D+(b+3) := by
    intro v
    have hd : (rowSupport A S v).card = degree edges S v := by
      congr 1
      ext e
      simp [rowSupport, A]
    have hs : rowSum A w v = ∑ e, if v ∈ edges e then w e else 0 := by
      unfold rowSum
      apply Finset.sum_congr rfl
      intro e _
      by_cases hv : v ∈ edges e <;> simp [A, hv]
    have he' := herr v
    rw [hd,hs] at he'
    norm_num only [Nat.cast_ofNat] at he'
    have he := abs_lt.mp he'
    have hl := abs_le.mp (hload v)
    constructor <;> linarith
  obtain ⟨M, hMS, hM, hrest⟩ := matching_of_degree_window edges S
    (fun e he => huniform e (hsupp e he)) (fun e _ f _ hne => hlinear e f hne)
    μ ε D (b+3) hμ hμone (by linarith) hwindow hcodegree hdegrees hsource
  exact ⟨M, hM, fun e he => hsupp e (hMS he), hrest⟩

end
end EndpointTransitions
