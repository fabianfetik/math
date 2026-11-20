import CorralFormalization.EndpointProof.Transitions.ActualWeights
import CorralFormalization.EndpointProof.Transitions.RestrictionMatching

/-!
# Ordinary near-perfect transitions

The only external matching theorem is the literal finite-set Pippenger
proposition. All Fourier, one-sided loss, explicit edge weight, exceptional
inventory, actual incidence, rounding, and uncovered-cardinality steps are
proved.  The local probabilistic retention step is replaced by the existing
deterministic column-three rounding theorem, with the stronger order
threshold `η n ≥ 3`. No independence between raw roles is assumed.
-/

open scoped Classical BigOperators

namespace EndpointTransitions

noncomputable section

open EndpointFlow.AbelianTransport EndpointMatching.Fractional.Rounding

universe u

/-- The manuscript's illustrative `n ≥ 10η⁻⁴` Hoeffding threshold also
pays the deterministic rounding threshold used in this proof. -/
theorem manuscript_order_pays_rounding (η n : ℝ) (hη : 0 < η) (hηone : η ≤ 1)
    (hn : 0 ≤ n) (horder : 10/η^4 ≤ n) : 3 ≤ η*n := by
  have hηsq : η^2 ≤ η := by nlinarith
  have hηfour' := pow_le_pow_left₀ (sq_nonneg η) hηsq 2
  have hηfour : η^4 ≤ η := by nlinarith [hηfour']
  have hmult := mul_le_mul_of_nonneg_right hηfour hn
  have hten := (div_le_iff₀ (pow_pos hη 4)).mp horder
  nlinarith

/-- The numerical Pippenger window after at most `9η²n` vertex deletions,
weighted-degree error `14ηn`, and rounding error less than three. -/
theorem ordinary_degree_window (q η μ n B : ℝ)
    (hη : 0 < η) (hηone : η ≤ 1) (hμ : 0 < μ) (hμhalf : μ ≤ 1/2)
    (hn : 0 ≤ n) (hηmu : η ≤ q^2*μ/1000)
    (hB : B ≤ 9*η^2*n) (hround : 3 ≤ η*n) (hlarge : 8 ≤ μ*q^2*n) :
    2*(14*η*n+B+3) ≤ μ*(q^2*n/2-(14*η*n+B+3)) ∧
    1 < μ*(q^2*n/2-(14*η*n+B+3)) := by
  have hηsq : η^2*n ≤ η*n := mul_le_mul_of_nonneg_right (by nlinarith) hn
  have hδ : 14*η*n+B+3 ≤ 24*η*n := by linarith
  have hμq := mul_le_mul_of_nonneg_left hμhalf (sq_nonneg q)
  have hηq : η ≤ q^2/2000 := by nlinarith
  have hηn := mul_le_mul_of_nonneg_right hηq hn
  have hlower : q^2*n/4 ≤ q^2*n/2-(14*η*n+B+3) := by
    nlinarith [mul_nonneg (sq_nonneg q) hn]
  have hsmall := mul_le_mul_of_nonneg_right hηmu hn
  have hleft : 2*(14*η*n+B+3) ≤ μ*(q^2*n/4) := by
    nlinarith [mul_nonneg (mul_nonneg hμ.le (sq_nonneg q)) hn]
  have hmul := mul_le_mul_of_nonneg_left hlower hμ.le
  exact ⟨hleft.trans hmul, lt_of_lt_of_le (by nlinarith : 1 < μ*(q^2*n/4)) hmul⟩

variable {G : Type u} [AddCommGroup G] [Fintype G]

/-- Transfer the indexed disjoint actual edges to the existing additive
`Matching` structure, with exactly the same covered vertices. -/
def matchingOfIndices (M : Finset (G × G)) (hM : IsMatching additiveEdge M) :
    Matching (M.biUnion additiveEdge) where
  edges := M.image additiveEdge
  valid := by
    intro E hE
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hE
    exact additiveEdge_valid e
  disjoint := by
    intro E hE F hF hEF
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hE
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hF
    exact hM he hf (fun hef => hEF (congrArg additiveEdge hef))
  cover := by
    ext v
    simp only [Finset.mem_biUnion,Finset.mem_image]
    aesop

theorem matchingOfIndices_card (M : Finset (G × G)) (hM : IsMatching additiveEdge M) :
    (matchingOfIndices M hM).edges.card = M.card := by
  exact Finset.card_image_of_injective M additiveEdge_injective

/-- ordinary-transition at explicit sufficient order thresholds.  Raw densities are allowed
to differ, the raw loss is one-sided, additions are arbitrary, and every
later target is quantified after the raw Fourier hypotheses. -/
theorem ordinary_transition_at {q t η μ : ℝ}
    (hq : 0 < q) (hqthird : q ≤ 1/3) (ht : 0 < t) (httenth : t ≤ 1/10)
    (hη : 0 < η) (hηq : η ≤ q/1000) (hηt : η ≤ t/100) (hηmu : η ≤ q^2*μ/1000)
    (hμ : 0 < μ) (hμhalf : μ ≤ 1/2)
    (hsource : ∀ (V : Type u) [Fintype V], PippengerInput V μ (t/2))
    (hround : 3 ≤ η*(Fintype.card G : ℝ))
    (hlarge : 8 ≤ μ*q^2*(Fintype.card G : ℝ))
    (a : Fin 3 → ℝ) (ha : ∀ i, DensityWindow q (a i))
    (R : Fin 3 → Finset G) (hraw : ∀ i, FourierGood (R i) (a i) η)
    (T : Fin 3 → Finset G) (ℓ : ℕ) (hbalance : ∀ i, (T i).card=ℓ)
    (hsize : |(ℓ : ℝ)-q*(Fintype.card G : ℝ)| ≤ η*(Fintype.card G : ℝ))
    (hloss : ∀ i, (((R i) \ (T i)).card : ℝ) ≤ η*(Fintype.card G : ℝ)) :
    ∃ (P : Finset (Vertex G)) (M : Matching P), P ⊆ targetVertices T ∧
      (ℓ : ℝ)-t*(Fintype.card G : ℝ) ≤ (M.edges.card : ℝ) := by
  have hηone : η ≤ 1 := by linarith
  have hB := badVertices_card hraw hη T
  have hwindow := ordinary_degree_window q η μ (Fintype.card G)
    (badVertices R T a η).card hη hηone hμ hμhalf (Nat.cast_nonneg _) hηmu hB hround hlarge
  have htarget (i : Fin 3) : |((T i).card : ℝ)-q*(Fintype.card G : ℝ)| ≤
      η*(Fintype.card G : ℝ) := by simpa only [hbalance] using hsize
  obtain ⟨I,hI,hsupp,hcover,hdeficit⟩ := weighted_matching_after_deletion
    additiveEdge additiveEdge_card additiveEdge_linear
    (targetVertices T) (badVertices R T a η) (ordinaryWeight R T a q)
    (ordinaryWeight_bounds hq ha) (ordinaryWeight_supported R T a q)
    μ (t/2) (q^2*(Fintype.card G : ℝ)/2) (14*η*(Fintype.card G : ℝ))
    hμ (by linarith) (by positivity) (by positivity) hwindow.1 hwindow.2
    (fun v hv hgood => ordinaryWeight_load_error hq (by linarith) ha hraw
      hη.le hηone htarget hloss v hv hgood)
    (by apply hsource)
  have hTcard : (targetVertices T).card = 3*ℓ := by
    rw [targetVertices_card]
    simp [hbalance]
  have hTreal : ((targetVertices T).card : ℝ) = 3*(ℓ : ℝ) := by exact_mod_cast hTcard
  rw [hTreal] at hdeficit
  have hℓ : (ℓ : ℝ) ≤ Fintype.card G := by
    have hc := Finset.card_le_univ (T 0)
    rw [hbalance] at hc
    exact_mod_cast hc
  have hηsq : η^2*(Fintype.card G : ℝ) ≤ η*(Fintype.card G : ℝ) :=
    mul_le_mul_of_nonneg_right (by nlinarith) (Nat.cast_nonneg _)
  have hηtn := mul_le_mul_of_nonneg_right hηt (Nat.cast_nonneg (α := ℝ) (Fintype.card G))
  have htℓ := mul_le_mul_of_nonneg_left hℓ (by positivity : 0 ≤ 3*t/2)
  have hcard : (ℓ : ℝ)-t*(Fintype.card G : ℝ) ≤ (I.card : ℝ) := by
    nlinarith
  refine ⟨_,matchingOfIndices I hI,?_,?_⟩
  · intro v hv
    obtain ⟨e,he,hve⟩ := Finset.mem_biUnion.mp hv
    letI : DecidableEq (Vertex G) := Classical.decEq _
    exact hcover (Finset.mem_biUnion.mpr ⟨e,he,hve⟩)
  · simpa only [matchingOfIndices_card] using hcard

/-- A single order threshold works for every finite abelian group and all
unequal raw densities, raw triples, and adaptive later targets. -/
theorem ordinary_transition_eventual (q t η μ : ℝ)
    (hq : 0 < q) (hqthird : q ≤ 1/3) (ht : 0 < t) (httenth : t ≤ 1/10)
    (hη : 0 < η) (hηq : η ≤ q/1000) (hηt : η ≤ t/100) (hηmu : η ≤ q^2*μ/1000)
    (hμ : 0 < μ) (hμhalf : μ ≤ 1/2)
    (hsource : ∀ (V : Type u) [Fintype V], PippengerInput V μ (t/2)) :
    ∃ N : ℕ, ∀ (G : Type u) [AddCommGroup G] [Fintype G], N ≤ Fintype.card G →
      ∀ (a : Fin 3 → ℝ), (∀ i, DensityWindow q (a i)) →
      ∀ (R : Fin 3 → Finset G), (∀ i, FourierGood (R i) (a i) η) →
      ∀ (T : Fin 3 → Finset G) (ℓ : ℕ), (∀ i, (T i).card=ℓ) →
      |(ℓ : ℝ)-q*(Fintype.card G : ℝ)| ≤ η*(Fintype.card G : ℝ) →
      (∀ i, (((R i) \ (T i)).card : ℝ) ≤ η*(Fintype.card G : ℝ)) →
      ∃ (P : Finset (Vertex G)) (M : Matching P), P ⊆ targetVertices T ∧
        (ℓ : ℝ)-t*(Fintype.card G : ℝ) ≤ (M.edges.card : ℝ) := by
  obtain ⟨N,hN⟩ := exists_nat_ge (max (3/η) (8/(μ*q^2)))
  refine ⟨N,?_⟩
  intro G _ _ horder a ha R hraw T ℓ hbalance hsize hloss
  have hn : (N : ℝ) ≤ Fintype.card G := by exact_mod_cast horder
  have hround : 3 ≤ η*(Fintype.card G : ℝ) := by
    have hh : 3/η ≤ (Fintype.card G : ℝ) := (le_max_left _ _).trans (hN.trans hn)
    have hh' := (div_le_iff₀ hη).mp hh
    nlinarith
  have hlarge : 8 ≤ μ*q^2*(Fintype.card G : ℝ) := by
    have hh : 8/(μ*q^2) ≤ (Fintype.card G : ℝ) := (le_max_right _ _).trans (hN.trans hn)
    have hh' := (div_le_iff₀ (mul_pos hμ (sq_pos_of_pos hq))).mp hh
    nlinarith
  exact ordinary_transition_at hq hqthird ht httenth hη hηq hηt hηmu hμ hμhalf
    hsource hround hlarge a ha R hraw T ℓ hbalance hsize hloss

/-- ordinary-transition with the only external premise being Alon--Yuster Theorem
1.1 (Pippenger), and with precisely its nonquantitative source constant. -/
theorem existsToleranceForOrdinaryMatching (hPippenger : PippengerTheorem.{u}) (q t : ℝ)
    (hq : 0 < q) (hqthird : q ≤ 1/3) (ht : 0 < t) (httenth : t ≤ 1/10) :
    ∃ μ : ℝ, 0 < μ ∧ μ ≤ 1/2 ∧ ∀ η : ℝ,
      0 < η → η ≤ q/1000 → η ≤ t/100 → η ≤ q^2*μ/1000 →
      ∃ N : ℕ, ∀ (G : Type u) [AddCommGroup G] [Fintype G], N ≤ Fintype.card G →
        ∀ (a : Fin 3 → ℝ), (∀ i, DensityWindow q (a i)) →
        ∀ (R : Fin 3 → Finset G), (∀ i, FourierGood (R i) (a i) η) →
        ∀ (T : Fin 3 → Finset G) (ℓ : ℕ), (∀ i, (T i).card=ℓ) →
        |(ℓ : ℝ)-q*(Fintype.card G : ℝ)| ≤ η*(Fintype.card G : ℝ) →
        (∀ i, (((R i) \ (T i)).card : ℝ) ≤ η*(Fintype.card G : ℝ)) →
        ∃ (P : Finset (Vertex G)) (M : Matching P), P ⊆ targetVertices T ∧
          (ℓ : ℝ)-t*(Fintype.card G : ℝ) ≤ (M.edges.card : ℝ) := by
  obtain ⟨μ,hμ,hμhalf,hsource⟩ := hPippenger.choose_mu (t/2) (by positivity)
  refine ⟨μ,hμ,hμhalf,?_⟩
  intro η hη hηq hηt hηmu
  exact ordinary_transition_eventual q t η μ hq hqthird ht httenth hη hηq hηt hηmu
    hμ hμhalf hsource

end
end EndpointTransitions
