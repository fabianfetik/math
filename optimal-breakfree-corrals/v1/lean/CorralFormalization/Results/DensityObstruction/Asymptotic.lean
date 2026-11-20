import CorralFormalization.Results.DensityObstruction.FiniteFamily

namespace CorralFormalization.Results.DensityObstruction

open scoped BigOperators
open CorralFormalization.LatinCompletion.TerraceCompletion

/-- Exactly the data hypotheses of the existing endpoint completion receiver,
together with failure of its actual path conclusion. -/
def EndpointCounterexample {n : ℕ} [NeZero n]
    (W D : Finset (ZMod n)) (x y : ZMod n) : Prop :=
  x ∈ W ∧ y ∈ W ∧ x ≠ y ∧ 0 ∉ D ∧
  D.card + 1 = W.card ∧ (∑ d ∈ D, d) = y-x ∧
  ¬ EndpointPathClaim W D x y

theorem family_counterexample (a b : ℕ) (_ha : 1 ≤ a)
    (T : Finset (ZMod (3 * height a b)))
    (hT : T ⊆ residueClass (height a b) 2) (hcard : T.card = a)
    (y : ZMod (3 * height a b)) (hy : y ∈ T) :
    EndpointCounterexample (vertices T) (colors T) (start T y) y := by
  exact ⟨family_start_mem a b T hT hcard y hy, Finset.mem_union_right _ hy,
    family_start_ne_end a b T hT hcard y hy, zero_not_mem_colors T,
    colors_card_add_one T, family_endpoint_sum T y,
    family_no_endpointPath a b T hT hcard y hy⟩

theorem family_exists (a b : ℕ) (ha : 1 ≤ a) :
    ∃ (T : Finset (ZMod (3 * height a b))) (y : ZMod (3 * height a b)),
      T ⊆ residueClass (height a b) 2 ∧ T.card = a ∧ y ∈ T ∧
      EndpointCounterexample (vertices T) (colors T) (start T y) y := by
  have hac : a ≤ (residueClass (height a b) 2).card := by
    rw [residueClass_card]
    dsimp [height]
    omega
  obtain ⟨T, hT, hcard⟩ := Finset.exists_subset_card_eq hac
  obtain ⟨y, hy⟩ := Finset.card_pos.mp (show 0 < T.card by omega)
  exact ⟨T, y, hT, hcard, hy, family_counterexample a b ha T hT hcard y hy⟩

theorem zero_b_exact_counts (a : ℕ) (_ha : 1 ≤ a)
    (T : Finset (ZMod (3 * height a 0)))
    (hT : T ⊆ residueClass (height a 0) 2) (hcard : T.card = a) :
    3 * height a 0 = 12*a+3 ∧
    (vertices T).card = 9*a+2 ∧
    (3 * height a 0) - (vertices T).card = 3*a+1 ∧
    4 * (vertices T).card + 1 = 3 * (3 * height a 0) ∧
    4 * ((3 * height a 0) - (vertices T).card) = 3 * height a 0 + 1 ∧
    (3 * height a 0) - (vertices T).card = (3 * height a 0 + 3) / 4 := by
  have hvc := vertices_card T hT hcard
  dsimp [height] at hvc ⊢
  omega

/-- At each order `12a+3`, the missing-vertex count is exactly `ceil(n/4)`.
The statement uses natural division `(n+3)/4` to make that ceiling explicit. -/
theorem zero_b_counterexample (a : ℕ) (ha : 1 ≤ a) :
    ∃ (W D : Finset (ZMod (3 * height a 0)))
      (x y : ZMod (3 * height a 0)),
      EndpointCounterexample W D x y ∧
      W.card = 9*a+2 ∧
      (3 * height a 0) - W.card = (3 * height a 0 + 3) / 4 ∧
      4 * W.card + 1 = 3 * (3 * height a 0) := by
  obtain ⟨T, y, hT, hcard, hy, hc⟩ := family_exists a 0 ha
  have hs := zero_b_exact_counts a ha T hT hcard
  exact ⟨vertices T, colors T, start T y, y, hc, hs.2.1, hs.2.2.2.2.2, hs.2.2.2.1⟩

/-- Full asymptotic quantifiers: every fixed missing fraction above `1/4`
admits actual counterexamples at arbitrarily large odd cyclic orders. The
subfamily `b=0` already suffices, so no interchange of two limits is needed. -/
theorem arbitrarily_large_density_obstructions (ε : ℝ) (hε : (1:ℝ)/4 < ε)
    (N : ℕ) :
    ∃ (n : ℕ) (hn : NeZero n), Odd n ∧ N ≤ n ∧
      ∃ (W D : Finset (ZMod n)) (x y : ZMod n),
        (n : ℝ) - ε*n ≤ (W.card : ℝ) ∧
        @EndpointCounterexample n hn W D x y := by
  have hδ : 0 < ε - (1:ℝ)/4 := by linarith
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / (ε - (1:ℝ)/4))
  let a : ℕ := N+k+1
  have ha : 1 ≤ a := by dsimp [a]; omega
  have hka : k ≤ a := by dsimp [a]; omega
  have hN : N ≤ 3 * height a 0 := by dsimp [a, height]; omega
  have hmul : 1 < (ε - (1:ℝ)/4) * (k : ℝ) := by
    have h := (div_lt_iff₀ hδ).mp hk
    nlinarith
  have hkareal : (k : ℝ) ≤ a := by exact_mod_cast hka
  have hma : 1 < (ε - (1:ℝ)/4) * (a : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hkareal hδ.le
    linarith
  obtain ⟨T, y, hT, hcard, hy, hc⟩ := family_exists a 0 ha
  refine ⟨3 * height a 0, family_neZero a 0, family_order_odd a 0 (by simp), hN,
    vertices T, colors T, start T y, y, ?_, hc⟩
  rw [vertices_card T hT hcard]
  simp only [height, Nat.mul_zero, Nat.add_zero, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_one]
  nlinarith

/-- The arbitrarily large counterexamples also satisfy the single-endpoint
budget `1 ≤ ε n` appearing in the path-factor formulation. -/
theorem arbitrarily_large_density_obstructions_with_endpoint_budget
    (ε : ℝ) (hε : (1:ℝ)/4 < ε) (N : ℕ) :
    ∃ (n : ℕ) (hn : NeZero n), Odd n ∧ N ≤ n ∧ (1:ℝ) ≤ ε*n ∧
      ∃ (W D : Finset (ZMod n)) (x y : ZMod n),
        (n : ℝ) - ε*n ≤ (W.card : ℝ) ∧
        @EndpointCounterexample n hn W D x y := by
  have hpos : 0 < ε := by linarith
  obtain ⟨k, hk⟩ := exists_nat_gt (1/ε)
  obtain ⟨n,hn,hodd,hN,W,D,x,y,hdense,hcounter⟩ :=
    arbitrarily_large_density_obstructions ε hε (max N k)
  have hkn : (k : ℝ) ≤ n := by exact_mod_cast ((le_max_right N k).trans hN)
  have hkpos : 1 < ε * (k : ℝ) := by
    have h := (div_lt_iff₀ hpos).mp hk
    nlinarith
  have hmul : ε * (k : ℝ) ≤ ε * (n : ℝ) := mul_le_mul_of_nonneg_left hkn hpos.le
  exact ⟨n,hn,hodd,(le_max_left N k).trans hN,by linarith,W,D,x,y,hdense,hcounter⟩

/-- The supplement's displayed scaling also works with full quantifier order:
choose `A` once from `ε`, then every `k≥1` supplies a dense counterexample.
The order can subsequently be made larger than any prescribed threshold. -/
theorem printed_scaling_density_obstructions (ε : ℝ) (hε : (1:ℝ)/4 < ε) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ k : ℕ, 1 ≤ k →
      ∃ (W D : Finset (ZMod (3 * height (A*k) (2*k))))
        (x y : ZMod (3 * height (A*k) (2*k))),
        Odd (3 * height (A*k) (2*k)) ∧
        (3 * height (A*k) (2*k) : ℝ) - ε * (3 * height (A*k) (2*k)) ≤ (W.card : ℝ) ∧
        W.card = 9*A*k+12*k+2 ∧ EndpointCounterexample W D x y := by
  have hδ : 0 < ε - (1:ℝ)/4 := by linarith
  obtain ⟨B, hB⟩ := exists_nat_gt (1 / (ε - (1:ℝ)/4))
  let A := B+1
  have hA : 1 ≤ A := by dsimp [A]; omega
  have hBA : (B : ℝ) ≤ A := by exact_mod_cast (show B ≤ A by dsimp [A]; omega)
  have hmA : 1 < (ε - (1:ℝ)/4) * (A : ℝ) := by
    have hmB := (div_lt_iff₀ hδ).mp hB
    have hh := mul_le_mul_of_nonneg_left hBA hδ.le
    nlinarith
  refine ⟨A, hA, ?_⟩
  intro k hk
  have hak : 1 ≤ A*k := by nlinarith
  have hkreal : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hmk : (k : ℝ) < ((ε - (1:ℝ)/4) * (A : ℝ)) * k := by
    nlinarith
  obtain ⟨T, y, hT, hcard, hy, hc⟩ := family_exists (A*k) (2*k) hak
  have hvc : (vertices T).card = 9*A*k+12*k+2 := by
    rw [vertices_card T hT hcard]
    dsimp [height]
    ring
  refine ⟨vertices T, colors T, start T y, y,
    family_order_odd (A*k) (2*k) (by exact even_two_mul k), ?_, hvc, hc⟩
  rw [hvc]
  simp only [height, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  have hδk : 0 ≤ (ε - (1:ℝ)/4) * (k : ℝ) := mul_nonneg hδ.le (by positivity)
  nlinarith

theorem printed_scaling_arbitrarily_large (ε : ℝ) (hε : (1:ℝ)/4 < ε) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ N : ℕ, ∃ k : ℕ, 1 ≤ k ∧
      N ≤ 3 * height (A*k) (2*k) ∧
      ∃ (W D : Finset (ZMod (3 * height (A*k) (2*k))))
        (x y : ZMod (3 * height (A*k) (2*k))),
        Odd (3 * height (A*k) (2*k)) ∧
        (3 * height (A*k) (2*k) : ℝ) - ε * (3 * height (A*k) (2*k)) ≤ (W.card : ℝ) ∧
        EndpointCounterexample W D x y := by
  obtain ⟨A, hA, hfamily⟩ := printed_scaling_density_obstructions ε hε
  refine ⟨A, hA, ?_⟩
  intro N
  let k := N+1
  have hk : 1 ≤ k := by dsimp [k]; omega
  have hNk : N ≤ 3 * height (A*k) (2*k) := by dsimp [height, k]; omega
  obtain ⟨W, D, x, y, hodd, hdense, hcard, hc⟩ := hfamily k hk
  exact ⟨k, hk, hNk, W, D, x, y, hodd, hdense, hc⟩

/-- No endpoint theorem with these exact hypotheses can have a fixed
missing fraction strictly larger than one quarter. -/
theorem no_uniform_endpoint_tolerance_above_quarter (ε : ℝ) (hε : (1:ℝ)/4 < ε) :
    ¬ ∃ N : ℕ, ∀ (n : ℕ) [NeZero n], Odd n → N ≤ n →
      ∀ (W D : Finset (ZMod n)) (x y : ZMod n),
        (n : ℝ) - ε*n ≤ (W.card : ℝ) →
        x ∈ W → y ∈ W → x ≠ y → 0 ∉ D →
        D.card+1 = W.card → (∑ d ∈ D, d) = y-x → EndpointPathClaim W D x y := by
  rintro ⟨N, H⟩
  obtain ⟨n, hn, hodd, hN, W, D, x, y, hdense, hc⟩ :=
    arbitrarily_large_density_obstructions ε hε N
  letI : NeZero n := hn
  obtain ⟨hx, hy, hxy, hzero, hcard, hsum, hno⟩ := hc
  exact hno (H n hodd hN W D x y hdense hx hy hxy hzero hcard hsum)

end CorralFormalization.Results.DensityObstruction
