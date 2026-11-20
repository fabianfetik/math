import CorralFormalization.EndpointProof.Matching.AbsorptionAssembly.PhysicalReceiver
import CorralFormalization.EndpointProof.Matching.AbsorptionAssembly.Deletion

/-!
# Actual additive edges and the single possible endpoint zero

This deterministic layer works with the unchanged tagged inventory.  Its
zero-edge supplier is stated separately; no near matching is assumed.  The
rooted counting adapter below pays for deleted vertices and later edge bans.
-/

open scoped Classical BigOperators

namespace EndpointMatching.Fractional.ActualRemainder

open EndpointFlow.AbelianTransport EndpointMatching.AbsorptionAssembly

noncomputable section

variable {G : Type*} [AddCommGroup G]

/-- Two different roles determine an actual zero-sum additive edge. -/
theorem hyperedge_eq_of_two_roles {E H : Finset (Vertex G)}
    (hE : Hyperedge E) (hH : Hyperedge H) {v w : Vertex G}
    (hvE : v ∈ E) (hvH : v ∈ H) (hwE : w ∈ E) (hwH : w ∈ H)
    (hp : v.1 ≠ w.1) : E = H := by
  obtain ⟨x, y, z, hxyz, rfl⟩ := hE
  obtain ⟨a, b, c, habc, rfl⟩ := hH
  rcases v with ⟨p, s⟩
  rcases w with ⟨q, t⟩
  fin_cases p <;> fin_cases q <;> simp_all [Prod.mk.injEq]
  all_goals
    have hcoord : x = a ∧ y = b ∧ z = c := by
      constructor
      · first | assumption | (apply add_right_cancel (b := y + z); simpa [add_assoc] using hxyz.trans habc.symm)
      · constructor
        · first | assumption | (apply add_left_cancel (a := x); apply add_right_cancel (b := z); simpa [add_assoc] using hxyz.trans habc.symm)
        · first | assumption | (apply add_left_cancel (a := x + y); simpa [add_assoc] using hxyz.trans habc.symm)
    simp_all

/-- The actual additive three-partite hypergraph is linear.  Numerical
coincidences between roles do not identify tagged vertices. -/
theorem hyperedge_inter_card_le_one {E H : Finset (Vertex G)}
    (hE : Hyperedge E) (hH : Hyperedge H) (hne : E ≠ H) :
    (E ∩ H).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro v hv w hw
  have hvE := (Finset.mem_inter.mp hv).1
  have hvH := (Finset.mem_inter.mp hv).2
  have hwE := (Finset.mem_inter.mp hw).1
  have hwH := (Finset.mem_inter.mp hw).2
  by_cases hp : v.1 = w.1
  · apply Prod.ext hp
    have hvE' : (w.1, v.2) ∈ E := by
      have hveq : v = (w.1, v.2) := Prod.ext hp rfl
      exact hveq ▸ hvE
    exact hyperedge_same_role_unique hE hvE' hwE
  · exact False.elim (hne (hyperedge_eq_of_two_roles hE hH hvE hvH hwE hwH hp))

/-- Every actual matching covers exactly three vertices per edge. -/
theorem matching_card {P : Finset (Vertex G)} (M : Matching P) :
    P.card = 3 * M.edges.card := by
  calc
    P.card = (M.edges.biUnion id).card := congrArg Finset.card M.cover.symm
    _ = ∑ E ∈ M.edges, E.card := Finset.card_biUnion M.disjoint
    _ = ∑ _E ∈ M.edges, (3 : ℕ) :=
      Finset.sum_congr rfl (fun E hE => hyperedge_card_eq_three (M.valid E hE))
    _ = 3 * M.edges.card := by simp [Nat.mul_comm]

theorem balanced_sdiff_matching {T P : Finset (Vertex G)} (hT : Balanced T)
    (M : Matching P) (hPT : P ⊆ T) : Balanced (T \ P) := by
  simpa only [AbsorptionAssembly.residual, Finset.empty_union] using
    (residual_balanced hT (matching_balanced (emptyMatching (G := G))) M
      (Finset.empty_subset T) hPT (by simp))

theorem zeroSum_sdiff_matching {T P : Finset (Vertex G)}
    (hT : ∑ v ∈ T, v.2 = 0) (M : Matching P) (hPT : P ⊆ T) :
    ∑ v ∈ T \ P, v.2 = 0 := by
  simpa only [AbsorptionAssembly.residual, Finset.empty_union] using
    (residual_sum_eq_zero hT (by simp : (∑ v ∈ (∅ : Finset (Vertex G)), v.2) = 0) M
      (Finset.empty_subset T) hPT (by simp))

omit [AddCommGroup G] in
/-- Cardinality of a balanced tagged inventory, including the empty one. -/
theorem balanced_card {T : Finset (Vertex G)} (hT : Balanced T) :
    T.card = 3 * (slice T 0).card := by
  have hparts : T.card = ∑ p : Fin 3, (slice T p).card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext v
      simp [slice]
    · intro p _ q _ hpq
      apply Finset.disjoint_left.mpr
      intro v hp hq
      exact hpq ((Finset.mem_filter.mp hp).2.symm.trans (Finset.mem_filter.mp hq).2)
  calc
    T.card = ∑ p : Fin 3, (slice T p).card := hparts
    _ = ∑ _p : Fin 3, (slice T 0).card :=
      Finset.sum_congr rfl (fun p _ => hT p)
    _ = 3 * (slice T 0).card := by simp

/-- The endpoint-zero step consists of zero or one actual allowed edge. -/
structure ZeroStep (W : Finset (Vertex G)) (F : Finset (Finset (Vertex G))) where
  covered : Finset (Vertex G)
  matching : Matching covered
  inside : covered ⊆ W
  allowed : ∀ E ∈ matching.edges, E ∉ F
  edges_le_one : matching.edges.card ≤ 1
  nonzero : ∀ v ∈ W \ covered, v.2 ≠ 0
  empty_if_nonzero : (∀ v ∈ W, v.2 ≠ 0) → covered = ∅

theorem ZeroStep.card_le_three {W : Finset (Vertex G)}
    {F : Finset (Finset (Vertex G))} (Z : ZeroStep W F) : Z.covered.card ≤ 3 := by
  rw [matching_card Z.matching]
  have := Z.edges_le_one
  omega

/-- A visible local edge supplier suffices for the entire zero preprocessing.
The physical target has at most one zero, so one edge removes every zero. -/
theorem zeroStep_exists {X Y C : Finset G}
    {T : Finset (Vertex G)} {F : Finset (Finset (Vertex G))}
    (hXY : Disjoint X Y) (hC : (0 : G) ∉ C)
    (hT : T ⊆ signedTarget X Y C)
    (hzero : ∀ z ∈ T, z.2 = 0 →
      ∃ E : Finset (Vertex G), Hyperedge E ∧ E ⊆ T ∧ z ∈ E ∧ E ∉ F) :
    Nonempty (ZeroStep T F) := by
  by_cases hnz : ∀ v ∈ T, v.2 ≠ 0
  · exact ⟨⟨∅, emptyMatching, by simp, by simp [emptyMatching], by simp [emptyMatching],
      by simpa using hnz, fun _ => rfl⟩⟩
  · push Not at hnz
    obtain ⟨z, hzT, hz0⟩ := hnz
    obtain ⟨E, hE, hET, hzE, hEF⟩ := hzero z hzT hz0
    let M : Matching E := {
      edges := {E}
      valid := by intro H hH; simpa using (Finset.mem_singleton.mp hH) ▸ hE
      disjoint := by simp
      cover := by simp }
    refine ⟨⟨E, M, hET, ?_, by simp [M], ?_, ?_⟩⟩
    · intro H hH
      simpa only [M, Finset.mem_singleton.mp hH] using hEF
    · intro v hv hv0
      have hvT := hT (Finset.mem_sdiff.mp hv).1
      have hzT' := hT hzT
      have hveq : v = (v.1, 0) := Prod.ext rfl hv0
      have hzeq : z = (z.1, 0) := Prod.ext rfl hz0
      have hp : v.1 = z.1 := signedTarget_zero_unique hXY hC
        (hveq ▸ hvT) (hzeq ▸ hzT')
      have hvz : v = z := Prod.ext hp (hv0.trans hz0.symm)
      exact (Finset.mem_sdiff.mp hv).2 (hvz ▸ hzE)
    · intro hnonzero
      exact False.elim (hnonzero z hzT hz0)

end
end EndpointMatching.Fractional.ActualRemainder
