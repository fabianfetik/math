import CorralFormalization.DiversityCompletion.OptimalCorralCensus
import CorralFormalization.ConstructionSupport.LatinTransfer

/-! A coarse but unconditional upper bound sufficient for the logarithmic
order in Theorem 10. This does not claim the stronger product of Theorem 8. -/

namespace CorralFormalization.PhysicalCensus

open PhysicalCorral CorralLatinTailMarker LatinCompletion LatinTransfer

/-- Forget the labels of a function assigning one row label to each site. -/
noncomputable def assignmentFamily {h n : ℕ} [NeZero (h*n)]
    (f : ZMod (h*n) → Fin h) : PhysicalFamily h n := by
  classical
  exact Finset.univ.image (fun i : Fin h => Finset.univ.filter (fun x => f x = i))

/-- Every actual optimal corral partition arises from an assignment of its
physical sites to the original row labels. -/
theorem exists_assignment_for_corral {h n : ℕ} [NeZero (h*n)]
    (R : CorralRows h n) (hw : width n = h*n) :
    ∃ f : ZMod (h*n) → Fin h, assignmentFamily f = realizedFamily R := by
  classical
  have part : ∀ x : ZMod (h*n), ∃ i : Fin h,
      x ∈ physicalSites (h*n) (R.sites i) := by
    intro x
    obtain ⟨S,⟨hS,hx⟩,_⟩ := realizedFamily_partition R hw x
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hS
    exact ⟨i, hi ▸ hx⟩
  let f : ZMod (h*n) → Fin h := fun x => Classical.choose (part x)
  have hf (x : ZMod (h*n)) : x ∈ physicalSites (h*n) (R.sites (f x)) :=
    Classical.choose_spec (part x)
  have hd (i j : Fin h) (hij : i ≠ j) :
      Disjoint (physicalSites (h*n) (R.sites i)) (physicalSites (h*n) (R.sites j)) := by
    have : NeZero (width n) := ⟨by rw [hw]; exact NeZero.ne _⟩
    have hh := corralRows_physical_disjoint R i j hij
    rw [hw] at hh
    exact hh
  have hrow (i : Fin h) : (Finset.univ.filter (fun x : ZMod (h*n) => f x = i)) =
      physicalSites (h*n) (R.sites i) := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · intro hi
      simpa only [hi] using hf x
    · intro hx
      by_contra hi
      exact Finset.disjoint_left.mp (hd (f x) i hi) (hf x) hx
  refine ⟨f, ?_⟩
  unfold assignmentFamily realizedFamily
  simp_rw [hrow]

theorem allAsymmetricCorralOrbits_le_assignments {h n : ℕ} [NeZero (h*n)] :
    (allAsymmetricCorralOrbits h n).card ≤ h^(h*n) := by
  classical
  have hsub : validOptimalFamilies h n ⊆
      (Finset.univ : Finset (ZMod (h*n) → Fin h)).image assignmentFamily := by
    intro P hP
    obtain ⟨hw,R,hR⟩ := (Finset.mem_filter.mp hP).2
    obtain ⟨f,hf⟩ := exists_assignment_for_corral R hw
    apply Finset.mem_image.mpr
    exact ⟨f,Finset.mem_univ _,hf.trans hR⟩
  calc
    (allAsymmetricCorralOrbits h n).card
        ≤ (validOptimalFamilies h n).card := by
          unfold allAsymmetricCorralOrbits
          exact Finset.card_image_le.trans (Finset.card_filter_le _ _)
    _ ≤ ((Finset.univ : Finset (ZMod (h*n) → Fin h)).image assignmentFamily).card :=
          Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (ZMod (h*n) → Fin h)).card := Finset.card_image_le
    _ = h^(h*n) := by simp [ZMod.card]

theorem A_h_le_assignments (h : ℕ) (hh : 2 ≤ h) :
    A_h h hh ≤ h^(h*(2*h-1)) := by
  have : NeZero (h*(2*h-1)) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  rw [A_h_eq hh rfl]
  exact allAsymmetricCorralOrbits_le_assignments

theorem A_h_log_upper (h : ℕ) (hh : 2 ≤ h) :
    Real.log (A_h h hh : ℝ) ≤ 2*(h : ℝ)^2*Real.log (h : ℝ) := by
  have hlog : 0 ≤ Real.log (h : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ h by omega))
  by_cases hz : A_h h hh = 0
  · simp [hz]
    positivity
  · have hp : 0 < (A_h h hh : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hz)
    have hcount : (A_h h hh : ℝ) ≤ (h : ℝ)^(h*(2*h-1)) := by
      exact_mod_cast A_h_le_assignments h hh
    have hl := Real.log_le_log hp hcount
    rw [Real.log_pow] at hl
    have he : ((h*(2*h-1) : ℕ) : ℝ) ≤ 2*(h : ℝ)^2 := by
      rw [Nat.cast_mul,Nat.cast_sub (by omega : 1 ≤ 2*h)]
      push_cast
      nlinarith
    have hb := mul_le_mul_of_nonneg_right he hlog
    nlinarith

end CorralFormalization.PhysicalCensus
