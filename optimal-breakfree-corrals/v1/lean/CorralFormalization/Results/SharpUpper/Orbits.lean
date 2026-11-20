import CorralFormalization.Results.SharpUpper.RowMotion
import CorralFormalization.Results.PrimeHeight.ModelBridges

/-!
# The full physical dihedral orbit divisor

The action is on actual unlabelled physical families. Motion invariance of the
row inventory is proved in `RowMotion`; the local/census equivalence is the
maintained exact model bridge. Thus the resulting mass bound has no closure
or orbit-size supplier as a hypothesis.
-/

namespace CorralFormalization.Results.SharpUpper

open Finset PhysicalCorral LatinCompletion CorralLatinTailMarker PhysicalCensus

section OrbitCard

variable {h n : ℕ} [NeZero (h*n)]

omit [NeZero (h*n)] in
lemma asymmetric_motion_injective (P : PhysicalFamily h n) (ha : PhysicallyAsymmetric P) :
    Function.Injective (fun f : Motion (h*n) => f.onFamily P) := by
  intro f g hfg
  change f.onFamily P = g.onFamily P at hfg
  have hfix : ((g⁻¹).compose f).onFamily P = P := by
    rw [Motion.onFamily_compose,hfg,← Motion.onFamily_compose]
    change (g⁻¹ * g).onFamily P = P
    simp only [inv_mul_cancel, Motion.one_eq, Motion.identity_onFamily]
  have hid : g⁻¹ * f = 1 := ha _ hfix
  have hm := congrArg (fun k : Motion (h*n) => g*k) hid
  simpa only [← mul_assoc, mul_inv_cancel, one_mul, mul_one] using hm

/-- The full physical orbit of an asymmetric unlabelled partition has
exactly `2M` members. Rotations and reflections are both counted. -/
theorem asymmetric_physicalOrbit_card (P : PhysicalFamily h n) (ha : PhysicallyAsymmetric P) :
    (physicalOrbit P).card = 2*(h*n) := by
  classical
  have heq : physicalOrbit P = univ.image (fun f : Motion (h*n) => f.onFamily P) := by
    ext Q
    rw [mem_physicalOrbit_iff]
    simp only [mem_image,mem_univ,true_and,PhysicallyEquivalent]
  rw [heq,card_image_of_injective _ (asymmetric_motion_injective P ha),card_univ,Motion.card]

lemma physicalOrbits_eq_of_common (P Q R : PhysicalFamily h n)
    (hP : R ∈ physicalOrbit P) (hQ : R ∈ physicalOrbit Q) :
    physicalOrbit P = physicalOrbit Q :=
  ((physicalOrbit_eq_iff P R).mpr ((mem_physicalOrbit_iff P R).mp hP)).trans
    ((physicalOrbit_eq_iff Q R).mpr ((mem_physicalOrbit_iff Q R).mp hQ)).symm

end OrbitCard

/-- The census of all actual valid physical partitions is closed under
every common physical motion, including the full reflection action. -/
theorem validOptimalFamilies_motion_closed {h n : ℕ} [NeZero (h*n)]
    (hn : 2 ≤ n) (hw : width n = h*n) (P : PhysicalFamily h n)
    (hP : P ∈ validOptimalFamilies h n) (f : Motion (h*n)) :
    f.onFamily P ∈ validOptimalFamilies h n := by
  classical
  obtain ⟨hcard,hdis,hgap⟩ := (PrimeHeight.mem_validOptimalFamilies_iff_local hn hw P).mp hP
  apply (PrimeHeight.mem_validOptimalFamilies_iff_local hn hw _).mpr
  have hinj : Function.Injective f.onRow :=
    Finset.image_injective (Motion.act_injective f)
  refine ⟨?_,?_,?_⟩
  · simpa only [Motion.onFamily,card_image_of_injective _ hinj] using hcard
  · intro S hS T hT hST
    obtain ⟨A,hA,rfl⟩ := mem_image.mp hS
    obtain ⟨B,hB,rfl⟩ := mem_image.mp hT
    have hAB : A ≠ B := fun h => hST (congrArg f.onRow h)
    apply disjoint_left.mpr
    intro x hxA hxB
    obtain ⟨a,ha,hax⟩ := mem_image.mp hxA
    obtain ⟨b,hb,hbx⟩ := mem_image.mp hxB
    have hab : a = b := Motion.act_injective f (hax.trans hbx.symm)
    exact disjoint_left.mp (hdis A hA B hB hAB) ha (hab ▸ hb)
  · intro S hS
    obtain ⟨A,hA,rfl⟩ := mem_image.mp hS
    have hvalid : A ∈ validRows (h*n) n := mem_filter.mpr ⟨mem_univ _,hgap A hA⟩
    exact (mem_filter.mp (validRows_motion_closed hn hw A hvalid f)).2

/-- The full asymmetric orbit sets in the maintained census are disjoint,
not merely disjoint traces on one selected constructed family. -/
theorem census_orbits_pairwise_disjoint {h n : ℕ} [NeZero (h*n)] :
    ∀ O ∈ allAsymmetricCorralOrbits h n, ∀ T ∈ allAsymmetricCorralOrbits h n,
      O ≠ T → Disjoint O T := by
  classical
  intro O hO T hT hOT
  obtain ⟨R,_,ha,hRO⟩ := (mem_allAsymmetricCorralOrbits O).mp hO
  obtain ⟨S,_,hb,hST⟩ := (mem_allAsymmetricCorralOrbits T).mp hT
  apply disjoint_left.mpr
  intro P hPO hPT
  rw [← hRO] at hPO
  rw [← hST] at hPT
  have heq := physicalOrbits_eq_of_common (realizedFamily R) (realizedFamily S) P hPO hPT
  exact hOT (hRO.symm.trans (heq.trans hST))

/-- The exact global physical orbit mass bound. Both the `2M` orbit size
and containment in the full valid-corral census are proved above. -/
theorem asymmetric_orbit_mass_le {h n : ℕ} [NeZero (h*n)]
    (hn : 2 ≤ n) (hw : width n = h*n) :
    (allAsymmetricCorralOrbits h n).card * (2*(h*n)) ≤ (validOptimalFamilies h n).card := by
  classical
  have hsub : (allAsymmetricCorralOrbits h n).biUnion id ⊆ validOptimalFamilies h n := by
    intro P hP
    obtain ⟨O,hO,hPO⟩ := mem_biUnion.mp hP
    obtain ⟨R,hRwidth,ha,hRO⟩ := (mem_allAsymmetricCorralOrbits O).mp hO
    rw [← hRO] at hPO
    obtain ⟨f,hf⟩ := (mem_physicalOrbit_iff _ _).mp hPO
    have hvalid : realizedFamily R ∈ validOptimalFamilies h n :=
      mem_filter.mpr ⟨mem_univ _,hRwidth,⟨R,rfl⟩⟩
    rw [← hf]
    exact validOptimalFamilies_motion_closed hn hw _ hvalid f
  have hcards : ∀ O ∈ allAsymmetricCorralOrbits h n, O.card = 2*(h*n) := by
    intro O hO
    obtain ⟨R,_,ha,hRO⟩ := (mem_allAsymmetricCorralOrbits O).mp hO
    rw [← hRO]
    exact asymmetric_physicalOrbit_card _ ha
  calc
    _ = ∑ O ∈ allAsymmetricCorralOrbits h n, O.card := by
      rw [sum_congr rfl hcards]
      simp
    _ = ((allAsymmetricCorralOrbits h n).biUnion id).card := by
      exact (card_biUnion (census_orbits_pairwise_disjoint (h := h) (n := n))).symm
    _ ≤ _ := card_le_card hsub

/-- The exact real division by all `2M` physical dihedral motions. -/
theorem asymmetric_orbit_count_le_div {h n : ℕ} [NeZero (h*n)]
    (hn : 2 ≤ n) (hw : width n = h*n) :
    ((allAsymmetricCorralOrbits h n).card : ℝ) ≤
      ((validOptimalFamilies h n).card : ℝ) / ((2*(h*n) : ℕ) : ℝ) := by
  have hpos : 0 < ((2*(h*n) : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < 2*(h*n) by have := NeZero.pos (h*n); omega)
  apply (le_div_iff₀ hpos).mpr
  exact_mod_cast asymmetric_orbit_mass_le hn hw

end CorralFormalization.Results.SharpUpper
