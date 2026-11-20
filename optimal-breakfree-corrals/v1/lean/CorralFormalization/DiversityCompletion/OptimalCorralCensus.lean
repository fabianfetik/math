import CorralFormalization.DiversityCompletion.EvenKForm
import CorralFormalization.DiversityCompletion.RealizedCorralOrbits
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace CorralFormalization.PhysicalCensus

open PhysicalCorral CorralLatinTailMarker LatinCompletion

section FiniteClock

variable {h n : ℕ} [NeZero (h*n)]

theorem mem_physicalOrbit_iff (P Q : PhysicalFamily h n) :
    Q ∈ physicalOrbit P ↔ PhysicallyEquivalent P Q := by
  simp only [physicalOrbit,Finset.mem_union,Finset.mem_image,Finset.mem_univ,true_and,
    PhysicallyEquivalent]
  constructor
  · rintro (⟨c,hc⟩ | ⟨c,hc⟩)
    · exact ⟨.rotation c,hc⟩
    · exact ⟨.reflection c,hc⟩
  · rintro ⟨f,hf⟩
    cases f with
    | rotation c => exact Or.inl ⟨c,hf⟩
    | reflection c => exact Or.inr ⟨c,hf⟩

theorem orbit_subset_of_motion (P Q : PhysicalFamily h n) (f : Motion (h*n))
    (hf : f.onFamily P = Q) : physicalOrbit Q ⊆ physicalOrbit P := by
  intro R hR
  obtain ⟨g,hg⟩ := (mem_physicalOrbit_iff Q R).mp hR
  exact (mem_physicalOrbit_iff P R).mpr
    ⟨g.compose f,by rw [Motion.onFamily_compose,hf,hg]⟩

/-- Equality of the finite full-orbit sets is exactly physical equivalence,
including all row permutations and both kinds of common motion. -/
theorem physicalOrbit_eq_iff (P Q : PhysicalFamily h n) :
    physicalOrbit P = physicalOrbit Q ↔ PhysicallyEquivalent P Q := by
  constructor
  · exact physicalOrbit_eq_gives_motion P Q
  · rintro ⟨f,hf⟩
    apply Finset.Subset.antisymm
    · cases f with
      | rotation c =>
        apply orbit_subset_of_motion Q P (.rotation (-c))
        rw [← hf,← Motion.onFamily_compose]
        simp [Motion.compose]
      | reflection c =>
        apply orbit_subset_of_motion Q P (.reflection c)
        rw [← hf,Motion.reflection_onFamily_involutive]
    · exact orbit_subset_of_motion P Q f hf

/-- All actual physical row families of valid optimal corrals. The explicit
clock equality ensures that taking residues is on the corrals' own clock. -/
noncomputable def validOptimalFamilies (h n : ℕ) [NeZero (h*n)] :
    Finset (PhysicalFamily h n) := by
  classical
  exact Finset.univ.filter (fun P => width n = h*n ∧
    ∃ R : CorralRows h n, realizedFamily R = P)

theorem realizedFamily_partition (R : CorralRows h n) (hwidth : width n=h*n) :
    ∀ x : ZMod (h*n), ∃! S, S ∈ realizedFamily R ∧ x ∈ S := by
  have : NeZero (width n) := ⟨by rw [hwidth]; exact NeZero.ne _⟩
  have hp := fun x : ZMod (width n) => corralRows_unlabelled_partition R hwidth x
  unfold physicalFamily at hp
  rw [hwidth] at hp
  exact hp

theorem realizedFamily_card (R : CorralRows h n) (hwidth : width n=h*n) :
    (realizedFamily R).card = h := by
  have : NeZero (width n) := ⟨by rw [hwidth]; exact NeZero.ne _⟩
  have hc := physicalFamily_card R
  unfold physicalFamily at hc
  rw [hwidth] at hc
  exact hc

theorem validOptimalFamilies_partition (P : PhysicalFamily h n)
    (hP : P ∈ validOptimalFamilies h n) :
    ∀ x : ZMod (h*n), ∃! S, S ∈ P ∧ x ∈ S := by
  classical
  obtain ⟨hw,R,hR⟩ := (Finset.mem_filter.mp hP).2
  subst P
  exact realizedFamily_partition R hw

/-- Full physical dihedral orbits of *all* asymmetric valid optimal corrals,
not just those met by one selected parameter family. -/
noncomputable def allAsymmetricCorralOrbits (h n : ℕ) [NeZero (h*n)] :
    Finset (Finset (PhysicalFamily h n)) := by
  classical
  exact ((validOptimalFamilies h n).filter PhysicallyAsymmetric).image physicalOrbit

theorem mem_allAsymmetricCorralOrbits (O : Finset (PhysicalFamily h n)) :
    O ∈ allAsymmetricCorralOrbits h n ↔
      ∃ R : CorralRows h n, width n = h*n ∧
        PhysicallyAsymmetric (realizedFamily R) ∧ physicalOrbit (realizedFamily R) = O := by
  classical
  simp only [allAsymmetricCorralOrbits,validOptimalFamilies,Finset.mem_image,
    Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨P,⟨⟨hw,⟨R,hR⟩⟩,ha⟩,hO⟩
    subst P
    exact ⟨R,hw,ha,hO⟩
  · rintro ⟨R,hw,ha,hO⟩
    exact ⟨realizedFamily R,⟨⟨hw,⟨R,rfl⟩⟩,ha⟩,hO⟩

variable {T : Type*} [Fintype T] [DecidableEq T]

/-- The intersection with a parameter family, computed from a full orbit. -/
noncomputable def orbitTrace (family : T → PhysicalFamily h n)
    (O : Finset (PhysicalFamily h n)) : Finset T := by
  classical
  exact Finset.univ.filter (fun t => family t ∈ O)

omit [DecidableEq T] in
theorem orbitTrace_physicalOrbit (family : T → PhysicalFamily h n) (t : T) :
    orbitTrace family (physicalOrbit (family t)) = physicalOrbitIntersection family t := by
  classical
  ext u
  simp only [orbitTrace,physicalOrbitIntersection,Finset.mem_filter,Finset.mem_univ,true_and]
  exact mem_physicalOrbit_iff _ _

/-- A distinct intersection of an asymmetric physical orbit with a selected
valid-corral family cannot increase the census of all such physical orbits.
No injectivity or rigidity assumption on the parameterization is needed. -/
theorem asymmetric_intersections_le_all (hwidth : width n = h*n)
    (C : T → CorralRows h n) :
    (asymmetricOrbitIntersections (fun t => realizedFamily (C t))).card ≤
      (allAsymmetricCorralOrbits h n).card := by
  classical
  let family := fun t => realizedFamily (C t)
  have hs : asymmetricOrbitIntersections family ⊆
      (allAsymmetricCorralOrbits h n).image (orbitTrace family) := by
    intro I hI
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hI
    have ha : PhysicallyAsymmetric (family t) := (Finset.mem_filter.mp ht).2
    refine Finset.mem_image.mpr ⟨physicalOrbit (family t),?_,?_⟩
    · exact (mem_allAsymmetricCorralOrbits _).mpr ⟨C t,hwidth,ha,rfl⟩
    · exact orbitTrace_physicalOrbit family t
  exact (Finset.card_le_card hs).trans (Finset.card_image_le)

omit [DecidableEq T] in
theorem full_orbit_image_le_all (hwidth : width n = h*n)
    (C : T → CorralRows h n) (ha : ∀ t, PhysicallyAsymmetric (realizedFamily (C t))) :
    (Finset.univ.image (fun t => physicalOrbit (realizedFamily (C t)))).card ≤
      (allAsymmetricCorralOrbits h n).card := by
  classical
  apply Finset.card_le_card
  intro O hO
  obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hO
  exact (mem_allAsymmetricCorralOrbits _).mpr ⟨C t,hwidth,ha t,rfl⟩

end FiniteClock

/-- The manuscript's A_h, on its faithful physical-dihedral domain h>=2.
The proof argument only records the domain; it adds no existence supplier. -/
noncomputable def A_h (h : ℕ) (hh : 2 ≤ h) : ℕ := by
  have : NeZero (h*(2*h-1)) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  exact (allAsymmetricCorralOrbits h (2*h-1)).card

theorem A_h_eq {h n : ℕ} [NeZero (h*n)] (hh : 2 ≤ h) (hn : n=2*h-1) :
    A_h h hh = (allAsymmetricCorralOrbits h n).card := by
  subst n
  rfl

open EvenSwitches

/-- The exact Theorem 3 family count is a lower bound for the total number
of asymmetric physical optimal-corral orbits. It is not a total census. -/
theorem evenSwitchFamily_total_lower (m : ℕ) (hm : 1 ≤ m) :
    (2^(4*m*m)-2^(2*m*m))/2 ≤ A_h (height m) (by unfold height; omega) := by
  have : NeZero (height m * order m) := ⟨by unfold height order; positivity⟩
  obtain ⟨C,_,hcount⟩ := evenSwitchFamily_explicit_corral_family m hm
  have hc := asymmetric_intersections_le_all (EvenSwitches.optimal_width m) C
  change (asymmetricOrbitIntersections (fun t => physicalCorralFamily m (C t))).card ≤ _ at hc
  rw [hcount] at hc
  have hn : order m = 2*height m-1 := by unfold order height; omega
  rw [A_h_eq (by unfold height; omega) hn]
  exact hc

theorem evenSwitchFamily_integer_lower (m : ℕ) (hm : 1 ≤ m) :
    2^(4*m*m-2) ≤ A_h (height m) (by unfold height; omega) :=
  (evenSwitchFamily_numerical_lower m hm).trans (evenSwitchFamily_total_lower m hm)

theorem evenSwitchFamily_odd_k_total_lower (k : ℕ) (hk : 3 ≤ k) (ho : Odd k) :
    (2^((k-1)^2)-2^(((k-1)^2)/2))/2 ≤ A_h (2*k) (by omega) := by
  obtain ⟨m,hm,_,hh,hn,C,_,hcount⟩ := evenSwitchFamily_odd_k k hk ho
  have : NeZero (height m * order m) := ⟨by unfold height order; positivity⟩
  have hc := asymmetric_intersections_le_all (EvenSwitches.optimal_width m) C
  change (asymmetricOrbitIntersections (fun t => physicalCorralFamily m (C t))).card ≤ _ at hc
  rw [hcount] at hc
  have horder : order m = 2*height m-1 := by rw [hh]; exact hn
  rw [← A_h_eq (by unfold height; omega) horder] at hc
  simpa only [hh] using hc

/-- The paper's real base-2 logarithmic inequality, first in h=4m+2 form. -/
theorem evenSwitchFamily_real_log_lower_m (m : ℕ) (hm : 1 ≤ m) :
    (height m : ℝ)^2/4 - (height m : ℝ)-1 ≤
      Real.logb 2 (A_h (height m) (by unfold height; omega) : ℝ) := by
  have hp : (2 : ℝ)^(4*m*m-2) ≤
      (A_h (height m) (by unfold height; omega) : ℝ) := by
    exact_mod_cast evenSwitchFamily_integer_lower m hm
  have hl := Real.logb_le_logb_of_le (b := 2) (by norm_num : (1 : ℝ)<2)
    (by positivity : (0 : ℝ)<2^(4*m*m-2)) hp
  rw [Real.logb_pow,Real.logb_self_eq_one (by norm_num),mul_one] at hl
  have he : ((4*m*m-2 : ℕ) : ℝ) = (height m : ℝ)^2/4-(height m : ℝ)-1 := by
    rw [Nat.cast_sub (by nlinarith : 2 ≤ 4*m*m)]
    unfold height
    push_cast
    ring
  rw [he] at hl
  exact hl

/-- For h=2k, odd k>=3: log_2 A_h >= h^2/4-h-1. -/
theorem evenSwitchFamily_real_log_lower (k : ℕ) (hk : 3 ≤ k) (ho : Odd k) :
    ((2*k : ℕ) : ℝ)^2/4 - ((2*k : ℕ) : ℝ)-1 ≤
      Real.logb 2 (A_h (2*k) (by omega) : ℝ) := by
  obtain ⟨m,hm,hk'⟩ := odd_k_parameters k hk ho
  have hh : height m = 2*k := by rw [hk']; unfold height; ring
  simpa only [hh] using evenSwitchFamily_real_log_lower_m m hm

end CorralFormalization.PhysicalCensus
