import CorralFormalization.EndpointProof.Sampling.InverseOrbits
import CorralFormalization.EndpointProof.Sampling.ReservoirCoupling

/-!
The original group-indexed source and the inverse-orbit augmentation.

The source measure has one original categorical vertex coordinate, one
independent colour indicator, and three thinning coins at every element of G,
including zero. A separate product supplies the orbit proposal, acceptance,
and P/Q coins. The regrouping retains zero as a separate coordinate.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

namespace EndpointFullProduct

open EndpointOriginalReservoir EndpointBlockAvailability EndpointSharedSample
open EndpointReservoirAvailability

noncomputable section

variable {G : Type*} [Fintype G] [AddCommGroup G]

/-- The complete original index set: one zero and both signs of every pair. -/
def fullPlace : Option (OddOrbit G × Bool) → G
  | none => 0
  | some z => orbitPlace z

theorem fullPlace_bijective (hodd : Odd (Fintype.card G)) :
    Function.Bijective (fullPlace (G := G)) := by
  constructor
  · intro x y h
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some z => exact False.elim (orbitPlace_nonzero z h.symm)
    | some z =>
      cases y with
      | none => exact False.elim (orbitPlace_nonzero z h)
      | some w => exact congrArg some (orbitPlace.injective h)
  · intro g
    by_cases hg : g = 0
    · exact ⟨none, hg.symm⟩
    · obtain ⟨z, hz⟩ := orbitPlace_covers_nonzero hodd hg
      exact ⟨some z, hz⟩

def fullPlaceEquiv (hodd : Odd (Fintype.card G)) :
    Option (OddOrbit G × Bool) ≃ G :=
  Equiv.ofBijective fullPlace (fullPlace_bijective hodd)

@[simp] theorem fullPlaceEquiv_none (hodd : Odd (Fintype.card G)) :
    fullPlaceEquiv hodd none = (0 : G) := rfl

@[simp] theorem fullPlaceEquiv_some (hodd : Odd (Fintype.card G))
    (z : OddOrbit G × Bool) : fullPlaceEquiv hodd (some z) = orbitPlace z := rfl

@[simp] theorem fullPlaceEquiv_symm_zero (hodd : Odd (Fintype.card G)) :
    (fullPlaceEquiv hodd).symm 0 = none :=
  (fullPlaceEquiv hodd).symm_apply_apply none

@[simp] theorem fullPlaceEquiv_symm_orbit (hodd : Odd (Fintype.card G))
    (z : OddOrbit G × Bool) :
    (fullPlaceEquiv hodd).symm (orbitPlace z) = some z :=
  (fullPlaceEquiv hodd).symm_apply_apply (some z)

/-- This finite-product identity explicitly accounts for the zero factor. -/
theorem prod_group_eq_zero_mul_orbits {M : Type*} [CommMonoid M]
    (hodd : Odd (Fintype.card G)) (f : G → M) :
    ∏ g, f g = f 0 * ∏ o : OddOrbit G,
      (f (orbitPlace (o, false)) * f (orbitPlace (o, true))) := by
  rw [← (fullPlaceEquiv hodd).prod_comp f, Fintype.prod_option]
  simp only [fullPlaceEquiv_none, fullPlaceEquiv_some, Fintype.prod_prod_type,
    Fintype.prod_bool]
  apply congrArg (fun x ↦ f 0 * x)
  apply Finset.prod_congr rfl
  intro o ho
  exact mul_comm _ _

theorem finiteLaw_measure_singleton {A : Type*} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (u : FiniteLaw A) (a : A) :
    u.measure {a} = ENNReal.ofReal (u.weight a) := by
  simp [FiniteLaw.measure, FiniteLaw.pmf, PMF.ofFintype_apply]

/-- A reusable finite-law fact; the product notation is actual measure product. -/
theorem finiteLaw_measure_prod {A B : Type*} [Fintype A] [Fintype B]
    [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B]
    (u : FiniteLaw A) (v : FiniteLaw B) :
    (u.prod v).measure = u.measure.prod v.measure := by
  apply Measure.ext_of_singleton
  rintro ⟨a, b⟩
  rw [finiteLaw_measure_singleton, ← Set.singleton_prod_singleton, Measure.prod_prod,
    finiteLaw_measure_singleton, finiteLaw_measure_singleton]
  exact ENNReal.ofReal_mul (u.nonneg a)

abbrev OrbitCoins := Part × (Bool × Part)

def orbitCoinsLaw (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    FiniteLaw OrbitCoins :=
  proposalLaw.prod ((coinLaw (1 / 3) (by norm_num) (by norm_num)).prod
    (childLaw a b ha hb hab))

/-- All original coordinates, including zero, plus independent orbit coins. -/
abbrev FullSample (G : Type*) [Fintype G] [AddCommGroup G] :=
  (G → Coordinate) × (OddOrbit G → OrbitCoins)

def fullMeasure (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b ≤ 1) : Measure (FullSample G) :=
  (Measure.pi fun _ : G ↦ (coordinateLaw q η hq0 hq1 hη0 hη1).measure).prod
    (Measure.pi fun _ : OddOrbit G ↦ (orbitCoinsLaw a b ha hb hab).measure)

instance fullMeasure_probability (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b ≤ 1) :
    IsProbabilityMeasure (fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab) := by
  unfold fullMeasure
  infer_instance

/-- Inverse-pair blocks first, the unused zero coordinate second. -/
def regroup (ω : FullSample G) : (OddOrbit G → OrbitInput) × Coordinate :=
  (fun o ↦ (ω.1 (orbitPlace (o, false)),
    (ω.1 (orbitPlace (o, true)), ω.2 o)), ω.1 0)

def ungroup (hodd : Odd (Fintype.card G))
    (s : (OddOrbit G → OrbitInput) × Coordinate) : FullSample G :=
  (fun g ↦ match (fullPlaceEquiv hodd).symm g with
    | none => s.2
    | some (o, false) => (s.1 o).1
    | some (o, true) => (s.1 o).2.1,
   fun o ↦ (s.1 o).2.2)

theorem ungroup_regroup (hodd : Odd (Fintype.card G)) (ω : FullSample G) :
    ungroup hodd (regroup ω) = ω := by
  apply Prod.ext
  · funext g
    obtain ⟨z, rfl⟩ := (fullPlaceEquiv hodd).surjective g
    cases z with
    | none => simp [ungroup, regroup]
    | some z =>
      rcases z with ⟨o, b⟩
      cases b <;> simp [ungroup, regroup]
  · rfl

theorem regroup_ungroup (hodd : Odd (Fintype.card G))
    (s : (OddOrbit G → OrbitInput) × Coordinate) : regroup (ungroup hodd s) = s := by
  apply Prod.ext
  · funext o
    simp [regroup, ungroup]
  · simp [regroup, ungroup]

def regroupEquiv (hodd : Odd (Fintype.card G)) :
    FullSample G ≃ (OddOrbit G → OrbitInput) × Coordinate where
  toFun := regroup
  invFun := ungroup hodd
  left_inv := ungroup_regroup hodd
  right_inv := regroup_ungroup hodd

def regroupMeasurableEquiv (hodd : Odd (Fintype.card G)) :
    FullSample G ≃ᵐ (OddOrbit G → OrbitInput) × Coordinate where
  toEquiv := regroupEquiv hodd
  measurable_toFun := by unfold regroupEquiv regroup; fun_prop
  measurable_invFun := measurable_of_countable _

theorem prod_measure_singleton {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [SFinite ν] (s : A × B) :
    (μ.prod ν) {s} = μ {s.1} * ν {s.2} := by
  rcases s with ⟨a, b⟩
  rw [← Set.singleton_prod_singleton, Measure.prod_prod]

/-- Equality of the complete laws, retaining zero independently of all blocks.
The original G-indexed product is the source, rather than an assumption about
the distribution of a pregrouped sample. -/
theorem regroup_measurePreserving (hodd : Odd (Fintype.card G))
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b ≤ 1) :
    MeasurePreserving (regroup (G := G))
      (fullMeasure q η a b hq0 hq1 hη0 hη1 ha hb hab)
      ((originalProductMeasure q η a b hq0 hq1 hη0 hη1 ha hb hab).prod
        (coordinateLaw q η hq0 hq1 hη0 hη1).measure) := by
  let μ := (coordinateLaw q η hq0 hq1 hη0 hη1).measure
  let ν := (orbitCoinsLaw a b ha hb hab).measure
  have horbit : (orbitInputLaw q η a b hq0 hq1 hη0 hη1 ha hb hab).measure =
      μ.prod (μ.prod ν) := by
    change ((coordinateLaw q η hq0 hq1 hη0 hη1).prod
      ((coordinateLaw q η hq0 hq1 hη0 hη1).prod
        (orbitCoinsLaw a b ha hb hab))).measure = _
    rw [finiteLaw_measure_prod, finiteLaw_measure_prod]
  refine ⟨by unfold regroup; fun_prop, ?_⟩
  apply Measure.ext_of_singleton
  rintro ⟨s, z⟩
  rw [Measure.map_apply (by unfold regroup; fun_prop) (measurableSet_singleton _)]
  have hpre : regroup ⁻¹' {(s, z)} = {ungroup hodd (s, z)} := by
    ext ω
    change regroup ω = (s, z) ↔ ω = ungroup hodd (s, z)
    exact (regroupEquiv hodd).eq_symm_apply.symm
  rw [hpre]
  change ((Measure.pi fun _ : G ↦ μ).prod
      (Measure.pi fun _ : OddOrbit G ↦ ν)) {ungroup hodd (s, z)} = _
  simp only [prod_measure_singleton, Measure.pi_singleton,
    originalProductMeasure, horbit]
  rw [prod_group_eq_zero_mul_orbits hodd]
  simp only [ungroup, fullPlaceEquiv_symm_zero, fullPlaceEquiv_symm_orbit]
  simp only [Finset.prod_mul_distrib, μ]
  ring

theorem ungroup_measurePreserving (hodd : Odd (Fintype.card G))
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b ≤ 1) :
    MeasurePreserving (ungroup (G := G) hodd)
      ((originalProductMeasure q η a b hq0 hq1 hη0 hη1 ha hb hab).prod
        (coordinateLaw q η hq0 hq1 hη0 hη1).measure)
      (fullMeasure q η a b hq0 hq1 hη0 hη1 ha hb hab) :=
  (regroup_measurePreserving hodd q η a b hq0 hq1 hη0 hη1 ha hb hab).symm
    (regroupMeasurableEquiv hodd)

/-- The reservoir marginal follows from the complete regrouping. -/
theorem blocks_measurePreserving (hodd : Odd (Fintype.card G))
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b ≤ 1) :
    MeasurePreserving (fun ω : FullSample G ↦ (regroup ω).1)
      (fullMeasure q η a b hq0 hq1 hη0 hη1 ha hb hab)
      (originalProductMeasure q η a b hq0 hq1 hη0 hη1 ha hb hab) :=
  measurePreserving_fst.comp
    (regroup_measurePreserving hodd q η a b hq0 hq1 hη0 hη1 ha hb hab)

/-- The physical interpretation of (-R1,R2,-R3), with all signs explicit. -/
def signedMinus (part : Part) (ω : FullSample G) (g : G) : Prop :=
  rawMinus part (ω.1 (if part = 1 then g else -g))

theorem signedRawMinus_eq_group (part : Part) (ω : FullSample G)
    (o : OddOrbit G) (side : Bool) :
    signedRawMinus part side ((regroup ω).1 o) ↔
      signedMinus part ω (orbitPlace (o, side)) := by
  by_cases hp : part = 1 <;> cases side <;>
    simp [signedRawMinus, signedMinus, regroup, hp, orbitPlace, orbitCoordinate]

theorem parent_signed_containment (part : Part) (ω : FullSample G)
    (o : OddOrbit G) (side : Bool)
    (h : parentLabel ((regroup ω).1 o) = some part) :
    signedMinus part ω (orbitPlace (o, side)) :=
  (signedRawMinus_eq_group part ω o side).1
    (accepted_signed_membership _ part side ((parentLabel_eq_iff _ part).1 h))

theorem child_signed_containment (part : Part) (kind side : Bool) (ω : FullSample G)
    (o : OddOrbit G) (h : childLabel ((regroup ω).1 o) = some (part, kind)) :
    signedMinus part ω (orbitPlace (o, side)) :=
  (signedRawMinus_eq_group part ω o side).1
    (child_signed_membership _ part kind side h)

end
end EndpointFullProduct
