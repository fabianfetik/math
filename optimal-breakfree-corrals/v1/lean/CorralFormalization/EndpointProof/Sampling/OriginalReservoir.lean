import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic

/-!
Original categorical coordinates and coins for inverse-orbit reservoirs.

All probabilities below are derived from explicit finite product weights.
The inputs are two independent original coordinates per inverse orbit,
with a categorical vertex role, an independent colour indicator, and three
independent thinning coins at each coordinate. Independent orbit-level
proposal, acceptance and P/Q relabelling coins complete the construction.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

namespace EndpointOriginalReservoir

noncomputable section

/-- A finite probability distribution represented by real point weights. -/
structure FiniteLaw (A : Type*) [Fintype A] where
  weight : A → ℝ
  nonneg : ∀ a, 0 ≤ weight a
  total : ∑ a, weight a = 1

def eventMass {A : Type*} [Fintype A] (w : A → ℝ) (E : A → Prop) : ℝ :=
  ∑ a, if E a then w a else 0

def productWeight {A B : Type*} (u : A → ℝ) (v : B → ℝ) : A × B → ℝ :=
  fun ab ↦ u ab.1 * v ab.2

theorem total_productWeight {A B : Type*} [Fintype A] [Fintype B]
    (u : A → ℝ) (v : B → ℝ) :
    ∑ z, productWeight u v z = (∑ a, u a) * (∑ b, v b) := by
  simp only [productWeight, Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]

theorem eventMass_product {A B : Type*} [Fintype A] [Fintype B]
    (u : A → ℝ) (v : B → ℝ) (E : A → Prop) (F : B → Prop) :
    eventMass (productWeight u v) (fun z ↦ E z.1 ∧ F z.2) =
      eventMass u E * eventMass v F := by
  unfold eventMass productWeight
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hE : E a <;> by_cases hF : F b <;> simp [hE, hF]

theorem eventMass_congr {A : Type*} [Fintype A] (w : A → ℝ)
    {E F : A → Prop} (h : ∀ a, E a ↔ F a) : eventMass w E = eventMass w F := by
  unfold eventMass
  apply Finset.sum_congr rfl
  intro a ha
  simp [h a]

@[simp] theorem eventMass_true {A : Type*} [Fintype A] (w : A → ℝ) :
    eventMass w (fun _ ↦ True) = ∑ a, w a := by simp [eventMass]

@[simp] theorem eventMass_eq {A : Type*} [Fintype A] (w : A → ℝ) (a : A) :
    eventMass w (fun x ↦ x = a) = w a := by simp [eventMass]

def FiniteLaw.prod {A B : Type*} [Fintype A] [Fintype B]
    (u : FiniteLaw A) (v : FiniteLaw B) : FiniteLaw (A × B) where
  weight := productWeight u.weight v.weight
  nonneg := fun z ↦ mul_nonneg (u.nonneg z.1) (v.nonneg z.2)
  total := by rw [total_productWeight, u.total, v.total, one_mul]

def FiniteLaw.pmf {A : Type*} [Fintype A] (u : FiniteLaw A) : PMF A :=
  PMF.ofFintype (fun a ↦ ENNReal.ofReal (u.weight a)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ ↦ u.nonneg a), u.total]
    norm_num)

def FiniteLaw.measure {A : Type*} [Fintype A] [MeasurableSpace A]
    (u : FiniteLaw A) : Measure A := u.pmf.toMeasure

instance {A : Type*} [Fintype A] [MeasurableSpace A] (u : FiniteLaw A) :
    IsProbabilityMeasure u.measure := by unfold FiniteLaw.measure; infer_instance

theorem FiniteLaw.real_event {A : Type*} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (u : FiniteLaw A) (E : A → Prop) :
    u.measure.real {a | E a} = eventMass u.weight E := by
  rw [measureReal_def, FiniteLaw.measure, PMF.toMeasure_apply_fintype,
    ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro a ha
    by_cases h : E a <;>
      simp [h, FiniteLaw.pmf, PMF.ofFintype_apply,
        ENNReal.toReal_ofReal, u.nonneg a]
  · intro a ha
    by_cases h : E a <;>
      simp [h, FiniteLaw.pmf, PMF.ofFintype_apply]

def coinWeight (t : ℝ) : Bool → ℝ := fun b ↦ if b then t else 1 - t

@[simp] theorem sum_coinWeight (t : ℝ) : ∑ b, coinWeight t b = 1 := by
  simp [coinWeight]

def coinLaw (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : FiniteLaw Bool where
  weight := coinWeight t
  nonneg := by intro b; cases b <;> simp [coinWeight] <;> linarith
  total := sum_coinWeight t

abbrev Part := Fin 3

/-- The original disjoint vertex classes: A, B, neither. -/
def vertexWeight (q : ℝ) : Part → ℝ := ![q, q, 1 - 2 * q]

@[simp] theorem sum_vertexWeight (q : ℝ) : ∑ a, vertexWeight q a = 1 := by
  simp [vertexWeight, Fin.sum_univ_succ]
  ring

def vertexLaw (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2) : FiniteLaw Part where
  weight := vertexWeight q
  nonneg := by intro a; fin_cases a <;> simp [vertexWeight] <;> linarith
  total := sum_vertexWeight q

/-- Original vertex role, original colour, and independent A/B/C thinning coins. -/
abbrev Coordinate := Part × (Bool × (Bool × (Bool × Bool)))

def coordinateWeight (q η : ℝ) : Coordinate → ℝ :=
  productWeight (vertexWeight q)
    (productWeight (coinWeight q)
      (productWeight (coinWeight η) (productWeight (coinWeight η) (coinWeight η))))

theorem sum_coordinateWeight (q η : ℝ) : ∑ s, coordinateWeight q η s = 1 := by
  simp only [coordinateWeight, total_productWeight, sum_vertexWeight, sum_coinWeight, mul_one]

def coordinateLaw (q η : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) : FiniteLaw Coordinate :=
  (vertexLaw q hq0 hq1).prod ((coinLaw q hq0 (by linarith)).prod
    ((coinLaw η hη0 hη1).prod ((coinLaw η hη0 hη1).prod (coinLaw η hη0 hη1))))

@[simp] theorem coordinateLaw_weight (q η : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    (coordinateLaw q η hq0 hq1 hη0 hη1).weight = coordinateWeight q η := rfl

def originalRole (a : Part) (s : Coordinate) : Prop :=
  if a = 0 then s.1 = 0 else if a = 1 then s.1 = 1 else s.2.1 = true

def thinningCoin (a : Part) (s : Coordinate) : Bool :=
  if a = 0 then s.2.2.1 else if a = 1 then s.2.2.2.1 else s.2.2.2.2

def rawMinus (a : Part) (s : Coordinate) : Prop :=
  originalRole a s ∧ thinningCoin a s = true

def rawPlus (a : Part) (s : Coordinate) : Prop :=
  originalRole a s ∧ thinningCoin a s = false

theorem original_vertex_disjoint (s : Coordinate) :
    ¬ (originalRole 0 s ∧ originalRole 1 s) := by
  simp only [originalRole, ↓reduceIte]
  rintro ⟨h0,h1⟩
  have he := h0.symm.trans h1
  norm_num at he

theorem raw_roles_partition (a : Part) (s : Coordinate) :
    (rawMinus a s ∨ rawPlus a s) ↔ originalRole a s := by
  unfold rawMinus rawPlus
  cases thinningCoin a s <;> simp

theorem raw_minus_plus_disjoint (a : Part) (s : Coordinate) :
    ¬ (rawMinus a s ∧ rawPlus a s) := by
  rintro ⟨⟨_,hm⟩,⟨_,hp⟩⟩
  have he := hm.symm.trans hp
  cases he

/-- Original Bernoulli marginals are derived from the categorical product law. -/
theorem originalRole_mass (q η : ℝ) (a : Part) :
    eventMass (coordinateWeight q η) (originalRole a) = q := by
  fin_cases a <;>
    simp [eventMass, coordinateWeight, productWeight, originalRole,
      Fintype.sum_prod_type, vertexWeight, coinWeight,
      Fin.sum_univ_succ] <;> ring

/-- Exact minus marginals from original variables and thinning coins. -/
theorem rawMinus_mass (q η : ℝ) (a : Part) :
    eventMass (coordinateWeight q η) (rawMinus a) = η * q := by
  fin_cases a <;>
    simp [eventMass, coordinateWeight, productWeight, originalRole, rawMinus, thinningCoin,
      Fintype.sum_prod_type, vertexWeight, coinWeight,
      Fin.sum_univ_succ] <;> ring

theorem rawPlus_mass (q η : ℝ) (a : Part) :
    eventMass (coordinateWeight q η) (rawPlus a) = (1 - η) * q := by
  fin_cases a <;>
    simp [eventMass, coordinateWeight, productWeight, originalRole, rawPlus, thinningCoin,
      Fintype.sum_prod_type, vertexWeight, coinWeight,
      Fin.sum_univ_succ] <;> ring

/-- The full five-way vertex law; it retains categorical dependence. -/
def refinedVertex (s : Coordinate) : Fin 5 :=
  if s.1 = 0 then (if s.2.2.1 then 0 else 1)
  else if s.1 = 1 then (if s.2.2.2.1 then 2 else 3) else 4

def refinedVertexWeight (q η : ℝ) : Fin 5 → ℝ :=
  ![η*q, (1-η)*q, η*q, (1-η)*q, 1-2*q]

theorem refinedVertex_mass (q η : ℝ) (l : Fin 5) :
    eventMass (coordinateWeight q η) (fun s ↦ refinedVertex s = l) =
      refinedVertexWeight q η l := by
  fin_cases l <;>
    simp [eventMass, coordinateWeight, productWeight, refinedVertex, refinedVertexWeight,
      Fintype.sum_prod_type, vertexWeight, coinWeight,
      Fin.sum_univ_succ] <;> ring

/-- P, Q, unused relabelling; a and b are the conditional probabilities. -/
def childWeight (a b : ℝ) : Part → ℝ := ![a, b, 1 - a - b]

@[simp] theorem sum_childWeight (a b : ℝ) : ∑ l, childWeight a b l = 1 := by
  simp [childWeight, Fin.sum_univ_succ]

def childLaw (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) : FiniteLaw Part where
  weight := childWeight a b
  nonneg := by intro l; fin_cases l <;> simp [childWeight] <;> linarith
  total := sum_childWeight a b

def proposalWeight : Part → ℝ := fun _ ↦ 1 / 3

@[simp] theorem sum_proposalWeight : ∑ l, proposalWeight l = 1 := by
  norm_num [proposalWeight, Fin.sum_univ_succ]

def proposalLaw : FiniteLaw Part where
  weight := proposalWeight
  nonneg := by intro l; norm_num [proposalWeight]
  total := sum_proposalWeight

/-- Two original coordinates, then independent proposal, accept, and child coins. -/
abbrev OrbitInput := Coordinate × (Coordinate × (Part × (Bool × Part)))

def orbitInputWeight (q η a b : ℝ) : OrbitInput → ℝ :=
  productWeight (coordinateWeight q η)
    (productWeight (coordinateWeight q η)
      (productWeight proposalWeight (productWeight (coinWeight (1/3)) (childWeight a b))))

def orbitInputLaw (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1) : FiniteLaw OrbitInput :=
  (coordinateLaw q η hq0 hq1 hη0 hη1).prod
    ((coordinateLaw q η hq0 hq1 hη0 hη1).prod
      (proposalLaw.prod ((coinLaw (1/3) (by norm_num) (by norm_num)).prod
        (childLaw a b ha hb hab))))

@[simp] theorem orbitInputLaw_weight (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1) :
    (orbitInputLaw q η a b hq0 hq1 hη0 hη1 ha hb hab).weight =
      orbitInputWeight q η a b := rfl

def accepted (part : Part) (s : OrbitInput) : Prop :=
  rawMinus part s.1 ∧ rawMinus part s.2.1 ∧ s.2.2.1 = part ∧ s.2.2.2.1 = true

def parentLabel (s : OrbitInput) : Option Part :=
  if accepted s.2.2.1 s then some s.2.2.1 else none

def childLabel (s : OrbitInput) : Option (Part × Bool) :=
  if accepted s.2.2.1 s then
    if s.2.2.2.2 = 0 then some (s.2.2.1, false)
    else if s.2.2.2.2 = 1 then some (s.2.2.1, true) else none
  else none

def rho (q η : ℝ) : ℝ := (η*q)^2 / 9

theorem parentLabel_eq_iff (s : OrbitInput) (part : Part) :
    parentLabel s = some part ↔ accepted part s := by
  unfold parentLabel
  by_cases h : accepted s.2.2.1 s
  · simp only [h, if_true, Option.some.injEq]
    constructor
    · intro hp; simpa [hp] using h
    · intro hp; exact hp.2.2.1
  · simp only [h, if_false, reduceCtorEq, false_iff]
    intro hp
    exact h (by simpa [hp.2.2.1] using hp)

theorem accepted_mass (q η a b : ℝ) (part : Part) :
    eventMass (orbitInputWeight q η a b) (accepted part) = rho q η := by
  have he : accepted part = (fun s : OrbitInput ↦ rawMinus part s.1 ∧
      (rawMinus part s.2.1 ∧ (s.2.2.1 = part ∧ (s.2.2.2.1 = true ∧ True)))) := by
    funext s; simp [accepted]
  rw [he]
  unfold orbitInputWeight
  rw [eventMass_product _ _ (rawMinus part)
    (fun t : Coordinate × (Part × (Bool × Part)) ↦
      rawMinus part t.1 ∧ t.2.1 = part ∧ t.2.2.1 = true ∧ True)]
  rw [eventMass_product _ _ (rawMinus part)
    (fun t : Part × (Bool × Part) ↦ t.1 = part ∧ t.2.1 = true ∧ True)]
  rw [eventMass_product _ _ (fun t : Part ↦ t = part)
    (fun t : Bool × Part ↦ t.1 = true ∧ True)]
  rw [eventMass_product _ _ (fun t : Bool ↦ t = true) (fun _ : Part ↦ True)]
  simp only [rawMinus_mass, eventMass_eq, eventMass_true, sum_childWeight,
    proposalWeight, coinWeight, if_true, rho]
  ring

theorem parentLabel_mass (q η a b : ℝ) (part : Part) :
    eventMass (orbitInputWeight q η a b) (fun s ↦ parentLabel s = some part) = rho q η := by
  rw [eventMass_congr _ (fun s ↦ parentLabel_eq_iff s part)]
  exact accepted_mass q η a b part

theorem childLabel_P_iff (s : OrbitInput) (part : Part) :
    childLabel s = some (part, false) ↔ accepted part s ∧ s.2.2.2.2 = 0 := by
  unfold childLabel
  by_cases h : accepted s.2.2.1 s
  · by_cases hp : s.2.2.2.2 = 0
    · simp only [h, hp, if_true, Option.some.injEq, Prod.mk.injEq, and_true]
      constructor
      · intro he; simpa [he] using h
      · intro he; exact he.2.2.1
    · simp [h, hp]
  · simp only [h, if_false, reduceCtorEq, false_iff, not_and]
    intro hp _
    exact h (by simpa [hp.2.2.1] using hp)

theorem childLabel_Q_iff (s : OrbitInput) (part : Part) :
    childLabel s = some (part, true) ↔ accepted part s ∧ s.2.2.2.2 = 1 := by
  unfold childLabel
  by_cases h : accepted s.2.2.1 s
  · by_cases hp : s.2.2.2.2 = 0
    · simp [h, hp]
    · by_cases hq : s.2.2.2.2 = 1
      · simp only [h, hq, if_pos, if_false, Fin.isValue,
          show (1 : Part) ≠ 0 by decide, Option.some.injEq, Prod.mk.injEq, and_true]
        constructor
        · intro he; simpa [he] using h
        · intro he; exact he.2.2.1
      · simp [h, hp, hq]
  · simp only [h, if_false, reduceCtorEq, false_iff, not_and]
    intro hp _
    exact h (by simpa [hp.2.2.1] using hp)

theorem accepted_child_mass (q η a b : ℝ) (part child : Part) :
    eventMass (orbitInputWeight q η a b)
      (fun s ↦ accepted part s ∧ s.2.2.2.2 = child) =
      rho q η * childWeight a b child := by
  have he : (fun s : OrbitInput ↦ accepted part s ∧ s.2.2.2.2 = child) =
      (fun s : OrbitInput ↦ rawMinus part s.1 ∧ (rawMinus part s.2.1 ∧
        (s.2.2.1 = part ∧ (s.2.2.2.1 = true ∧ s.2.2.2.2 = child)))) := by
    funext s; simp [accepted, and_assoc]
  rw [he]
  unfold orbitInputWeight
  rw [eventMass_product _ _ (rawMinus part)
    (fun t : Coordinate × (Part × (Bool × Part)) ↦
      rawMinus part t.1 ∧ t.2.1 = part ∧ t.2.2.1 = true ∧ t.2.2.2 = child)]
  rw [eventMass_product _ _ (rawMinus part)
    (fun t : Part × (Bool × Part) ↦ t.1 = part ∧ t.2.1 = true ∧ t.2.2 = child)]
  rw [eventMass_product _ _ (fun t : Part ↦ t = part)
    (fun t : Bool × Part ↦ t.1 = true ∧ t.2 = child)]
  rw [eventMass_product _ _ (fun t : Bool ↦ t = true) (fun t : Part ↦ t = child)]
  simp only [rawMinus_mass, eventMass_eq, proposalWeight, coinWeight, if_true, rho]
  ring

theorem childLabel_P_mass (q η a b : ℝ) (part : Part) :
    eventMass (orbitInputWeight q η a b) (fun s ↦ childLabel s = some (part,false)) =
      rho q η * a := by
  rw [eventMass_congr _ (fun s ↦ childLabel_P_iff s part), accepted_child_mass]
  simp [childWeight]

theorem childLabel_Q_mass (q η a b : ℝ) (part : Part) :
    eventMass (orbitInputWeight q η a b) (fun s ↦ childLabel s = some (part,true)) =
      rho q η * b := by
  rw [eventMass_congr _ (fun s ↦ childLabel_Q_iff s part), accepted_child_mass]
  simp [childWeight]

/-- The signs (-R1,R2,-R3): false is g and true is -g. -/
def signedRawMinus (part : Part) (side : Bool) (s : OrbitInput) : Prop :=
  rawMinus part (if (if part = 1 then side else !side) then s.2.1 else s.1)

theorem accepted_signed_membership (s : OrbitInput) (part : Part) (side : Bool)
    (h : accepted part s) : signedRawMinus part side s := by
  unfold signedRawMinus
  split_ifs <;> first | exact h.1 | exact h.2.1

theorem child_subset_parent (s : OrbitInput) (part : Part) (kind : Bool)
    (h : childLabel s = some (part,kind)) : parentLabel s = some part := by
  apply (parentLabel_eq_iff s part).2
  cases kind
  · exact ((childLabel_P_iff s part).1 h).1
  · exact ((childLabel_Q_iff s part).1 h).1

theorem child_signed_membership (s : OrbitInput) (part : Part) (kind side : Bool)
    (h : childLabel s = some (part,kind)) : signedRawMinus part side s := by
  exact accepted_signed_membership s part side
    ((parentLabel_eq_iff s part).1 (child_subset_parent s part kind h))

/-- Categorical exclusion is literal exclusivity, including across parts. -/
theorem child_labels_disjoint (s : OrbitInput) (l k : Part × Bool) (hne : l ≠ k) :
    ¬ (childLabel s = some l ∧ childLabel s = some k) := by
  rintro ⟨hl,hk⟩
  exact hne (Option.some.inj (hl.symm.trans hk))

instance parentLabelMeasurableSpace : MeasurableSpace (Option Part) := ⊤
instance parentLabelMeasurableSingleton : MeasurableSingletonClass (Option Part) := ⟨fun _ ↦ trivial⟩
instance childLabelMeasurableSpace : MeasurableSpace (Option (Part × Bool)) := ⊤
instance childLabelMeasurableSingleton : MeasurableSingletonClass (Option (Part × Bool)) :=
  ⟨fun _ ↦ trivial⟩

/-- Original coordinates and all orbit coins are sampled before output labels. -/
def originalProductMeasure {O : Type*} [Fintype O]
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1) :
    Measure (O → OrbitInput) :=
  Measure.pi (fun _ ↦ (orbitInputLaw q η a b hq0 hq1 hη0 hη1 ha hb hab).measure)

theorem original_to_independent_parent_labels {O : Type*} [Fintype O]
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1) :
    iIndepFun (fun o (ω : O → OrbitInput) ↦ parentLabel (ω o))
      (originalProductMeasure q η a b hq0 hq1 hη0 hη1 ha hb hab) := by
  exact iIndepFun_pi (X := fun _ ↦ parentLabel) (fun _ ↦ by fun_prop)

theorem original_to_independent_child_labels {O : Type*} [Fintype O]
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1) :
    iIndepFun (fun o (ω : O → OrbitInput) ↦ childLabel (ω o))
      (originalProductMeasure q η a b hq0 hq1 hη0 hη1 ha hb hab) := by
  exact iIndepFun_pi (X := fun _ ↦ childLabel) (fun _ ↦ by fun_prop)

theorem original_to_P_probability (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1)
    (part : Part) :
    (orbitInputLaw q η a b hq0 hq1 hη0 hη1 ha hb hab).measure.real
      {s | childLabel s = some (part,false)} = rho q η * a := by
  rw [FiniteLaw.real_event, orbitInputLaw_weight, childLabel_P_mass]

theorem original_to_Q_probability (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1)
    (part : Part) :
    (orbitInputLaw q η a b hq0 hq1 hη0 hη1 ha hb hab).measure.real
      {s | childLabel s = some (part,true)} = rho q η * b := by
  rw [FiniteLaw.real_event, orbitInputLaw_weight, childLabel_Q_mass]

/-- Full original vertex/colour joint law, before thinning. -/
theorem original_vertex_colour_joint_mass (q η : ℝ) (v : Part) (c : Bool) :
    eventMass (coordinateWeight q η) (fun s ↦ s.1 = v ∧ s.2.1 = c) =
      vertexWeight q v * coinWeight q c := by
  fin_cases v <;> cases c <;>
    simp [eventMass, coordinateWeight, productWeight, Fintype.sum_prod_type,
      vertexWeight, coinWeight] <;> ring

theorem sum_eventMass_fibers {A B : Type*} [Fintype A] [Fintype B]
    (w : A → ℝ) (f : A → B) :
    ∑ b, eventMass w (fun a ↦ f a = b) = ∑ a, w a := by
  unfold eventMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  simp

theorem sum_orbitInputWeight (q η a b : ℝ) : ∑ s, orbitInputWeight q η a b s = 1 := by
  simp only [orbitInputWeight, total_productWeight, sum_coordinateWeight,
    sum_proposalWeight, sum_coinWeight, sum_childWeight, mul_one]

theorem parentLabel_none_mass (q η a b : ℝ) :
    eventMass (orbitInputWeight q η a b) (fun s ↦ parentLabel s = none) = 1 - 3*rho q η := by
  have ht := sum_eventMass_fibers (orbitInputWeight q η a b) parentLabel
  rw [sum_orbitInputWeight, Fintype.sum_option] at ht
  simp only [parentLabel_mass, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_ofNat] at ht
  linarith

theorem childLabel_none_mass (q η a b : ℝ) :
    eventMass (orbitInputWeight q η a b) (fun s ↦ childLabel s = none) =
      1 - 3*rho q η*(a+b) := by
  have ht := sum_eventMass_fibers (orbitInputWeight q η a b) childLabel
  rw [sum_orbitInputWeight, Fintype.sum_option, Fintype.sum_prod_type] at ht
  simp only [Fintype.sum_bool, childLabel_P_mass, childLabel_Q_mass, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] at ht
  linarith

/-- Independence holds for the whole nested label, not just separate marginals. -/
theorem original_to_independent_joint_labels {O : Type*} [Fintype O]
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1) :
    iIndepFun (fun o (ω : O → OrbitInput) ↦ (parentLabel (ω o), childLabel (ω o)))
      (originalProductMeasure q η a b hq0 hq1 hη0 hη1 ha hb hab) := by
  exact iIndepFun_pi (X := fun _ s ↦ (parentLabel s, childLabel s)) (fun _ ↦ by fun_prop)

theorem original_to_parent_probability (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1)
    (part : Part) :
    (orbitInputLaw q η a b hq0 hq1 hη0 hη1 ha hb hab).measure.real
      {s | parentLabel s = some part} = rho q η := by
  rw [FiniteLaw.real_event, orbitInputLaw_weight, parentLabel_mass]

theorem ratio_relabelling (q η p τ : ℝ) (hr : 0 < rho q η)
    (hp : 0 ≤ p) (hτ : 0 ≤ τ) (hpτ : p+τ ≤ rho q η) :
    0 ≤ p / rho q η ∧ 0 ≤ τ / rho q η ∧ p / rho q η + τ / rho q η ≤ 1 ∧
      rho q η * (p / rho q η) = p ∧ rho q η * (τ / rho q η) = τ := by
  refine ⟨div_nonneg hp hr.le, div_nonneg hτ hr.le, ?_, ?_, ?_⟩
  · rw [← add_div]
    exact (div_le_one hr).2 hpτ
  · field_simp
  · field_simp

end
end EndpointOriginalReservoir
