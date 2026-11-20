import CorralFormalization.EndpointProof.Probability.PairInventoryCounts
import CorralFormalization.EndpointProof.Matching.UniversalCore.PairedCoverInventory
import CorralFormalization.EndpointProof.Matching.UniversalCore.QuadraticCapacityBudget

/-!
Exact conversion of the categorical orbit counts to the core's physical
pair inventories. Numerical deletion removes at most |U| pairs in total
across the three parts of either fixed P/Q kind. All statements are
pointwise, and hence apply to arbitrary U chosen after a single count event.
-/

open scoped Classical BigOperators NNReal
namespace EndpointMatching.UniversalCore
open EndpointFlow.AbelianTransport
open EndpointSelector.FixedCardinality
open EndpointFullProduct EndpointOriginalReservoir EndpointBlockAvailability
open EndpointSharedSample EndpointReservoirAvailability EndpointPairInventoryCounts
noncomputable section
variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- One actual tagged inverse pair for one numerical inverse orbit. -/
def orbitPair (part : Fin 3) (o : OddOrbit G) : Finset (Vertex G) :=
  pairOf (part,orbitPlace (o,false))

theorem orbitPair_injective (part : Fin 3) : Function.Injective (orbitPair (G := G) part) := by
  intro o o' he
  have hm : (part,orbitPlace (o,false)) ∈ orbitPair part o' := by
    rw [← he]
    exact pairOf_mem _
  simp only [orbitPair, pairOf, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq,
    true_and] at hm
  rcases hm with hm | hm
  · exact congrArg Prod.fst (orbitPlace.injective hm)
  · have he' : orbitPlace (o,false) = orbitPlace (o',true) :=
      hm.trans (by simpa using (orbitPlace_neg o' false).symm)
    exact congrArg Prod.fst (orbitPlace.injective he')

def survivingPairOrbits (w : OddOrbit G → Label) (part : Fin 3) (kind : Bool)
    (U : Finset G) : Finset (OddOrbit G) :=
  (pairOrbitSet w part kind).filter (fun o =>
    orbitPlace (o,false) ∉ U ∧ orbitPlace (o,true) ∉ U)

/-- The existing availablePairInventory is exactly the image of surviving
categorical orbit labels. This works for P and Q on the same sample. -/
theorem availablePairInventory_eq_surviving (ω : FullSample G)
    (U : Finset G) (part : Fin 3) (kind : Bool) :
    availablePairInventory (ReservoirVertex ω kind) U part =
      (survivingPairOrbits (fullLabels ω) part kind U).image (orbitPair part) := by
  ext T
  constructor
  · intro hT
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hT
    have ha' := (Finset.mem_filter.mp ha).2
    obtain ⟨o,side,ho,hl⟩ := ha'.1
    have hlabel : fullLabels ω o = pairLabel part kind := congrArg encodeChild hl
    refine Finset.mem_image.mpr ⟨o,Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hlabel⟩,?_⟩,?_⟩
    · cases side with
      | false =>
        refine ⟨by simpa only [ho] using ha'.2.1, ?_⟩
        simpa only [show orbitPlace (o,true) = -orbitPlace (o,false) from orbitPlace_neg o false,
          ho] using ha'.2.2
      | true =>
        refine ⟨?_, by simpa only [ho] using ha'.2.1⟩
        have hn : orbitPlace (o,false) = -a := by
          simpa only [Bool.not_true] using (orbitPlace_neg o true).trans (congrArg Neg.neg ho)
        simpa only [hn] using ha'.2.2
    · cases side with
      | false => simp only [orbitPair,ho]
      | true =>
        have hneg : orbitPlace (o,false) = -a := by
          simpa only [Bool.not_true] using (orbitPlace_neg o true).trans (congrArg Neg.neg ho)
        simp [orbitPair,pairOf,hneg,Finset.pair_comm]
  · intro hT
    obtain ⟨o,ho,rfl⟩ := Finset.mem_image.mp hT
    have hs := Finset.mem_filter.mp ho
    have hl := (Finset.mem_filter.mp hs.1).2
    have hchild : childLabel ((regroup ω).1 o) = some (part,kind) :=
      encodeChild_bijective.injective hl
    apply Finset.mem_image.mpr
    refine ⟨orbitPlace (o,false),Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,⟨o,false,rfl,hchild⟩,hs.2.1,?_⟩,rfl⟩
    simpa only [← show orbitPlace (o,true) = -orbitPlace (o,false) from orbitPlace_neg o false]
      using hs.2.2

/-- Cardinality equality avoids any factor-of-two ambiguity between tagged
vertices and physical inverse pairs. -/
theorem availablePairInventory_card_eq_surviving (ω : FullSample G)
    (U : Finset G) (part : Fin 3) (kind : Bool) :
    (availablePairInventory (ReservoirVertex ω kind) U part).card =
      (survivingPairOrbits (fullLabels ω) part kind U).card := by
  rw [availablePairInventory_eq_surviving]
  exact Finset.card_image_of_injective _ (orbitPair_injective part)

/-- With no numerical deletion, the sampled orbit count is exactly the
cardinality of the existing physical pair inventory. -/
theorem availablePairInventory_empty_card (ω : FullSample G) (part : Fin 3) (kind : Bool) :
    (availablePairInventory (ReservoirVertex ω kind) ∅ part).card = sampledPairCount ω part kind := by
  rw [availablePairInventory_card_eq_surviving]
  simp [survivingPairOrbits, sampledPairCount]

/-- A deterministic numerical set meets at most |U| distinct inverse
orbits. Choosing the sign inside U gives an injection into U. -/
def hitOrbits (U : Finset G) : Finset (OddOrbit G) :=
  Finset.univ.filter (fun o => orbitPlace (o,false) ∈ U ∨ orbitPlace (o,true) ∈ U)

def hitSide (U : Finset G) (o : OddOrbit G) : Bool :=
  if orbitPlace (o,false) ∈ U then false else true

theorem hitOrbits_card_le (U : Finset G) : (hitOrbits U).card ≤ U.card := by
  apply Finset.card_le_card_of_injOn (fun o => orbitPlace (o,hitSide U o))
  · intro o ho
    have hh := (Finset.mem_filter.mp ho).2
    dsimp only [hitSide]
    split_ifs with h
    · exact h
    · exact hh.resolve_left h
  · intro o _ o' _ he
    exact congrArg Prod.fst (orbitPlace.injective he)

def deletedPairOrbits (w : OddOrbit G → Label) (part : Fin 3) (kind : Bool)
    (U : Finset G) : Finset (OddOrbit G) :=
  pairOrbitSet w part kind \ survivingPairOrbits w part kind U

theorem deletedPairOrbits_subset_hit (w : OddOrbit G → Label) (part : Fin 3)
    (kind : Bool) (U : Finset G) : deletedPairOrbits w part kind U ⊆ hitOrbits U := by
  intro o ho
  obtain ⟨hop,hos⟩ := Finset.mem_sdiff.mp ho
  have hhit : orbitPlace (o,false) ∈ U ∨ orbitPlace (o,true) ∈ U := by
    by_contra h
    apply hos
    exact Finset.mem_filter.mpr ⟨hop,by simpa only [not_or] using h⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hhit⟩

theorem pairLabel_injective (kind : Bool) : Function.Injective (fun p => pairLabel p kind) := by
  intro p q h
  exact congrArg Prod.fst (Option.some.inj (encodeChild_bijective.injective h))

/-- The categorical law puts each numerical orbit into at most one part
for a fixed P/Q kind, so losses sum to at most |U| across all three parts. -/
theorem total_deletedPairOrbits_le (w : OddOrbit G → Label) (kind : Bool) (U : Finset G) :
    (∑ part : Fin 3, (deletedPairOrbits w part kind U).card) ≤ U.card := by
  have hdis : (↑(Finset.univ : Finset (Fin 3)) : Set (Fin 3)).PairwiseDisjoint
      (fun part => deletedPairOrbits w part kind U) := by
    intro part _ part' _ hne
    apply Finset.disjoint_left.mpr
    intro o ho ho'
    have hl := (Finset.mem_filter.mp (Finset.mem_sdiff.mp ho).1).2
    have hl' := (Finset.mem_filter.mp (Finset.mem_sdiff.mp ho').1).2
    exact hne (pairLabel_injective kind (hl.symm.trans hl'))
  have hsub : Finset.univ.biUnion (fun part : Fin 3 => deletedPairOrbits w part kind U) ⊆
      hitOrbits U := by
    intro o ho
    obtain ⟨part,_,hpart⟩ := Finset.mem_biUnion.mp ho
    exact deletedPairOrbits_subset_hit w part kind U hpart
  calc
    _ = (Finset.univ.biUnion (fun part : Fin 3 => deletedPairOrbits w part kind U)).card :=
      (Finset.card_biUnion hdis).symm
    _ ≤ (hitOrbits U).card := Finset.card_le_card hsub
    _ ≤ U.card := hitOrbits_card_le U

/-- Deletion cannot increase a part's physical inverse-pair inventory. -/
theorem availablePairInventory_card_le_count (ω : FullSample G) (U : Finset G)
    (part : Fin 3) (kind : Bool) :
    (availablePairInventory (ReservoirVertex ω kind) U part).card ≤ sampledPairCount ω part kind := by
  rw [availablePairInventory_card_eq_surviving]
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- Exact lost-pair identity for one part. -/
theorem availablePairInventory_loss_eq (ω : FullSample G) (U : Finset G)
    (part : Fin 3) (kind : Bool) :
    sampledPairCount ω part kind - (availablePairInventory (ReservoirVertex ω kind) U part).card =
      (deletedPairOrbits (fullLabels ω) part kind U).card := by
  rw [availablePairInventory_card_eq_surviving]
  exact (Finset.card_sdiff_of_subset (Finset.filter_subset _ _)).symm

/-- The numerical deletion invoice is global across the three parts,
not a separate |U| charge in each part. It holds for every later U. -/
theorem availablePairInventory_total_loss_le (ω : FullSample G) (U : Finset G) (kind : Bool) :
    (∑ part : Fin 3, (sampledPairCount ω part kind -
      (availablePairInventory (ReservoirVertex ω kind) U part).card)) ≤ U.card := by
  simp_rw [availablePairInventory_loss_eq]
  exact total_deletedPairOrbits_le (fullLabels ω) kind U

/-- Each individual part also loses at most |U| pairs, in additive form
that avoids truncated subtraction when deriving real lower bounds. -/
theorem count_le_availablePairInventory_add (ω : FullSample G) (U : Finset G)
    (part : Fin 3) (kind : Bool) :
    sampledPairCount ω part kind ≤
      (availablePairInventory (ReservoirVertex ω kind) U part).card + U.card := by
  have hcard := availablePairInventory_card_le_count ω U part kind
  have hsum := availablePairInventory_total_loss_le ω U kind
  have hpart : sampledPairCount ω part kind -
      (availablePairInventory (ReservoirVertex ω kind) U part).card ≤ U.card := by
    exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ part)).trans hsum
  omega

/-- Exact real bounds obtained from the common count event after any
later U, before coarse pair-availability constants are chosen. -/
theorem inventory_bounds_of_pairCountEvent (p τ : ℝ≥0) (ω : FullSample G)
    (hevent : PairCountEvent p τ ω) (U : Finset G) (part : Fin 3) (kind : Bool) :
    (pairDensity p τ kind : ℝ)*((Fintype.card G : ℝ)-1)/2 -
      (pairDensity p τ kind : ℝ)*(Fintype.card G : ℝ)/12 - (U.card : ℝ) ≤
        ((availablePairInventory (ReservoirVertex ω kind) U part).card : ℝ) ∧
    ((availablePairInventory (ReservoirVertex ω kind) U part).card : ℝ) ≤
      (pairDensity p τ kind : ℝ)*((Fintype.card G : ℝ)-1)/2 +
        (pairDensity p τ kind : ℝ)*(Fintype.card G : ℝ)/12 := by
  have hb := abs_le.mp (hevent part kind)
  have hl : (sampledPairCount ω part kind : ℝ) ≤
      ((availablePairInventory (ReservoirVertex ω kind) U part).card : ℝ) + U.card := by
    exact_mod_cast count_le_availablePairInventory_add ω U part kind
  have hu : ((availablePairInventory (ReservoirVertex ω kind) U part).card : ℝ) ≤
      (sampledPairCount ω part kind : ℝ) := by
    exact_mod_cast availablePairInventory_card_le_count ω U part kind
  constructor <;> linarith

/-- pair-availability with an explicit sufficient threshold: n≥7 and |U|≤τn/100.
The statement is pointwise in an arbitrary later U, after the common event. -/
theorem qInventory_bounds_of_pairCountEvent (p τ : ℝ≥0) (ω : FullSample G)
    (hevent : PairCountEvent p τ ω) (hn : 7 ≤ Fintype.card G)
    (U : Finset G) (hU : (U.card : ℝ) ≤ (τ : ℝ)*(Fintype.card G : ℝ)/100)
    (part : Fin 3) :
    (τ : ℝ)*(Fintype.card G : ℝ)/3 ≤
      ((availablePairInventory (ReservoirVertex ω true) U part).card : ℝ) ∧
    ((availablePairInventory (ReservoirVertex ω true) U part).card : ℝ) ≤
      (τ : ℝ)*(Fintype.card G : ℝ) := by
  have hb := inventory_bounds_of_pairCountEvent p τ ω hevent U part true
  simp only [pairDensity, ↓reduceIte] at hb
  have hn' : (7 : ℝ) ≤ (Fintype.card G : ℝ) := by exact_mod_cast hn
  have hslack := mul_nonneg (NNReal.coe_nonneg τ)
    (show 0 ≤ 11*(Fintype.card G : ℝ)-75 by linarith)
  have hnonneg := mul_nonneg (NNReal.coe_nonneg τ) (Nat.cast_nonneg (Fintype.card G) :
    (0 : ℝ) ≤ Fintype.card G)
  constructor <;> nlinarith

/-- The P assertion following pair-inventory concerns actual physical P pairs:
at n≥6 each tagged part has between pn/3 and pn such pairs. -/
theorem pInventory_empty_linear_bounds (p τ : ℝ≥0) (ω : FullSample G)
    (hevent : PairCountEvent p τ ω) (hn : 6 ≤ Fintype.card G) (part : Fin 3) :
    (p : ℝ)*(Fintype.card G : ℝ)/3 ≤
      ((availablePairInventory (ReservoirVertex ω false) ∅ part).card : ℝ) ∧
    ((availablePairInventory (ReservoirVertex ω false) ∅ part).card : ℝ) ≤
      (p : ℝ)*(Fintype.card G : ℝ) := by
  rw [availablePairInventory_empty_card]
  simpa only [pairDensity, Bool.false_eq_true, ↓reduceIte] using
    pairCountEvent_linear_bounds p τ ω hevent hn part false

/-- Exactly the uniform Q-inventory input consumed by the quadratic core.
This definition puts every U after the single sample event. -/
def QPairInventoryEvent (τ : ℝ) (ω : FullSample G) : Prop :=
  ∀ U : Finset G, U.card ≤ quadraticCoreCapacity τ (Fintype.card G) → ∀ part : Fin 3,
    τ*(Fintype.card G : ℝ)/3 ≤
      ((availablePairInventory (ReservoirVertex ω true) U part).card : ℝ) ∧
    ((availablePairInventory (ReservoirVertex ω true) U part).card : ℝ) ≤
      τ*(Fintype.card G : ℝ)

/-- The pair-inventory event supplies the core's exact later-U inventory hypothesis
at its actual floor capacity, with n≥7 and τ≤1/3 explicitly recorded. -/
theorem qInventoryEvent_of_pairCountEvent (p τ : ℝ≥0) (ω : FullSample G)
    (hevent : PairCountEvent p τ ω) (hτmax : (τ : ℝ) ≤ 1/3)
    (hn : 7 ≤ Fintype.card G) : QPairInventoryEvent (τ : ℝ) ω := by
  intro U hU part
  have hc : (quadraticCoreCapacity (τ : ℝ) (Fintype.card G) : ℝ) ≤
      (1/10^6 : ℝ)*(τ : ℝ)^2*(Fintype.card G : ℝ) := by
    unfold quadraticCoreCapacity
    exact Nat.floor_le (by positivity)
  have hUc : (U.card : ℝ) ≤ quadraticCoreCapacity (τ : ℝ) (Fintype.card G) := by
    exact_mod_cast hU
  have hτ1 : (τ : ℝ) ≤ 1 := hτmax.trans (by norm_num)
  have hsquare : (τ : ℝ)^2 ≤ (τ : ℝ) := by
    nlinarith [mul_nonneg (NNReal.coe_nonneg τ) (sub_nonneg.mpr hτ1)]
  have hprod := mul_le_mul_of_nonneg_right hsquare
    (Nat.cast_nonneg (Fintype.card G) : (0 : ℝ) ≤ Fintype.card G)
  have hnonneg := mul_nonneg (NNReal.coe_nonneg τ)
    (Nat.cast_nonneg (Fintype.card G) : (0 : ℝ) ≤ Fintype.card G)
  have hUreal : (U.card : ℝ) ≤ (τ : ℝ)*(Fintype.card G : ℝ)/100 := by
    nlinarith
  exact qInventory_bounds_of_pairCountEvent p τ ω hevent hn U hUreal part

/-- The actual categorical law provides τ≤1/3, so only the stated group
size threshold is needed in this law-specialized inventory probability. -/
theorem qInventoryEvent_failure_probability (hodd : Odd (Fintype.card G))
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1)
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1)
    (hP : (p : ℝ) = rho q η*a) (hQ : (τ : ℝ) = rho q η*b)
    (hn : 7 ≤ Fintype.card G) :
    (fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab).real
      {ω | ¬ QPairInventoryEvent (τ : ℝ) ω} ≤
        6 * Real.exp (-(p : ℝ)^2 * (Fintype.card G : ℝ)/36) +
        6 * Real.exp (-(τ : ℝ)^2 * (Fintype.card G : ℝ)/36) := by
  let μ := fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab
  have hτmax : (τ : ℝ) ≤ 1/3 := by
    have hreal : 3*(p : ℝ)+3*(τ : ℝ) ≤ 1 := by exact_mod_cast h
    nlinarith [NNReal.coe_nonneg p]
  have hsub : {ω : FullSample G | ¬ QPairInventoryEvent (τ : ℝ) ω} ⊆
      {ω | ¬ PairCountEvent p τ ω} := by
    intro ω hbad hgood
    exact hbad (qInventoryEvent_of_pairCountEvent p τ ω hgood hτmax hn)
  exact (MeasureTheory.measureReal_mono hsub (MeasureTheory.measure_ne_top μ _)).trans
    (pairCountEvent_failure_probability hodd q η a b hq0 hq1 hη0 hη1 ha hb hab p τ h hP hQ)

end
end EndpointMatching.UniversalCore
