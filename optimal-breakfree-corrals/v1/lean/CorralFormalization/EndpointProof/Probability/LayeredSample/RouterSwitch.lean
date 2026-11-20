import CorralFormalization.EndpointProof.Probability.LayeredSample.Augmentation
import CorralFormalization.EndpointProof.Factor.LayeredTransitions
import CorralFormalization.EndpointProof.Router.Trials

/-!
Actual switch availability on the reserve augmentation of the layer sample.

The router's flat `(Bool × G) → Bool` process is obtained from the proved
pair of thinned Bernoulli reserve channels by an explicit measure-preserving
map.  The paper budget is the literal natural floor of `b*n`, with
`b=u^22/20000`.  The switch tail is proved, not a new supplier hypothesis.
This file makes no assertion about the router's separate idle operation.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators Classical

set_option autoImplicit false

namespace EndpointLayeredSample

open EndpointOriginalReservoir EndpointFullProduct
open EndpointMatching.Fractional.Rounding

noncomputable section
universe v

/-- Channel `false` is the vertex reserve; channel `true` is the colour
reserve, exactly as in `Switch.requestLocation`. -/
def flattenReserves {G : Type*} (z : (G → Bool) × (G → Bool)) : Bool × G → Bool :=
  fun bg => if bg.1 then z.2 bg.2 else z.1 bg.2

def unflattenReserves {G : Type*} (w : Bool × G → Bool) : (G → Bool) × (G → Bool) :=
  (fun g => w (false, g), fun g => w (true, g))

@[simp] theorem unflatten_flattenReserves {G : Type*} (z : (G → Bool) × (G → Bool)) :
    unflattenReserves (flattenReserves z) = z := by
  cases z
  rfl

@[simp] theorem flatten_unflattenReserves {G : Type*} (w : Bool × G → Bool) :
    flattenReserves (unflattenReserves w) = w := by
  funext bg
  rcases bg with ⟨b, g⟩
  cases b <;> rfl

/-- The two independent numerical channels are the literal independent
product over the router's tagged numerical coordinates. -/
theorem flattenReserves_measurePreserving {G : Type*} [Fintype G]
    (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    MeasurePreserving flattenReserves
      ((Measure.pi fun _ : G => (coinLaw u hu0 hu1).measure).prod
        (Measure.pi fun _ : G => (coinLaw u hu0 hu1).measure))
      (EndpointRouter.Bernoulli.measure (O := Bool × G) u hu0 hu1) := by
  refine ⟨measurable_of_countable _, ?_⟩
  apply Measure.ext_of_singleton
  intro w
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have hpre : flattenReserves ⁻¹' {w} = {unflattenReserves w} := by
    ext z
    change flattenReserves z = w ↔ z = unflattenReserves w
    constructor
    · intro h
      rw [← h, unflatten_flattenReserves]
    · rintro rfl
      exact flatten_unflattenReserves w
  rw [hpre, prod_measure_singleton, Measure.pi_singleton, Measure.pi_singleton]
  change (∏ g : G, (coinLaw u hu0 hu1).measure {(unflattenReserves w).1 g}) *
      (∏ g : G, (coinLaw u hu0 hu1).measure {(unflattenReserves w).2 g}) =
    (Measure.pi fun _ : Bool × G => (coinLaw u hu0 hu1).measure) {w}
  rw [Measure.pi_singleton]
  simp [unflattenReserves, Fintype.prod_prod_type, mul_comm]

def routerBits {G : Type*} {m : ℕ} (s : AugmentedSample G m) : Bool × G → Bool :=
  flattenReserves (thinnedReserves s)

/-- At the exact independent coin rate `u/r`, the actual reserve
augmentation supplies exactly the source law of the router trial theorem. -/
theorem routerBits_measurePreserving {G : Type*} [Fintype G] {m : ℕ}
    (d : Densities m) (hr : 0 < d.r) (u : ℝ) (hu0 : 0 ≤ u) (hur : u ≤ d.r) :
    MeasurePreserving routerBits
      (augmentedMeasure (G := G) d (u / d.r) (div_nonneg hu0 hr.le)
        ((div_le_one hr).mpr hur))
      (EndpointRouter.Bernoulli.measure (O := Bool × G)
        u hu0 (hur.trans d.r_le_one)) := by
  exact (flattenReserves_measurePreserving u hu0 (hur.trans d.r_le_one)).comp
    (thinnedReserves_measurePreserving d hr u hu0 hur)

@[simp] theorem routerBits_vertex {G : Type*} {m : ℕ} (s : AugmentedSample G m) (g : G) :
    routerBits s (false, g) = (thinnedReserves s).1 g := rfl

@[simp] theorem routerBits_colour {G : Type*} {m : ℕ} (s : AugmentedSample G m) (g : G) :
    routerBits s (true, g) = (thinnedReserves s).2 g := rfl

def switchBudgetDensity (u : ℝ) : ℝ := u^22 / 20000

def explicitSwitchBudget (u : ℝ) (n : ℕ) : ℕ := ⌊switchBudgetDensity u * (n : ℝ)⌋₊

theorem explicitSwitchBudget_le (u : ℝ) (n : ℕ) :
    (explicitSwitchBudget u n : ℝ) ≤ u^22 * (n : ℝ) / 20000 := by
  have h := Nat.floor_le (show 0 ≤ switchBudgetDensity u * (n : ℝ) by
    unfold switchBudgetDensity
    positivity)
  change (explicitSwitchBudget u n : ℝ) ≤ _ at h
  exact h.trans_eq (by unfold switchBudgetDensity; ring)

/-- The switch event is defined without choosing an odd-order proof before
the group is fixed.  In an odd group it is exactly the router theorem's
universal event, including all legal port queries and later forbidden sets. -/
def AugmentedSwitchEvent {G : Type*} [Fintype G] [AddCommGroup G] {m : ℕ}
    (budget : ℕ) (s : AugmentedSample G m) : Prop :=
  ∀ hodd : Odd (Fintype.card G),
    EndpointRouter.Switch.UniversallyAvailable hodd budget (routerBits s)

theorem augmentedSwitchEvent_iff {G : Type*} [Fintype G] [AddCommGroup G] {m : ℕ}
    (hodd : Odd (Fintype.card G)) (budget : ℕ) (s : AugmentedSample G m) :
    AugmentedSwitchEvent budget s ↔
      EndpointRouter.Switch.UniversallyAvailable hodd budget (routerBits s) := by
  exact ⟨fun h => h hodd, fun h _ => h⟩

def switchFailureBound (u : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ)^4 * Real.exp (-(u^18 / 32000) * (n : ℝ))

/-- The actual proved switch tail on the categorical reserve augmentation,
at the literal floor budget `floor((u^22/20000)*n)`. -/
theorem augmentedSwitchEvent_failure_probability
    {G : Type*} [Fintype G] [AddCommGroup G] {m : ℕ}
    (d : Densities m) (hr : 0 < d.r) (u : ℝ) (hu0 : 0 ≤ u) (hur : u ≤ d.r)
    (hodd : Odd (Fintype.card G)) (hn : 4000 ≤ Fintype.card G) :
    (augmentedMeasure (G := G) d (u / d.r) (div_nonneg hu0 hr.le)
      ((div_le_one hr).mpr hur)).real
        {s | ¬ AugmentedSwitchEvent (explicitSwitchBudget u (Fintype.card G)) s} ≤
      switchFailureBound u (Fintype.card G) := by
  have hp := routerBits_measurePreserving (G := G) d hr u hu0 hur
  have htail := EndpointRouter.Switch.universallyAvailable_explicit_probability
    hodd hn u hu0 (hur.trans d.r_le_one)
    (explicitSwitchBudget u (Fintype.card G)) (explicitSwitchBudget_le u (Fintype.card G))
  rw [← hp.measureReal_preimage (by measurability)] at htail
  have heq : {s : AugmentedSample G m |
      ¬ AugmentedSwitchEvent (explicitSwitchBudget u (Fintype.card G)) s} =
      routerBits ⁻¹' {w | ¬ EndpointRouter.Switch.UniversallyAvailable hodd
        (explicitSwitchBudget u (Fintype.card G)) w} := by
    ext s
    exact not_congr (augmentedSwitchEvent_iff hodd _ s)
  rw [heq]
  simpa only [switchFailureBound,
    show -(u^18 * (Fintype.card G : ℝ)) / 32000 =
      -(u^18 / 32000) * (Fintype.card G : ℝ) by ring] using htail

theorem switchFailureBound_tendsto_zero (u : ℝ) (hu : 0 < u) :
    Tendsto (switchFailureBound u) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    4 (u^18 / 32000) (by positivity)).comp tendsto_natCast_atTop_atTop
  have h' : Tendsto (fun n : ℕ =>
      (n : ℝ)^4 * Real.exp (-(u^18 / 32000) * (n : ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.rpow_ofNat] using h
  refine Tendsto.congr ?_ h'
  intro n
  rfl

/-- exact-matching, every later ordinary-transition transition, all raw pair/size events and the
actual universal switch event hold on one reserve augmentation.  All
thresholds are uniform over group types and the thinning rate is `u/r`.
Only the pre-existing AKS and Pippenger theorem parameters remain. -/
theorem exists_goodAugmented_layeredTransitions_and_switches
    (hAKS : ∃ K D₀ C : ℝ, 0 < K ∧ 0 < C ∧ AKSSetFamilyTheorem.{v} K D₀ C)
    (hPippenger : EndpointTransitions.PippengerTheorem.{v})
    {m : ℕ} (d : Densities m) (t u : ℝ)
    (hq : 0 < d.q) (hqthird : d.q ≤ 1/3) (ht : 0 < t) (httenth : t ≤ 1/10)
    (hr : 0 < d.r) (hu : 0 < u) (hur : u ≤ d.r) :
    ∃ μ : ℝ, 0 < μ ∧ μ ≤ 1/2 ∧ ∀ η : ℝ,
      0 < η → η ≤ d.q/1000 → η ≤ t/100 → η ≤ d.q^2*μ/1000 →
      ∃ N : ℕ, ∀ (G : Type v) [Fintype G] [AddCommGroup G],
        Odd (Fintype.card G) → N ≤ Fintype.card G →
        ∃ s : AugmentedSample G m,
          GoodSample d (explicitSizeTolerance (Fintype.card G)) (forgetAugmented s) ∧
          LayerTransitionEvent d t η (forgetAugmented s) ∧
          AugmentedSwitchEvent (explicitSwitchBudget u (Fintype.card G)) s := by
  let event : ∀ (G : Type v) [Fintype G] [AddCommGroup G], AugmentedSample G m → Prop :=
    fun G _ _ => AugmentedSwitchEvent (explicitSwitchBudget u (Fintype.card G))
  have hrouter : ∃ N : ℕ, ∀ (G : Type v) [Fintype G] [AddCommGroup G],
      Odd (Fintype.card G) → N ≤ Fintype.card G →
      (augmentedMeasure (G := G) d (u / d.r) (div_nonneg hu.le hr.le)
        ((div_le_one hr).mpr hur)).real {s | ¬ event G s} ≤
          switchFailureBound u (Fintype.card G) := by
    refine ⟨4000, ?_⟩
    intro G _ _ hodd hn
    exact augmentedSwitchEvent_failure_probability d hr u hu.le hur hodd hn
  exact exists_goodAugmented_and_layeredTransitions hAKS hPippenger d t (u / d.r)
    hq hqthird ht httenth (div_nonneg hu.le hr.le) ((div_le_one hr).mpr hur)
    event (switchFailureBound u) (switchFailureBound_tendsto_zero u hu) hrouter

end
end EndpointLayeredSample
