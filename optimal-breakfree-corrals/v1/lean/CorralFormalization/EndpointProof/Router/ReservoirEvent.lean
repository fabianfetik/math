import CorralFormalization.EndpointProof.Router.IdleProjection
import CorralFormalization.EndpointProof.Router.Ports

/-! # A proved common reservoir event for all router primitives

Both idle and exchange queries are supplied by the same actual source
sample.  The event also pays the vertex-reservoir size needed to choose
intermediate ports.  No universal-availability event is taken as a premise
of the probability theorem.
-/
namespace EndpointRouter

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
noncomputable section
universe u
variable {G : Type u} [AddCommGroup G] [Fintype G] [DecidableEq G]

def vertexReservoir (ω : Bool × G → Bool) : Set G := {g | ω (false,g) = true}
def colorReservoir (ω : Bool × G → Bool) : Set G := {g | ω (true,g) = true}

def LocalSupply (budget : ℕ) (ω : Bool × G → Bool) : Prop :=
  ∀ q : Query G, q.Legal → ∀ F : Finset G, F.card ≤ budget →
    ∃ P : Primitive G, P.Good (vertexReservoir ω) (colorReservoir ω) q ∧ Disjoint P.support F

/-- The common switch trial event already includes every single idle query. -/
theorem localSupply_of_switch_event (hodd : Odd (Fintype.card G))
    (hn : 6 ≤ Fintype.card G) (budget : ℕ) (ω : Bool × G → Bool)
    (h : Switch.UniversallyAvailable hodd budget ω) : LocalSupply budget ω := by
  exact local_supply_of_switch_event hodd hn budget ω h

theorem localSupply_probability (hodd : Odd (Fintype.card G))
    (hn : 4000 ≤ Fintype.card G) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (budget : ℕ) (hbudget : (budget : ℝ) ≤ u^22*(Fintype.card G : ℝ)/20000) :
    (Bernoulli.measure u hu0 hu1).real {ω : Bool × G → Bool | ¬ LocalSupply budget ω} ≤
      (Fintype.card G : ℝ)^4 * Real.exp (-(u^18*(Fintype.card G : ℝ))/32000) := by
  apply le_trans (measureReal_mono ?_)
    (Switch.universallyAvailable_explicit_probability hodd hn u hu0 hu1 budget hbudget)
  intro ω hbad hevent
  exact hbad (localSupply_of_switch_event hodd (by omega) budget ω hevent)

def vertexPool (ω : Bool × G → Bool) : Finset G :=
  Finset.univ.filter (fun g => ω (false,g) = true)

def vertexEmbedding : G × Fin 1 ↪ Bool × G where
  toFun gi := (false,gi.1)
  inj' := by
    rintro ⟨g,i⟩ ⟨h,j⟩ he
    exact Prod.ext (congrArg Prod.snd he) (Subsingleton.elim _ _)

theorem vertex_indicator_sum (ω : Bool × G → Bool) :
    (∑ g, Bernoulli.indicator g (Bernoulli.project (vertexEmbedding (G := G)) ω)) =
      ((vertexPool ω).card : ℝ) := by
  have heq (g : G) : Bernoulli.indicator g (Bernoulli.project (vertexEmbedding (G := G)) ω) =
      if ω (false,g) = true then (1 : ℝ) else 0 := by
    have hb : Bernoulli.project (vertexEmbedding (G := G)) ω g = (fun _ : Fin 1 => true) ↔
        ω (false,g) = true := by
      change ((fun _ : Fin 1 => ω (false,g)) = (fun _ : Fin 1 => true)) ↔ _
      exact ⟨fun h => congrFun h 0,fun h => funext (fun _ => h)⟩
    simp only [Bernoulli.indicator,hb]
  simp only [heq,vertexPool,Finset.sum_boole]

/-- The vertex-pool Chernoff tail on the same Bernoulli source. -/
theorem vertexPool_small_probability (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (Bernoulli.measure u hu0 hu1).real
      {ω : Bool × G → Bool | ((vertexPool ω).card : ℝ) < u*(Fintype.card G : ℝ)/2} ≤
      Real.exp (-(u*(Fintype.card G : ℝ))/8) := by
  have hraw := Bernoulli.shared_half_tail u hu0 hu1 (vertexEmbedding (G := G))
  have hraw' : (Bernoulli.measure u hu0 hu1).real
      {ω | (∑ g, Bernoulli.indicator g (Bernoulli.project (vertexEmbedding (G := G)) ω)) ≤
        u*(Fintype.card G : ℝ)/2} ≤ Real.exp (-(u*(Fintype.card G : ℝ))/8) := by
    simpa [mul_comm] using hraw
  apply le_trans (measureReal_mono ?_) hraw'
  intro ω hω
  change (∑ g, Bernoulli.indicator g (Bernoulli.project (vertexEmbedding (G := G)) ω)) ≤ _
  rw [vertex_indicator_sum]
  exact le_of_lt hω

/-- A single concrete event for local router primitives and enough
intermediate-port vertices, before any later query or forbidden set. -/
def ReservoirEvent (u : ℝ) (budget : ℕ) (ω : Bool × G → Bool) : Prop :=
  LocalSupply budget ω ∧ u*(Fintype.card G : ℝ)/2 ≤ (vertexPool ω).card

/-- The paper's requested common failure bound (in fact the proof needs
only n⁴+1, since the same switch event supplies all idle queries). -/
theorem reservoirEvent_probability (hodd : Odd (Fintype.card G))
    (hn : 4000 ≤ Fintype.card G) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (budget : ℕ) (hbudget : (budget : ℝ) ≤ u^22*(Fintype.card G : ℝ)/20000) :
    (Bernoulli.measure u hu0 hu1).real {ω : Bool × G → Bool | ¬ ReservoirEvent u budget ω} ≤
      ((Fintype.card G : ℝ)^4 + (Fintype.card G : ℝ)^2 + 1) *
        Real.exp (-(u^18*(Fintype.card G : ℝ))/32000) := by
  have hswitch := localSupply_probability hodd hn u hu0 hu1 budget hbudget
  have hvertex := vertexPool_small_probability (G := G) u hu0 hu1
  have hpow : u^18 ≤ u := by
    have hp : u^17 ≤ 1 := pow_le_one₀ hu0 hu1
    rw [show 18 = 1+17 by decide,pow_add,pow_one]
    nlinarith
  have hexp : Real.exp (-(u*(Fintype.card G : ℝ))/8) ≤
      Real.exp (-(u^18*(Fintype.card G : ℝ))/32000) := by
    apply Real.exp_le_exp.mpr
    have h1 := mul_le_mul_of_nonneg_right hpow (show 0 ≤ (Fintype.card G : ℝ) by positivity)
    have h2 : 0 ≤ u*(Fintype.card G : ℝ) := by positivity
    nlinarith
  have hset : {ω : Bool × G → Bool | ¬ ReservoirEvent u budget ω} =
      {ω : Bool × G → Bool | ¬ LocalSupply budget ω} ∪
      {ω : Bool × G → Bool | ((vertexPool ω).card : ℝ) < u*(Fintype.card G : ℝ)/2} := by
    ext ω
    simp only [Set.mem_ofPred_eq,Set.mem_union,ReservoirEvent,not_and_or,not_le]
  rw [hset]
  calc
    _ ≤ (Bernoulli.measure u hu0 hu1).real {ω : Bool × G → Bool | ¬ LocalSupply budget ω} +
        (Bernoulli.measure u hu0 hu1).real
          {ω : Bool × G → Bool | ((vertexPool ω).card : ℝ) < u*(Fintype.card G : ℝ)/2} := measureReal_union_le _ _
    _ ≤ (Fintype.card G : ℝ)^4 * Real.exp (-(u^18*(Fintype.card G : ℝ))/32000) +
        Real.exp (-(u^18*(Fintype.card G : ℝ))/32000) :=
      add_le_add hswitch (hvertex.trans hexp)
    _ ≤ _ := by
      have he : 0 ≤ Real.exp (-(u^18*(Fintype.card G : ℝ))/32000) := Real.exp_nonneg _
      nlinarith [mul_nonneg (sq_nonneg (Fintype.card G : ℝ)) he]

/-- The event supplies the existing deterministic installer directly. -/
theorem ReservoirEvent.install (u : ℝ) (budget : ℕ) (ω : Bool × G → Bool) (h : ReservoirEvent u budget ω)
    (queries : List (Query G)) (F : Finset G)
    (hlegal : ∀ q ∈ queries, q.Legal)
    (hbudget : F.card + (queries.map (fun q => 9*q.arity)).sum ≤ budget) :
    ∃ installed : List (Primitive G),
      List.Forall₂ (Primitive.Good (vertexReservoir ω) (colorReservoir ω)) queries installed ∧
      installed.Pairwise (fun P Q => Disjoint P.support Q.support) ∧
      (∀ P ∈ installed, Disjoint P.support F) := by
  exact install_router_primitives (vertexReservoir ω) (colorReservoir ω)
    budget queries F hlegal hbudget h.1

/-- The maximal integer forbidden-set budget below the paper's b*n. -/
def routerTrialBudget (u : ℝ) (n : ℕ) : ℕ := ⌊u^22*(n : ℝ)/20000⌋₊

/-- The displayed paper constants require no residual mean or budget
separation hypothesis. -/
theorem explicit_reservoirEvent_probability (hodd : Odd (Fintype.card G))
    (hn : 4000 ≤ Fintype.card G) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (Bernoulli.measure u hu0 hu1).real
      {ω : Bool × G → Bool | ¬ ReservoirEvent u (routerTrialBudget u (Fintype.card G)) ω} ≤
      ((Fintype.card G : ℝ)^4 + (Fintype.card G : ℝ)^2 + 1) *
        Real.exp (-(u^18*(Fintype.card G : ℝ))/32000) := by
  apply reservoirEvent_probability hodd hn u hu0 hu1
  exact Nat.floor_le (by positivity)

/-- The same event's actual vertex pool supplies the earlier deterministic
intermediate-port constructor. The sole remaining condition here is its
explicit finite cardinality inequality. -/
theorem ReservoirEvent.choose_ports (u : ℝ) (budget : ℕ) (ω : Bool × G → Bool)
    (h : ReservoirEvent u budget ω) (F : Finset G) (previous : G) (deltas : List G)
    (hcard : (F.card : ℝ) + deltas.length + 2 < u*(Fintype.card G : ℝ)/2) :
    ∃ ports : List G,
      ports.length = deltas.length ∧ ports.Nodup ∧
      (∀ m ∈ ports, m ∈ vertexPool ω ∧ m ∉ F) ∧
      List.Forall₂ (fun difference delta => difference ≠ delta ∧ difference ≠ -delta)
        (EndpointFactor.edgeLabels (fun a b : G => b-a) (previous::ports)) deltas := by
  apply choose_intermediate_ports (vertexPool ω) F previous deltas
  have hh := hcard.trans_le h.2
  exact_mod_cast hh

end
end EndpointRouter
