import CorralFormalization.EndpointProof.Router.Packing
import CorralFormalization.EndpointProof.Router.Bernoulli
import CorralFormalization.EndpointProof.Sampling.BlockAvailability

/-! # Actual router trials in one Bernoulli vertex/colour sample

The source coordinates are (channel, numerical label).  Vertex and colour
channels are independent even when a candidate uses the same numerical
label in both channels.  Both within-candidate injectivity and between-
candidate disjointness are proved before applying the product law.
-/
namespace EndpointRouter
namespace Switch

open EndpointRouter.Affine MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
noncomputable section
universe u
variable {G : Type u} [AddCommGroup G] [Fintype G] [DecidableEq G]

def requestLocation (S : Switch G) (t : Parameters G) : Request → Bool × G
  | .inl i => (false,S.randomRequest t (.inl i))
  | .inr i => (true,S.randomRequest t (.inr i))

@[simp] theorem requestLocation_snd (S : Switch G) (t : Parameters G) (r : Request) :
    (S.requestLocation t r).2 = S.randomRequest t r := by cases r <;> rfl

theorem requestLocation_injective (S : Switch G) (t : Parameters G)
    (h : (S.withParameters t).CollisionFree) : Function.Injective (S.requestLocation t) := by
  have hv := List.nodup_ofFn.mp (vertices_ofFn (S.withParameters t) ▸ h.1)
  have hc := List.nodup_ofFn.mp (colors_ofFn (S.withParameters t) ▸ h.2)
  intro i j he
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      have he' := congrArg Prod.snd he
      have hh := hv he'
      have hh' := congrArg Fin.val hh
      apply congrArg Sum.inl
      apply Fin.ext
      dsimp at hh'
      omega
    | inr j => exact Bool.noConfusion (congrArg Prod.fst he)
  | inr i =>
    cases j with
    | inl j => exact Bool.noConfusion (congrArg Prod.fst he)
    | inr j => exact congrArg Sum.inr (hc (congrArg Prod.snd he))

/-- The actual eighteen requests per packed candidate, embedded in the
single source reservoir coordinate set. -/
def Packed.requestEmbedding {S : Switch G} {M : ℕ} (P : S.Packed M) :
    Fin M × Request ↪ Bool × G where
  toFun ir := S.requestLocation (P.parameter ir.1) ir.2
  inj' := by
    rintro ⟨i,r⟩ ⟨j,s⟩ he
    have he' : S.randomRequest (P.parameter i) r = S.randomRequest (P.parameter j) s := by
      simpa only [requestLocation_snd] using congrArg Prod.snd he
    have hij : i = j := by
      by_contra hij
      apply Finset.disjoint_left.mp (P.disjoint hij)
        (Finset.mem_image.mpr ⟨r,Finset.mem_univ _,rfl⟩)
      exact Finset.mem_image.mpr ⟨s,Finset.mem_univ _,he'.symm⟩
    subst j
    exact Prod.ext rfl (requestLocation_injective S _ (P.valid i) he)

/-- A candidate succeeds when every actual vertex/colour request is met. -/
def Packed.Success {S : Switch G} {M : ℕ} (P : S.Packed M)
    (ω : Bool × G → Bool) (i : Fin M) : Prop :=
  ∀ r, ω (P.requestEmbedding (i,r)) = true

theorem Packed.success_iff_project {S : Switch G} {M : ℕ} (P : S.Packed M)
    (ω : Bool × G → Bool) (i : Fin M) :
    P.Success ω i ↔ Bernoulli.project P.requestEmbedding ω i = (fun _ => true) := by
  exact ⟨fun h => funext h,fun h r => congrFun h r⟩

theorem interior_ofFn (S : Switch G) :
    S.interior = List.ofFn (fun i : Fin 8 => S.vertexValue ⟨i.val+4,by omega⟩) := by rfl

/-- Success is related to the reservoirs by an actual coordinate proof. -/
theorem Packed.success_reservoirs {S : Switch G} {M : ℕ} (P : S.Packed M)
    (ω : Bool × G → Bool) (i : Fin M) (hi : P.Success ω i) :
    (∀ z ∈ (S.withParameters (P.parameter i)).interior, ω (false,z) = true) ∧
    (∀ c ∈ (S.withParameters (P.parameter i)).colors, ω (true,c) = true) := by
  constructor
  · intro z hz
    rw [interior_ofFn] at hz
    obtain ⟨r,rfl⟩ := List.mem_ofFn.mp hz
    exact hi (.inl r)
  · intro c hc
    rw [colors_ofFn] at hc
    obtain ⟨r,rfl⟩ := List.mem_ofFn.mp hc
    exact hi (.inr r)

theorem Packed.sum_indicator_eq_card {S : Switch G} {M : ℕ} (P : S.Packed M)
    (ω : Bool × G → Bool) :
    (∑ i, Bernoulli.indicator i (Bernoulli.project P.requestEmbedding ω)) =
      ((Finset.univ.filter (P.Success ω)).card : ℝ) := by
  simp only [Bernoulli.indicator,← P.success_iff_project]
  simp [Finset.sum_boole]

/-- Four fixed ports are a query. Free parameters do not occur in it. -/
def seed (p : G × G × G × G) : Switch G :=
  ⟨p.1,p.2.1,p.2.2.1,p.2.2.2,0,0,0⟩

abbrev PortQuery (G : Type u) [AddCommGroup G] :=
  {p : G × G × G × G // (seed p).LegalPorts}

instance portQuery_fintype : Fintype (PortQuery G) := Fintype.ofFinite _

theorem portQuery_card_le : Fintype.card (PortQuery G) ≤ (Fintype.card G)^4 := by
  have h := Fintype.card_le_of_injective (fun q : PortQuery G => q.val) Subtype.val_injective
  simpa [Fintype.card_prod,pow_succ,Nat.mul_assoc] using h

/-- Chosen once as a deterministic function of the group and port query. -/
def queryPacking (hodd : Odd (Fintype.card G)) (q : PortQuery G) :
    (seed q.val).Packed (Fintype.card G / 2000) :=
  Classical.choice (exists_packed_floor hodd _ q.property)

/-- This event quantifies over every legal query and every later forbidden
set; its witnesses are actual fixed packed candidates. -/
def UniversallyAvailable (hodd : Odd (Fintype.card G)) (budget : ℕ)
    (ω : Bool × G → Bool) : Prop :=
  ∀ q : PortQuery G, ∀ F : Finset G, F.card ≤ budget →
    ∃ i, (queryPacking hodd q).Success ω i ∧
      Disjoint ((seed q.val).numericalSupport ((queryPacking hodd q).parameter i)) F

theorem universallyAvailable_probability (hodd : Odd (Fintype.card G))
    (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (budget : ℕ)
    (hmean : (budget : ℝ) ≤ (Fintype.card G / 2000 : ℕ)*u^18/2) :
    (Bernoulli.measure u hu0 hu1).real {ω | ¬ UniversallyAvailable hodd budget ω} ≤
      (Fintype.card (PortQuery G) : ℝ) *
        Real.exp (-((Fintype.card G / 2000 : ℕ)*u^18)/8) := by
  let support := fun q : PortQuery G => fun i : Fin (Fintype.card G / 2000) =>
    (seed q.val).numericalSupport ((queryPacking hodd q).parameter i)
  let success := fun q : PortQuery G => (queryPacking hodd q).Success
  have hd : ∀ q, Pairwise (fun i j => Disjoint (support q i) (support q j)) :=
    fun q => (queryPacking hodd q).disjoint
  have ht (q : PortQuery G) : (Bernoulli.measure u hu0 hu1).real
      {ω | (Finset.univ.filter (success q ω)).card ≤ budget} ≤
        Real.exp (-((Fintype.card G / 2000 : ℕ)*u^18)/8) := by
    have hraw := Bernoulli.shared_half_tail u hu0 hu1 (queryPacking hodd q).requestEmbedding
    have hraw' : (Bernoulli.measure u hu0 hu1).real
        {ω | (∑ i, Bernoulli.indicator i (Bernoulli.project
          (queryPacking hodd q).requestEmbedding ω)) ≤
          (Fintype.card G / 2000 : ℕ)*u^18/2} ≤
        Real.exp (-((Fintype.card G / 2000 : ℕ)*u^18)/8) := by
      simpa [Fintype.card_sum] using hraw
    apply le_trans (measureReal_mono ?_) hraw'
    intro ω hω
    change (∑ i, Bernoulli.indicator i (Bernoulli.project
      (queryPacking hodd q).requestEmbedding ω)) ≤ _
    rw [Packed.sum_indicator_eq_card]
    exact le_trans (by exact_mod_cast hω) hmean
  have hh := EndpointBlockAvailability.finite_query_failure_bound
    (Bernoulli.measure u hu0 hu1) support success hd budget
    (fun _ => Real.exp (-((Fintype.card G / 2000 : ℕ)*u^18)/8)) ht
  simpa only [UniversallyAvailable,EndpointBlockAvailability.UniversallyAvailable,
    support,success,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using hh

/-- A simple floor estimate used for the written exponential rate. -/
theorem floor_packing_lower_bound (n : ℕ) (hn : 4000 ≤ n) : n ≤ 4000*(n/2000) := by
  have hmod := Nat.mod_lt n (by decide : 0 < 2000)
  have he := Nat.mod_add_div n 2000
  omega

/-- The paper's actual b=u²²/20000 budget is below half the mean of the
proved packed switch trials. -/
theorem explicit_budget_below_half_mean (n : ℕ) (hn : 4000 ≤ n)
    (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    u^22*(n : ℝ)/20000 ≤ (n/2000 : ℕ)*u^18/2 := by
  have hfloor : (n : ℝ) ≤ 4000*(n/2000 : ℕ) := by exact_mod_cast floor_packing_lower_bound n hn
  have hpow4 : u^4 ≤ 1 := pow_le_one₀ hu0 hu1
  have hpow : u^22 ≤ u^18 := by
    rw [show 22 = 18+4 by decide,pow_add]
    nlinarith [pow_nonneg hu0 18]
  have h1 := mul_le_mul_of_nonneg_right hfloor (pow_nonneg hu0 18)
  have h2 := mul_le_mul_of_nonneg_right hpow (show 0 ≤ (n : ℝ) by positivity)
  have h3 : 0 ≤ (n/2000 : ℕ)*u^18 := by positivity
  nlinarith

/-- The concrete common switch event with the exponential rate.
All query-dependent packings precede the one random source sample. -/
theorem universallyAvailable_explicit_probability (hodd : Odd (Fintype.card G))
    (hn : 4000 ≤ Fintype.card G) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (budget : ℕ) (hbudget : (budget : ℝ) ≤ u^22*(Fintype.card G : ℝ)/20000) :
    (Bernoulli.measure u hu0 hu1).real {ω | ¬ UniversallyAvailable hodd budget ω} ≤
      (Fintype.card G : ℝ)^4 * Real.exp (-(u^18*(Fintype.card G : ℝ))/32000) := by
  have hm := explicit_budget_below_half_mean (Fintype.card G) hn u hu0 hu1
  have hraw := universallyAvailable_probability hodd u hu0 hu1 budget (hbudget.trans hm)
  have hfloor : (Fintype.card G : ℝ) ≤ 4000*(Fintype.card G/2000 : ℕ) := by
    exact_mod_cast floor_packing_lower_bound (Fintype.card G) hn
  have hexp : Real.exp (-((Fintype.card G/2000 : ℕ)*u^18)/8) ≤
      Real.exp (-(u^18*(Fintype.card G : ℝ))/32000) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hfloor (pow_nonneg hu0 18)]
  have hcard : (Fintype.card (PortQuery G) : ℝ) ≤ (Fintype.card G : ℝ)^4 := by
    exact_mod_cast (portQuery_card_le (G := G))
  exact hraw.trans (mul_le_mul hcard hexp (Real.exp_nonneg _) (by positivity))

end
end Switch
end EndpointRouter
