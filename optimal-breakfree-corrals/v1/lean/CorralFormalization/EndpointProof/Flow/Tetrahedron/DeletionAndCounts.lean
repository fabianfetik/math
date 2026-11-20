import CorralFormalization.EndpointProof.Flow.Tetrahedron.Supplier
import CorralFormalization.EndpointProof.Flow.Tetrahedron.Reservoir
import CorralFormalization.EndpointProof.Probability.QuadraticDeletion

open scoped Classical BigOperators
namespace EndpointMatching.Tetrahedron
open EndpointFlow.AbelianTransport
open CorralFormalization.EndpointProof.Probability.QuadraticDeletion
noncomputable section
variable {G : Type*} [AddCommGroup G]

def representativeSlot : Fin 12 → Slot := ![
  (0,2),(0,4),(0,6),(0,8),
  (1,2),(1,4),(1,6),(1,8),
  (2,2),(2,4),(2,6),(2,8)]

def signedSlot (i : Fin 12 × Bool) : Slot :=
  if i.2 then slotFlip (representativeSlot i.1) else representativeSlot i.1

theorem signedSlots_eq_added :
    (Finset.univ : Finset (Fin 12 × Bool)).image signedSlot = addedSlots := by decide

theorem signedSlot_injective : Function.Injective signedSlot := by decide

theorem representativeSlot_mem_added (i : Fin 12) : representativeSlot i ∈ addedSlots := by
  fin_cases i <;> decide

theorem representativeSlot_value (r : TetrahedronRoots G) (t : TetrahedronParameters G)
    (i : Fin 12) :
    (place r.a₁ r.a₂ r.b₁ r.b₂ r.c₁ r.c₂ t.1 t.2.1 t.2.2 (representativeSlot i)).2 =
      tetrahedronRepresentative r i t := by
  rw [tetrahedron_representative_expanded]
  fin_cases i <;> simp [representativeSlot, place, coordinate]

/-- The concrete 24 added vertices have exactly the numerical inverse-pair
support used by the previously checked section-count/deletion theorem. -/
theorem concrete_support_eq_twelvePairSupport (r : TetrahedronRoots G)
    (t : TetrahedronParameters G) :
    support (added r.a₁ r.a₂ r.b₁ r.b₂ r.c₁ r.c₂ t.1 t.2.1 t.2.2) =
      twelvePairSupport (tetrahedronRepresentative r) t := by
  let A := added r.a₁ r.a₂ r.b₁ r.b₂ r.c₁ r.c₂ t.1 t.2.1 t.2.2
  let f := place r.a₁ r.a₂ r.b₁ r.b₂ r.c₁ r.c₂ t.1 t.2.1 t.2.2
  have hsupport : support A = A.image Prod.snd := by
    apply Finset.union_eq_left.mpr
    intro g hg
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hg
    exact Finset.mem_image.mpr ⟨(v.1,-v.2), added_paired _ _ _ _ _ _ _ _ _ v hv, rfl⟩
  rw [hsupport]
  change (addedSlots.image f).image Prod.snd = _
  rw [← signedSlots_eq_added, Finset.image_image, Finset.image_image]
  unfold twelvePairSupport
  congr 1
  funext i
  rcases i with ⟨j,b⟩
  cases b
  · simpa only [signedSlot, Bool.false_eq_true, ↓reduceIte, Function.comp_apply] using
      representativeSlot_value r t j
  · simp only [signedSlot, ↓reduceIte, Function.comp_apply]
    have hflip := congrArg Prod.snd (coordinate_flip r.a₁ r.a₂ r.b₁ r.b₂ r.c₁ r.c₂
      t.1 t.2.1 t.2.2 (representativeSlot j) (representativeSlot_mem_added j))
    change (f (slotFlip (representativeSlot j))).2 = -tetrahedronRepresentative r j t
    rw [hflip, representativeSlot_value r t j]

/-- On a paired Q reservoir, checking all 24 vertices is exactly checking
the twelve representatives: their inverses are in the same reservoir. -/
theorem added_Q_iff_representatives (Q : Vertex G → Prop)
    (hQ : EndpointSelector.FixedCardinality.PairReservoir Q)
    (r : TetrahedronRoots G) (t : TetrahedronParameters G) :
    (∀ v ∈ added r.a₁ r.a₂ r.b₁ r.b₂ r.c₁ r.c₂ t.1 t.2.1 t.2.2, Q v) ↔
      ∀ i : Fin 12,
        Q (place r.a₁ r.a₂ r.b₁ r.b₂ r.c₁ r.c₂ t.1 t.2.1 t.2.2 (representativeSlot i)) := by
  constructor
  · intro h i
    apply h
    exact Finset.mem_image.mpr ⟨representativeSlot i, representativeSlot_mem_added i, rfl⟩
  · intro h v hv
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hv
    rw [← signedSlots_eq_added] at hs
    obtain ⟨⟨i,b⟩,_,rfl⟩ := Finset.mem_image.mp hs
    cases b
    · simpa [signedSlot] using h i
    · simpa only [signedSlot, ↓reduceIte,
        coordinate_flip r.a₁ r.a₂ r.b₁ r.b₂ r.c₁ r.c₂ t.1 t.2.1 t.2.2
          (representativeSlot i) (representativeSlot_mem_added i)] using
        hQ.paired _ (h i)

/-- Successful representatives use twelve distinct numerical inverse
orbits in the actual categorical Q sample, even across different parts. -/
theorem sampled_representative_orbits_distinct [Fintype G]
    (ω : EndpointFullProduct.FullSample G) (r : TetrahedronRoots G)
    (t : TetrahedronParameters G)
    (hinj : Function.Injective
      (place r.a₁ r.a₂ r.b₁ r.b₂ r.c₁ r.c₂ t.1 t.2.1 t.2.2))
    (hQ : ∀ v ∈ added r.a₁ r.a₂ r.b₁ r.b₂ r.c₁ r.c₂ t.1 t.2.1 t.2.2,
      ReservoirVertex ω true v) :
    ∀ i j : Fin 12, i ≠ j →
      tetrahedronRepresentative r i t ≠ tetrahedronRepresentative r j t ∧
      tetrahedronRepresentative r i t ≠ -tetrahedronRepresentative r j t := by
  let f := place r.a₁ r.a₂ r.b₁ r.b₂ r.c₁ r.c₂ t.1 t.2.1 t.2.2
  have hrepQ (i : Fin 12) : ReservoirVertex ω true (f (representativeSlot i)) :=
    (added_Q_iff_representatives (ReservoirVertex ω true)
      (EndpointSelector.FixedCardinality.pairReservoir_of_reservoirVertex ω true) r t).mp hQ i
  intro i j hij
  constructor
  · intro he
    have hval : (f (representativeSlot i)).2 = (f (representativeSlot j)).2 := by
      simpa [f, representativeSlot_value] using he
    have hp : (f (representativeSlot i)).1 = (f (representativeSlot j)).1 :=
      reservoir_part_unique_up_to_sign ω true _ _ _ _ (hrepQ i) (hrepQ j) (Or.inl hval)
    have hs : representativeSlot i = representativeSlot j := hinj (Prod.ext hp hval)
    have he' : signedSlot (i,false) = signedSlot (j,false) := by simpa [signedSlot] using hs
    exact hij (congrArg Prod.fst (signedSlot_injective he'))
  · intro he
    have hval : (f (representativeSlot i)).2 = -(f (representativeSlot j)).2 := by
      simpa [f, representativeSlot_value] using he
    have hp : (f (representativeSlot i)).1 = (f (representativeSlot j)).1 :=
      reservoir_part_unique_up_to_sign ω true _ _ _ _ (hrepQ i) (hrepQ j) (Or.inr hval)
    have hflip := coordinate_flip r.a₁ r.a₂ r.b₁ r.b₂ r.c₁ r.c₂
      t.1 t.2.1 t.2.2 (representativeSlot j) (representativeSlot_mem_added j)
    change f (slotFlip (representativeSlot j)) =
      ((f (representativeSlot j)).1, -(f (representativeSlot j)).2) at hflip
    have hv : f (representativeSlot i) = f (slotFlip (representativeSlot j)) := by
      rw [hflip]
      exact Prod.ext hp hval
    have hs := hinj hv
    have he' : signedSlot (i,false) = signedSlot (j,true) := by simpa [signedSlot] using hs
    exact hij (congrArg Prod.fst (signedSlot_injective he'))

/-- Exactly the six-root admissibility conditions in the written merge;
roots in different parts may coincide and two roots may be inverses. -/
def admissibleRoots (r : TetrahedronRoots G) : Prop :=
  r.a₁ ≠ r.a₂ ∧ r.b₁ ≠ r.b₂ ∧ r.c₁ ≠ r.c₂ ∧
  r.a₁ ≠ 0 ∧ r.a₂ ≠ 0 ∧ r.b₁ ≠ 0 ∧ r.b₂ ≠ 0 ∧ r.c₁ ≠ 0 ∧ r.c₂ ≠ 0

/-- Successful parameter triples on the actual Q reservoir. The test
includes numerical freshness from all six roots but no later forbidden set. -/
def goodCandidates [Fintype G] (Q : Vertex G → Prop) (r : TetrahedronRoots G) :
    Finset (TetrahedronParameters G) :=
  Finset.univ.filter (fun t =>
    Function.Injective (place r.a₁ r.a₂ r.b₁ r.b₂ r.c₁ r.c₂ t.1 t.2.1 t.2.2) ∧
    (∀ v ∈ added r.a₁ r.a₂ r.b₁ r.b₂ r.c₁ r.c₂ t.1 t.2.1 t.2.2, Q v) ∧
    Disjoint (support (added r.a₁ r.a₂ r.b₁ r.b₂ r.c₁ r.c₂ t.1 t.2.1 t.2.2))
      (support (roots r.a₁ r.a₂ r.b₁ r.b₂ r.c₁ r.c₂ t.1 t.2.1 t.2.2)))

/-- Total-success and six section-count lower/upper bounds for the actual
successful triples give all later fresh parameter queries. The count bounds
and their probability remain explicit assumptions. -/
theorem parameters_available_of_section_counts [Fintype G]
    (Q : Vertex G → Prop) (budget : ℕ) (τ n : ℝ) (hτ : 0 < τ) (hn : 0 < n)
    (hbudget : (budget : ℝ) ≤ τ^2 * n / 192)
    (htotal : ∀ r : TetrahedronRoots G, admissibleRoots r →
      τ^12 * n^3 / 2 ≤ ((goodCandidates Q r).card : ℝ))
    (hsection : ∀ r : TetrahedronRoots G, admissibleRoots r → ∀ i g,
      (((goodCandidates Q r).filter (fun t => tetrahedronDirection i t = g)).card : ℝ) ≤
        2 * τ^10 * n^2) :
    TetrahedronParametersAvailable Q budget := by
  intro a1 a2 b1 b2 c1 c2 ha hb hc ha1 ha2 hb1 hb2 hc1 hc2 F hF
  let r : TetrahedronRoots G := ⟨a1,a2,b1,b2,c1,c2⟩
  have hr : admissibleRoots r := ⟨ha,hb,hc,ha1,ha2,hb1,hb2,hc1,hc2⟩
  have hFreal : (F.card : ℝ) ≤ τ^2 * n / 192 :=
    (Nat.cast_le.mpr hF).trans hbudget
  obtain ⟨_,t,ht,htF⟩ := tetrahedron_available_of_section_counts r
    (goodCandidates Q r) τ n hτ hn (htotal r hr) (hsection r hr) F hFreal
  have hgood := (Finset.mem_filter.mp ht).2
  have hFdis : Disjoint (support (added a1 a2 b1 b2 c1 c2 t.1 t.2.1 t.2.2)) F := by
    rw [concrete_support_eq_twelvePairSupport r t]
    exact htF
  exact ⟨t.1,t.2.1,t.2.2,hgood.1,hgood.2.1,
    Finset.disjoint_union_right.mpr ⟨hFdis,hgood.2.2⟩⟩

/-- Finite index of exactly the admissible six-root queries, avoiding an
invalid demand for successful candidates when equal roots are supplied. -/
abbrev RootTuple (G : Type*) := G × G × G × G × G × G

def tupleRoots (t : RootTuple G) : TetrahedronRoots G :=
  ⟨t.1,t.2.1,t.2.2.1,t.2.2.2.1,t.2.2.2.2.1,t.2.2.2.2.2⟩

def AdmissibleRootQuery (G : Type*) [AddCommGroup G] :=
  {t : RootTuple G // admissibleRoots (tupleRoots t)}

noncomputable instance [Fintype G] : Fintype (AdmissibleRootQuery G) := by
  classical
  unfold AdmissibleRootQuery RootTuple
  infer_instance

theorem admissibleRootQuery_card_le [Fintype G] :
    Fintype.card (AdmissibleRootQuery G) ≤ (Fintype.card G)^6 := by
  have h := Fintype.card_le_of_injective
    (fun q : AdmissibleRootQuery G => q.1) Subtype.val_injective
  simpa [RootTuple, Fintype.card_prod, pow_succ, Nat.mul_assoc] using h

def queryRoots (q : AdmissibleRootQuery G) : TetrahedronRoots G := tupleRoots q.1

/-- The existing common deletion event now supplies exactly the parameters
for the concrete tetrahedron, for the same Q reservoir and every later F. -/
theorem parameters_of_deletion_event [Fintype G]
    {Ω : Type*} (Q : Ω → Vertex G → Prop) (ω : Ω)
    (τ n : ℝ) (budget : ℕ) (hbudget : (budget : ℝ) ≤ τ^2 * n / 192)
    (hgood : TetrahedronAvailable queryRoots
      (fun ω q => goodCandidates (Q ω) (queryRoots q)) τ n ω) :
    TetrahedronParametersAvailable (Q ω) budget := by
  intro a1 a2 b1 b2 c1 c2 ha hb hc ha1 ha2 hb1 hb2 hc1 hc2 F hF
  let q : AdmissibleRootQuery G :=
    ⟨(a1,a2,b1,b2,c1,c2),⟨ha,hb,hc,ha1,ha2,hb1,hb2,hc1,hc2⟩⟩
  have hFreal : (F.card : ℝ) ≤ τ^2 * n / 192 := (Nat.cast_le.mpr hF).trans hbudget
  obtain ⟨_, t, ht, htF⟩ := hgood q F hFreal
  dsimp [queryRoots, tupleRoots, q] at ht htF
  have hvalid := (Finset.mem_filter.mp ht).2
  have hFdis : Disjoint (support (added a1 a2 b1 b2 c1 c2 t.1 t.2.1 t.2.2)) F := by
    rw [concrete_support_eq_twelvePairSupport ⟨a1,a2,b1,b2,c1,c2⟩ t]
    exact htF
  exact ⟨t.1,t.2.1,t.2.2,hvalid.1,hvalid.2.1,
    Finset.disjoint_union_right.mpr ⟨hFdis,hvalid.2.2⟩⟩

/-- The proved finite union bound transfers to the actual PC4 parameter
supply. Its two concentration-tail bounds remain explicit probabilistic
inputs; no independence of the correlated query events is assumed. -/
theorem parameters_probability_of_count_tails [Fintype G]
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsFiniteMeasure μ] (Q : Ω → Vertex G → Prop)
    (τ n u v : ℝ) (budget : ℕ) (hτ : 0 < τ) (hn : 0 < n)
    (hbudget : (budget : ℝ) ≤ τ^2 * n / 192)
    (htotal : ∀ q : AdmissibleRootQuery G,
      μ.real {ω | ¬ τ^12 * n^3 / 2 ≤ ((goodCandidates (Q ω) (queryRoots q)).card : ℝ)} ≤ u)
    (hsection : ∀ (q : AdmissibleRootQuery G) i g,
      μ.real {ω | ¬
        (((goodCandidates (Q ω) (queryRoots q)).filter
          (fun t => tetrahedronDirection i t = g)).card : ℝ) ≤ 2 * τ^10 * n^2} ≤ v) :
    μ.real {ω | ¬ TetrahedronParametersAvailable (Q ω) budget} ≤
      (Fintype.card (AdmissibleRootQuery G) : ℝ) * u +
        (Fintype.card (AdmissibleRootQuery G) : ℝ) * 6 * (Fintype.card G : ℝ) * v := by
  have hsub : {ω | ¬ TetrahedronParametersAvailable (Q ω) budget} ⊆
      {ω | ¬ TetrahedronAvailable queryRoots
        (fun ω q => goodCandidates (Q ω) (queryRoots q)) τ n ω} := by
    intro ω hbad hgood
    exact hbad (parameters_of_deletion_event Q ω τ n budget hbudget hgood)
  exact (MeasureTheory.measureReal_mono hsub (MeasureTheory.measure_ne_top μ _)).trans
    (tetrahedron_common_event_probability μ queryRoots
      (fun ω q => goodCandidates (Q ω) (queryRoots q)) τ n u v hτ hn htotal hsection)

end
end EndpointMatching.Tetrahedron
