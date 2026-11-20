import CorralFormalization.EndpointProof.Sampling.OriginalLaw

/-!
The actual categorical layer sample for the path-factor construction.

There are `m + 3` vertex layers, of which first, second and last have mass
`q`, and `m + 1` ordinary colour banks.  Each channel is a product over all
group elements, including zero; the two channels are independent.  Roles
within the same channel are categorical and therefore disjoint.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

set_option autoImplicit false

namespace EndpointLayeredSample

open EndpointOriginalReservoir EndpointFullProduct

noncomputable section

/-- `m = J - 3`; the four distinguished labels are reserve, first, second,
and last, in this order. -/
abbrev VertexRole (m : ℕ) := Fin 4 ⊕ Fin m

/-- The two distinguished colour labels are reserve and the special bank.
The ordinary banks are indexed by `Fin (m + 1)`. -/
abbrev ColourRole (m : ℕ) := Fin 2 ⊕ Fin (m + 1)

instance {m : ℕ} : MeasurableSpace (VertexRole m) := ⊤
instance {m : ℕ} : MeasurableSingletonClass (VertexRole m) := ⟨fun _ => trivial⟩
instance {m : ℕ} : MeasurableSpace (ColourRole m) := ⊤
instance {m : ℕ} : MeasurableSingletonClass (ColourRole m) := ⟨fun _ => trivial⟩

abbrev reserveVertex (m : ℕ) : VertexRole m := Sum.inl 0
abbrev firstVertex (m : ℕ) : VertexRole m := Sum.inl 1
abbrev secondVertex (m : ℕ) : VertexRole m := Sum.inl 2
abbrev lastVertex (m : ℕ) : VertexRole m := Sum.inl 3
abbrev reserveColour (m : ℕ) : ColourRole m := Sum.inl 0
abbrev specialColour (m : ℕ) : ColourRole m := Sum.inl 1

/-- The exact mass equations from §5, without committing to a later choice
of constants or requiring division by a nonzero number of generic layers. -/
structure Densities (m : ℕ) where
  r : ℝ
  q : ℝ
  a : ℝ
  c : ℝ
  r_nonneg : 0 ≤ r
  q_nonneg : 0 ≤ q
  a_nonneg : 0 ≤ a
  c_nonneg : 0 ≤ c
  vertex_total : r + 3 * q + m * a = 1
  colour_total : r + q + (m + 1 : ℕ) * c = 1

theorem Densities.q_le_half {m : ℕ} (d : Densities m) : d.q ≤ 1 / 2 := by
  have hma : 0 ≤ (m : ℝ) * d.a := mul_nonneg (Nat.cast_nonneg _) d.a_nonneg
  linarith [d.vertex_total, d.r_nonneg]

/-- The literal densities of §5: `a = (1-r-3q)/(J-3)` and
`c = (1-r-q)/(J-2)`, with `J = m+3`. -/
def Densities.ofLayerParameters (m : ℕ) (hm : 0 < m) (r q : ℝ)
    (hr : 0 ≤ r) (hq : 0 ≤ q) (hrq : r + 3 * q ≤ 1) : Densities m where
  r := r
  q := q
  a := (1 - r - 3 * q) / m
  c := (1 - r - q) / ((m : ℝ) + 1)
  r_nonneg := hr
  q_nonneg := hq
  a_nonneg := div_nonneg (by linarith) (Nat.cast_nonneg _)
  c_nonneg := div_nonneg (by linarith) (by positivity)
  vertex_total := by
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
    field_simp [hm0]
    <;> ring
  colour_total := by
    have hm0 : (m : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp [hm0]
    <;> ring

def vertexWeight {m : ℕ} (d : Densities m) : VertexRole m → ℝ
  | Sum.inl i => if i = 0 then d.r else d.q
  | Sum.inr _ => d.a

def colourWeight {m : ℕ} (d : Densities m) : ColourRole m → ℝ
  | Sum.inl i => if i = 0 then d.r else d.q
  | Sum.inr _ => d.c

def vertexLaw {m : ℕ} (d : Densities m) : FiniteLaw (VertexRole m) where
  weight := vertexWeight d
  nonneg := by
    rintro (i | i)
    · dsimp [vertexWeight]; split_ifs <;> first | exact d.r_nonneg | exact d.q_nonneg
    · exact d.a_nonneg
  total := by
    simpa [vertexWeight, Fintype.sum_sum_type, Fin.sum_univ_succ,
      show (3 : ℝ) * d.q = d.q + (d.q + d.q) by ring, add_assoc] using d.vertex_total

def colourLaw {m : ℕ} (d : Densities m) : FiniteLaw (ColourRole m) where
  weight := colourWeight d
  nonneg := by
    rintro (i | i)
    · dsimp [colourWeight]; split_ifs <;> first | exact d.r_nonneg | exact d.q_nonneg
    · exact d.c_nonneg
  total := by
    simpa [colourWeight, Fintype.sum_sum_type, Fin.sum_univ_succ, add_assoc]
      using d.colour_total

abbrev Sample (G : Type*) (m : ℕ) := (G → VertexRole m) × (G → ColourRole m)

/-- One actual sample: independent vertex and colour channels, each with
independent categorical coordinates over every element of `G`. -/
def sampleMeasure {G : Type*} [Fintype G] {m : ℕ} (d : Densities m) :
    Measure (Sample G m) :=
  (Measure.pi fun _ : G => (vertexLaw d).measure).prod
    (Measure.pi fun _ : G => (colourLaw d).measure)

instance {G : Type*} [Fintype G] {m : ℕ} (d : Densities m) :
    IsProbabilityMeasure (sampleMeasure (G := G) d) := by
  unfold sampleMeasure; infer_instance

/-- uniform exact-matching theorem's tail is the last layer and its head is the first layer.  The
second special layer, reserve and every generic layer are forgotten. -/
def projectVertex {m : ℕ} : VertexRole m → Part
  | Sum.inl i => if i = 3 then 0 else if i = 1 then 1 else 2
  | Sum.inr _ => 2

def projectColour {m : ℕ} : ColourRole m → Bool
  | Sum.inl i => decide (i = 1)
  | Sum.inr _ => false

theorem projectVertex_mass {m : ℕ} (d : Densities m) (p : Part) :
    eventMass (vertexWeight d) (fun v => projectVertex v = p) =
      EndpointOriginalReservoir.vertexWeight d.q p := by
  fin_cases p <;>
    simp [eventMass, vertexWeight, projectVertex, Fintype.sum_sum_type,
      Fin.sum_univ_succ, EndpointOriginalReservoir.vertexWeight]
  linarith [d.vertex_total]

theorem projectColour_mass {m : ℕ} (d : Densities m) (b : Bool) :
    eventMass (colourWeight d) (fun c => projectColour c = b) = coinWeight d.q b := by
  cases b <;>
    simp [eventMass, colourWeight, projectColour, Fintype.sum_sum_type,
      Fin.sum_univ_succ, coinWeight]
  have ht := d.colour_total
  push_cast at ht
  linarith

theorem projectVertex_measurePreserving {m : ℕ} (d : Densities m) :
    MeasurePreserving projectVertex (vertexLaw d).measure
      (EndpointOriginalReservoir.vertexLaw d.q d.q_nonneg d.q_le_half).measure := by
  refine ⟨measurable_of_countable _, ?_⟩
  apply Measure.ext_of_measureReal_singleton
  intro p
  rw [map_measureReal_apply (measurable_of_countable _) (measurableSet_singleton _)]
  change (vertexLaw d).measure.real {v | projectVertex v = p} =
    (EndpointOriginalReservoir.vertexLaw d.q d.q_nonneg d.q_le_half).measure.real
      {p' | p' = p}
  rw [FiniteLaw.real_event, FiniteLaw.real_event]
  simpa [vertexLaw, EndpointOriginalReservoir.vertexLaw] using projectVertex_mass d p

theorem projectColour_measurePreserving {m : ℕ} (d : Densities m) :
    MeasurePreserving projectColour (colourLaw d).measure
      (coinLaw d.q d.q_nonneg (d.q_le_half.trans (by norm_num))).measure := by
  refine ⟨measurable_of_countable _, ?_⟩
  apply Measure.ext_of_measureReal_singleton
  intro b
  rw [map_measureReal_apply (measurable_of_countable _) (measurableSet_singleton _)]
  change (colourLaw d).measure.real {c | projectColour c = b} =
    (coinLaw d.q d.q_nonneg (d.q_le_half.trans (by norm_num))).measure.real
      {b' | b' = b}
  rw [FiniteLaw.real_event, FiniteLaw.real_event]
  simpa [colourLaw, coinLaw] using projectColour_mass d b

def project {G : Type*} {m : ℕ} (s : Sample G m) : OriginalSample G :=
  (fun g => projectVertex (s.1 g), fun g => projectColour (s.2 g))

/-- Exact equality with the pre-existing original exact-matching law.  In particular,
the two endpoint roles are not replaced by independent Bernoulli sets. -/
theorem project_measurePreserving {G : Type*} [Fintype G] {m : ℕ}
    (d : Densities m) :
    MeasurePreserving project (sampleMeasure (G := G) d)
      (originalMeasure d.q d.q_nonneg d.q_le_half) := by
  exact (measurePreserving_pi _ _ (fun _ : G => projectVertex_measurePreserving d)).prod
    (measurePreserving_pi _ _ (fun _ : G => projectColour_measurePreserving d))

def vertexSet {G : Type*} [Fintype G] {m : ℕ} (s : Sample G m)
    (v : VertexRole m) : Finset G := Finset.univ.filter (fun g => s.1 g = v)

def colourSet {G : Type*} [Fintype G] {m : ℕ} (s : Sample G m)
    (c : ColourRole m) : Finset G := Finset.univ.filter (fun g => s.2 g = c)

theorem vertexSet_disjoint {G : Type*} [Fintype G] {m : ℕ} (s : Sample G m)
    {v w : VertexRole m} (h : v ≠ w) : Disjoint (vertexSet s v) (vertexSet s w) := by
  apply Finset.disjoint_left.mpr
  intro g hv hw
  exact h ((Finset.mem_filter.mp hv).2.symm.trans (Finset.mem_filter.mp hw).2)

theorem colourSet_disjoint {G : Type*} [Fintype G] {m : ℕ} (s : Sample G m)
    {c e : ColourRole m} (h : c ≠ e) : Disjoint (colourSet s c) (colourSet s e) := by
  apply Finset.disjoint_left.mpr
  intro g hc he
  exact h ((Finset.mem_filter.mp hc).2.symm.trans (Finset.mem_filter.mp he).2)

@[simp] theorem projectVertex_eq_zero {m : ℕ} (v : VertexRole m) :
    projectVertex v = 0 ↔ v = lastVertex m := by
  rcases v with i | i
  · fin_cases i <;> simp [projectVertex, lastVertex]
  · simp [projectVertex, lastVertex]

@[simp] theorem projectVertex_eq_one {m : ℕ} (v : VertexRole m) :
    projectVertex v = 1 ↔ v = firstVertex m := by
  rcases v with i | i
  · fin_cases i <;> simp [projectVertex, firstVertex]
  · simp [projectVertex, firstVertex]

@[simp] theorem projectColour_eq_true {m : ℕ} (c : ColourRole m) :
    projectColour c = true ↔ c = specialColour m := by
  rcases c with i | i
  · fin_cases i <;> simp [projectColour, specialColour]
  · simp [projectColour, specialColour]

end
end EndpointLayeredSample
