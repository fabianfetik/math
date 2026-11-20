import CorralFormalization.EndpointProof.AbsorberInputs.AffineAvailability.ActiveSlots
import CorralFormalization.EndpointProof.AbsorberInputs.AffineAvailability.FloorPacking
import CorralFormalization.EndpointProof.AbsorberInputs.PackedAvailability.ExistingLaw
import CorralFormalization.EndpointProof.Sampling.FullAvailability

/-!
# Affine construction and one shared categorical availability event

For every query the affine and collision data construct the packing and the
sampled-orbit embedding. Requested labels may vary by candidate and may be
absent on some of its orbits. The whole signed geometric support is used for
later numerical avoidance, including the orbits without label requirements.
-/

open MeasureTheory ProbabilityTheory
open scoped Classical NNReal

namespace AbsorberInputs.AffineAvailability

open AbsorberInputs.CandidatePacking EndpointOriginalReservoir
open EndpointBlockAvailability EndpointSharedSample

noncomputable section

variable {Q G : Type*} [Fintype Q] [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The fixed fraction supplied by the explicit floor packing. -/
def packingFraction (m : ℕ) : ℝ := 1 / (2*(4*(m : ℝ)*m))

theorem packingFraction_pos (m : ℕ) (hm : 0 < m) : 0 < packingFraction m := by
  unfold packingFraction
  positivity

/-- The explicit per-query rate before absorbing a polynomial query count. -/
def packingRate (m : ℕ) (v : ℝ) : ℝ := packingFraction m * (min v 1)^m / 8

theorem packingRate_pos (m : ℕ) (hm : 0 < m) (v : ℝ) (hv : 0 < v) :
    0 < packingRate m v := by
  have hp := packingFraction_pos m hm
  have hv' : 0 < min v 1 := lt_min hv (by norm_num)
  unfold packingRate
  positivity

/-- Success expressed directly in the actual affine representatives rather
than in a separately supplied categorical embedding. -/
def actualSuccess {L : Type*} (e r s : Q → ℕ) (D : ∀ q, Data (e q) (r q) (s q) G)
    {M : ℕ} (P : ∀ q, Packed (D q) M) (hodd : Odd (Fintype.card G))
    (require : ∀ q, (Fin (e q) → G) → Fin (r q) → Option L)
    (q : Q) (i : Fin M) (ω : OddOrbit G → L) : Prop :=
  ∀ j l, require q ((P q).parameter i) j = some l →
    ω ((P q).orbitEmbedding hodd (i,j)) = l

def successfulCandidates {L : Type*} (e r s : Q → ℕ) (D : ∀ q, Data (e q) (r q) (s q) G)
    {M : ℕ} (P : ∀ q, Packed (D q) M) (hodd : Odd (Fintype.card G))
    (require : ∀ q, (Fin (e q) → G) → Fin (r q) → Option L)
    (q : Q) (ω : OddOrbit G → L) : Finset (Fin M) := by
  classical
  exact Finset.univ.filter (fun i => actualSuccess e r s D P hodd require q i ω)

/-- Paper-facing event: the count refers to actual successful candidates,
whose full signed supports are physically distinct, followed by any later
numerical forbidden set smaller than that actual successful count. -/
def AffineAvailabilityEvent {L : Type*}
    (e r s : Q → ℕ) (D : ∀ q, Data (e q) (r q) (s q) G)
    {M : ℕ} (P : ∀ q, Packed (D q) M) (hodd : Odd (Fintype.card G))
    (require : ∀ q, (Fin (e q) → G) → Fin (r q) → Option L)
    (threshold : ℝ) (ω : OddOrbit G → L) : Prop :=
  ∀ q,
    let S := successfulCandidates e r s D P hodd require q ω
    threshold ≤ (S.card : ℝ) ∧
    (S.image (fullSupport e r s D P q)).card = S.card ∧
    ∀ F : Finset G, F.card < S.card →
      ∃ i ∈ S, Disjoint (fullSupport e r s D P q i) F

omit [Fintype Q] in
/-- The probability event implies the literal requested-label event and
counts distinct signed supports, without assuming either correspondence. -/
theorem affineAvailabilityEvent_of_fullSupportEvent
    {L : Type*} [Fintype L] [MeasurableSpace L] [MeasurableSingletonClass L]
    (e r s : Q → ℕ) (D : ∀ q, Data (e q) (r q) (s q) G)
    {M : ℕ} (P : ∀ q, Packed (D q) M) (hodd : Odd (Fintype.card G))
    (hr : ∀ q, 0 < r q)
    (require : ∀ q, (Fin (e q) → G) → Fin (r q) → Option L)
    (threshold : ℝ) (ω : OddOrbit G → L)
    (hgood : PackedAvailability.FullSupportEvent
      (activeEmbedding e r s D P hodd require) (fullSupport e r s D P)
      (activeDemand e r s D P require) (fun _ => threshold) ω) :
    AffineAvailabilityEvent e r s D P hodd require threshold ω := by
  classical
  intro q
  have hequiv (i : Fin M) :
      PackedAvailability.project (activeEmbedding e r s D P hodd require q) ω i =
        activeDemand e r s D P require q i ↔
      actualSuccess e r s D P hodd require q i ω := by
    change (fun j : Active e r s D P require q i =>
      ω (activeEmbedding e r s D P hodd require q ⟨i,j⟩)) =
        activeDemand e r s D P require q i ↔ _
    exact active_word_iff_requirements e r s D P hodd require q i ω
  have hcount : threshold ≤
      ((successfulCandidates e r s D P hodd require q ω).card : ℝ) := by
    simpa only [successfulCandidates, ← hequiv] using (hgood q).1
  refine ⟨hcount, ?_, ?_⟩
  · exact Finset.card_image_of_injective _ ((P q).physical_support_injective (hr q))
  · intro F hF
    obtain ⟨i, hi, hd⟩ := (hgood q).2 F
      (by simpa only [successfulCandidates, ← hequiv] using hF)
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hequiv i).mp hi⟩, hd⟩

/-- Complete affine and categorical packed-availability event. The only existence input is
ordinary affine coefficient/collision data: neither an orbit embedding nor
an already-good sample or packed-candidate family is assumed. The family
`P` is selected before the shared sample and all later queries and forbidden
sets. Its entries contain actual valid affine gadgets and pairwise disjoint
full signed numerical supports. -/
theorem affine_categorical_availability
    (e r s : Q → ℕ) (D : ∀ q, Data (e q) (r q) (s q) G)
    (hodd : Odd (Fintype.card G)) (m C : ℕ) (hm : 0 < m)
    (hr : ∀ q, 0 < r q) (hrm : ∀ q, r q ≤ m)
    (hreg : ∀ q, (D q).Regular) (hpiv : ∀ q, (D q).IndividualPivots)
    (hC : ∀ q, (D q).collisionCount ≤ C)
    (hn : 2*C < Fintype.card G)
    (hnFloor : 2*(4*m*m) ≤ Fintype.card G)
    (p τ : ℝ≥0) (hLaw : 3*p+3*τ ≤ 1)
    (require : ∀ q, (Fin (e q) → G) → Fin (r q) → Option Label)
    (v : ℝ) (hv : 0 ≤ v)
    (hmin : ∀ q t, (D q).Valid t → ∀ j l, require q t j = some l →
      v ≤ (labelWeights p τ l : ℝ)) :
    ∃ P : ∀ q, Packed (D q) (Fintype.card G/(4*m*m)),
      (orbitMeasure p τ hLaw).real
        {ω | ¬ PackedAvailability.FullSupportEvent
          (activeEmbedding e r s D P hodd require)
          (fullSupport e r s D P)
          (activeDemand e r s D P require)
          (fun _ => packingFraction m * Fintype.card G * (min v 1)^m/2) ω} ≤
      (Fintype.card Q : ℝ) *
        Real.exp (-(packingFraction m * Fintype.card G * (min v 1)^m)/8) := by
  let M := Fintype.card G/(4*m*m)
  let P : ∀ q, Packed (D q) M := fun q =>
    Classical.choice (exists_linear_packed (D q) hodd (hr q) (hreg q) (hpiv q)
      m C (hrm q) (hC q) hn)
  refine ⟨P, ?_⟩
  apply PackedAvailability.seven_label_full_support_linear_event_tail p τ hLaw
    (activeEmbedding e r s D P hodd require) (fullSupport e r s D P)
    (fun q => fullSupport_disjoint e r s D P q)
    (activeDemand e r s D P require) m (min v 1) (le_min hv (by norm_num))
    (min_le_right _ _) (fun q i => (active_card_le e r s D P require q i).trans (hrm q))
    (fun q i j => ?_) (Fintype.card G) (packingFraction m) (fun q => ?_)
  · exact (min_le_left v 1).trans (hmin q ((P q).parameter i) ((P q).valid i) j.val
      (activeDemand e r s D P require q i j) (activeDemand_spec e r s D P require q i j))
  · simpa only [Fintype.card_fin, M, packingFraction] using
      affine_packing_floor_linear (Fintype.card G) m hm hnFloor

/-- The end-to-end statement for an arbitrary finite categorical alphabet
and arbitrary independent per-orbit laws. Actual requested labels may vary
with the query and candidate; unrequested orbits still remain in the full
support which must avoid every later forbidden numerical set. -/
theorem affine_general_categorical_availability
    {L : Type*} [Fintype L] [MeasurableSpace L] [MeasurableSingletonClass L]
    (ν : OddOrbit G → Measure L) [∀ o, IsProbabilityMeasure (ν o)]
    (e r s : Q → ℕ) (D : ∀ q, Data (e q) (r q) (s q) G)
    (hodd : Odd (Fintype.card G)) (m C : ℕ) (hm : 0 < m)
    (hr : ∀ q, 0 < r q) (hrm : ∀ q, r q ≤ m)
    (hreg : ∀ q, (D q).Regular) (hpiv : ∀ q, (D q).IndividualPivots)
    (hC : ∀ q, (D q).collisionCount ≤ C)
    (hn : 2*C < Fintype.card G)
    (hnFloor : 2*(4*m*m) ≤ Fintype.card G)
    (require : ∀ q, (Fin (e q) → G) → Fin (r q) → Option L)
    (v : ℝ) (hv : 0 ≤ v)
    (hmin : ∀ q t (ht : (D q).Valid t) j l, require q t j = some l →
      v ≤ (ν (actualOrbit hodd ((D q).value t j) (ht.1 j))).real {l}) :
    ∃ P : ∀ q, Packed (D q) (Fintype.card G/(4*m*m)),
      (PackedAvailability.categoricalMeasure ν).real
        {ω | ¬ AffineAvailabilityEvent e r s D P hodd require
          (packingFraction m * Fintype.card G * (min v 1)^m/2) ω} ≤
      (Fintype.card Q : ℝ) *
        Real.exp (-(packingFraction m * Fintype.card G * (min v 1)^m)/8) := by
  let M := Fintype.card G/(4*m*m)
  let P : ∀ q, Packed (D q) M := fun q =>
    Classical.choice (exists_linear_packed (D q) hodd (hr q) (hreg q) (hpiv q)
      m C (hrm q) (hC q) hn)
  refine ⟨P, ?_⟩
  have htail := PackedAvailability.categorical_full_support_linear_event_tail_clipped ν
    (activeEmbedding e r s D P hodd require) (fullSupport e r s D P)
    (fun q => fullSupport_disjoint e r s D P q) (activeDemand e r s D P require)
    m v hv (fun q i => (active_card_le e r s D P require q i).trans (hrm q))
    (fun q i j => hmin q ((P q).parameter i) ((P q).valid i) j.val
      (activeDemand e r s D P require q i j) (activeDemand_spec e r s D P require q i j))
    (Fintype.card G) (packingFraction m) (fun q => by
      simpa only [Fintype.card_fin, M, packingFraction] using
        affine_packing_floor_linear (Fintype.card G) m hm hnFloor)
  apply (measureReal_mono ?_ (measure_ne_top _ _)).trans htail
  intro ω hbad hgood
  exact hbad (affineAvailabilityEvent_of_fullSupportEvent e r s D P hodd hr require _ ω hgood)

/-- A polynomial number of queries is eventually absorbed at half the
positive fixed-density rate. The threshold is independent of group type,
query family, affine data, label prescriptions, and the later forbidden set. -/
theorem affine_categorical_eventual_threshold
    (m C k : ℕ) (K v : ℝ) (hm : 0 < m) (hv : 0 < v) :
    ∃ N : ℕ, ∀ n ≥ N,
      2*C < n ∧ 2*(4*m*m) ≤ n ∧
      K*(n : ℝ)^k * Real.exp (-(packingRate m v)*n) ≤
        Real.exp (-(packingRate m v/2)*n) := by
  obtain ⟨N₀, hN₀⟩ := polynomial_failure_absorbed K (packingRate m v) k
    (packingRate_pos m hm v hv)
  refine ⟨max (2*C+1) (max (2*(4*m*m)) N₀), ?_⟩
  intro n hn
  have hC : 2*C+1 ≤ n := (le_max_left _ _).trans hn
  have hfloor : 2*(4*m*m) ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hrate : N₀ ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  exact ⟨by omega, hfloor, hN₀ n hrate⟩

omit [DecidableEq G] in
/-- Every event on the sampled orbit labels has exactly the same probability
under the original augmented sample and under the categorical orbit law. -/
theorem fullSample_orbit_event_probability
    (hodd : Odd (Fintype.card G))
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1)
    (p τ : ℝ≥0) (hLaw : 3*p+3*τ ≤ 1)
    (hP : (p : ℝ) = EndpointOriginalReservoir.rho q η*a)
    (hQ : (τ : ℝ) = EndpointOriginalReservoir.rho q η*b)
    (E : (OddOrbit G → Label) → Prop) :
    (EndpointFullProduct.fullMeasure q η a b hq0 hq1 hη0 hη1 ha hb hab).real
      {ω : EndpointFullProduct.FullSample G | E (EndpointFullProduct.fullLabels ω)} =
    (orbitMeasure p τ hLaw).real {ω | E ω} := by
  have hp := EndpointFullProduct.fullLabels_measurePreserving hodd q η a b
    hq0 hq1 hη0 hη1 ha hb hab p τ hLaw hP hQ
  exact hp.measureReal_preimage (s := {ω | E ω}) (by measurability)

end
end AbsorberInputs.AffineAvailability

namespace AbsorberInputs.AffineAvailability

open AbsorberInputs.CandidatePacking EndpointOriginalReservoir
open EndpointBlockAvailability EndpointSharedSample
open MeasureTheory ProbabilityTheory
open scoped Classical NNReal

noncomputable section

universe uG uQ uL

/-- General packed-availability for arbitrary finite categorical alphabets and independent
per-orbit laws, uniformly over all sufficiently large odd abelian groups.
The group, queries, affine forms, categorical laws, and demand policy all
follow the single threshold; the one resulting sample precedes every later
query and forbidden numerical set. -/
theorem uniform_affine_general_categorical_availability
    (m C k : ℕ) (K v : ℝ) (hm : 0 < m) (hv : 0 < v) :
    ∃ N : ℕ,
      ∀ (G : Type uG) [AddCommGroup G] [Fintype G] [DecidableEq G]
        (Q : Type uQ) [Fintype Q] (L : Type uL) [Fintype L]
        [MeasurableSpace L] [MeasurableSingletonClass L]
        (hodd : Odd (Fintype.card G)),
        N ≤ Fintype.card G →
        (Fintype.card Q : ℝ) ≤ K*(Fintype.card G : ℝ)^k →
        ∀ (e r s : Q → ℕ) (D : ∀ q, Data (e q) (r q) (s q) G),
          (∀ q, 0 < r q) → (∀ q, r q ≤ m) →
          (∀ q, (D q).Regular) → (∀ q, (D q).IndividualPivots) →
          (∀ q, (D q).collisionCount ≤ C) →
          ∀ (ν : OddOrbit G → Measure L) [∀ o, IsProbabilityMeasure (ν o)]
            (require : ∀ q, (Fin (e q) → G) → Fin (r q) → Option L),
            (∀ q t (ht : (D q).Valid t) j l, require q t j = some l →
              v ≤ (ν (actualOrbit hodd ((D q).value t j) (ht.1 j))).real {l}) →
            ∃ P : ∀ q, Packed (D q) (Fintype.card G/(4*m*m)),
              (PackedAvailability.categoricalMeasure ν).real
                {ω | ¬ AffineAvailabilityEvent e r s D P hodd require
                  (packingFraction m * Fintype.card G * (min v 1)^m/2) ω} ≤
                Real.exp (-(packingRate m v/2)*Fintype.card G) := by
  obtain ⟨N, hN⟩ := affine_categorical_eventual_threshold m C k K v hm hv
  refine ⟨N, ?_⟩
  intro G _ _ _ Q _ L _ _ _ hodd hn hQ e r s D hr hrm hreg hpiv hC ν _ require hmin
  have hb := hN (Fintype.card G) hn
  obtain ⟨P, hP⟩ := affine_general_categorical_availability ν e r s D hodd m C hm hr hrm
    hreg hpiv hC hb.1 hb.2.1 require v (le_of_lt hv) hmin
  refine ⟨P, hP.trans ?_⟩
  have hexp : Real.exp (-(packingFraction m * Fintype.card G * (min v 1)^m)/8) =
      Real.exp (-(packingRate m v)*Fintype.card G) := by
    congr 1
    unfold packingRate
    ring
  rw [hexp]
  exact (mul_le_mul_of_nonneg_right hQ (Real.exp_nonneg _)).trans hb.2.2

/-- The full standalone packed-availability conclusion for every finite odd abelian group,
with polynomially many queries and a single event before all later queries
and numerical deletions. The threshold is chosen before the group, its
queries, all affine forms, and all label prescriptions. -/
theorem uniform_affine_categorical_availability
    (m C k : ℕ) (K v : ℝ) (hm : 0 < m) (hv : 0 < v) :
    ∃ N : ℕ,
      ∀ (G : Type uG) [AddCommGroup G] [Fintype G] [DecidableEq G]
        (Q : Type uQ) [Fintype Q] (hodd : Odd (Fintype.card G)),
        N ≤ Fintype.card G →
        (Fintype.card Q : ℝ) ≤ K*(Fintype.card G : ℝ)^k →
        ∀ (e r s : Q → ℕ) (D : ∀ q, Data (e q) (r q) (s q) G),
          (∀ q, 0 < r q) → (∀ q, r q ≤ m) →
          (∀ q, (D q).Regular) → (∀ q, (D q).IndividualPivots) →
          (∀ q, (D q).collisionCount ≤ C) →
          ∀ (p τ : ℝ≥0) (hLaw : 3*p+3*τ ≤ 1)
            (require : ∀ q, (Fin (e q) → G) → Fin (r q) → Option Label),
            (∀ q t, (D q).Valid t → ∀ j l, require q t j = some l →
              v ≤ (labelWeights p τ l : ℝ)) →
            ∃ P : ∀ q, Packed (D q) (Fintype.card G/(4*m*m)),
              (orbitMeasure p τ hLaw).real
                {ω | ¬ AffineAvailabilityEvent e r s D P hodd require
                  (packingFraction m * Fintype.card G * (min v 1)^m/2) ω} ≤
                Real.exp (-(packingRate m v/2)*Fintype.card G) := by
  obtain ⟨N, hN⟩ := affine_categorical_eventual_threshold m C k K v hm hv
  refine ⟨N, ?_⟩
  intro G _ _ _ Q _ hodd hn hQ e r s D hr hrm hreg hpiv hC p τ hLaw require hmin
  have hb := hN (Fintype.card G) hn
  obtain ⟨P, hP⟩ := affine_categorical_availability e r s D hodd m C hm hr hrm
    hreg hpiv hC hb.1 hb.2.1 p τ hLaw require v (le_of_lt hv) hmin
  have htransfer : (orbitMeasure p τ hLaw).real
      {ω | ¬ AffineAvailabilityEvent e r s D P hodd require
        (packingFraction m * Fintype.card G * (min v 1)^m/2) ω} ≤
      (orbitMeasure p τ hLaw).real
        {ω | ¬ PackedAvailability.FullSupportEvent
          (activeEmbedding e r s D P hodd require) (fullSupport e r s D P)
          (activeDemand e r s D P require)
          (fun _ => packingFraction m * Fintype.card G * (min v 1)^m/2) ω} := by
    apply measureReal_mono ?_ (measure_ne_top _ _)
    intro ω hbad hgood
    exact hbad (affineAvailabilityEvent_of_fullSupportEvent e r s D P hodd hr require _ ω hgood)
  refine ⟨P, (htransfer.trans hP).trans ?_⟩
  have hexp : Real.exp (-(packingFraction m * Fintype.card G * (min v 1)^m)/8) =
      Real.exp (-(packingRate m v)*Fintype.card G) := by
    congr 1
    unfold packingRate
    ring
  rw [hexp]
  exact (mul_le_mul_of_nonneg_right hQ (Real.exp_nonneg _)).trans hb.2.2

/-- The same uniform result on the actual augmented source sample. The
orbit labels are extracted from that sample by the already proved law
transport, so the event is on the same augmentation as the endpoint proof. -/
theorem uniform_affine_availability_on_augmented_sample
    (m C k : ℕ) (K v : ℝ) (hm : 0 < m) (hv : 0 < v) :
    ∃ N : ℕ,
      ∀ (G : Type uG) [AddCommGroup G] [Fintype G] [DecidableEq G]
        (Q : Type uQ) [Fintype Q] (hodd : Odd (Fintype.card G)),
        N ≤ Fintype.card G →
        (Fintype.card Q : ℝ) ≤ K*(Fintype.card G : ℝ)^k →
        ∀ (e r s : Q → ℕ) (D : ∀ q, Data (e q) (r q) (s q) G),
          (∀ q, 0 < r q) → (∀ q, r q ≤ m) →
          (∀ q, (D q).Regular) → (∀ q, (D q).IndividualPivots) →
          (∀ q, (D q).collisionCount ≤ C) →
          ∀ (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2)
            (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1)
            (p τ : ℝ≥0) (_hLaw : 3*p+3*τ ≤ 1)
            (_hP : (p : ℝ) = EndpointOriginalReservoir.rho q η*a)
            (_hQ : (τ : ℝ) = EndpointOriginalReservoir.rho q η*b)
            (require : ∀ q, (Fin (e q) → G) → Fin (r q) → Option Label),
            (∀ q t, (D q).Valid t → ∀ j l, require q t j = some l →
              v ≤ (labelWeights p τ l : ℝ)) →
            ∃ P : ∀ q, Packed (D q) (Fintype.card G/(4*m*m)),
              (EndpointFullProduct.fullMeasure q η a b hq0 hq1 hη0 hη1 ha hb hab).real
                {ω : EndpointFullProduct.FullSample G |
                  ¬ AffineAvailabilityEvent e r s D P hodd require
                    (packingFraction m * Fintype.card G * (min v 1)^m/2)
                    (EndpointFullProduct.fullLabels ω)} ≤
                Real.exp (-(packingRate m v/2)*Fintype.card G) := by
  obtain ⟨N,hN⟩ := uniform_affine_categorical_availability m C k K v hm hv
  refine ⟨N, ?_⟩
  intro G _ _ _ Q _ hodd hn hqcard e r s D hr hrm hreg hpiv hC
    q η a b hq0 hq1 hη0 hη1 ha hb hab p τ hLaw hP hQ require hmin
  obtain ⟨P,hPbound⟩ := hN G Q hodd hn hqcard e r s D hr hrm hreg hpiv hC
    p τ hLaw require hmin
  refine ⟨P, ?_⟩
  let E : (OddOrbit G → Label) → Prop := fun ω =>
    ¬ AffineAvailabilityEvent e r s D P hodd require
      (packingFraction m * Fintype.card G * (min v 1)^m/2) ω
  have heq := fullSample_orbit_event_probability hodd q η a b hq0 hq1 hη0 hη1 ha hb hab
    p τ hLaw hP hQ E
  change (EndpointFullProduct.fullMeasure q η a b hq0 hq1 hη0 hη1 ha hb hab).real
    {ω : EndpointFullProduct.FullSample G | E (EndpointFullProduct.fullLabels ω)} ≤ _
  rw [heq]
  exact hPbound

end
end AbsorberInputs.AffineAvailability
