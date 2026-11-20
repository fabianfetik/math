import CorralFormalization.EndpointProof.Flow.Tetrahedron.ConcentrationTails
import CorralFormalization.EndpointProof.Matching.UniversalCore.Buffer.Availability

/-!
Pure inverse-orbit categorical Q laws, without an upstream q-reservoir.
The deterministic section below is used only to inherit pointwise reservoir
facts. All probabilities in the following modules are computed directly
under orbitMeasure; no parent fullMeasure law is imposed or transported.
-/

open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators NNReal ENNReal
namespace AbsorberInputs.CategoricalQ
open EndpointOriginalReservoir EndpointBlockAvailability EndpointSharedSample
open EndpointFullProduct EndpointReservoirAvailability
open EndpointFlow.AbelianTransport EndpointSelector.FixedCardinality
open EndpointMatching.Tetrahedron
noncomputable section
variable {G : Type*} [AddCommGroup G] [Fintype G]

def coordinateForPart (p : Part) : Coordinate := (p,true,true,true,true)

def inputOfChild : Option (Part × Bool) → OrbitInput
  | none => (coordinateForPart 0,coordinateForPart 0,0,false,2)
  | some (p,b) => (coordinateForPart p,coordinateForPart p,p,true,if b then 1 else 0)

theorem childLabel_inputOfChild (l : Option (Part × Bool)) :
    childLabel (inputOfChild l) = l := by
  cases l with
  | none => simp [inputOfChild,childLabel,accepted]
  | some v =>
    rcases v with ⟨p,b⟩
    fin_cases p <;> cases b <;>
      norm_num [inputOfChild,coordinateForPart,childLabel,accepted,rawMinus,originalRole,thinningCoin]

def inputOfLabel (l : Label) : OrbitInput :=
  inputOfChild (Classical.choose (encodeChild_bijective.surjective l))

theorem sevenLabel_inputOfLabel (l : Label) : sevenLabel (inputOfLabel l) = l := by
  rw [sevenLabel,inputOfLabel,childLabel_inputOfChild]
  exact Classical.choose_spec (encodeChild_bijective.surjective l)

/-- This is a deterministic section of fullLabels, not a claim about its
distribution under any parent reservoir law. -/
def labelSection (hodd : Odd (Fintype.card G)) (w : OddOrbit G → Label) : FullSample G :=
  ungroup hodd (fun o => inputOfLabel (w o),coordinateForPart 0)

theorem fullLabels_labelSection (hodd : Odd (Fintype.card G)) (w : OddOrbit G → Label) :
    fullLabels (labelSection hodd w) = w := by
  funext o
  simp [fullLabels,labelSection,regroup_ungroup,sevenLabel_inputOfLabel]

theorem reservoir_labelSection (hodd : Odd (Fintype.card G)) (w : OddOrbit G → Label) :
    ReservoirVertex (labelSection hodd w) true = categoricalQ w := by
  rw [← categoricalQ_fullLabels,fullLabels_labelSection]

theorem pairReservoir (hodd : Odd (Fintype.card G)) (w : OddOrbit G → Label) :
    PairReservoir (categoricalQ w) := by
  rw [← reservoir_labelSection hodd w]
  exact pairReservoir_of_reservoirVertex _ _

theorem goodCandidates_subset_valid (hodd : Odd (Fintype.card G))
    (w : OddOrbit G → Label)
    (r : CorralFormalization.EndpointProof.Probability.QuadraticDeletion.TetrahedronRoots G) :
    goodCandidates (categoricalQ w) r ⊆ validParameterSet r := by
  rw [← reservoir_labelSection hodd w]
  exact sampled_goodCandidates_subset_valid _ _

theorem goodSection_subset_validReduced (hodd : Odd (Fintype.card G))
    (w : OddOrbit G → Label)
    (r : CorralFormalization.EndpointProof.Probability.QuadraticDeletion.TetrahedronRoots G)
    (i : Fin 6) (g : G) :
    (goodCandidates (categoricalQ w) r).filter
      (fun t => CorralFormalization.EndpointProof.Probability.QuadraticDeletion.tetrahedronDirection i t = g) ⊆
      validReducedSection (categoricalQ w) r i g := by
  rw [← reservoir_labelSection hodd w]
  exact EndpointMatching.Tetrahedron.goodSection_subset_validReduced _ _ _ _

theorem representative_iff_label (hodd : Odd (Fintype.card G))
    (r : CorralFormalization.EndpointProof.Probability.QuadraticDeletion.TetrahedronRoots G)
    (t : CorralFormalization.EndpointProof.Probability.QuadraticDeletion.TetrahedronParameters G)
    (hv : geometricallyValid r t) (w : OddOrbit G → Label) (i : Fin 12) :
    categoricalQ w
      (place r.a₁ r.a₂ r.b₁ r.b₂ r.c₁ r.c₂ t.1 t.2.1 t.2.2 (representativeSlot i)) ↔
    w ((representativeOrbitPoint hodd r t hv i).1) = qDemand () i := by
  have h := representative_Q_iff_encoded hodd r t hv (labelSection hodd w) i
  rwa [reservoir_labelSection,fullLabels_labelSection] at h

theorem buffer_coordinate_iff_label (hodd : Odd (Fintype.card G))
    (t : EndpointMatching.UniversalCore.Buffer.Parameters G)
    (hv : EndpointMatching.UniversalCore.Buffer.GeometricallyValid t)
    (w : OddOrbit G → Label) (i : Fin 3) :
    categoricalQ w (i,EndpointMatching.UniversalCore.Buffer.coordinate t i) ↔
    w ((EndpointMatching.UniversalCore.Buffer.orbitPoint hodd t hv i).1) =
      EndpointMatching.UniversalCore.Buffer.demand () i := by
  have h := EndpointMatching.UniversalCore.Buffer.coordinate_Q_iff_encoded
    hodd t hv (labelSection hodd w) i
  rwa [reservoir_labelSection,fullLabels_labelSection] at h

end
end AbsorberInputs.CategoricalQ
