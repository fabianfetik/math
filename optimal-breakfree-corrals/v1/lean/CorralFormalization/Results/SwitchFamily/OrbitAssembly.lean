import CorralFormalization.Results.SwitchFamily.FamilySwitches
import CorralFormalization.Results.GeneralTiles.TerraceTileConstruction
import CorralFormalization.Results.PrimeHeight.ModelBridges

/-!
# Assembly of switch choices into the full physical orbit census

For a specified genuine terrace and the fixed layout of Appendix A, this
module joins the simultaneous-switch permutation, the general marker lemma,
and the actual physical census. The remaining input `hmod` requires every
chosen permutation to be realized as actual palette- and edge-preserving
row modifications. The concrete Appendix A site geometry, marker isolation,
different-owner and `hmod` inputs are not assumed to have been constructed
by this file.
-/

open Finset EndpointRouter CorralLatinTailMarker
open CorralFormalization.PhysicalCorral CorralFormalization.PhysicalCensus
open CorralFormalization.Results.PrimeHeight
open CorralFormalization.LatinCompletion
open CorralFormalization.LatinCompletion.TerraceCompletion
open CorralFormalization.LatinCompletion.GeneralTiles
open CorralFormalization.Results.SwitchFamily.FamilySwitches

namespace CorralFormalization.Results.SwitchFamily.OrbitAssembly

noncomputable section

variable {h n : ℕ} [NeZero h] [NeZero n] [NeZero (h*n)]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The exact `2^k` orbit lower bound from actual switch permutations and
actual row-modification witnesses, with `k` the number of disjoint pairs.
All input markers and owner inequalities refer to physical sites of the
given baseline family. No orbit-count or asymmetric-family premise occurs. -/
theorem fixed_layout_switches_give_asymmetric_orbits
    (D : DirectedTerrace n) (hn : n=2*h-1) (hsmall : 65≤n)
    (hp : HasSpecifiedPrefix D) (tiles : CyclicTiling h ι)
    (p : ZMod h) (hthree : tiles.threeStarts={p} ∨ tiles.threeStarts={p,p-3})
    (layer : MatchingLayer (ZMod (h*n)))
    (mark : Finset (ZMod (h*n)) → ZMod (h*n))
    (hmark : ∀ R ∈ tiles.family (completedOfSpecifiedPrefix D hsmall hp),
      mark R ∈ R ∧ layer.Isolated (mark R))
    (howner : ∀ e ∈ layer.edges,
      ∃ R ∈ tiles.family (completedOfSpecifiedPrefix D hsmall hp), e.1 ∈ R ∧ e.2 ∉ R)
    (hmod : ∀ T ∈ layer.edges.toFinset.powerset,
      ∃ P : RowModification n (tiles.family (completedOfSpecifiedPrefix D hsmall hp)),
        P.family = switchedFamily layer (tiles.family (completedOfSpecifiedPrefix D hsmall hp)) T) :
    2^layer.edges.length ≤ (allAsymmetricCorralOrbits h n).card := by
  classical
  let base := tiles.family (completedOfSpecifiedPrefix D hsmall hp)
  let choices := layer.edges.toFinset.powerset
  let out := switchedFamily layer base
  have hdis : ∀ R ∈ base, ∀ S ∈ base, R ≠ S → Disjoint R S := by
    intro R hR S hS hne
    exact tiles.disjoint _ hn (by omega) R S hR hS hne
  have hinj : Set.InjOn out (choices : Set (Finset (ZMod (h*n) × ZMod (h*n)))) :=
    switchedFamily_injective_on_choices layer base mark hdis hmark howner
  have hw : width n = h*n := LatinTransfer.optimal_width (NeZero.pos h) hn
  have hvalid : ∀ T ∈ choices, out T ∈ validOptimalFamilies h n := by
    intro T hT
    obtain ⟨P,hP⟩ := hmod T hT
    apply (mem_validOptimalFamilies_iff_local (by omega) hw (out T)).mpr
    refine ⟨?_,?_,?_⟩
    · change (imageFamily base (selectedMotion layer T)).card = h
      rw [imageFamily_card]
      exact tiles.card _ hn (by omega)
    · exact imageFamily_disjoint base (selectedMotion layer T) hdis
    · intro R hR
      change R ∈ switchedFamily layer base T at hR
      rw [← hP] at hR
      obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hR
      exact P.palette r
  have hidentity : ∀ T ∈ choices, ∀ U ∈ choices, ∀ f : Motion (h*n),
      f.onFamily (out T) = out U → f = Motion.rotation 0 := by
    intro T hT U hU f hf
    obtain ⟨P,hP⟩ := hmod T hT
    obtain ⟨Q,hQ⟩ := hmod U hU
    apply explicit_modified_same_layout_identity D D hn hsmall hp hp tiles P Q p hthree f
    rw [hP,hQ]
    exact hf
  have hOrbitsInj : Set.InjOn (fun T => physicalOrbit (out T))
      (choices : Set (Finset (ZMod (h*n) × ZMod (h*n)))) := by
    intro T hT U hU heq
    obtain ⟨f,hf⟩ := (physicalOrbit_eq_iff (out T) (out U)).mp heq
    have hfid := hidentity T hT U hU f hf
    rw [hfid] at hf
    have hfamilies : out T = out U := by simpa using hf
    exact hinj hT hU hfamilies
  have hsub : choices.image (fun T => physicalOrbit (out T)) ⊆
      allAsymmetricCorralOrbits h n := by
    intro O hO
    obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hO
    have ha : PhysicallyAsymmetric (out T) := by
      intro f hf
      exact hidentity T hT T hT f hf
    apply Finset.mem_image.mpr
    exact ⟨out T,Finset.mem_filter.mpr ⟨hvalid T hT,ha⟩,rfl⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hOrbitsInj] at hc
  simpa [choices, Finset.card_powerset, List.toFinset_card_of_nodup layer.nodup] using hc

end
end CorralFormalization.Results.SwitchFamily.OrbitAssembly
