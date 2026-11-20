import CorralFormalization.EndpointProof.Factor.RouterAttachment.Core
import CorralFormalization.EndpointProof.Factor.Allocation.PhysicalRouter

/-! # The actual fixed router prepended for every admissible setting -/

open scoped Classical BigOperators
namespace EndpointFactor.RouterAttachment
open OrdinaryFragments Allocation EndpointRouter EndpointLayeredSample
noncomputable section
universe u
variable {G : Type u} [Fintype G] [AddCommGroup G] [DecidableEq G]
variable {m ℓ : ℕ} {sample : AugmentedSample G m}
variable {special : Fin 3 → Finset G} {W D : Finset G}

namespace PhysicalRouter
variable (R : PhysicalRouter sample special W D ℓ) (F : Family G)
    (hstarts : F.starts = special 1)

/-- Select the unique actual ordinary path beginning at this numerical
router output. -/
def outputKey (i : Fin ℓ) : F.Index := Classical.choose
  ((F.mem_starts (R.output i)).mp (hstarts.symm ▸ R.output_mem i))

@[simp] theorem outputKey_first (i : Fin ℓ) :
    F.first (outputKey R F hstarts i) = R.output i := Classical.choose_spec
  ((F.mem_starts (R.output i)).mp (hstarts.symm ▸ R.output_mem i))

theorem outputKey_bijective : Function.Bijective (outputKey R F hstarts) := by
  constructor
  · intro i j hij
    apply R.output_injective
    exact (outputKey_first R F hstarts i).symm.trans
      ((congrArg F.first hij).trans (outputKey_first R F hstarts j))
  · intro k
    have hk : F.first k ∈ special 1 := by
      rw [← hstarts]
      exact (F.mem_starts _).mpr ⟨k,rfl⟩
    obtain ⟨i,hi⟩ := R.output_covers _ hk
    exact ⟨i,F.first_injective ((outputKey_first R F hstarts i).trans hi)⟩

def outputKeyEquiv : Fin ℓ ≃ F.Index := Equiv.ofBijective _ (outputKey_bijective R F hstarts)

@[simp] theorem outputKeyEquiv_first (i : Fin ℓ) :
    F.first (outputKeyEquiv R F hstarts i) = R.output i := outputKey_first R F hstarts i

/-- The initial ports are enumerated without repeats or omissions. -/
theorem input_image : Finset.univ.image R.input = special 0 := by
  ext g
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i,rfl⟩; exact R.input_mem i
  · exact R.input_covers g

variable (a b : List (Fin ℓ × Fin ℓ))
    (ha : a.Sublist (firstLayer ℓ)) (hb : b.Sublist (secondLayer ℓ))

abbrev routes : Fin ℓ → Segment G := installedRoutes R.first R.second a b

def settingKeys : Fin ℓ ≃ F.Index :=
  (switchProduct b * switchProduct a).trans (outputKeyEquiv R F hstarts)

include ha hb

@[simp] theorem settingKeys_join (i : Fin ℓ) :
    (routes R a b i).last = F.first (settingKeys R F hstarts a b i) := by
  rw [(installedRoutes_endpoints R.first R.second a b ha hb i).2]
  exact (outputKeyEquiv_first R F hstarts _).symm

theorem routes_bodyInventory : bodyInventory (routes R a b) =
    special 0 ∪ fixedInteriorFinset R.first R.second := by
  have hfixed := (R.settings_valid a b ha hb).2.2.1
  ext g
  rw [mem_bodyInventory, Finset.mem_union]
  constructor
  · rintro ⟨i,hi⟩
    have hf := (installedRoutes_endpoints R.first R.second a b ha hb i).1
    simp only [Segment.body, List.mem_cons] at hi
    rcases hi with hi | hi
    · exact Or.inl ((hi.trans hf).symm ▸ R.input_mem i)
    · apply Or.inr
      rw [← hfixed, mem_routeInteriorFinset]
      exact ⟨i,hi⟩
  · rintro (hg | hg)
    · obtain ⟨i,hi⟩ := R.input_covers g hg
      refine ⟨i,?_⟩
      simp only [Segment.body, List.mem_cons]
      exact Or.inl (hi.symm.trans (installedRoutes_endpoints R.first R.second a b ha hb i).1.symm)
    · rw [← hfixed, mem_routeInteriorFinset] at hg
      obtain ⟨i,hi⟩ := hg
      exact ⟨i,by simp [Segment.body,hi]⟩

theorem routes_colorInventory : colorInventory (routes R a b) =
    fixedColorFinset R.first R.second := by
  rw [← (R.settings_valid a b ha hb).2.2.2]
  ext g
  simp only [mem_colorInventory, mem_routeColorFinset]

section Prepend
variable (hvertex : Disjoint (special 0 ∪ fixedInteriorFinset R.first R.second) F.vertices)
    (hcolor : Disjoint (fixedColorFinset R.first R.second) F.colors)

include hvertex hcolor

/-- Construct the actual physical family for this setting.  Both raw
freshness conditions concern physical inventories already fixed before
settings are selected. -/
def prependRouter : Family G :=
  prepend F (routes R a b) (settingKeys R F hstarts a b)
    (settingKeys_join R F hstarts a b ha hb)
    (R.settings_valid a b ha hb).1 (R.settings_valid a b ha hb).2.1
    (by rw [routes_bodyInventory R a b ha hb]; exact hvertex)
    (by rw [routes_colorInventory R a b ha hb]; exact hcolor)

/-- The exact old path is attached to the router output reached by track i. -/
theorem prependRouter_track (i : Fin ℓ) :
    (prependRouter R F hstarts a b ha hb hvertex hcolor).path
      (settingKeys R F hstarts a b i) =
      (routes R a b i).body ++ F.path (outputKeyEquiv R F hstarts
        ((switchProduct b * switchProduct a) i)) := by
  change (routes R a b ((settingKeys R F hstarts a b).symm
    (settingKeys R F hstarts a b i))).body ++ F.path (settingKeys R F hstarts a b i) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- Physical start of the track-indexed concatenation. -/
@[simp] theorem prependRouter_track_first (i : Fin ℓ) :
    (prependRouter R F hstarts a b ha hb hvertex hcolor).first
      (settingKeys R F hstarts a b i) = R.input i := by
  change FragmentChecksum.firstOrZero
    ((routes R a b ((settingKeys R F hstarts a b).symm
      (settingKeys R F hstarts a b i))).body ++ F.path (settingKeys R F hstarts a b i)) = _
  rw [Equiv.symm_apply_apply]
  simp only [Segment.body,List.cons_append,FragmentChecksum.firstOrZero,List.head?_cons,Option.getD_some]
  exact (installedRoutes_endpoints R.first R.second a b ha hb i).1

/-- Physical end after following router track i and its unique ordinary path. -/
@[simp] theorem prependRouter_track_last (i : Fin ℓ) :
    (prependRouter R F hstarts a b ha hb hvertex hcolor).last
      (settingKeys R F hstarts a b i) =
      F.last (outputKeyEquiv R F hstarts ((switchProduct b * switchProduct a) i)) := by
  exact prepend_last _ _ _ _ _ _ _ _ _

@[simp] theorem prependRouter_vertices :
    (prependRouter R F hstarts a b ha hb hvertex hcolor).vertices =
      (special 0 ∪ fixedInteriorFinset R.first R.second) ∪ F.vertices := by
  rw [prependRouter,prepend_vertices,routes_bodyInventory R a b ha hb]

@[simp] theorem prependRouter_colors :
    (prependRouter R F hstarts a b ha hb hvertex hcolor).colors =
      fixedColorFinset R.first R.second ∪ F.colors := by
  rw [prependRouter,prepend_colors,routes_colorInventory R a b ha hb]

@[simp] theorem prependRouter_starts :
    (prependRouter R F hstarts a b ha hb hvertex hcolor).starts = special 0 := by
  rw [prependRouter,prepend_starts]
  have he : (fun i => (routes R a b i).first) = R.input := by
    funext i
    exact (installedRoutes_endpoints R.first R.second a b ha hb i).1
  rw [he,input_image R]

@[simp] theorem prependRouter_ends :
    (prependRouter R F hstarts a b ha hb hvertex hcolor).ends = F.ends := by
  exact prepend_ends _ _ _ _ _ _ _ _

end Prepend
end PhysicalRouter
end
end EndpointFactor.RouterAttachment
