import CorralFormalization.EndpointProof.Matching.Fractional.RawEvent.Adaptive
import CorralFormalization.EndpointProof.Matching.AbsorptionAssembly.PhysicalMatching

/-! Raw degrees are cardinalities of actual rooted, signed, additive edges.
The root need not belong to the sampled inventory; both partner vertices do.
-/
open scoped Classical BigOperators symmDiff

namespace EndpointFractionalRawEvent
open EndpointOriginalReservoir EndpointFullProduct
open EndpointFlow.AbelianTransport EndpointMatching.AbsorptionAssembly
noncomputable section
variable {G : Type*} [Fintype G] [AddCommGroup G]

/-- Physical numerical parameter for every candidate through the root. -/
def rawParameters (s : OriginalSample G) (i : Fin 3) (v : G) : Finset G :=
  if i=0 then Finset.univ.filter (fun y => y ∈ rawSet s 1 ∧ y-v ∈ rawSet s 2)
  else if i=1 then Finset.univ.filter (fun x => x ∈ rawSet s 0 ∧ v-x ∈ rawSet s 2)
  else Finset.univ.filter (fun x => x ∈ rawSet s 0 ∧ x+v ∈ rawSet s 1)

def signedRoot (i : Fin 3) (v : G) : Vertex G := (i,if i=1 then v else -v)

def edgeAt (i : Fin 3) (v t : G) : Finset (Vertex G) :=
  if i=0 then {(0,-v),(1,t),(2,-(t-v))}
  else if i=1 then {(0,-t),(1,v),(2,-(v-t))}
  else {(0,-t),(1,t+v),(2,-v)}

def rawEdgesAt (s : OriginalSample G) (i : Fin 3) (v : G) : Finset (Finset (Vertex G)) :=
  (rawParameters s i v).image (edgeAt i v)

def signedRawTarget (s : OriginalSample G) : Finset (Vertex G) :=
  signedTarget (rawSet s 0) (rawSet s 1) (rawSet s 2)

private theorem product_sum_card (S T : Finset G) (a b : G → G) :
    (∑ g, setBit S (a g)*setBit T (b g)) =
      ((Finset.univ.filter (fun g => a g ∈ S ∧ b g ∈ T)).card : ℝ) := by
  have he (g : G) : setBit S (a g)*setBit T (b g) =
      if a g ∈ S ∧ b g ∈ T then (1:ℝ) else 0 := by
    by_cases hS : a g ∈ S <;> by_cases hT : b g ∈ T <;> simp [setBit,hS,hT]
  simp_rw [he]
  simp

/-- The real-valued raw degree is the exact cardinality of its concrete
physical candidate parameters. -/
theorem rawDegree_eq_card_parameters (s : OriginalSample G) (i : Fin 3) (v : G) :
    rawDegree s i v = ((rawParameters s i v).card : ℝ) := by
  rw [rawDegree_eq_targetDegree]
  fin_cases i <;> simp [targetDegree,rawParameters,rawTarget,product_sum_card]

/-- Three tagged roles remain distinct even at numerical coincidences. -/
theorem edgeAt_hyperedge (i : Fin 3) (v t : G) : Hyperedge (edgeAt i v t) := by
  fin_cases i
  · refine ⟨-v,t,-(t-v),?_,by simp [edgeAt]⟩
    simp [sub_eq_add_neg,neg_add_rev,add_assoc,add_comm,add_left_comm]
  · refine ⟨-t,v,-(v-t),?_,by simp [edgeAt]⟩
    simp [sub_eq_add_neg,neg_add_rev,add_assoc,add_comm,add_left_comm]
  · refine ⟨-t,t+v,-v,?_,by simp [edgeAt]⟩
    simp [add_assoc,add_comm,add_left_comm]

theorem signedRoot_mem_edgeAt (i : Fin 3) (v t : G) : signedRoot i v ∈ edgeAt i v t := by
  fin_cases i <;> simp [edgeAt,signedRoot]

/-- The physical parameter identifies the actual tagged edge injectively. -/
theorem edgeAt_injective (i : Fin 3) (v : G) : Function.Injective (edgeAt (G := G) i v) := by
  intro t u he
  fin_cases i
  · have hm : (1,t) ∈ edgeAt (0 : Fin 3) v u := he ▸ (by simp [edgeAt])
    simpa [edgeAt,Prod.mk.injEq] using hm
  · have hm : (0,-t) ∈ edgeAt (1 : Fin 3) v u := he ▸ (by simp [edgeAt])
    have h : -t = -u := by simpa [edgeAt,Prod.mk.injEq] using hm
    exact neg_injective h
  · have hm : (0,-t) ∈ edgeAt (2 : Fin 3) v u := he ▸ (by simp [edgeAt])
    have h : -t = -u := by simpa [edgeAt,Prod.mk.injEq] using hm
    exact neg_injective h

/-- Exact raw degree as number of actual additive edges through the signed
root; all later collision arguments may use this identity directly. -/
theorem rawDegree_eq_card_edges (s : OriginalSample G) (i : Fin 3) (v : G) :
    rawDegree s i v = ((rawEdgesAt s i v).card : ℝ) := by
  rw [rawDegree_eq_card_parameters]
  unfold rawEdgesAt
  rw [Finset.card_image_of_injective _ (edgeAt_injective i v)]

theorem rawEdgesAt_valid (s : OriginalSample G) (i : Fin 3) (v : G) :
    ∀ E ∈ rawEdgesAt s i v, Hyperedge E := by
  intro E hE
  obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hE
  exact edgeAt_hyperedge i v t

theorem rawEdgesAt_root (s : OriginalSample G) (i : Fin 3) (v : G) :
    ∀ E ∈ rawEdgesAt s i v, signedRoot i v ∈ E := by
  intro E hE
  obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hE
  exact signedRoot_mem_edgeAt i v t

/-- Both partners lie in the genuine signed raw inventory, without any
condition that the root itself has been selected. -/
theorem rawEdgesAt_inside (s : OriginalSample G) (i : Fin 3) (v : G) :
    ∀ E ∈ rawEdgesAt s i v, E ⊆ insert (signedRoot i v) (signedRawTarget s) := by
  intro E hE
  obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hE
  fin_cases i
  all_goals simp [rawParameters] at ht
  all_goals
    intro z hz
    simp [edgeAt] at hz
    rcases hz with rfl | rfl | rfl
    all_goals simp [signedRoot,signedRawTarget,signedTarget,ht.1,ht.2,Prod.mk.injEq]
  all_goals exact ⟨_,ht.2,by simp⟩

/-- The categorical endpoint sample has no raw edge of colour zero. -/
theorem rawDegree_colour_zero (s : OriginalSample G) : rawDegree s 2 0 = 0 := by
  rw [rawDegree_eq_card_parameters]
  have he : rawParameters s 2 0 = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hx' : x ∈ rawSet s 0 ∧ x ∈ rawSet s 1 := by simpa [rawParameters] using hx
    have hX := hx'.1
    have hY := hx'.2
    simp [rawSet,selected,sites] at hX hY
    have he := hX.symm.trans hY
    norm_num at he
  rw [he]
  simp

/-- Decode the physical numerical root from the paper's signed tagged root. -/
def physicalRoot (z : Vertex G) : G := if z.1=1 then z.2 else -z.2

def vertexCandidates (s : OriginalSample G) (z : Vertex G) : Finset (Finset (Vertex G)) :=
  rawEdgesAt s z.1 (physicalRoot z)

@[simp] theorem signedRoot_physicalRoot (z : Vertex G) : signedRoot z.1 (physicalRoot z) = z := by
  rcases z with ⟨i,v⟩
  fin_cases i <;> simp [signedRoot,physicalRoot]

theorem vertexCandidates_valid (s : OriginalSample G) :
    ∀ z E, E ∈ vertexCandidates s z → Hyperedge E := by
  intro z E hE
  exact rawEdgesAt_valid s z.1 (physicalRoot z) E hE

theorem vertexCandidates_root (s : OriginalSample G) :
    ∀ z E, E ∈ vertexCandidates s z → z ∈ E := by
  intro z E hE
  simpa using rawEdgesAt_root s z.1 (physicalRoot z) E hE

theorem vertexCandidates_inside (s : OriginalSample G) :
    ∀ z E, E ∈ vertexCandidates s z → E ⊆ insert z (signedRawTarget s) := by
  intro z E hE
  simpa using rawEdgesAt_inside s z.1 (physicalRoot z) E hE

/-- Exact lower raw candidate count in signed coordinates, for all endpoint
roots and all nonzero colour roots. -/
theorem GoodDegrees.vertexCandidates_lower {q ρ : ℝ} {s : OriginalSample G}
    (h : GoodDegrees q ρ s) (z : Vertex G) (hz : z.1=2 → z.2 ≠ 0) :
    (q^2-ρ)*(Fintype.card G : ℝ) ≤ ((vertexCandidates s z).card : ℝ) := by
  have hv : z.1=2 → physicalRoot z ≠ 0 := by
    intro hp
    have hn := hz hp
    simp [physicalRoot,hp,hn]
  have hd := h z.1 (physicalRoot z) hv
  rw [rawDegree_eq_card_edges] at hd
  have hlo := (abs_le.mp hd).1
  change (q^2-ρ)*(Fintype.card G : ℝ) ≤ ((rawEdgesAt s z.1 (physicalRoot z)).card : ℝ)
  linarith

/-- Natural lower counts may be chosen after the raw real lower bound is
proved; the eventual collision/deletion lemma can consume this signature. -/
theorem GoodDegrees.vertexCandidates_nat_lower {q ρ : ℝ} {s : OriginalSample G}
    (h : GoodDegrees q ρ s) (L : ℕ)
    (hL : (L : ℝ) ≤ (q^2-ρ)*(Fintype.card G : ℝ)) (z : Vertex G)
    (hz : z.1=2 → z.2 ≠ 0) : L ≤ (vertexCandidates s z).card := by
  exact_mod_cast hL.trans (h.vertexCandidates_lower z hz)

end
end EndpointFractionalRawEvent
