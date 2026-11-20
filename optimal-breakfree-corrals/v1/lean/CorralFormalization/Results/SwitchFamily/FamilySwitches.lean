import CorralFormalization.EndpointProof.Router.LayerAction

/-!
# Simultaneous site switches and recovery from unlabelled families

This finite construction uses the existing matching-layer permutation. Its
assumptions are actual pairwise-disjoint switch sites, disjoint original rows,
and fixed marker sites in those rows. It proves coverage, disjointness and
recovery of the chosen switch set from the resulting unlabelled family.

It does not prove a cyclic gap palette, the existence of appropriate markers
in a particular corral, physical-isometry inequivalence, or the concrete
switch geometry from Appendix A; those are separate obligations.
-/

namespace CorralFormalization.Results.SwitchFamily.FamilySwitches

open Finset EndpointRouter
open scoped Classical
noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Select the edges requested by the finite set, retaining their original
matching-layer order. -/
def selectedEdges (L : MatchingLayer α) (T : Finset (α × α)) : List (α × α) :=
  L.edges.filter (fun e => e ∈ T)

/-- The simultaneous switches are an actual permutation of all sites. -/
def selectedMotion (L : MatchingLayer α) (T : Finset (α × α)) : Equiv.Perm α :=
  switchProduct (selectedEdges L T)

omit [Fintype α] in
theorem selectedEdges_sublist (L : MatchingLayer α) (T : Finset (α × α)) :
    (selectedEdges L T).Sublist L.edges := List.filter_sublist

theorem selectedMotion_left (L : MatchingLayer α) (T : Finset (α × α))
    (e : α × α) (he : e ∈ L.edges) :
    selectedMotion L T e.1 = if e ∈ T then e.2 else e.1 := by
  have hp := L.product_left (selectedEdges L T) (selectedEdges_sublist L T) e he
  simpa [selectedMotion, selectedEdges, he] using hp

theorem selectedMotion_right (L : MatchingLayer α) (T : Finset (α × α))
    (e : α × α) (he : e ∈ L.edges) :
    selectedMotion L T e.2 = if e ∈ T then e.1 else e.2 := by
  have hp := L.product_right (selectedEdges L T) (selectedEdges_sublist L T) e he
  simpa [selectedMotion, selectedEdges, he] using hp

theorem selectedMotion_isolated (L : MatchingLayer α) (T : Finset (α × α))
    (x : α) (hx : L.Isolated x) : selectedMotion L T x = x :=
  L.product_isolated (selectedEdges L T) (selectedEdges_sublist L T) x hx

/-- A common site permutation acts on actual rows and then on the
unlabelled family of those rows. -/
def imageFamily (F : Finset (Finset α)) (p : Equiv.Perm α) : Finset (Finset α) :=
  F.image (fun R => R.image p)

omit [Fintype α] in
theorem imageFamily_card (F : Finset (Finset α)) (p : Equiv.Perm α) :
    (imageFamily F p).card = F.card := by
  exact Finset.card_image_of_injective _ (Finset.image_injective p.injective)

omit [Fintype α] in
theorem imageFamily_union (F : Finset (Finset α)) (p : Equiv.Perm α) :
    (imageFamily F p).biUnion id = (F.biUnion id).image p := by
  ext x
  constructor
  · intro hx
    obtain ⟨S,hS,hxS⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨R,hR,rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨y,hy,hyx⟩ := Finset.mem_image.mp hxS
    exact Finset.mem_image.mpr ⟨y,Finset.mem_biUnion.mpr ⟨R,hR,hy⟩,hyx⟩
  · intro hx
    obtain ⟨y,hy,hyx⟩ := Finset.mem_image.mp hx
    obtain ⟨R,hR,hyR⟩ := Finset.mem_biUnion.mp hy
    apply Finset.mem_biUnion.mpr
    exact ⟨R.image p,Finset.mem_image.mpr ⟨R,hR,rfl⟩,Finset.mem_image.mpr ⟨y,hyR,hyx⟩⟩

omit [Fintype α] in
theorem imageFamily_disjoint (F : Finset (Finset α)) (p : Equiv.Perm α)
    (hdis : ∀ R ∈ F, ∀ S ∈ F, R ≠ S → Disjoint R S) :
    ∀ R ∈ imageFamily F p, ∀ S ∈ imageFamily F p, R ≠ S → Disjoint R S := by
  intro R hR S hS hRS
  obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hR
  obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hS
  have hAB : A ≠ B := fun he => hRS (by rw [he])
  apply Finset.disjoint_left.mpr
  intro x hxA hxB
  obtain ⟨a,ha,haeq⟩ := Finset.mem_image.mp hxA
  obtain ⟨b,hb,hbeq⟩ := Finset.mem_image.mp hxB
  have hab : a=b := p.injective (haeq.trans hbeq.symm)
  exact Finset.disjoint_left.mp (hdis A hA B hB hAB) ha (hab ▸ hb)

/-- A permutation preserves full physical coverage, not merely the number
of occupied positions. -/
theorem imageFamily_full (F : Finset (Finset α)) (p : Equiv.Perm α)
    (hfull : F.biUnion id = Finset.univ) :
    (imageFamily F p).biUnion id = Finset.univ := by
  rw [imageFamily_union, hfull]
  ext x
  simp

omit [Fintype α] in
/-- Markers fixed by both site permutations identify every original row in
two equal unlabelled output families. -/
theorem imageFamily_eq_identifies_rows
    (F : Finset (Finset α)) (p q : Equiv.Perm α) (mark : Finset α → α)
    (hdis : ∀ R ∈ F, ∀ S ∈ F, R ≠ S → Disjoint R S)
    (hmark : ∀ R ∈ F, mark R ∈ R)
    (hfixedp : ∀ R ∈ F, p (mark R) = mark R)
    (hfixedq : ∀ R ∈ F, q (mark R) = mark R)
    (heq : imageFamily F p = imageFamily F q) :
    ∀ R ∈ F, R.image p = R.image q := by
  intro R hR
  have hmemp : R.image p ∈ imageFamily F p := Finset.mem_image.mpr ⟨R,hR,rfl⟩
  rw [heq] at hmemp
  obtain ⟨S,hS,hSrow⟩ := Finset.mem_image.mp hmemp
  have hmarker : mark R ∈ R.image p :=
    Finset.mem_image.mpr ⟨mark R,hmark R hR,hfixedp R hR⟩
  rw [← hSrow] at hmarker
  obtain ⟨z,hz,hzq⟩ := Finset.mem_image.mp hmarker
  have hzmark : z = mark R := q.injective (hzq.trans (hfixedq R hR).symm)
  have hmS : mark R ∈ S := by simpa [hzmark] using hz
  have hSR : S=R := by
    by_contra hne
    exact Finset.disjoint_left.mp (hdis R hR S hS (Ne.symm hne)) (hmark R hR) hmS
  subst S
  exact hSrow.symm

/-- Each chosen switch set yields one actual, unlabelled site family. -/
def switchedFamily (L : MatchingLayer α) (F : Finset (Finset α))
    (T : Finset (α × α)) : Finset (Finset α) := imageFamily F (selectedMotion L T)

/-- With one fixed marker per original row and different original owners at
each switch pair, the unlabelled output family determines every switch bit.
No row labels are supplied to the output. -/
theorem switchedFamily_injective_on_choices
    (L : MatchingLayer α) (F : Finset (Finset α)) (mark : Finset α → α)
    (hdis : ∀ R ∈ F, ∀ S ∈ F, R ≠ S → Disjoint R S)
    (hmark : ∀ R ∈ F, mark R ∈ R ∧ L.Isolated (mark R))
    (howner : ∀ e ∈ L.edges, ∃ R ∈ F, e.1 ∈ R ∧ e.2 ∉ R) :
    Set.InjOn (switchedFamily L F) (L.edges.toFinset.powerset : Set (Finset (α × α))) := by
  intro T hT U hU heq
  have hTsub : T ⊆ L.edges.toFinset := Finset.mem_powerset.mp hT
  have hUsub : U ⊆ L.edges.toFinset := Finset.mem_powerset.mp hU
  have hrows := imageFamily_eq_identifies_rows F (selectedMotion L T) (selectedMotion L U) mark
    hdis (fun R hR => (hmark R hR).1)
    (fun R hR => selectedMotion_isolated L T _ (hmark R hR).2)
    (fun R hR => selectedMotion_isolated L U _ (hmark R hR).2) heq
  apply Finset.ext
  intro e
  constructor
  · intro heT
    have he : e ∈ L.edges := List.mem_toFinset.mp (hTsub heT)
    by_contra heU
    obtain ⟨R,hRF,hx,hy⟩ := howner e he
    have hqu : selectedMotion L U e.1 = e.1 := by
      rw [selectedMotion_left L U e he, if_neg heU]
    have hpt : selectedMotion L T e.2 = e.1 := by
      rw [selectedMotion_right L T e he, if_pos heT]
    have hmemU : e.1 ∈ R.image (selectedMotion L U) :=
      Finset.mem_image.mpr ⟨e.1,hx,hqu⟩
    rw [← hrows R hRF] at hmemU
    obtain ⟨z,hz,hzT⟩ := Finset.mem_image.mp hmemU
    have hz2 : z=e.2 := (selectedMotion L T).injective (hzT.trans hpt.symm)
    exact hy (hz2 ▸ hz)
  · intro heU
    have he : e ∈ L.edges := List.mem_toFinset.mp (hUsub heU)
    by_contra heT
    obtain ⟨R,hRF,hx,hy⟩ := howner e he
    have hqt : selectedMotion L T e.1 = e.1 := by
      rw [selectedMotion_left L T e he, if_neg heT]
    have hpu : selectedMotion L U e.2 = e.1 := by
      rw [selectedMotion_right L U e he, if_pos heU]
    have hmemT : e.1 ∈ R.image (selectedMotion L T) :=
      Finset.mem_image.mpr ⟨e.1,hx,hqt⟩
    rw [hrows R hRF] at hmemT
    obtain ⟨z,hz,hzU⟩ := Finset.mem_image.mp hmemT
    have hz2 : z=e.2 := (selectedMotion L U).injective (hzU.trans hpu.symm)
    exact hy (hz2 ▸ hz)

/-- The exact number of distinct unlabelled site families obtained from all
choices, before any cyclic-palette or physical-isometry claim. -/
theorem switchedFamily_exact_count
    (L : MatchingLayer α) (F : Finset (Finset α)) (mark : Finset α → α)
    (hdis : ∀ R ∈ F, ∀ S ∈ F, R ≠ S → Disjoint R S)
    (hmark : ∀ R ∈ F, mark R ∈ R ∧ L.Isolated (mark R))
    (howner : ∀ e ∈ L.edges, ∃ R ∈ F, e.1 ∈ R ∧ e.2 ∉ R) :
    (L.edges.toFinset.powerset.image (switchedFamily L F)).card = 2^L.edges.length := by
  rw [Finset.card_image_of_injOn (switchedFamily_injective_on_choices L F mark hdis hmark howner),
    Finset.card_powerset, List.toFinset_card_of_nodup L.nodup]

end
end CorralFormalization.Results.SwitchFamily.FamilySwitches
