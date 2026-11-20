import CorralFormalization.EndpointProof.Factor.CycleExpansion.Labels

/-! # A constructed marked physical cycle supplies both terminal cases -/

open scoped Classical BigOperators
namespace EndpointFactor.CycleExpansion
open OrdinaryFragments FragmentChecksum EndpointMatching.AbsorptionAssembly
noncomputable section
universe u
variable {G : Type u} [AddCommGroup G] [DecidableEq G]

/-- Actual finite output of the expansion, before any virtual edge is cut. -/
structure MarkedCycle (W D X Y : Finset G) where
  vertices : List G
  nonempty : vertices ≠ []
  next : G → G
  last_marked : Y.Nonempty → vertices.getLast nonempty ∈ Y
  simple : vertices.Nodup
  vertex_inventory : vertices.toFinset = W
  marked_in_target : Y ⊆ W
  virtual_heads : Y.image next = X
  follows : vertices.IsChain (fun a b => next a = b)
  wraps : next (vertices.getLast nonempty) = vertices.head nonempty
  real_rainbow : (CycleCut.cyclicRealDifferences Y vertices nonempty).Nodup
  real_inventory : (CycleCut.cyclicRealDifferences Y vertices nonempty).toFinset = D

theorem MarkedCycle.endpointConclusion {W D X Y : Finset G} (C : MarkedCycle W D X Y) :
    CycleCut.PhysicalEndpointConclusion W D X Y :=
  CycleCut.endpointConclusion_of_marked_cycle W D X Y C.vertices C.next C.nonempty C.last_marked
    C.simple C.vertex_inventory C.marked_in_target C.virtual_heads C.follows C.wraps
    C.real_rainbow C.real_inventory

/-- Expand a genuine path family and the supplied single-cycle contracted
closure, using the actual real closing matching and virtual bijection.
Every physical marked-cycle obligation is proved, not supplied. -/
theorem exists_markedCycle_of_familyClosure {n : ℕ} (hn : 0 < n)
    (F : Family G) (key : Fin n ≃ F.Index) (ρ : Equiv.Perm (Fin n))
    (hc : ρ.IsCycleOn Set.univ) (W D E S X Y H : Finset G)
    (hV : F.vertices = W) (hUsed : F.colors = D \ H) (hHD : H ⊆ D)
    (hYE : Y ⊆ E) (M : PhysicalDifferenceMatching (E \ Y) (S \ X) H)
    (endAt : Fin n ≃ E) (hEnd : ∀ i, F.last (key i) = (endAt i).val)
    (virtual : Y ≃ X)
    (hVirtual : ∀ i, ∀ hy : (endAt i).val ∈ Y,
      F.first (key (ρ i)) = (virtual ⟨(endAt i).val,hy⟩).val)
    (hReal : ∀ i, ∀ hy : (endAt i).val ∉ Y,
      (M.color ⟨(endAt i).val,Finset.mem_sdiff.mpr ⟨(endAt i).property,hy⟩⟩).val =
        F.first (key (ρ i))-F.last (key i)) :
    Nonempty (MarkedCycle W D X Y) := by
  have hYF : Y ⊆ F.ends := by
    intro y hy
    obtain ⟨i,hi⟩ := endAt.surjective ⟨y,hYE hy⟩
    apply (F.mem_ends y).mpr
    exact ⟨key i,(hEnd i).trans (congrArg (fun z : E => z.val) hi)⟩
  have hFresh : Disjoint H F.colors := by
    rw [hUsed]
    apply Finset.disjoint_left.mpr
    intro c hc hc'
    exact (Finset.mem_sdiff.mp hc').2 hc
  have hroot : ∃ root : Fin n, Y.Nonempty →
      F.last (key ((trackOrder ρ root hc).order.getLast (trackOrder ρ root hc).nonempty)) ∈ Y := by
    by_cases hne : Y.Nonempty
    · obtain ⟨y,hy⟩ := hne
      let iy := endAt.symm ⟨y,hYE hy⟩
      refine ⟨ρ iy,fun _ => ?_⟩
      let order := trackOrder ρ (ρ iy) hc
      have hcLast : ρ (order.order.getLast order.nonempty) = ρ iy :=
        order.closes _ (List.getLast?_eq_some_getLast order.nonempty)
      have hlast : order.order.getLast order.nonempty = iy := ρ.injective hcLast
      change F.last (key (order.order.getLast order.nonempty)) ∈ Y
      rw [hlast,hEnd]
      simpa [iy] using hy
    · exact ⟨⟨0,hn⟩,fun h => False.elim (hne h)⟩
  obtain ⟨root,hroot⟩ := hroot
  let q := vertices F key ρ root hc
  have hqn : q ≠ [] := vertices_nonempty F key ρ root hc
  have hqnodup : q.Nodup := vertices_nodup F key ρ root hc
  have hqLast : q.getLast hqn =
      F.last (key ((trackOrder ρ root hc).order.getLast (trackOrder ρ root hc).nonempty)) := by
    have he := vertices_last F key ρ root hc
    rw [List.getLast?_eq_some_getLast hqn] at he
    exact Option.some.inj he
  have hnext (y : Y) : q.formPerm y.val = (virtual y).val := by
    let ey : E := ⟨y.val,hYE y.property⟩
    let i := endAt.symm ey
    have hi : endAt i = ey := endAt.apply_symm_apply ey
    have hival : (endAt i).val = y.val := congrArg (fun z : E => z.val) hi
    have hl : F.last (key i) = y.val := (hEnd i).trans hival
    rw [← hl,successor_at_end F key ρ root hc i]
    have hyi : (endAt i).val ∈ Y := hival.symm ▸ y.property
    have hv := hVirtual i hyi
    have he : (⟨(endAt i).val,hyi⟩ : Y) = y := Subtype.ext hival
    exact hv.trans (congrArg (fun z : Y => (virtual z).val) he)
  have hX : Y.image q.formPerm = X := by
    ext x
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨y,hy,hx⟩
      rw [hnext ⟨y,hy⟩] at hx
      exact hx ▸ (virtual ⟨y,hy⟩).property
    · intro hx
      obtain ⟨y,hy⟩ := virtual.surjective ⟨x,hx⟩
      exact ⟨y.val,y.property,(hnext y).trans (congrArg (fun z : X => z.val) hy)⟩
  have hYtarget : Y ⊆ W := by
    intro y hy
    rw [← hV]
    exact F.ends_subset (hYF hy)
  have hD : (CycleCut.cyclicRealDifferences Y q hqn).toFinset = D := by
    rw [cyclicRealDifferences_inventory E S X Y H M endAt F key ρ hYF hEnd hReal root hc,hUsed]
    ext c
    have hh : c ∈ H → c ∈ D := fun h => hHD h
    simp only [Finset.mem_union,Finset.mem_sdiff]
    tauto
  exact ⟨{
    vertices := q
    nonempty := hqn
    next := q.formPerm
    last_marked := fun h => hqLast.symm ▸ hroot h
    simple := hqnodup
    vertex_inventory := (vertices_inventory F key ρ root hc).trans hV
    marked_in_target := hYtarget
    virtual_heads := hX
    follows := formPerm_chain q hqnodup
    wraps := formPerm_wrap q hqn
    real_rainbow := cyclicRealDifferences_nodup E S X Y H M endAt F key ρ hYF hEnd hReal hFresh root hc
    real_inventory := hD }⟩

end
end EndpointFactor.CycleExpansion
