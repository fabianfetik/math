import CorralFormalization.EndpointProof.Matching.AbsorptionAssembly.ActualTarget

/-!
Decode the existing additive tagged matching into uniform exact-matching theorem's physical endpoint
bijection and a bijection with the prescribed color set.  Equal numerical
coordinates in different roles remain distinct tagged vertices throughout.
-/

open scoped Classical BigOperators

namespace EndpointMatching.AbsorptionAssembly

open EndpointFlow.AbelianTransport

noncomputable section

variable {G : Type*} [AddCommGroup G]

/-- The paper's actual signed target `(-X)_A ⊔ Y_B ⊔ (-C)_C`. -/
def signedTarget (X Y C : Finset G) : Finset (Vertex G) :=
  (X.image (fun x => (0, -x))) ∪ (Y.image (fun y => (1, y))) ∪
    (C.image (fun c => (2, -c)))

@[simp] theorem signedTarget_tail_mem (X Y C : Finset G) (x : G) :
    (0, -x) ∈ signedTarget X Y C ↔ x ∈ X := by
  simp [signedTarget, Prod.mk.injEq]

@[simp] theorem signedTarget_head_mem (X Y C : Finset G) (y : G) :
    (1, y) ∈ signedTarget X Y C ↔ y ∈ Y := by
  simp [signedTarget, Prod.mk.injEq]

@[simp] theorem signedTarget_color_mem (X Y C : Finset G) (c : G) :
    (2, -c) ∈ signedTarget X Y C ↔ c ∈ C := by
  simp [signedTarget, Prod.mk.injEq]

theorem hyperedge_same_role_unique {E : Finset (Vertex G)} (hE : Hyperedge E)
    {p : Fin 3} {a b : G} (ha : (p, a) ∈ E) (hb : (p, b) ∈ E) : a = b := by
  obtain ⟨x, y, z, _, rfl⟩ := hE
  fin_cases p <;> simp_all

/-- A coordinate projection of the actual edge family is bijective as soon
as it meets every target vertex in that role.  Injectivity is paid by
disjointness, and surjectivity by exact coverage. -/
theorem matching_projection_bijective {T : Finset (Vertex G)} (M : Matching T)
    (S : Finset G) (p : Fin 3) (embed : G → G) (hembed : Function.Injective embed)
    (f : M.edges → S)
    (hmem : ∀ e, (p, embed (f e).val) ∈ e.val)
    (hT : ∀ x ∈ S, (p, embed x) ∈ T) : Function.Bijective f := by
  constructor
  · intro e d hed
    apply Subtype.ext
    by_contra hne
    have hd := M.disjoint e.property d.property hne
    apply Finset.disjoint_left.mp hd (hmem e)
    simpa only [hed] using hmem d
  · intro x
    have hx := hT x.val x.property
    rw [← M.cover] at hx
    obtain ⟨E, hE, hx⟩ := Finset.mem_biUnion.mp hx
    let e : M.edges := ⟨E, hE⟩
    refine ⟨e, Subtype.ext (hembed ?_)⟩
    exact hyperedge_same_role_unique (M.valid E hE) (hmem e) hx

/-- Both bijections are needed: the endpoint bijection alone would not say
that each prescribed color is used exactly once. -/
structure PhysicalDifferenceMatching (X Y C : Finset G) where
  endpoint : X ≃ Y
  color : X ≃ C
  difference : ∀ x, (color x).val = (endpoint x).val - x.val

private structure EdgeTriple (X Y C : Finset G) (E : Finset (Vertex G)) where
  tail : X
  head : Y
  color : C
  tail_mem : (0, -tail.val) ∈ E
  head_mem : (1, head.val) ∈ E
  color_mem : (2, -color.val) ∈ E
  difference : color.val = head.val - tail.val

private theorem edgeTriple_nonempty {X Y C : Finset G}
    (M : Matching (signedTarget X Y C)) (e : M.edges) :
    Nonempty (EdgeTriple X Y C e.val) := by
  obtain ⟨a, b, c, hsum, hshape⟩ := M.valid e.val e.property
  have ha : (0, a) ∈ e.val := by simp [hshape]
  have hb : (1, b) ∈ e.val := by simp [hshape]
  have hc : (2, c) ∈ e.val := by simp [hshape]
  have hX : -a ∈ X := by
    have := matching_edge_subset M e.property ha
    apply (signedTarget_tail_mem X Y C (-a)).mp
    simpa only [neg_neg] using this
  have hY : b ∈ Y := (signedTarget_head_mem X Y C b).mp
    (matching_edge_subset M e.property hb)
  have hC : -c ∈ C := by
    have := matching_edge_subset M e.property hc
    apply (signedTarget_color_mem X Y C (-c)).mp
    simpa only [neg_neg] using this
  refine ⟨⟨⟨-a, hX⟩, ⟨b, hY⟩, ⟨-c, hC⟩, ?_, hb, ?_, ?_⟩⟩
  · simpa using ha
  · simpa using hc
  · apply neg_eq_iff_add_eq_zero.mpr
    calc
      c + (b - -a) = a + b + c := by abel
      _ = 0 := hsum

private def edgeTriple {X Y C : Finset G} (M : Matching (signedTarget X Y C))
    (e : M.edges) : EdgeTriple X Y C e.val := Classical.choice (edgeTriple_nonempty M e)

/-- Kernel-checked decoding of a perfect tagged zero-sum matching into the
physical contract in the uniform exact-matching theorem, including exactly-once use of every color. -/
def physicalDifferenceMatching_of_signedMatching {X Y C : Finset G}
    (M : Matching (signedTarget X Y C)) : PhysicalDifferenceMatching X Y C := by
  let tailMap : M.edges → X := fun e => (edgeTriple M e).tail
  let headMap : M.edges → Y := fun e => (edgeTriple M e).head
  let colorMap : M.edges → C := fun e => (edgeTriple M e).color
  let tailEquiv : M.edges ≃ X := Equiv.ofBijective tailMap
    (matching_projection_bijective M X 0 Neg.neg neg_injective tailMap
      (fun e => (edgeTriple M e).tail_mem)
      (fun x hx => (signedTarget_tail_mem X Y C x).mpr hx))
  let headEquiv : M.edges ≃ Y := Equiv.ofBijective headMap
    (matching_projection_bijective M Y 1 id Function.injective_id headMap
      (fun e => (edgeTriple M e).head_mem)
      (fun y hy => (signedTarget_head_mem X Y C y).mpr hy))
  let colorEquiv : M.edges ≃ C := Equiv.ofBijective colorMap
    (matching_projection_bijective M C 2 Neg.neg neg_injective colorMap
      (fun e => (edgeTriple M e).color_mem)
      (fun c hc => (signedTarget_color_mem X Y C c).mpr hc))
  refine ⟨tailEquiv.symm.trans headEquiv, tailEquiv.symm.trans colorEquiv, ?_⟩
  intro x
  have hx : (edgeTriple M (tailEquiv.symm x)).tail = x := tailEquiv.apply_symm_apply x
  change (edgeTriple M (tailEquiv.symm x)).color.val =
    (edgeTriple M (tailEquiv.symm x)).head.val - x.val
  simpa only [hx] using (edgeTriple M (tailEquiv.symm x)).difference


end
end EndpointMatching.AbsorptionAssembly
