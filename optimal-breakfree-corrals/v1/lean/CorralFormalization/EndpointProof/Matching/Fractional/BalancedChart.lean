import CorralFormalization.EndpointProof.Matching.AbsorptionAssembly.FiniteAssembly

/-! A balanced actual tagged inventory is canonically equivalent, up to
finite choices, to three copies of one common finite index set. The chart
preserves the part label and does not identify numerical coordinates across
roles. -/

open scoped Classical BigOperators
namespace EndpointMatching.UniversalCore
open EndpointFlow.AbelianTransport
noncomputable section
variable {G : Type*} [AddCommGroup G] [Fintype G]

abbrev PartIndex (W : Finset (Vertex G)) (p : Fin 3) := ↥(slice W p)

abbrev CommonIndex (W : Finset (Vertex G)) := PartIndex W 0

/-- Balance supplies an equivalence of each actual part with the first part;
it also works for the empty inventory. -/
def partIndexEquiv (W : Finset (Vertex G)) (hW : Balanced W) (p : Fin 3) :
    CommonIndex W ≃ PartIndex W p := by
  apply Fintype.equivOfCardEq
  simpa [CommonIndex, PartIndex] using (hW p).symm

def chartVertex (W : Finset (Vertex G)) (hW : Balanced W) (pi : Fin 3 × CommonIndex W) : W :=
  ⟨((partIndexEquiv W hW pi.1) pi.2).val,
    (Finset.mem_filter.mp ((partIndexEquiv W hW pi.1) pi.2).property).1⟩

omit [AddCommGroup G] [Fintype G] in
@[simp] theorem chartVertex_part (W : Finset (Vertex G)) (hW : Balanced W)
    (pi : Fin 3 × CommonIndex W) : (chartVertex W hW pi).val.1 = pi.1 := by
  exact (Finset.mem_filter.mp ((partIndexEquiv W hW pi.1) pi.2).property).2

theorem chartVertex_injective (W : Finset (Vertex G)) (hW : Balanced W) :
    Function.Injective (chartVertex W hW) := by
  rintro ⟨p,i⟩ ⟨q,j⟩ h
  have hpq : p = q := by
    have hpart := congrArg (fun v : W => v.val.1) h
    simpa only [chartVertex_part] using hpart
  subst q
  congr 1
  apply (partIndexEquiv W hW p).injective
  apply Subtype.ext
  change ((partIndexEquiv W hW p) i).val = ((partIndexEquiv W hW p) j).val
  exact congrArg (fun v : W => v.val) h

omit [AddCommGroup G] [Fintype G] in
theorem chartVertex_surjective (W : Finset (Vertex G)) (hW : Balanced W) :
    Function.Surjective (chartVertex W hW) := by
  intro v
  let k : PartIndex W v.val.1 := ⟨v.val, by simp [slice, v.property]⟩
  refine ⟨(v.val.1, (partIndexEquiv W hW v.val.1).symm k), ?_⟩
  apply Subtype.ext
  change ((partIndexEquiv W hW v.val.1) ((partIndexEquiv W hW v.val.1).symm k)).val = v.val
  rw [Equiv.apply_symm_apply]

/-- The actual inventory, with its true part label, is exactly a disjoint
threefold copy of the common index. -/
def balancedChart (W : Finset (Vertex G)) (hW : Balanced W) :
    W ≃ (Fin 3 × CommonIndex W) :=
  (Equiv.ofBijective (chartVertex W hW)
    ⟨chartVertex_injective W hW, chartVertex_surjective W hW⟩).symm

@[simp] theorem balancedChart_symm_apply (W : Finset (Vertex G)) (hW : Balanced W)
    (p : Fin 3) (i : CommonIndex W) :
    (balancedChart W hW).symm (p,i) = chartVertex W hW (p,i) := rfl

@[simp] theorem balancedChart_symm_part (W : Finset (Vertex G)) (hW : Balanced W)
    (p : Fin 3) (i : CommonIndex W) : ((balancedChart W hW).symm (p,i)).val.1 = p :=
  chartVertex_part W hW (p,i)

@[simp] theorem balancedChart_part (W : Finset (Vertex G)) (hW : Balanced W) (v : W) :
    (balancedChart W hW v).1 = v.val.1 := by
  have h := chartVertex_part W hW (balancedChart W hW v)
  have hv : chartVertex W hW (balancedChart W hW v) = v :=
    (balancedChart W hW).symm_apply_apply v
  rw [hv] at h
  exact h.symm

end
end EndpointMatching.UniversalCore
