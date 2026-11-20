import CorralFormalization.EndpointProof.Selector.Assembly.FixedCardinality.PortRouting
import Mathlib.Combinatorics.Hall.Finite

open scoped Classical BigOperators

namespace EndpointSelector.FixedCardinality.GraphExpansion
noncomputable section

variable {L R : Type*} [Fintype L] [DecidableEq L] [DecidableEq R]

def rightNeighbors (N : L → Finset R) (B : Finset R) : Finset L :=
  Finset.univ.filter (fun i => (N i ∩ B).Nonempty)

/-- The two expansion properties used in E.T imply every requested routing.
The statement is deterministic and does not assume graph existence. -/
theorem route_of_expansion (s : ℕ) (F W₀ : Finset R) (N : L → Finset R)
    (hLcard : Fintype.card L = 3 * s) (hFcard : F.card = 2 * s)
    (hWcard : W₀.card = s) (hdis : Disjoint F W₀)
    (hsmall : ∀ A : Finset L, A.card ≤ s →
      A.card ≤ ((A.biUnion N) ∩ F).card)
    (hright : ∀ B : Finset R, B.card ≤ 2 * s →
      B.card ≤ (rightNeighbors N B).card) :
    ∃ f : L → R, Function.Injective f ∧ (∀ i, f i ∈ N i) ∧
      Finset.univ.image f = F ∪ W₀ := by
  classical
  let T := F ∪ W₀
  have hTcard : T.card = 3 * s := by
    dsimp [T]
    rw [Finset.card_union_of_disjoint hdis, hFcard, hWcard]
    omega
  let H : L → Finset R := fun i => N i ∩ T
  have hHall : ∀ A : Finset L, A.card ≤ (A.biUnion H).card := by
    intro A
    have hbridge : A.biUnion H = (A.biUnion N) ∩ T := by
      ext x
      simp only [H, Finset.mem_biUnion, Finset.mem_inter]
      aesop
    rw [hbridge]
    by_cases hAsmall : A.card ≤ s
    · apply (hsmall A hAsmall).trans
      apply Finset.card_le_card
      intro x hx
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1,
        Finset.mem_union_left _ (Finset.mem_inter.mp hx).2⟩
    · by_contra hfail
      have hlt : ((A.biUnion N) ∩ T).card < A.card := by omega
      have hAmax : A.card ≤ 3 * s := by
        simpa only [hLcard] using Finset.card_le_univ A
      have hBneed : 3 * s - A.card + 1 ≤ (T \ A.biUnion N).card := by
        have hsplit := Finset.card_sdiff_add_card_inter T (A.biUnion N)
        rw [Finset.inter_comm T (A.biUnion N), hTcard] at hsplit
        omega
      obtain ⟨B, hBsub, hBcard⟩ := Finset.exists_subset_card_eq hBneed
      have hBsmall : B.card ≤ 2 * s := by rw [hBcard]; omega
      have hRN := hright B hBsmall
      have hNsub : rightNeighbors N B ⊆ Finset.univ \ A := by
        intro i hi
        have hi' := (Finset.mem_filter.mp hi).2
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
        intro hiA
        obtain ⟨x, hx⟩ := hi'
        have hxN := (Finset.mem_inter.mp hx).1
        have hxB := (Finset.mem_inter.mp hx).2
        have hxBad := (Finset.mem_sdiff.mp (hBsub hxB)).2
        exact hxBad (Finset.mem_biUnion.mpr ⟨i, hiA, hxN⟩)
      have hRNbound := Finset.card_le_card hNsub
      have hcomp : (Finset.univ \ A).card = 3 * s - A.card := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ A), Finset.card_univ, hLcard]
      omega
  obtain ⟨f, hfinj, hf⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' H).mp hHall
  have hfN : ∀ i, f i ∈ N i := fun i => (Finset.mem_inter.mp (hf i)).1
  have hfsub : Finset.univ.image f ⊆ T := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_inter.mp (hf i)).2
  have hfcard : (Finset.univ.image f).card = 3 * s := by
    rw [Finset.card_image_of_injective _ hfinj, Finset.card_univ, hLcard]
  have hfimage : Finset.univ.image f = T :=
    Finset.eq_of_subset_of_card_le hfsub (by rw [hTcard, hfcard])
  exact ⟨f, hfinj, hfN, hfimage⟩

/-- The first half of the right ports, as in the written E.T graph. -/
def fixedPorts (s : ℕ) : Finset (Fin (4 * s)) :=
  Finset.univ.filter (fun w => w.val < 2 * s)

theorem fixedPorts_card (s : ℕ) : (fixedPorts s).card = 2 * s := by
  classical
  let embed : Fin (2 * s) → Fin (4 * s) := Fin.castLE (by omega)
  have hembed : Function.Injective embed := by
    intro i j he
    apply Fin.ext
    have hv := congrArg Fin.val he
    simpa [embed] using hv
  have hset : fixedPorts s = Finset.univ.image embed := by
    ext w
    simp only [fixedPorts, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hw
      refine ⟨⟨w.val, hw⟩, ?_⟩
      apply Fin.ext
      rfl
    · rintro ⟨i, rfl⟩
      exact i.isLt
  rw [hset, Finset.card_image_of_injective _ hembed, Finset.card_univ, Fintype.card_fin]

/-- The written left/right expansion conditions imply exactly the
contiguous-index robust selection graph required by the selector compiler. -/
def contiguousGraph_of_expansion (s degree : ℕ) (hs : 1 ≤ s)
    (N : Fin (3 * s) → Finset (Fin (4 * s)))
    (hdegree : ∀ i, (N i).card ≤ degree)
    (hsmall : ∀ A : Finset (Fin (3 * s)), A.card ≤ s →
      A.card ≤ ((A.biUnion N) ∩ fixedPorts s).card)
    (hright : ∀ B : Finset (Fin (4 * s)), B.card ≤ 2 * s →
      B.card ≤ (rightNeighbors N B).card) : ContiguousSelectionGraph s degree := by
  classical
  refine ⟨N, ?_, hdegree, ?_⟩
  · intro i
    have h := hsmall {i} (by simpa using hs)
    have hpos : 0 < (N i ∩ fixedPorts s).card := by simpa using h
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
    exact ⟨v, (Finset.mem_inter.mp hv).1⟩
  · intro W₀ hWlower hWcard
    have hdis : Disjoint (fixedPorts s) W₀ := by
      apply Finset.disjoint_left.mpr
      intro w hw hW
      have hlt : w.val < 2 * s := (Finset.mem_filter.mp hw).2
      have hge := hWlower w hW
      omega
    exact route_of_expansion s (fixedPorts s) W₀ N (by simp) (fixedPorts_card s)
      hWcard hdis hsmall hright

end
end EndpointSelector.FixedCardinality.GraphExpansion
