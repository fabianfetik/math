import CorralFormalization.EndpointProof.Factor.OrdinaryFragments.Extend

/-!
# Ordinary path decomposition from the actual layers and near matchings

`j` is the number of ordinary transitions (the paper's `J-2`), so there
are `j+1` ordinary layers. Every transition carries its actual covered
physical sets and both matching bijections. No equality of numerical
vertices in distinct layers is permitted.
-/

open scoped Classical BigOperators
namespace EndpointFactor.OrdinaryFragments
open EndpointMatching.AbsorptionAssembly FragmentChecksum
noncomputable section
universe u
variable {G : Type u} [AddCommGroup G] [DecidableEq G]

structure LayerData (G : Type u) [AddCommGroup G] (j ℓ : ℕ) where
  layer : Fin (j+1) → Finset G
  size : ∀ i, (layer i).card = ℓ
  layer_disjoint : ∀ i k, i ≠ k → Disjoint (layer i) (layer k)
  tail : Fin j → Finset G
  head : Fin j → Finset G
  color : Fin j → Finset G
  tail_subset : ∀ i, tail i ⊆ layer i.castSucc
  head_subset : ∀ i, head i ⊆ layer i.succ
  matching : ∀ i, PhysicalDifferenceMatching (tail i) (head i) (color i)
  color_disjoint : ∀ i k, i ≠ k → Disjoint (color i) (color k)
  color_nonzero : ∀ i, (0 : G) ∉ color i

namespace LayerData
variable {j ℓ : ℕ} (D : LayerData G j ℓ)

def vertices : Finset G := Finset.univ.biUnion D.layer
def colors : Finset G := Finset.univ.biUnion D.color
def deficit : ℕ := ∑ i, (ℓ-(D.tail i).card)

@[simp] theorem mem_vertices (g : G) : g ∈ D.vertices ↔ ∃ i, g ∈ D.layer i := by
  simp [vertices]
@[simp] theorem mem_colors (g : G) : g ∈ D.colors ↔ ∃ i, g ∈ D.color i := by
  simp [colors]

theorem tail_card_le (i : Fin j) : (D.tail i).card ≤ ℓ := by
  simpa only [D.size] using Finset.card_le_card (D.tail_subset i)
theorem matching_card (i : Fin j) : (D.color i).card = (D.tail i).card := by
  simpa only [Fintype.card_coe] using Fintype.card_congr (D.matching i).color.symm

theorem vertices_card : D.vertices.card = (j+1)*ℓ := by
  rw [vertices, Finset.card_biUnion]
  · simp [D.size]
  · intro i _ k _ hik
    exact D.layer_disjoint i k hik

theorem colors_card : D.colors.card + D.deficit = j*ℓ := by
  have hc : D.colors.card = ∑ i, (D.tail i).card := by
    rw [colors, Finset.card_biUnion]
    · simp only [D.matching_card]
    · intro i _ k _ hik
      exact D.color_disjoint i k hik
  rw [hc, deficit, ← Finset.sum_add_distrib]
  have he : ∀ i : Fin j, (D.tail i).card + (ℓ-(D.tail i).card) = ℓ :=
    fun i => Nat.add_sub_of_le (D.tail_card_le i)
  simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

theorem colors_nonzero : (0 : G) ∉ D.colors := by
  rintro h
  obtain ⟨i, hi⟩ := (D.mem_colors 0).mp h
  exact D.color_nonzero i hi

/-- Restrict all actual data to the preceding layers and transitions. -/
def initial (D : LayerData G (j+1) ℓ) : LayerData G j ℓ where
  layer := fun i => D.layer i.castSucc
  size := fun i => D.size i.castSucc
  layer_disjoint := by
    intro i k hik
    exact D.layer_disjoint i.castSucc k.castSucc (fun h => hik (Fin.castSucc_inj.mp h))
  tail := fun i => D.tail i.castSucc
  head := fun i => D.head i.castSucc
  color := fun i => D.color i.castSucc
  tail_subset := fun i => D.tail_subset i.castSucc
  head_subset := fun i => D.head_subset i.castSucc
  matching := fun i => D.matching i.castSucc
  color_disjoint := by
    intro i k hik
    exact D.color_disjoint i.castSucc k.castSucc (fun h => hik (Fin.castSucc_inj.mp h))
  color_nonzero := fun i => D.color_nonzero i.castSucc

private theorem union_last {n : ℕ} (f : Fin (n+1) → Finset G) :
    Finset.univ.biUnion f = (Finset.univ.biUnion (fun i : Fin n => f i.castSucc)) ∪ f (Fin.last n) := by
  ext g
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · rintro ⟨i, hi⟩
    by_cases hlt : i.val < n
    · let k : Fin n := ⟨i.val, hlt⟩
      have he : k.castSucc = i := Fin.ext rfl
      exact Or.inl ⟨k, he.symm ▸ hi⟩
    · have he : i = Fin.last n := Fin.ext (by simp; omega)
      exact Or.inr (he ▸ hi)
  · rintro (⟨i, hi⟩ | hi)
    · exact ⟨i.castSucc, hi⟩
    · exact ⟨Fin.last n, hi⟩

@[simp] theorem vertices_initial (D : LayerData G (j+1) ℓ) :
    D.vertices = D.initial.vertices ∪ D.layer (Fin.last (j+1)) := by
  exact union_last D.layer
@[simp] theorem colors_initial (D : LayerData G (j+1) ℓ) :
    D.colors = D.initial.colors ∪ D.color (Fin.last j) := by
  exact union_last D.color
@[simp] theorem deficit_initial (D : LayerData G (j+1) ℓ) :
    D.deficit = D.initial.deficit + (ℓ-(D.tail (Fin.last j)).card) := by
  exact Fin.sum_univ_castSucc _

theorem last_layer_fresh (D : LayerData G (j+1) ℓ) :
    Disjoint (D.layer (Fin.last (j+1))) D.initial.vertices := by
  apply Finset.disjoint_left.mpr
  intro g hg hg'
  obtain ⟨i, hi⟩ := (D.initial.mem_vertices g).mp hg'
  exact Finset.disjoint_left.mp (D.layer_disjoint (Fin.last (j+1)) i.castSucc
    (by intro he; have hv := congrArg Fin.val he; simp at hv; omega)) hg hi

theorem last_color_fresh (D : LayerData G (j+1) ℓ) :
    Disjoint (D.color (Fin.last j)) D.initial.colors := by
  apply Finset.disjoint_left.mpr
  intro g hg hg'
  obtain ⟨i, hi⟩ := (D.initial.mem_colors g).mp hg'
  exact Finset.disjoint_left.mp (D.color_disjoint (Fin.last j) i.castSucc
    (by intro he; have hv := congrArg Fin.val he; simp at hv; omega)) hg hi

/-- The paths themselves are constructed by layer extension.  In particular
all isolated layer vertices, including unmatched intermediate points, occur
exactly once. -/
theorem exists_family (D : LayerData G j ℓ) :
    ∃ F : Family G, F.vertices = D.vertices ∧ F.colors = D.colors ∧
      D.layer 0 ⊆ F.starts ∧ D.layer (Fin.last j) ⊆ F.ends ∧
      Fintype.card F.Index = ℓ + D.deficit := by
  induction j with
  | zero =>
    refine ⟨singletons (D.layer 0), ?_, ?_, ?_, ?_, ?_⟩
    · simp [vertices]
    · simp [colors]
    · simp
    · simp
    · simp [deficit, D.size]
  | succ j ih =>
    obtain ⟨F, hV, hC, hS, hE, hcard⟩ := ih D.initial
    let M := D.matching (Fin.last j)
    let N := D.layer (Fin.last (j+1))
    have hX : D.tail (Fin.last j) ⊆ F.ends :=
      (D.tail_subset (Fin.last j)).trans hE
    have hYN : D.head (Fin.last j) ⊆ N := D.head_subset (Fin.last j)
    have hNV : Disjoint N F.vertices := by rw [hV]; exact D.last_layer_fresh
    have hCF : Disjoint (D.color (Fin.last j)) F.colors := by rw [hC]; exact D.last_color_fresh
    let F' := F.extend M N hX hYN hNV hCF
    refine ⟨F', ?_, ?_, ?_, ?_, ?_⟩
    · rw [Family.extend_vertices, hV, ← D.vertices_initial]
    · rw [Family.extend_colors, hC, ← D.colors_initial]
    · rw [Family.extend_starts]
      exact hS.trans Finset.subset_union_left
    · rw [Family.extend_ends]
      exact Finset.subset_union_right
    · have hcount := F.extend_count M N hX hYN hNV hCF
      have htail := D.tail_card_le (Fin.last j)
      have hc := D.matching_card (Fin.last j)
      have hn : N.card = ℓ := D.size _
      change Fintype.card (F.extend M N hX hYN hNV hCF).Index = ℓ + D.deficit
      rw [D.deficit_initial]
      rw [hcard, hn, hc] at hcount
      omega

end LayerData

end
end EndpointFactor.OrdinaryFragments
