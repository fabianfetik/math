import CorralFormalization.EndpointProof.Router.GlobalGeometry.Layer

namespace EndpointRouter
open EndpointFactor
open scoped Classical
noncomputable section
universe u
variable {G : Type u} [AddCommGroup G]
variable {n : ℕ} {L₁ L₂ : MatchingLayer (Fin n)}
variable {input intermediate output : Fin n → G}
variable {first : LayerGeometry L₁ input intermediate}
variable {second : LayerGeometry L₂ intermediate output}

namespace TwoLayerSupport
variable (H : TwoLayerSupport first second)
include H

theorem first_disjoint : Pairwise (fun u v : L₁.Unit =>
    Disjoint (first.unitSupport u) (first.unitSupport v)) := by
  intro u v huv
  exact H.disjoint (show Sum.inl u ≠ Sum.inl v from fun h => huv (Sum.inl.inj h))

theorem second_disjoint : Pairwise (fun u v : L₂.Unit =>
    Disjoint (second.unitSupport u) (second.unitSupport v)) := by
  intro u v huv
  exact H.disjoint (show Sum.inr u ≠ Sum.inr v from fun h => huv (Sum.inr.inj h))

theorem cross_disjoint (u : L₁.Unit) (v : L₂.Unit) :
    Disjoint (first.unitSupport u) (second.unitSupport v) :=
  H.disjoint (by simp : Sum.inl u ≠ Sum.inr v)

theorem support_not_port (u : Sum L₁.Unit L₂.Unit) (p : Fin 3 × Fin n) :
    routerPort input intermediate output p ∉ twoLayerUnitSupport first second u := by
  intro hm
  exact Finset.disjoint_left.mp (H.avoid_ports u) hm
    (Finset.mem_image.mpr ⟨p, Finset.mem_univ p, rfl⟩)

theorem first_interior_not_port (chosen : List (Fin n × Fin n)) (i : Fin n)
    (p : Fin 3 × Fin n) :
    routerPort input intermediate output p ∉ (first.path chosen i).interior := by
  intro hz
  exact H.support_not_port (.inl (L₁.unitOf i)) p (first.path_interior_support chosen i hz)

theorem second_interior_not_port (chosen : List (Fin n × Fin n)) (i : Fin n)
    (p : Fin 3 × Fin n) :
    routerPort input intermediate output p ∉ (second.path chosen i).interior := by
  intro hz
  exact H.support_not_port (.inr (L₂.unitOf i)) p (second.path_interior_support chosen i hz)

theorem cross_interiors (f s : List (Fin n × Fin n)) (i j : Fin n) :
    List.Disjoint (first.path f i).interior (second.path s j).interior :=
  List.disjoint_left.mpr fun _z hz hz' =>
    Finset.disjoint_left.mp (H.cross_disjoint _ _)
      (first.path_interior_support f i hz) (second.path_interior_support s j hz')

theorem cross_colors (f s : List (Fin n × Fin n)) (i j : Fin n) :
    List.Disjoint ((first.path f i).colors (fun a b : G => b-a))
      ((second.path s j).colors (fun a b : G => b-a)) :=
  List.disjoint_left.mpr fun _z hz hz' =>
    Finset.disjoint_left.mp (H.cross_disjoint _ _)
      (first.path_color_support f i hz) (second.path_color_support s j hz')

theorem intermediate_injective : Function.Injective intermediate := by
  intro i j hij
  exact congrArg Prod.snd (H.ports_injective
    (show routerPort input intermediate output (1, i) =
      routerPort input intermediate output (1, j) from hij))

theorem input_ne_intermediate (i j : Fin n) : input i ≠ intermediate j := by
  intro hij
  have he := congrArg Prod.fst (H.ports_injective
    (show routerPort input intermediate output (0, i) =
      routerPort input intermediate output (1, j) from hij))
  exact (by decide : (0 : Fin 3) ≠ 1) he

theorem output_ne_intermediate (i j : Fin n) : output i ≠ intermediate j := by
  intro hij
  have he := congrArg Prod.fst (H.ports_injective
    (show routerPort input intermediate output (2, i) =
      routerPort input intermediate output (1, j) from hij))
  exact (by decide : (2 : Fin 3) ≠ 1) he

theorem input_ne_output (i j : Fin n) : input i ≠ output j := by
  intro hij
  have he := congrArg Prod.fst (H.ports_injective
    (show routerPort input intermediate output (0, i) =
      routerPort input intermediate output (2, j) from hij))
  exact (by decide : (0 : Fin 3) ≠ 2) he

theorem input_injective : Function.Injective input := by
  intro i j hij
  exact congrArg Prod.snd (H.ports_injective
    (show routerPort input intermediate output (0, i) =
      routerPort input intermediate output (0, j) from hij))

theorem output_injective : Function.Injective output := by
  intro i j hij
  exact congrArg Prod.snd (H.ports_injective
    (show routerPort input intermediate output (2, i) =
      routerPort input intermediate output (2, j) from hij))

end TwoLayerSupport
end
end EndpointRouter
