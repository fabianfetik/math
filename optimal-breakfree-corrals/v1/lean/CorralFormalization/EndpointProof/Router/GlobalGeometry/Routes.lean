import CorralFormalization.EndpointProof.Router.GlobalGeometry.TwoLayer

/-! # Global geometry of the actual composed routes

Every setting is covered.  Global nonrepetition is derived from local affine
collision tests and the raw support/port certificate, rather than assumed.
-/
namespace EndpointRouter
open EndpointFactor Equiv Equiv.Perm
open scoped Classical
noncomputable section
universe u
variable {G : Type u} [AddCommGroup G]
variable {n : ℕ} {input intermediate output : Fin n → G}
variable (first : LayerGeometry (firstMatchingLayer n) input intermediate)
variable (second : LayerGeometry (secondMatchingLayer n) intermediate output)

theorem installedRoutes_interior_eq (f s : List (Fin n × Fin n))
    (hf : f.Sublist (firstLayer n)) (i : Fin n) :
    (installedRoutes first second f s i).interior =
      (first.path f i).interior ++ [intermediate (switchProduct f i)] ++
        (second.path s (switchProduct f i)).interior := by
  change (first.path f i).interior ++ [(first.path f i).last] ++
    (second.path s (switchProduct f i)).interior = _
  rw [(first.endpoints f hf i).2]

theorem installedRoutes_colors_eq (f s : List (Fin n × Fin n))
    (hf : f.Sublist (firstLayer n)) (hs : s.Sublist (secondLayer n)) (i : Fin n) :
    (installedRoutes first second f s i).colors (fun a b : G => b-a) =
      (first.path f i).colors (fun a b : G => b-a) ++
        (second.path s (switchProduct f i)).colors (fun a b : G => b-a) :=
  compose_colors _ _ _ (installedRoutes_join first second f s hf hs i)

namespace TwoLayerSupport
variable {first second} (H : TwoLayerSupport first second)
include H

theorem route_interior_nodup (f s : List (Fin n × Fin n))
    (hf : f.Sublist (firstLayer n)) (i : Fin n) :
    (installedRoutes first second f s i).interior.Nodup := by
  rw [installedRoutes_interior_eq first second f s hf i]
  have hP : (first.path f i).interior.Nodup :=
    (first.path_valid f i).2.1.of_append_left.of_cons
  have hQ : (second.path s (switchProduct f i)).interior.Nodup :=
    (second.path_valid s (switchProduct f i)).2.1.of_append_left.of_cons
  have hPm : List.Disjoint (first.path f i).interior [intermediate (switchProduct f i)] := by
    apply List.disjoint_left.mpr
    intro z hz hm
    have he := List.mem_singleton.mp hm
    subst z
    exact H.first_interior_not_port f i (1, switchProduct f i) hz
  apply (hP.append (by simp) hPm).append hQ
  apply List.disjoint_left.mpr
  intro z hz hzQ
  rcases List.mem_append.mp hz with hz | hz
  · exact List.disjoint_left.mp (H.cross_interiors f s i (switchProduct f i)) hz hzQ
  · have he := List.mem_singleton.mp hz
    subst z
    exact H.second_interior_not_port s (switchProduct f i) (1, switchProduct f i) hzQ

theorem route_interiors_pairwise (f s : List (Fin n × Fin n))
    (hf : f.Sublist (firstLayer n)) :
    Pairwise (fun i j => List.Disjoint
      (installedRoutes first second f s i).interior
      (installedRoutes first second f s j).interior) := by
  intro i j hij
  rw [installedRoutes_interior_eq first second f s hf i,
    installedRoutes_interior_eq first second f s hf j]
  apply List.disjoint_left.mpr
  intro z hzi hzj
  simp only [List.mem_append, List.mem_singleton] at hzi hzj
  rcases hzi with (hzi | hzi) | hzi <;> rcases hzj with (hzj | hzj) | hzj
  · exact List.disjoint_left.mp (first.interiors_pairwise H.first_disjoint f hij) hzi hzj
  · subst z
    exact H.first_interior_not_port f i (1, switchProduct f j) hzi
  · exact List.disjoint_left.mp (H.cross_interiors f s i (switchProduct f j)) hzi hzj
  · subst z
    exact H.first_interior_not_port f j (1, switchProduct f i) hzj
  · exact hij ((switchProduct f).injective (H.intermediate_injective (hzi.symm.trans hzj)))
  · subst z
    exact H.second_interior_not_port s (switchProduct f j) (1, switchProduct f i) hzj
  · exact List.disjoint_left.mp (H.cross_interiors f s j (switchProduct f i)).symm hzi hzj
  · subst z
    exact H.second_interior_not_port s (switchProduct f i) (1, switchProduct f j) hzi
  · exact List.disjoint_left.mp (second.interiors_pairwise H.second_disjoint s
      (fun he => hij ((switchProduct f).injective he))) hzi hzj

theorem route_input_not_interior (f s : List (Fin n × Fin n))
    (hf : f.Sublist (firstLayer n)) (i j : Fin n) :
    input i ∉ (installedRoutes first second f s j).interior := by
  rw [installedRoutes_interior_eq first second f s hf j]
  intro hz
  simp only [List.mem_append, List.mem_singleton] at hz
  rcases hz with (hz | hz) | hz
  · exact H.first_interior_not_port f j (0, i) hz
  · exact H.input_ne_intermediate i (switchProduct f j) hz
  · exact H.second_interior_not_port s (switchProduct f j) (0, i) hz

theorem route_output_not_interior (f s : List (Fin n × Fin n))
    (hf : f.Sublist (firstLayer n)) (i j : Fin n) :
    output i ∉ (installedRoutes first second f s j).interior := by
  rw [installedRoutes_interior_eq first second f s hf j]
  intro hz
  simp only [List.mem_append, List.mem_singleton] at hz
  rcases hz with (hz | hz) | hz
  · exact H.first_interior_not_port f j (2, i) hz
  · exact H.output_ne_intermediate i (switchProduct f j) hz
  · exact H.second_interior_not_port s (switchProduct f j) (2, i) hz

theorem route_vertices_nodup (f s : List (Fin n × Fin n))
    (hf : f.Sublist (firstLayer n)) (hs : s.Sublist (secondLayer n)) (i : Fin n) :
    (installedRoutes first second f s i).vertices.Nodup := by
  have he := installedRoutes_endpoints first second f s hf hs i
  rw [Segment.vertices, Segment.body, he.1, he.2]
  apply (List.nodup_cons.mpr
    ⟨H.route_input_not_interior f s hf i i, H.route_interior_nodup f s hf i⟩).append (by simp)
  apply List.disjoint_left.mpr
  intro z hz hz'
  have hz' := List.mem_singleton.mp hz'
  subst z
  rcases List.mem_cons.mp hz with hz | hz
  · exact H.input_ne_output i _ hz.symm
  · exact H.route_output_not_interior f s hf _ i hz

theorem route_vertices_pairwise (f s : List (Fin n × Fin n))
    (hf : f.Sublist (firstLayer n)) (hs : s.Sublist (secondLayer n)) :
    Pairwise (fun i j => List.Disjoint
      (installedRoutes first second f s i).vertices
      (installedRoutes first second f s j).vertices) := by
  intro i j hij
  have hi := installedRoutes_endpoints first second f s hf hs i
  have hj := installedRoutes_endpoints first second f s hf hs j
  rw [Segment.vertices, Segment.body, Segment.vertices, Segment.body,
    hi.1, hi.2, hj.1, hj.2]
  apply List.disjoint_left.mpr
  intro z hzi hzj
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hzi hzj
  rcases hzi with (hzi | hzi) | hzi <;> rcases hzj with (hzj | hzj) | hzj
  · exact hij (H.input_injective (hzi.symm.trans hzj))
  · subst z
    exact H.route_input_not_interior f s hf i j hzj
  · exact H.input_ne_output i _ (hzi.symm.trans hzj)
  · subst z
    exact H.route_input_not_interior f s hf j i hzi
  · exact List.disjoint_left.mp (H.route_interiors_pairwise f s hf hij) hzi hzj
  · subst z
    exact H.route_output_not_interior f s hf _ i hzi
  · exact H.input_ne_output j _ (hzj.symm.trans hzi)
  · subst z
    exact H.route_output_not_interior f s hf _ j hzj
  · exact hij ((switchProduct s * switchProduct f).injective
      (H.output_injective (hzi.symm.trans hzj)))

theorem route_colors_nodup (f s : List (Fin n × Fin n))
    (hf : f.Sublist (firstLayer n)) (hs : s.Sublist (secondLayer n)) (i : Fin n) :
    ((installedRoutes first second f s i).colors (fun a b : G => b-a)).Nodup := by
  rw [installedRoutes_colors_eq first second f s hf hs i]
  exact (first.path_valid f i).2.2.append
    (second.path_valid s (switchProduct f i)).2.2 (H.cross_colors f s i _)

theorem route_colors_pairwise (f s : List (Fin n × Fin n))
    (hf : f.Sublist (firstLayer n)) (hs : s.Sublist (secondLayer n)) :
    Pairwise (fun i j => List.Disjoint
      ((installedRoutes first second f s i).colors (fun a b : G => b-a))
      ((installedRoutes first second f s j).colors (fun a b : G => b-a))) := by
  intro i j hij
  rw [installedRoutes_colors_eq first second f s hf hs i,
    installedRoutes_colors_eq first second f s hf hs j]
  apply List.disjoint_left.mpr
  intro z hzi hzj
  rcases List.mem_append.mp hzi with hzi | hzi <;>
    rcases List.mem_append.mp hzj with hzj | hzj
  · exact List.disjoint_left.mp (first.colors_pairwise H.first_disjoint f hij) hzi hzj
  · exact List.disjoint_left.mp (H.cross_colors f s i (switchProduct f j)) hzi hzj
  · exact List.disjoint_left.mp (H.cross_colors f s j (switchProduct f i)).symm hzi hzj
  · exact List.disjoint_left.mp (second.colors_pairwise H.second_disjoint s
      (fun he => hij ((switchProduct f).injective he))) hzi hzj

theorem route_colors_nonzero (f s : List (Fin n × Fin n))
    (hf : f.Sublist (firstLayer n)) (hs : s.Sublist (secondLayer n)) (i : Fin n) :
    ∀ c ∈ (installedRoutes first second f s i).colors (fun a b : G => b-a), c ≠ 0 :=
  difference_labels_nonzero _ (H.route_vertices_nodup f s hf hs i)

end TwoLayerSupport
end
end EndpointRouter
