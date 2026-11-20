import CorralFormalization.EndpointProof.Router.LayerAction

/-! # Constructing paths from concrete local layer geometry

The input data store actual local affine switches and idle paths, with
correct ports and local collision tests.  Endpoint permutations, actual
track paths and their setting-independent inventories are proved below;
they are not fields of the input structure.
-/
namespace EndpointRouter

open EndpointFactor Equiv Equiv.Perm
open scoped Classical
noncomputable section
universe u v w
variable {α : Type u} [Fintype α] [DecidableEq α]
variable {G : Type v} [AddCommGroup G]

structure LayerGeometry (L : MatchingLayer α) (input output : α → G) where
  exchange : (α × α) → Switch G
  idle : α → Idle G
  exchange_ports : ∀ e ∈ L.edges,
    (exchange e).x = input e.1 ∧ (exchange e).y = input e.2 ∧
    (exchange e).v = output e.1 ∧ (exchange e).w = output e.2
  exchange_valid : ∀ e ∈ L.edges, (exchange e).CollisionFree
  idle_ports : ∀ i, L.Isolated i → (idle i).x = input i ∧ (idle i).y = output i
  idle_valid : ∀ i, L.Isolated i → (idle i).Valid

namespace MatchingLayer
variable (L : MatchingLayer α)

def incidentEdge (i : α) (hi : ¬ L.Isolated i) : α × α :=
  Classical.choose (not_not.mp hi)

theorem incidentEdge_mem (i : α) (hi : ¬ L.Isolated i) : L.incidentEdge i hi ∈ L.edges :=
  (Classical.choose_spec (not_not.mp hi)).1

theorem incidentEdge_incident (i : α) (hi : ¬ L.Isolated i) : L.Incident i (L.incidentEdge i hi) :=
  (Classical.choose_spec (not_not.mp hi)).2

theorem incidentEdge_eq (i : α) (hi : ¬ L.Isolated i) (e : α × α)
    (he : e ∈ L.edges) (hie : L.Incident i e) : L.incidentEdge i hi = e :=
  L.incident_unique i _ (L.incidentEdge_mem i hi) e he (L.incidentEdge_incident i hi) hie

end MatchingLayer

namespace LayerGeometry
variable {L : MatchingLayer α} {input output : α → G} (D : LayerGeometry L input output)

/-- Construct the actual path on each track; only one local setting bit
is chosen for the incident switch. -/
def path (chosen : List (α × α)) (i : α) : Segment G :=
  if hi : L.Isolated i then (D.idle i).path else
    let e := L.incidentEdge i hi
    (D.exchange e).path (decide (e ∈ chosen)) (decide (i = e.2))

theorem path_isolated (chosen : List (α × α)) (i : α) (hi : L.Isolated i) :
    D.path chosen i = (D.idle i).path := by simp only [path,dif_pos hi]

theorem path_left (chosen : List (α × α)) (e : α × α) (he : e ∈ L.edges) :
    D.path chosen e.1 = (D.exchange e).path (decide (e ∈ chosen)) false := by
  have hi : ¬ L.Isolated e.1 := fun h => h ⟨e,he,Or.inl rfl⟩
  have hchoose := L.incidentEdge_eq e.1 hi e he (Or.inl rfl)
  simp only [path,dif_neg hi,hchoose,decide_eq_false_iff_not.mpr (L.no_loop e he)]

theorem path_right (chosen : List (α × α)) (e : α × α) (he : e ∈ L.edges) :
    D.path chosen e.2 = (D.exchange e).path (decide (e ∈ chosen)) true := by
  have hi : ¬ L.Isolated e.2 := fun h => h ⟨e,he,Or.inr rfl⟩
  have hchoose := L.incidentEdge_eq e.2 hi e he (Or.inr rfl)
  simp only [path,dif_neg hi,hchoose,decide_true]

/-- The locally constructed paths realize exactly the selected installed
permutation; the endpoint claim is a theorem, not supplied geometry. -/
theorem endpoints (chosen : List (α × α)) (hsub : chosen.Sublist L.edges) (i : α) :
    (D.path chosen i).first = input i ∧
      (D.path chosen i).last = output (switchProduct chosen i) := by
  by_cases hi : L.Isolated i
  · rw [D.path_isolated chosen i hi,L.product_isolated chosen hsub i hi]
    exact D.idle_ports i hi
  · obtain ⟨e,he,hie⟩ : ∃ e ∈ L.edges, L.Incident i e := not_not.mp hi
    obtain ⟨hx,hy,hv,hw⟩ := D.exchange_ports e he
    rcases hie with rfl | rfl
    · rw [D.path_left chosen e he,L.product_left chosen hsub e he]
      by_cases hc : e ∈ chosen <;> simp [hc,hx,hy,hv,hw]
    · rw [D.path_right chosen e he,L.product_right chosen hsub e he]
      by_cases hc : e ∈ chosen <;> simp [hc,hx,hy,hv,hw]

/-- Every actual track path has four internal vertices, is simple and
rainbow. Global cross-track disjointness remains a separate condition. -/
theorem path_valid (chosen : List (α × α)) (i : α) :
    (D.path chosen i).interior.length = 4 ∧
    (D.path chosen i).vertices.Nodup ∧
    ((D.path chosen i).colors (fun a b : G => b-a)).Nodup := by
  by_cases hi : L.Isolated i
  · rw [D.path_isolated chosen i hi]
    exact ⟨rfl,(D.idle_valid i hi).1,(D.idle_valid i hi).2⟩
  · obtain ⟨e,he,hie⟩ : ∃ e ∈ L.edges, L.Incident i e := not_not.mp hi
    have hv := (D.exchange e).setting_valid (D.exchange_valid e he) (decide (e ∈ chosen))
    rcases hie with rfl | rfl
    · rw [D.path_left chosen e he]
      exact ⟨Switch.path_interior_length _ _ _,hv.2.2.1 false,hv.2.2.2.1 false⟩
    · rw [D.path_right chosen e he]
      exact ⟨Switch.path_interior_length _ _ _,hv.2.2.1 true,hv.2.2.2.1 true⟩

/-- Generic finite inventory expansion. The only local input is the
already proved two-track inventory identity of the concrete switch. -/
theorem inventory {C : Type w} (field : Segment G → List C) (common : Switch G → List C)
    (hcommon : ∀ S : Switch G, ∀ cross z,
      z ∈ field (S.path cross false) ∨ z ∈ field (S.path cross true) ↔ z ∈ common S)
    (chosen : List (α × α)) (z : C) :
    (∃ i, z ∈ field (D.path chosen i)) ↔
      (∃ e ∈ L.edges, z ∈ common (D.exchange e)) ∨
      (∃ i, L.Isolated i ∧ z ∈ field (D.idle i).path) := by
  constructor
  · rintro ⟨i,hz⟩
    by_cases hi : L.Isolated i
    · right
      exact ⟨i,hi,by simpa only [D.path_isolated chosen i hi] using hz⟩
    · obtain ⟨e,he,hie⟩ : ∃ e ∈ L.edges, L.Incident i e := not_not.mp hi
      left
      refine ⟨e,he,?_⟩
      apply (hcommon (D.exchange e) (decide (e ∈ chosen)) z).mp
      rcases hie with rfl | rfl
      · exact Or.inl (by simpa only [D.path_left chosen e he] using hz)
      · exact Or.inr (by simpa only [D.path_right chosen e he] using hz)
  · rintro (⟨e,he,hz⟩ | ⟨i,hi,hz⟩)
    · rcases (hcommon (D.exchange e) (decide (e ∈ chosen)) z).mpr hz with hz | hz
      · exact ⟨e.1,by simpa only [D.path_left chosen e he] using hz⟩
      · exact ⟨e.2,by simpa only [D.path_right chosen e he] using hz⟩
    · exact ⟨i,by simpa only [D.path_isolated chosen i hi] using hz⟩

/-- Exact fixed internal-vertex inventory for every setting. -/
theorem interior_inventory (chosen : List (α × α)) (z : G) :
    (∃ i, z ∈ (D.path chosen i).interior) ↔
      (∃ e ∈ L.edges, z ∈ (D.exchange e).interior) ∨
      (∃ i, L.Isolated i ∧ z ∈ (D.idle i).interior) :=
  D.inventory Segment.interior Switch.interior Switch.interior_inventory chosen z

/-- Exact fixed actual-difference inventory for every setting. -/
theorem color_inventory (chosen : List (α × α)) (z : G) :
    (∃ i, z ∈ (D.path chosen i).colors (fun a b : G => b-a)) ↔
      (∃ e ∈ L.edges, z ∈ (D.exchange e).colors) ∨
      (∃ i, L.Isolated i ∧ z ∈ (D.idle i).colors) :=
  D.inventory (fun P => P.colors (fun a b : G => b-a)) Switch.colors Switch.color_inventory chosen z

end LayerGeometry
end
end EndpointRouter
