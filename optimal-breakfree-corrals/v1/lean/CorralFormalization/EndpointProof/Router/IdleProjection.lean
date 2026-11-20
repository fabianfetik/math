import CorralFormalization.EndpointProof.Router.Trials
import CorralFormalization.EndpointProof.Router.Greedy

/-! # Idle paths supplied by the same universal switch event

For a single x→v idle query, choose two harmless additional fixed ports and
use the straight x→v path of an actual successful full router switch.
The full eighteen-request event is stronger than the nine-request idle
event and has already been paid in the common probability estimate.
-/
namespace EndpointRouter

open EndpointRouter.Affine
open scoped Classical
noncomputable section
universe u
variable {G : Type u} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Only five labels are forbidden in the second auxiliary-port choice. -/
theorem legal_auxiliary_ports (hn : 6 ≤ Fintype.card G) (x v : G) (hxv : x ≠ v) :
    ∃ y w : G, (Switch.seed (x,y,v,w)).LegalPorts := by
  have hfirst : ({x,v} : Finset G).card < (Finset.univ : Finset G).card := by
    have hc : ({x,v} : Finset G).card ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
    simp only [Finset.card_univ]
    omega
  obtain ⟨y,_,hy⟩ := Finset.exists_mem_notMem_of_card_lt_card hfirst
  have hy' : y ≠ x ∧ y ≠ v := by simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using hy
  let bad : Finset G := ([x,y,v,v-(x-y),v+(x-y)] : List G).toFinset
  have hbad : bad.card < (Finset.univ : Finset G).card := by
    have hc : bad.card ≤ 5 := List.toFinset_card_le _
    simp only [Finset.card_univ]
    omega
  obtain ⟨w,_,hw⟩ := Finset.exists_mem_notMem_of_card_lt_card hbad
  have hw' : w ≠ x ∧ w ≠ y ∧ w ≠ v ∧ w ≠ v-(x-y) ∧ w ≠ v+(x-y) := by
    simpa only [bad,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false,not_or] using hw
  refine ⟨y,w,?_,?_,?_⟩
  · change [x,y,v,w].Nodup
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or,and_true,List.nodup_nil]
    grind
  · change v-w ≠ x-y
    intro he
    apply hw'.2.2.2.1
    have hh := sub_eq_iff_eq_add.mp he
    rw [hh]
    abel
  · change v-w ≠ -(x-y)
    intro he
    apply hw'.2.2.2.2
    have hh := sub_eq_iff_eq_add.mp he
    rw [hh]
    abel

namespace Switch

def idleProjection (S : Switch G) : Idle G :=
  ⟨S.x,S.v,S.a,S.d+S.x,S.d+S.h,S.f+S.x⟩

@[simp] theorem idleProjection_path (S : Switch G) :
    S.idleProjection.path = S.path false false := rfl

theorem idleProjection_valid (S : Switch G) (h : S.CollisionFree) : S.idleProjection.Valid := by
  have hs := S.setting_valid h false
  exact ⟨hs.2.2.1 false,hs.2.2.2.1 false⟩

theorem idleProjection_interior_subset (S : Switch G) : S.idleProjection.interior ⊆ S.interior := by
  intro z hz
  simpa only [idleProjection,Idle.interior,interior,List.mem_cons,List.not_mem_nil,or_false] using
    (show z = S.a ∨ z = S.h ∨ z = S.d+S.x ∨ z = S.d+S.y ∨ z = S.d+S.h ∨
      z = S.d+S.c ∨ z = S.f+S.x ∨ z = S.f+S.y from by
      simp only [idleProjection,Idle.interior,List.mem_cons,List.not_mem_nil,or_false] at hz
      grind)

theorem idleProjection_colors_subset (S : Switch G) : S.idleProjection.colors ⊆ S.colors := by
  intro c hc
  exact (S.colors_perm false).mem_iff.mp (List.mem_append_left _ hc)

/-- The deterministic combined request support is exactly the fixed
interior/colour inventory used by the primitive installation interface. -/
theorem numericalSupport_eq_inventory (S : Switch G) (t : Parameters G) :
    S.numericalSupport t = ((S.withParameters t).interior ++ (S.withParameters t).colors).toFinset := by
  ext z
  simp only [numericalSupport,Finset.mem_image,Finset.mem_univ,true_and,
    List.mem_toFinset,List.mem_append]
  constructor
  · rintro ⟨i,rfl⟩
    cases i with
    | inl i =>
      left
      rw [interior_ofFn]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    | inr i =>
      right
      rw [colors_ofFn]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
  · rintro (hz | hz)
    · rw [interior_ofFn] at hz
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
      exact ⟨.inl i,rfl⟩
    · rw [colors_ofFn] at hz
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
      exact ⟨.inr i,rfl⟩

end Switch

/-- The proved universal switch event supplies the exact local primitive
contract for *both* exchanges and single idle paths.  No extra idle event,
matching or reservoir assumption is introduced. -/
theorem local_supply_of_switch_event (hodd : Odd (Fintype.card G))
    (hn : 6 ≤ Fintype.card G) (budget : ℕ) (ω : Bool × G → Bool)
    (hevent : Switch.UniversallyAvailable hodd budget ω)
    (q : Query G) (hq : q.Legal) (F : Finset G) (hF : F.card ≤ budget) :
    ∃ P : Primitive G,
      P.Good {z | ω (false,z) = true} {c | ω (true,c) = true} q ∧
      Disjoint P.support F := by
  cases q with
  | exchange x y v w =>
    let r : Switch.PortQuery G := ⟨(x,y,v,w),hq⟩
    let packing := Switch.queryPacking hodd r
    obtain ⟨i,hi,hd⟩ := hevent r F hF
    let S := (Switch.seed r.val).withParameters (packing.parameter i)
    have hrs := packing.success_reservoirs ω i hi
    refine ⟨.exchange S,?_,?_⟩
    · exact ⟨rfl,rfl,rfl,rfl,packing.valid i,hrs.1,hrs.2⟩
    · simpa only [Primitive.support,Primitive.interior,Primitive.colors,
        Switch.numericalSupport_eq_inventory] using hd
  | idle x v =>
    obtain ⟨y,w,hr⟩ := legal_auxiliary_ports hn x v hq
    let r : Switch.PortQuery G := ⟨(x,y,v,w),hr⟩
    let packing := Switch.queryPacking hodd r
    obtain ⟨i,hi,hd⟩ := hevent r F hF
    let S := (Switch.seed r.val).withParameters (packing.parameter i)
    have hrs := packing.success_reservoirs ω i hi
    refine ⟨.idle S.idleProjection,?_,?_⟩
    · refine ⟨rfl,rfl,S.idleProjection_valid (packing.valid i),?_,?_⟩
      · intro z hz
        exact hrs.1 z (S.idleProjection_interior_subset hz)
      · intro c hc
        exact hrs.2 c (S.idleProjection_colors_subset hc)
    · apply hd.mono_left
      rw [Switch.numericalSupport_eq_inventory]
      intro z hz
      simp only [Primitive.support,Primitive.interior,Primitive.colors,List.mem_toFinset,List.mem_append] at hz ⊢
      rcases hz with hz | hz
      · exact Or.inl (S.idleProjection_interior_subset hz)
      · exact Or.inr (S.idleProjection_colors_subset hz)

end
end EndpointRouter
