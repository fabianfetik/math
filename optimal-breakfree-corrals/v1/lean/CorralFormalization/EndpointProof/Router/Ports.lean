import CorralFormalization.EndpointProof.Router.Switch
import Mathlib.Data.Finset.Card

/-! # Deterministic intermediate-port selection

At each step the two difference exclusions cost at most two numerical
labels.  This module chooses an actual distinct sequence from a finite
reservoir.  The alternating input/output differences in the two-layer router construction
may be supplied as the prescribed `deltas` list.
-/
namespace EndpointRouter

open EndpointFactor
universe u
variable {G : Type u} [AddCommGroup G] [DecidableEq G]

def portExclusions (previous delta : G) : Finset G :=
  {previous+delta, previous-delta}

theorem portExclusions_card (previous delta : G) :
    (portExclusions previous delta).card ≤ 2 :=
  (Finset.card_insert_le _ _).trans (by simp)

theorem avoids_portExclusions (previous delta m : G)
    (h : m ∉ portExclusions previous delta) :
    m-previous ≠ delta ∧ m-previous ≠ -delta := by
  simp only [portExclusions,Finset.mem_insert,Finset.mem_singleton,not_or] at h
  constructor
  · intro he
    apply h.1
    have hh := sub_eq_iff_eq_add.mp he
    simpa [add_comm] using hh
  · intro he
    apply h.2
    have hh := sub_eq_iff_eq_add.mp he
    simpa [sub_eq_add_neg,add_comm] using hh

theorem fresh_intermediate_port (RV F used : Finset G) (previous delta : G)
    (hcard : F.card + used.card + 2 < RV.card) :
    ∃ m ∈ RV, m ∉ F ∧ m ∉ used ∧ m-previous ≠ delta ∧ m-previous ≠ -delta := by
  let bad := F ∪ used ∪ portExclusions previous delta
  have hb : bad.card < RV.card := by
    have h1 := Finset.card_union_le F used
    have h2 := Finset.card_union_le (F ∪ used) (portExclusions previous delta)
    have h3 := portExclusions_card previous delta
    dsimp [bad]
    omega
  obtain ⟨m,hm,hbad⟩ := Finset.exists_mem_notMem_of_card_lt_card hb
  have hnot : m ∉ F ∧ m ∉ used ∧ m ∉ portExclusions previous delta := by
    simpa only [bad,Finset.mem_union,not_or,and_assoc] using hbad
  obtain ⟨hplus,hminus⟩ := avoids_portExclusions previous delta m hnot.2.2
  exact ⟨m,hm,hnot.1,hnot.2.1,hplus,hminus⟩

/-- Choose the whole sequence once.  All ports lie in the reservoir,
are distinct, avoid F, and meet the prescribed pairwise difference
restrictions.  The first restriction from `previous` may be harmlessly
added when only consecutive intermediate ports are constrained. -/
theorem choose_intermediate_ports (RV F : Finset G) (previous : G) (deltas : List G)
    (hcard : F.card + deltas.length + 2 < RV.card) :
    ∃ ports : List G,
      ports.length = deltas.length ∧ ports.Nodup ∧
      (∀ m ∈ ports, m ∈ RV ∧ m ∉ F) ∧
      List.Forall₂ (fun difference delta => difference ≠ delta ∧ difference ≠ -delta)
        (edgeLabels (fun a b : G => b-a) (previous::ports)) deltas := by
  induction deltas generalizing F previous with
  | nil => exact ⟨[],rfl,by simp,by simp,.nil⟩
  | cons delta rest ih =>
    have hc : F.card + (∅ : Finset G).card + 2 < RV.card := by
      simp only [List.length_cons] at hcard
      simp
      omega
    obtain ⟨m,hm,hF,_,hplus,hminus⟩ := fresh_intermediate_port RV F ∅ previous delta hc
    have hcard' : (insert m F).card + rest.length + 2 < RV.card := by
      have hi := Finset.card_insert_le m F
      simp only [List.length_cons] at hcard
      omega
    obtain ⟨ports,hlen,hnd,havoid,hchain⟩ := ih (insert m F) m hcard'
    refine ⟨m::ports,by simp [hlen],?_,?_,?_⟩
    · exact hnd.cons (fun hin => (havoid m hin).2 (Finset.mem_insert_self _ _))
    · intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact ⟨hm,hF⟩
      · exact ⟨(havoid z hz).1,fun hzF => (havoid z hz).2 (Finset.mem_insert_of_mem hzF)⟩
    · exact .cons ⟨hplus,hminus⟩ hchain

end EndpointRouter
