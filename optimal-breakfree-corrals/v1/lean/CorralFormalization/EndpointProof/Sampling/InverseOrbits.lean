import CorralFormalization.EndpointProof.Sampling.OriginalReservoir
import Mathlib.GroupTheory.OrderOfElement

open scoped Classical

namespace EndpointOriginalReservoir

noncomputable section

/-- Odd cardinality rules out nonzero fixed points of negation. -/
theorem neg_ne_self_of_odd {G : Type*} [Fintype G] [AddCommGroup G]
    (hodd : Odd (Fintype.card G)) {g : G} (hg : g ≠ 0) : -g ≠ g := by
  have hcop : (Nat.card G).Coprime 2 := by
    rw [Nat.card_eq_fintype_card]
    exact hodd.coprime_two_right
  have hinj : Function.Injective (fun x : G ↦ (2 : ℕ) • x) :=
    hcop.nsmul_right_bijective.injective
  intro hn
  apply hg
  apply hinj
  simp only [nsmul_zero]
  rw [two_nsmul]
  calc
    g+g = g+(-g) := congrArg (fun x ↦ g+x) hn.symm
    _ = 0 := add_neg_cancel g

/-- Deterministically choose the earlier member of each nonzero inverse pair. -/
def OddOrbit (G : Type*) [Fintype G] [AddCommGroup G] :=
  {g : G // g ≠ 0 ∧ Fintype.equivFin G g < Fintype.equivFin G (-g)}

instance {G : Type*} [Fintype G] [AddCommGroup G] : Fintype (OddOrbit G) :=
  inferInstanceAs (Fintype {g : G // g ≠ 0 ∧ Fintype.equivFin G g < Fintype.equivFin G (-g)})

def orbitCoordinate {G : Type*} [Fintype G] [AddCommGroup G]
    (z : OddOrbit G × Bool) : G := if z.2 then -z.1.val else z.1.val

theorem orbitCoordinate_injective {G : Type*} [Fintype G] [AddCommGroup G] :
    Function.Injective (orbitCoordinate (G := G)) := by
  rintro ⟨r,b⟩ ⟨s,c⟩ h
  cases b <;> cases c
  · have he : r.val = s.val := by simpa [orbitCoordinate] using h
    have hrs : r = s := Subtype.ext he
    simp [hrs]
  · have he : r.val = -s.val := by simpa [orbitCoordinate] using h
    have hr := r.property.2
    have hs := s.property.2
    rw [he, neg_neg] at hr
    exact False.elim (lt_asymm hs hr)
  · have he : -r.val = s.val := by simpa [orbitCoordinate] using h
    have hr := r.property.2
    have hs := s.property.2
    rw [← he, neg_neg] at hs
    exact False.elim (lt_asymm hr hs)
  · have he : -r.val = -s.val := by simpa [orbitCoordinate] using h
    have hrs : r = s := Subtype.ext (neg_injective he)
    simp [hrs]

def orbitPlace {G : Type*} [Fintype G] [AddCommGroup G] : OddOrbit G × Bool ↪ G :=
  ⟨orbitCoordinate, orbitCoordinate_injective⟩

theorem orbitPlace_nonzero {G : Type*} [Fintype G] [AddCommGroup G]
    (z : OddOrbit G × Bool) : orbitPlace z ≠ 0 := by
  rcases z with ⟨r,b⟩
  cases b <;> simpa [orbitPlace, orbitCoordinate] using r.property.1

theorem orbitPlace_neg {G : Type*} [Fintype G] [AddCommGroup G]
    (o : OddOrbit G) (b : Bool) : orbitPlace (o,!b) = -orbitPlace (o,b) := by
  cases b <;> simp [orbitPlace, orbitCoordinate]

theorem orbitPlace_covers_nonzero {G : Type*} [Fintype G] [AddCommGroup G]
    (hodd : Odd (Fintype.card G)) {g : G} (hg : g ≠ 0) :
    ∃ z : OddOrbit G × Bool, orbitPlace z = g := by
  have hne : Fintype.equivFin G g ≠ Fintype.equivFin G (-g) := by
    intro he
    exact neg_ne_self_of_odd hodd hg ((Fintype.equivFin G).injective he).symm
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact ⟨(⟨g,hg,hlt⟩,false), by simp [orbitPlace, orbitCoordinate]⟩
  · refine ⟨(⟨-g, by simpa using hg, by simpa using hgt⟩,true), ?_⟩
    simp [orbitPlace, orbitCoordinate]

/-- A concrete inverse-pair coordinate system for every finite odd abelian group. -/
theorem odd_inverse_orbit_coordinate_system {G : Type*} [Fintype G] [AddCommGroup G]
    (hodd : Odd (Fintype.card G)) :
    (∀ z : OddOrbit G × Bool, orbitPlace z ≠ 0) ∧
    (∀ o b, orbitPlace (o,!b) = -(orbitPlace (o,b) : G)) ∧
    (∀ g : G, g ≠ 0 → ∃ z : OddOrbit G × Bool, orbitPlace z = g) := by
  exact ⟨orbitPlace_nonzero, orbitPlace_neg, fun _ hg ↦ orbitPlace_covers_nonzero hodd hg⟩

end
end EndpointOriginalReservoir
