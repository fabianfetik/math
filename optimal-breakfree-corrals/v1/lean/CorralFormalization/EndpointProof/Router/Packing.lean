import CorralFormalization.EndpointProof.Router.Counts

/-! # A linear packing of actual router switch candidates

The parameter family is chosen from the group and the four fixed ports
alone.  Its numerical supports are disjoint before any random reservoir
or any later forbidden set is supplied.
-/
namespace EndpointRouter
namespace Switch

open Affine
open scoped BigOperators
universe u
variable {G : Type u} [AddCommGroup G] [Fintype G] [DecidableEq G]

omit [Fintype G] in
theorem numericalSupport_nonempty (S : Switch G) (t : Parameters G) :
    (S.numericalSupport t).Nonempty := by
  exact ⟨S.randomRequest t (.inl 0),Finset.mem_image.mpr ⟨.inl 0,Finset.mem_univ _,rfl⟩⟩

theorem family_numericalSupport_card_le (S : Switch G) (B : Finset (Parameters G)) :
    (B.biUnion S.numericalSupport).card ≤ 18*B.card := by
  calc
    _ ≤ ∑ t ∈ B, (S.numericalSupport t).card := Finset.card_biUnion_le
    _ ≤ ∑ _t ∈ B, 18 := Finset.sum_le_sum (fun t _ => numericalSupport_card_le S t)
    _ = _ := by simp [Nat.mul_comm]

/-- Constructive greedy packing from the proved exclusion counts. -/
theorem exists_disjoint_parameters (hodd : Odd (Fintype.card G))
    (S : Switch G) (h : S.LegalPorts) (M : ℕ)
    (hsize : 121+324*M < Fintype.card G) :
    ∃ B : Finset (Parameters G), B.card = M ∧
      (∀ t ∈ B, (S.withParameters t).CollisionFree) ∧
      (∀ t ∈ B, ∀ u ∈ B, t ≠ u → Disjoint (S.numericalSupport t) (S.numericalSupport u)) := by
  induction M with
  | zero => exact ⟨∅,by simp,by simp,by simp⟩
  | succ M ih =>
    obtain ⟨B,hB,hvalid,hdisj⟩ := ih (by omega)
    let F := B.biUnion S.numericalSupport
    have hF : 121+18*F.card < Fintype.card G := by
      have hc := family_numericalSupport_card_le S B
      have hm := Nat.mul_le_mul_left 18 hc
      rw [hB] at hm
      dsimp [F]
      omega
    obtain ⟨t,htvalid,htdis⟩ := exists_fresh_parameters hodd S h F hF
    have htB : t ∉ B := by
      intro ht
      obtain ⟨z,hz⟩ := numericalSupport_nonempty S t
      apply Finset.disjoint_left.mp htdis hz
      exact Finset.mem_biUnion.mpr ⟨t,ht,hz⟩
    have htb : ∀ u ∈ B, Disjoint (S.numericalSupport t) (S.numericalSupport u) := by
      intro u hu
      exact htdis.mono_right (Finset.subset_biUnion_of_mem S.numericalSupport hu)
    refine ⟨insert t B,by simp [htB,hB],?_,?_⟩
    · intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact htvalid
      · exact hvalid u hu
    · intro x hx y hy hxy
      rcases Finset.mem_insert.mp hx with hxt | hxb
      · subst x
        rcases Finset.mem_insert.mp hy with hyt | hyb
        · subst y; exact (hxy rfl).elim
        · exact htb y hyb
      · rcases Finset.mem_insert.mp hy with hyt | hyb
        · subst y; exact (htb x hxb).symm
        · exact hdisj x hxb y hyb hxy

/-- A fixed indexed family, suitable for independent reservoir trials. -/
structure Packed (S : Switch G) (M : ℕ) where
  parameter : Fin M ↪ Parameters G
  valid : ∀ i, (S.withParameters (parameter i)).CollisionFree
  disjoint : Pairwise (fun i j =>
    Disjoint (S.numericalSupport (parameter i)) (S.numericalSupport (parameter j)))

theorem exists_packed (hodd : Odd (Fintype.card G))
    (S : Switch G) (h : S.LegalPorts) (M : ℕ)
    (hsize : 121+324*M < Fintype.card G) : Nonempty (S.Packed M) := by
  obtain ⟨B,hB,hvalid,hdisj⟩ := exists_disjoint_parameters hodd S h M hsize
  let e : B ≃ Fin M := Fintype.equivFinOfCardEq (by simpa using hB)
  let f : Fin M ↪ Parameters G :=
    ⟨fun i => (e.symm i).val,Subtype.val_injective.comp e.symm.injective⟩
  refine ⟨⟨f,fun i => hvalid _ (e.symm i).property,?_⟩⟩
  intro i j hij
  exact hdisj _ (e.symm i).property _ (e.symm j).property (fun he => hij (f.injective he))

/-- The paper's actual linear candidate count, with no large-order
premise: below 2000 the family is empty, as required by the floor. -/
theorem exists_packed_floor (hodd : Odd (Fintype.card G))
    (S : Switch G) (h : S.LegalPorts) : Nonempty (S.Packed (Fintype.card G / 2000)) := by
  by_cases hm : Fintype.card G / 2000 = 0
  · rw [hm]
    refine ⟨⟨Function.Embedding.ofIsEmpty,?_,?_⟩⟩
    · intro i; exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
  · apply exists_packed hodd S h
    have hd := Nat.div_mul_le_self (Fintype.card G) 2000
    omega

end Switch
end EndpointRouter
