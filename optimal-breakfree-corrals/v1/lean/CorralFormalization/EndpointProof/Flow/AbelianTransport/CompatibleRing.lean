import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.Algebra.Ring.Pi
import Mathlib.Algebra.Ring.InjSurj

/-!
A commutative ring structure on a finite abelian group which retains its
already specified additive structure. Multiplication and one are auxiliary;
the original zero, addition, negation, subtraction and integer actions are
used unchanged in the injective pullback.
-/

open scoped Classical

namespace EndpointFlow.AbelianTransport

noncomputable section

variable {G R : Type*} [AddCommGroup G] [CommRing R]

/-- Pull back multiplication along an additive equivalence, keeping the
original additive operations rather than transporting a second copy of them. -/
abbrev commRingOfAddEquiv (e : G ≃+ R) : CommRing G := by
  letI : One G := ⟨e.symm 1⟩
  letI : Mul G := ⟨fun x y ↦ e.symm (e x * e y)⟩
  letI : Pow G ℕ := ⟨fun x n ↦ e.symm (e x ^ n)⟩
  letI : NatCast G := ⟨fun n ↦ e.symm (n : R)⟩
  letI : IntCast G := ⟨fun n ↦ e.symm (n : R)⟩
  exact Function.Injective.commRing (e : G → R) e.injective
    e.map_zero (e.apply_symm_apply 1) e.map_add
    (fun x y ↦ e.apply_symm_apply (e x * e y))
    e.map_neg e.map_sub
    (fun n x ↦ map_nsmul e n x) (fun n x ↦ map_zsmul e n x)
    (fun x n ↦ e.apply_symm_apply (e x ^ n))
    (fun n ↦ e.apply_symm_apply (n : R))
    (fun n ↦ e.apply_symm_apply (n : R))

/-- This equality is by reflexivity (proof fields are irrelevant), not just
an isomorphism of two different additions on the same underlying type. -/
theorem commRingOfAddEquiv_additive (e : G ≃+ R) :
    (commRingOfAddEquiv e).toAddCommGroup = (inferInstance : AddCommGroup G) := rfl

/-- Every finite abelian group admits a commutative ring structure with
exactly its existing additive group structure. Oddness is not required here. -/
theorem exists_compatible_commRing (G : Type*) [AddCommGroup G] [Finite G] :
    ∃ ring : CommRing G, ring.toAddCommGroup = (inferInstance : AddCommGroup G) := by
  obtain ⟨ι,hι,p,hp,n,⟨e⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite G
  letI : Fintype ι := hι
  let a : G ≃+ ((i : ι) → ZMod (p i ^ n i)) :=
    e.trans (DirectSum.addEquivProd (fun i ↦ ZMod (p i ^ n i)))
  exact ⟨commRingOfAddEquiv a,commRingOfAddEquiv_additive a⟩

end
end EndpointFlow.AbelianTransport
