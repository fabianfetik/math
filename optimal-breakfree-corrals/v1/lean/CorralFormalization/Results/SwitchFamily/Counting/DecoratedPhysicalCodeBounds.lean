import CorralFormalization.Results.SwitchFamily.Counting.DecoratedPhysicalCode

/-!
# The fixed paper alphabet and actual physical switch coordinates

Here m is literally switchMultiplicity (2*h-1), fixed at the target height.
The phasewise binary decoding and the actual site-pair choice bijection
are composed into a genuine equivariant bijection. No m is recomputed at
any smaller period.
-/

namespace CorralFormalization.Results.SwitchFamily.Counting.DecoratedPhysicalCode

open CorralFormalization.LatinCompletion
open CorralFormalization.Results.SwitchFamily
open CorralFormalization.Results.SwitchFamily.Physical
open CorralFormalization.Results.SwitchFamily.LayoutPhysicalBridge

noncomputable section

/-- Our word action is positive precomposition; geometric bits move by -t. -/
theorem phaseBitsEquiv_precompose {h m : ℕ} (t : ZMod h) (f : ZMod h → Fin (2^m)) :
    phaseBitsEquiv h m (fun q => f (q+t)) = bitShift (-t) (phaseBitsEquiv h m f) := by
  funext ⟨i,q⟩
  simp only [phaseBitsEquiv,Equiv.coe_fn_mk,bitShift,sub_neg_eq_add]

variable {h : ℕ} [NeZero h] [NeZero (2*h-1)] [NeZero (h*(2*h-1))]

/-- The existing exact floor parameter pays the physical site-pair geometry. -/
theorem explicitSizeBound (hh : 33 ≤ h) :
    (5*switchMultiplicity (2*h-1)+8)^2 ≤ 2*h-1 := by
  change (5*Prefix.count (2*h-1)+8)^2 ≤ 2*h-1
  exact Prefix.count_square_bound (by omega)

/-- A bijection with the actual physical switch subsets, at the actual fixed m. -/
def explicitChoiceEquiv (hh : 33 ≤ h) :
    (Bit (switchMultiplicity (2*h-1)) h → Bool) ≃ SwitchChoice hh :=
  bitsChoiceEquiv (explicitSizeBound hh)

/-- Actual geometric whole-phase translation of the physical selected pairs. -/
def explicitShiftChoice (hh : 33 ≤ h) (a : ZMod h) (U : SwitchChoice hh) : SwitchChoice hh :=
  shiftChoice (explicitSizeBound hh) a U

@[simp] theorem explicitShiftChoice_val (hh : 33 ≤ h) (a : ZMod h) (U : SwitchChoice hh) :
    (explicitShiftChoice hh a U).1 =
      U.1.image (fun e => (e.1+TerraceLift.zeroSite h (2*h-1) a,
        e.2+TerraceLift.zeroSite h (2*h-1) a)) := rfl

/-- A genuine bijection between the exact counted type and the actual
layout/physical-switch-choice parameter space. -/
def decoratedPhysicalEquiv (hh : 33 ≤ h) :
    DecoratedLayout h (2^switchMultiplicity (2*h-1)) ≃ Layout h × SwitchChoice hh :=
  (decoratedEquiv h (2^switchMultiplicity (2*h-1))).trans
    (Equiv.prodCongr (Equiv.refl (Layout h))
      ((phaseBitsEquiv h (switchMultiplicity (2*h-1))).trans (explicitChoiceEquiv hh)))

/-- This observable is literally the binary digit deciding the corresponding
concrete physical pair. It rules out a mere cardinality correspondence. -/
theorem decoratedPhysicalEquiv_pair_mem (hh : 33 ≤ h)
    (u : DecoratedLayout h (2^switchMultiplicity (2*h-1)))
    (k : Bit (switchMultiplicity (2*h-1)) h) :
    sitePair (n:=2*h-1) k ∈ (decoratedPhysicalEquiv hh u).2.1 ↔
      colorBitsEquiv (switchMultiplicity (2*h-1)) ((u k.2).2) k.1 = true := by
  exact selectedPairs_mem_iff (explicitSizeBound hh) _ k

/-- Actual equivariance, with the physical image translation shown explicitly.
Precomposition by t shifts all tile/bit phases geometrically by -t. -/
theorem decoratedPhysicalEquiv_rotate (hh : 33 ≤ h)
    (t : ZMod h) (u : DecoratedLayout h (2^switchMultiplicity (2*h-1))) :
    decoratedPhysicalEquiv hh (t +ᵥ u) =
      (LocalWord.rotate t (decoratedPhysicalEquiv hh u).1,
        explicitShiftChoice hh (-t) (decoratedPhysicalEquiv hh u).2) := by
  apply Prod.ext
  · apply LocalWord.ext
    intro q
    rfl
  · change explicitChoiceEquiv hh
      (phaseBitsEquiv h (switchMultiplicity (2*h-1)) (fun q => (u (q+t)).2)) =
        explicitShiftChoice hh (-t)
          (explicitChoiceEquiv hh (phaseBitsEquiv h (switchMultiplicity (2*h-1)) (fun q => (u q).2)))
    rw [phaseBitsEquiv_precompose t (fun q => (u q).2)]
    exact bitsChoiceEquiv_shift (explicitSizeBound hh) (-t) _

theorem decoratedPhysicalEquiv_injective (hh : 33 ≤ h) :
    Function.Injective (decoratedPhysicalEquiv hh) := (decoratedPhysicalEquiv hh).injective

theorem decoratedPhysicalEquiv_surjective (hh : 33 ≤ h) :
    Function.Surjective (decoratedPhysicalEquiv hh) := (decoratedPhysicalEquiv hh).surjective

/-- The explicit counted code can immediately be realized by the existing
anchored physical-family constructor. -/
def anchoredDecoratedFamily (hh : 33 ≤ h)
    (D : TerraceCompletion.DirectedTerrace (2*h-1))
    (hD : Prefix.PrescribedTerrace (switchMultiplicity (2*h-1)) D)
    (u : DecoratedLayout h (2^switchMultiplicity (2*h-1))) :=
  anchoredFamily hh D hD (decoratedPhysicalEquiv hh u)

theorem anchoredDecoratedFamily_injective (hh : 33 ≤ h)
    (D : TerraceCompletion.DirectedTerrace (2*h-1))
    (hD : Prefix.PrescribedTerrace (switchMultiplicity (2*h-1)) D) :
    Function.Injective (anchoredDecoratedFamily hh D hD) :=
  (anchoredFamily_injective hh D hD).comp (decoratedPhysicalEquiv hh).injective

end
end CorralFormalization.Results.SwitchFamily.Counting.DecoratedPhysicalCode
