import CorralFormalization.EndpointProof.Matching.Fractional.RobustWeights.ActualBlocks
import CorralFormalization.EndpointProof.Matching.Fractional.ActualRemainder.Budget

/-!
# Physical and signed coordinates have the same edit distance

The signs are exactly `(-X, Y, -C)`.  The raw masks are reflected once,
before use in the matrix.  Later target edits are paid by their physical
distance and require no new Fourier assertion.
-/

open scoped Classical BigOperators Matrix Matrix.Norms.Operator symmDiff

namespace EndpointMatching.Fractional.RobustWeights

open EndpointFlow.AbelianTransport EndpointMatching.AbsorptionAssembly
open EndpointMatching.UniversalCore EndpointFractionalRawEvent
open EndpointMatching.Fractional.ActualRemainder
noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G]

def signCoordinate (r : Fin 3) (g : G) : G := if r = 1 then g else -g

theorem signCoordinate_involutive (r : Fin 3) : Function.Involutive (signCoordinate (G := G) r) := by
  intro g
  by_cases h : r = 1 <;> simp [signCoordinate, h]

theorem signCoordinate_injective (r : Fin 3) : Function.Injective (signCoordinate (G := G) r) :=
  (signCoordinate_involutive r).injective

/-- Rolewise reflection of the original physical masks or an actual target. -/
def signedSets (T : PhysicalTarget G) (r : Fin 3) : Finset G :=
  (T r).image (signCoordinate r)

theorem signedSets_mem (T : PhysicalTarget G) (r : Fin 3) (g : G) :
    g ∈ signedSets T r ↔ signCoordinate r g ∈ T r := by
  constructor
  · rintro hg
    obtain ⟨x,hx,hxg⟩ := Finset.mem_image.mp hg
    rw [← hxg, signCoordinate_involutive r x]
    exact hx
  · intro hg
    exact Finset.mem_image.mpr ⟨signCoordinate r g, hg, signCoordinate_involutive r g⟩

theorem signedSets_bit (T : PhysicalTarget G) (r : Fin 3) (g : G) :
    setBit (signedSets T r) g = setBit (T r) (signCoordinate r g) := by
  unfold setBit
  exact if_congr (signedSets_mem T r g) rfl rfl

/-- The slice-coordinate system of the paper's actual tagged target is
precisely the reflected physical system. -/
theorem signedCoordinateSet_signedTarget (T : PhysicalTarget G) :
    signedCoordinateSet (signedTarget (T 0) (T 1) (T 2)) = signedSets T := by
  funext r
  ext g
  rw [signedCoordinateSet_mem, signedSets_mem]
  fin_cases r <;> simp [signedTarget, signCoordinate, Prod.mk.injEq, neg_eq_iff_eq_neg]

theorem signedSets_distance (T R : PhysicalTarget G) :
    editDistance (signedSets T) (signedSets R) = editDistance T R := by
  unfold editDistance
  apply Finset.sum_congr rfl
  intro r _
  unfold signedSets
  rw [← Finset.image_symmDiff _ _ (signCoordinate_injective r),
    Finset.card_image_of_injective _ (signCoordinate_injective r)]

theorem signedSets_involutive (T : PhysicalTarget G) : signedSets (signedSets T) = T := by
  funext r
  ext g
  simp only [signedSets_mem, signCoordinate_involutive r g]

/-- Decode any actual tagged inventory into its three physical sets. -/
def physicalSets (W : Finset (Vertex G)) : PhysicalTarget G := signedSets (signedCoordinateSet W)

theorem signedSets_physicalSets (W : Finset (Vertex G)) :
    signedSets (physicalSets W) = signedCoordinateSet W := signedSets_involutive _

/-- The decoder reconstructs the identical actual tagged inventory. -/
theorem signedTarget_physicalSets (W : Finset (Vertex G)) :
    signedTarget (physicalSets W 0) (physicalSets W 1) (physicalSets W 2) = W := by
  ext ⟨r,g⟩
  rw [← signedCoordinateSet_mem
    (signedTarget (physicalSets W 0) (physicalSets W 1) (physicalSets W 2)) r g,
    signedCoordinateSet_signedTarget, signedSets_physicalSets]
  exact signedCoordinateSet_mem W r g

private theorem symmDiff_card (S U : Finset G) :
    (S ∆ U).card = (S \ U).card + (U \ S).card := by
  have heq : S ∆ U = (S \ U) ∪ (U \ S) := by
    ext g
    simp only [Finset.mem_symmDiff, Finset.mem_union, Finset.mem_sdiff]
  rw [heq, Finset.card_union_of_disjoint]
  exact Finset.disjoint_left.mpr (fun _ hS hU => (Finset.mem_sdiff.mp hU).2 (Finset.mem_sdiff.mp hS).1)

/-- Compatibility between the earlier natural-valued physical metric and
the raw-event real-valued symmetric-difference metric. -/
theorem editDistance_eq_physicalEditDistance (T R : PhysicalTarget G) :
    editDistance T R = (physicalEditDistance (R 0) (R 1) (R 2) (T 0) (T 1) (T 2) : ℝ) := by
  simp [editDistance, Fin.sum_univ_succ, physicalEditDistance, symmDiff_card]
  ring

/-- No decoding loss occurs for arbitrary later actual inventories. -/
theorem physicalSets_taggedDistance (W : Finset (Vertex G)) (R : PhysicalTarget G) :
    editDistance (physicalSets W) R =
      (taggedDistance (signedTarget (R 0) (R 1) (R 2)) W : ℝ) := by
  calc
    editDistance (physicalSets W) R =
        (physicalEditDistance (R 0) (R 1) (R 2)
          (physicalSets W 0) (physicalSets W 1) (physicalSets W 2) : ℝ) :=
      editDistance_eq_physicalEditDistance _ _
    _ = (taggedDistance (signedTarget (R 0) (R 1) (R 2))
        (signedTarget (physicalSets W 0) (physicalSets W 1) (physicalSets W 2)) : ℝ) := by
      rw [taggedDistance_signedTarget]
    _ = _ := by rw [signedTarget_physicalSets]

theorem signedTarget_distance (T R : PhysicalTarget G) :
    editDistance (signedCoordinateSet (signedTarget (T 0) (T 1) (T 2))) (signedSets R) =
      editDistance T R := by
  rw [signedCoordinateSet_signedTarget, signedSets_distance]

/-- The constructed actual edit matrix satisfies the literal physical
distance bound from the manuscript. -/
theorem actualEditMatrix_norm_le_physical (T R : PhysicalTarget G)
    (hW : Balanced (signedTarget (T 0) (T 1) (T 2))) :
    ‖actualEditMatrix (signedTarget (T 0) (T 1) (T 2)) hW (signedSets R)‖ ≤
      editDistance T R := by
  simpa only [signedTarget_distance] using
    actualEditMatrix_norm_le (signedTarget (T 0) (T 1) (T 2)) hW (signedSets R)

/-- The edit norm bound also uses the unchanged tagged inventory metric for
arbitrary later `W`, including actual complements of reserved/frozen edges. -/
theorem actualEditMatrix_norm_le_tagged (W : Finset (Vertex G)) (hW : Balanced W)
    (R : PhysicalTarget G) :
    ‖actualEditMatrix W hW (signedSets R)‖ ≤
      (taggedDistance (signedTarget (R 0) (R 1) (R 2)) W : ℝ) := by
  have h := actualEditMatrix_norm_le W hW (signedSets R)
  rw [← signedSets_physicalSets W, signedSets_distance, physicalSets_taggedDistance] at h
  exact h

end
end EndpointMatching.Fractional.RobustWeights
