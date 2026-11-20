import CorralFormalization.Results.ConstructionCorrespondence.SwitchBits

/-! Literal switch-row coordinate identity, with two complete bit strings
as inputs. This deliberately does not replace them by a merely equinumerous
family. Only their actually used indices matter. -/

namespace CorralFormalization.Results.ConstructionCorrespondence.LiteralSwitchRows

open EvenSwitches
open Results.ConstructionCorrespondence.SwitchBits

def literalRowA (m : ℕ) (e f : ℕ → ℕ) : Finset ℕ :=
  {0} ∪ (Finset.range (halfHeight m)).image
      (fun j => (2*j+1+e j)*(height m-1)) ∪
    (Finset.Ico 1 (halfHeight m)).image (fun i => 2*height m*i-i%2) ∪
    (Finset.range (halfHeight m)).image
      (fun j => (height m+2+2*j)*(height m-1)+f j) ∪
    (Finset.range m).biUnion
      (fun r => {2*height m*(halfHeight m+1+2*r),
        2*height m*(halfHeight m+1+2*r)+height m-1})

def literalRowB (m : ℕ) (e f : ℕ → ℕ) : Finset ℕ :=
  {(height m)^2-1, (height m)^2, clock m-1} ∪
    (Finset.range (halfHeight m)).image
      (fun j => (2*j+2-e j)*(height m-1)) ∪
    (Finset.Ico 1 (halfHeight m)).image
      (fun i => 2*height m*i-(1-i%2)) ∪
    (Finset.range (halfHeight m)).image
      (fun j => (height m+2+2*j)*(height m-1)+1-f j) ∪
    (Finset.range (m-1)).biUnion
      (fun r => {2*height m*(halfHeight m+2+2*r),
        2*height m*(halfHeight m+2+2*r)+height m-1})

theorem rowA_eq_literalRowA (m : ℕ) (a : Choices m) (e f : ℕ → ℕ)
    (he : ∀ j, j ≤ 2*m → eta m a.1 j = e j)
    (hf : ∀ j, j ≤ 2*m → epsilon m a.2 j = f j) :
    rowA m a = literalRowA m e f := by
  have hlow : (Finset.range (halfHeight m)).image (lowerA m a.1) =
      (Finset.range (halfHeight m)).image (fun j => (2*j+1+e j)*(height m-1)) := by
    apply Finset.image_congr
    intro j hj
    have hj' : j ≤ 2*m := by have := Finset.mem_range.mp hj; unfold halfHeight at *; omega
    rw [lowerA, he j hj']
  have hup : (Finset.range (halfHeight m)).image (upperA m a.2) =
      (Finset.range (halfHeight m)).image (fun j => (height m+2+2*j)*(height m-1)+f j) := by
    apply Finset.image_congr
    intro j hj
    have hj' : j ≤ 2*m := by have := Finset.mem_range.mp hj; unfold halfHeight at *; omega
    rw [upperA, hf j hj']
  simp only [rowA, literalRowA, hlow, hup, fixedA]
  rfl

theorem rowB_eq_literalRowB (m : ℕ) (a : Choices m) (e f : ℕ → ℕ)
    (he : ∀ j, j ≤ 2*m → eta m a.1 j = e j)
    (hf : ∀ j, j ≤ 2*m → epsilon m a.2 j = f j) :
    rowB m a = literalRowB m e f := by
  have hlow : (Finset.range (halfHeight m)).image (lowerB m a.1) =
      (Finset.range (halfHeight m)).image (fun j => (2*j+2-e j)*(height m-1)) := by
    apply Finset.image_congr
    intro j hj
    have hj' : j ≤ 2*m := by have := Finset.mem_range.mp hj; unfold halfHeight at *; omega
    rw [lowerB, he j hj']
  have hup : (Finset.range (halfHeight m)).image (upperB m a.2) =
      (Finset.range (halfHeight m)).image (fun j => (height m+2+2*j)*(height m-1)+1-f j) := by
    apply Finset.image_congr
    intro j hj
    have hj' : j ≤ 2*m := by have := Finset.mem_range.mp hj; unfold halfHeight at *; omega
    rw [upperB, hf j hj']
  simp only [rowB, literalRowB, hlow, hup, fixedB]
  rfl

theorem symmetric_bit_rows_represented (m : ℕ) (hm : 1 ≤ m) (e f : ℕ → ℕ)
    (hebin : ∀ j, j ≤ 2*m → e j ≤ 1) (hfbin : ∀ j, j ≤ 2*m → f j ≤ 1)
    (hesym : ∀ j, j ≤ 2*m → e (2*m-j) = e j)
    (hfsym : ∀ j, j ≤ 2*m → f (2*m-j) = f j)
    (hezero : e 0 = 1) (helast : e (2*m) = 1)
    (hfzero : f 0 = 1) (hflast : f (2*m) = 1)
    (hfone : f 1 = 0) (hfpenultimate : f (2*m-1) = 0) :
    ∃ a : Choices m, rowA m a = literalRowA m e f ∧ rowB m a = literalRowB m e f := by
  obtain ⟨a, he, hf⟩ := symmetric_bit_choices_surjective m hm e f hebin hfbin hesym hfsym
    hezero helast hfzero hflast hfone hfpenultimate
  exact ⟨a, rowA_eq_literalRowA m a e f he hf, rowB_eq_literalRowB m a e f he hf⟩

end CorralFormalization.Results.ConstructionCorrespondence.LiteralSwitchRows
