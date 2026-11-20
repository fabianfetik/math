import CorralFormalization.Basic

set_option maxHeartbeats 0

namespace CorralFormalization

/-- The odd-core proper-prefix residues indexed in the proposed actual word
order. The `L/H` terms interleave first, followed by the interleaved `E/F`
terms; identification with concrete word-prefix sums is not proved here. -/
def oddCorePrefixResidueValue (A j : ℕ) : ℕ :=
  if j = 0 then 0 else
  if j = 1 then 2 else
  if j ≤ 2 * A + 1 then
    if j % 2 = 0 then j - 1 else 4 * A + 4 - j
  else if j = 2 * A + 2 then 2 * A + 1 else
  if j ≤ 4 * A then
    if j % 2 = 1 then 4 * A + 5 - j else j
  else if j = 4 * A + 1 then 4 else 4 * A + 2

/-- Explicit inverse index for the odd-core prefix-residue list. -/
def oddCorePrefixInverseValue (A v : ℕ) : ℕ :=
  if v = 0 then 0 else
  if v = 2 then 1 else
  if v = 4 * A + 2 then 4 * A + 2 else
  if v % 2 = 1 then
    if v ≤ 2 * A + 1 then v + 1 else 4 * A + 4 - v
  else if v ≤ 2 * A + 2 then 4 * A + 5 - v else v

/-- Quotient column transcribed from the normalized odd-core prefix table `(p+z)
mod U`, where `z=2A-3` and `U=(2A+3)(4A+3)`. Its identity with sums of the
concrete gap word is not proved in this module. -/
def oddCorePrefixQuotientValue (A j : ℕ) : ℕ :=
  if j = 0 then 0 else
  if j = 1 then 1 else
  if j ≤ 2 * A + 1 then
    if j % 2 = 0 then j / 2 + 1
    else if j ≤ 2 * A - 3 then (j + 3) / 2 else (j + 1) / 2
  else if j = 2 * A + 2 then A + 2 else
  if j ≤ 4 * A then
    if j % 2 = 1 then (j + 3) / 2
    else if j = 2 * A + 4 then A + 3 else j / 2 + 2
  else if j = 4 * A + 1 then 2 * A + 2 else 0

theorem oddCorePrefixResidueValue_lt (A : ℕ) (hA : 2 ≤ A)
    (j : Fin (4 * A + 3)) : oddCorePrefixResidueValue A j.val < 4 * A + 3 := by
  unfold oddCorePrefixResidueValue
  split_ifs <;> omega

theorem oddCorePrefixInverseValue_lt (A : ℕ) (hA : 2 ≤ A)
    (v : Fin (4 * A + 3)) : oddCorePrefixInverseValue A v.val < 4 * A + 3 := by
  unfold oddCorePrefixInverseValue
  split_ifs <;> omega

theorem oddCorePrefixQuotientValue_lt (A : ℕ) (hA : 2 ≤ A)
    (j : Fin (4 * A + 3)) : oddCorePrefixQuotientValue A j.val < 2 * A + 3 := by
  unfold oddCorePrefixQuotientValue
  split_ifs <;> omega

def oddCorePrefixResidue (A : ℕ) (hA : 2 ≤ A) (j : Fin (4 * A + 3)) : Fin (4 * A + 3) :=
  ⟨oddCorePrefixResidueValue A j.val, oddCorePrefixResidueValue_lt A hA j⟩

/-- Remainder column of the translated odd-core table, formed by cyclically adding
`z=2A-3` to the table-coded source prefix residue. The link to concrete word
sums remains a separate obligation. -/
def oddCoreTranslatedPrefixResidue (A : ℕ) (hA : 2 ≤ A)
    (j : Fin (4 * A + 3)) : Fin (4 * A + 3) :=
  oddCorePrefixResidue A hA j + ⟨2 * A - 3, by omega⟩

def oddCorePrefixInverse (A : ℕ) (hA : 2 ≤ A) (v : Fin (4 * A + 3)) : Fin (4 * A + 3) :=
  ⟨oddCorePrefixInverseValue A v.val, oddCorePrefixInverseValue_lt A hA v⟩

def oddCorePrefixQuotient (A : ℕ) (hA : 2 ≤ A) (j : Fin (4 * A + 3)) :
    Fin (2 * A + 3) :=
  ⟨oddCorePrefixQuotientValue A j.val, oddCorePrefixQuotientValue_lt A hA j⟩

theorem oddCorePrefixInverseValue_residueValue (A : ℕ) (hA : 2 ≤ A)
    (j : Fin (4 * A + 3)) :
    oddCorePrefixInverseValue A (oddCorePrefixResidueValue A j.val) = j.val := by
  by_cases hj0 : j.val = 0
  · simp [oddCorePrefixResidueValue, oddCorePrefixInverseValue, hj0]
  · by_cases hj1 : j.val = 1
    · simp [oddCorePrefixResidueValue, oddCorePrefixInverseValue, hj0, hj1]
    · by_cases hjLH : j.val ≤ 2 * A + 1
      · by_cases heven : j.val % 2 = 0
        · have hform : oddCorePrefixResidueValue A j.val = j.val - 1 := by
            simp [oddCorePrefixResidueValue, hj0, hj1, hjLH, heven]
          rw [hform]
          unfold oddCorePrefixInverseValue
          split_ifs <;> omega
        · have hform : oddCorePrefixResidueValue A j.val = 4 * A + 4 - j.val := by
            simp [oddCorePrefixResidueValue, hj0, hj1, hjLH, heven]
          rw [hform]
          unfold oddCorePrefixInverseValue
          split_ifs <;> omega
      · by_cases hjLA : j.val = 2 * A + 2
        · have hform : oddCorePrefixResidueValue A j.val = 2 * A + 1 := by
            simp [oddCorePrefixResidueValue, hj0, hj1, hjLH, hjLA]
          rw [hform]
          have hn0 : 2 * A + 1 ≠ 0 := by omega
          have hn2 : 2 * A + 1 ≠ 2 := by omega
          have hnlast : 2 * A + 1 ≠ 4 * A + 2 := by omega
          have hodd : (2 * A + 1) % 2 = 1 := by omega
          have hlow : 2 * A + 1 ≤ 2 * A + 1 := le_rfl
          simp only [oddCorePrefixInverseValue, if_neg hn0, if_neg hn2, if_neg hnlast,
            if_pos hodd, if_pos hlow]
          omega
        · by_cases hjEF : j.val ≤ 4 * A
          · by_cases hodd : j.val % 2 = 1
            · have hform : oddCorePrefixResidueValue A j.val = 4 * A + 5 - j.val := by
                simp [oddCorePrefixResidueValue, hj0, hj1, hjLH, hjLA, hjEF, hodd]
              rw [hform]
              unfold oddCorePrefixInverseValue
              split_ifs <;> omega
            · have hform : oddCorePrefixResidueValue A j.val = j.val := by
                simp [oddCorePrefixResidueValue, hj0, hj1, hjLH, hjLA, hjEF, hodd]
              rw [hform]
              unfold oddCorePrefixInverseValue
              split_ifs <;> omega
          · by_cases hjEA : j.val = 4 * A + 1
            · have hform : oddCorePrefixResidueValue A j.val = 4 := by
                rw [hjEA]
                have hn0 : 4 * A + 1 ≠ 0 := by omega
                have hn1 : 4 * A + 1 ≠ 1 := by omega
                have hnLH : ¬ 4 * A + 1 ≤ 2 * A + 1 := by omega
                have hnLA : 4 * A + 1 ≠ 2 * A + 2 := by omega
                have hnEF : ¬ 4 * A + 1 ≤ 4 * A := by omega
                simp only [oddCorePrefixResidueValue, if_neg hn0, if_neg hn1,
                  if_neg hnLH, if_neg hnLA, if_neg hnEF, if_true]
              rw [hform]
              have hn0 : (4 : ℕ) ≠ 0 := by omega
              have hn2 : (4 : ℕ) ≠ 2 := by omega
              have hnlast : (4 : ℕ) ≠ 4 * A + 2 := by omega
              have hnotodd : ¬ ((4 : ℕ) % 2 = 1) := by omega
              have hlow : (4 : ℕ) ≤ 2 * A + 2 := by omega
              simp only [oddCorePrefixInverseValue, if_neg hn0, if_neg hn2, if_neg hnlast,
                if_neg hnotodd, if_pos hlow]
              omega
            · have hjLast : j.val = 4 * A + 2 := by omega
              have hform : oddCorePrefixResidueValue A j.val = 4 * A + 2 := by
                simp [oddCorePrefixResidueValue, hj0, hj1, hjLH, hjLA, hjEF, hjEA]
              rw [hform]
              have hn0 : 4 * A + 2 ≠ 0 := by omega
              have hn2 : 4 * A + 2 ≠ 2 := by omega
              simp only [oddCorePrefixInverseValue, if_neg hn0, if_neg hn2, if_true]
              exact hjLast.symm

theorem oddCorePrefixResidueValue_inverseValue (A : ℕ) (hA : 2 ≤ A)
    (v : Fin (4 * A + 3)) :
    oddCorePrefixResidueValue A (oddCorePrefixInverseValue A v.val) = v.val := by
  by_cases hv0 : v.val = 0
  · simp [oddCorePrefixResidueValue, oddCorePrefixInverseValue, hv0]
  · by_cases hv2 : v.val = 2
    · simp [oddCorePrefixResidueValue, oddCorePrefixInverseValue, hv0, hv2]
    · by_cases hvlast : v.val = 4 * A + 2
      · have hform : oddCorePrefixInverseValue A v.val = 4 * A + 2 := by
          simp only [oddCorePrefixInverseValue, if_neg hv0, if_neg hv2, if_pos hvlast]
        rw [hform]
        have hres : oddCorePrefixResidueValue A (4 * A + 2) = 4 * A + 2 := by
          have hn0 : 4 * A + 2 ≠ 0 := by omega
          have hn1 : 4 * A + 2 ≠ 1 := by omega
          have hnLH : ¬ 4 * A + 2 ≤ 2 * A + 1 := by omega
          have hnLA : 4 * A + 2 ≠ 2 * A + 2 := by omega
          have hnEF : ¬ 4 * A + 2 ≤ 4 * A := by omega
          have hnEA : 4 * A + 2 ≠ 4 * A + 1 := by omega
          simp only [oddCorePrefixResidueValue, if_neg hn0, if_neg hn1, if_neg hnLH,
            if_neg hnLA, if_neg hnEF, if_neg hnEA]
        rw [hres]
        exact hvlast.symm
      · by_cases hvodd : v.val % 2 = 1
        · by_cases hlow : v.val ≤ 2 * A + 1
          · have hform : oddCorePrefixInverseValue A v.val = v.val + 1 := by
              simp [oddCorePrefixInverseValue, hv0, hv2, hvlast, hvodd, hlow]
            rw [hform]
            unfold oddCorePrefixResidueValue
            split_ifs <;> simp_all <;> omega
          · have hform : oddCorePrefixInverseValue A v.val = 4 * A + 4 - v.val := by
              simp [oddCorePrefixInverseValue, hv0, hv2, hvlast, hvodd, hlow]
            rw [hform]
            unfold oddCorePrefixResidueValue
            split_ifs <;> simp_all <;> omega
        · by_cases hlow : v.val ≤ 2 * A + 2
          · have hform : oddCorePrefixInverseValue A v.val = 4 * A + 5 - v.val := by
              simp [oddCorePrefixInverseValue, hv0, hv2, hvlast, hvodd, hlow]
            rw [hform]
            let q : ℕ := 4 * A + 5 - v.val
            change oddCorePrefixResidueValue A q = v.val
            have hqlo : 2 * A + 3 ≤ q := by dsimp [q]; omega
            have hqhi : q ≤ 4 * A + 1 := by
              have hv4 : 4 ≤ v.val := by omega
              dsimp [q]
              omega
            by_cases hv4 : v.val = 4
            · have hqeq : q = 4 * A + 1 := by dsimp [q]; omega
              rw [hqeq]
              have hE : oddCorePrefixResidueValue A (4 * A + 1) = 4 := by
                have hn0 : 4 * A + 1 ≠ 0 := by omega
                have hn1 : 4 * A + 1 ≠ 1 := by omega
                have hnLH : ¬ 4 * A + 1 ≤ 2 * A + 1 := by omega
                have hnLA : 4 * A + 1 ≠ 2 * A + 2 := by omega
                have hnEF : ¬ 4 * A + 1 ≤ 4 * A := by omega
                simp only [oddCorePrefixResidueValue, if_neg hn0, if_neg hn1,
                  if_neg hnLH, if_neg hnLA, if_neg hnEF, if_true]
              rw [hE]
              omega
            · have hqneLast : q ≠ 4 * A + 1 := by dsimp [q]; omega
              have hqle : q ≤ 4 * A := by omega
              have hqodd : q % 2 = 1 := by dsimp [q]; omega
              have hqne0 : q ≠ 0 := by omega
              have hqne1 : q ≠ 1 := by omega
              have hqneLA : q ≠ 2 * A + 2 := by omega
              have hqhigh : ¬ q ≤ 2 * A + 1 := by omega
              simp only [oddCorePrefixResidueValue, if_neg hqne0, if_neg hqne1,
                if_neg hqhigh, if_neg hqneLA, if_pos hqle, if_pos hqodd]
              omega
          · have hform : oddCorePrefixInverseValue A v.val = v.val := by
              simp [oddCorePrefixInverseValue, hv0, hv2, hvlast, hvodd, hlow]
            rw [hform]
            unfold oddCorePrefixResidueValue
            split_ifs <;> simp_all <;> omega

/-- The displayed table-coded prefix-residue enumeration has an explicit
inverse, uniformly for all `A≥2`. This proves the transversal property of the
encoded table; identifying it with concrete word-prefix sums and the physical
cut/profile argument remain separate. -/
theorem oddCorePrefixResidue_bijective (A : ℕ) (hA : 2 ≤ A) :
    Function.Bijective (oddCorePrefixResidue A hA) := by
  have hleft : Function.LeftInverse (oddCorePrefixInverse A hA) (oddCorePrefixResidue A hA) := by
    intro j
    apply Fin.ext
    change oddCorePrefixInverseValue A (oddCorePrefixResidueValue A j.val) = j.val
    exact oddCorePrefixInverseValue_residueValue A hA j
  have hright : Function.RightInverse (oddCorePrefixInverse A hA) (oddCorePrefixResidue A hA) := by
    intro v
    apply Fin.ext
    change oddCorePrefixResidueValue A (oddCorePrefixInverseValue A v.val) = v.val
    exact oddCorePrefixResidueValue_inverseValue A hA v
  exact ⟨hleft.injective, hright.surjective⟩

theorem oddCoreTranslatedPrefixResidue_bijective (A : ℕ) (hA : 2 ≤ A) :
    Function.Bijective (oddCoreTranslatedPrefixResidue A hA) := by
  letI : NeZero (4 * A + 3) := ⟨by omega⟩
  let z : Fin (4 * A + 3) := ⟨2 * A - 3, by omega⟩
  have hshift : Function.Bijective (fun r : Fin (4 * A + 3) => r + z) := by
    exact (Equiv.addRight z).bijective
  change Function.Bijective ((fun r : Fin (4 * A + 3) => r + z) ∘
    oddCorePrefixResidue A hA)
  exact Function.Bijective.comp hshift (oddCorePrefixResidue_bijective A hA)

end CorralFormalization
