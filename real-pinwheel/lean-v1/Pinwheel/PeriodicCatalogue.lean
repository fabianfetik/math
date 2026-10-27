import Pinwheel.PeriodicScan
import Pinwheel.CatalogueData
import Mathlib.Tactic.FinCases

/-!
# Kernel certificates for all 84 periodic word cases

Generated from the original R021 evidence by `export_r021_periodic_lean.py`.
Array/list and cap equalities connect every literal case to CatalogueData.
Each label's finite scan is reduced by the Lean kernel. Separate declarations
keep the largest computations within the available memory.
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel
namespace Catalogue

-- Case 0: F0082; period 18.
def periodicArray0 : Array (Fin 5) := #[0, 0, 1, 0, 0, 4, 0, 2, 0, 1, 0, 0, 3, 0, 0, 1, 0, 2]
def periodicWord0 (k : Fin 18) : Fin 5 :=
  periodicArray0[k.val]
def periodicCaps0 : Fin 5 → RateCap
  | 0 => { bound := (3/5 : ℚ), closed := false }
  | 1 => { bound := (1/6 : ℚ), closed := false }
  | 2 => { bound := (1/9 : ℚ), closed := false }
  | 3 => { bound := (1/18 : ℚ), closed := true }
  | 4 => { bound := (1/18 : ℚ), closed := true }

theorem periodicArray0_toList :
    periodicArray0.toList = words 0 := by rfl
theorem periodicCaps0_eq : periodicCaps0 = wordCaps 0 := by rfl

theorem periodicScan0_0 : ∀ s : Fin 18,
    prefixCheck 18 (by decide) periodicWord0
      (periodicCaps0 0) 0 s 18 0 0 = true := by
  decide +kernel

theorem periodicScan0_1 : ∀ s : Fin 18,
    prefixCheck 18 (by decide) periodicWord0
      (periodicCaps0 1) 1 s 18 0 0 = true := by
  decide +kernel

theorem periodicScan0_2 : ∀ s : Fin 18,
    prefixCheck 18 (by decide) periodicWord0
      (periodicCaps0 2) 2 s 18 0 0 = true := by
  decide +kernel

theorem periodicScan0_3 : ∀ s : Fin 18,
    prefixCheck 18 (by decide) periodicWord0
      (periodicCaps0 3) 3 s 18 0 0 = true := by
  decide +kernel

theorem periodicScan0_4 : ∀ s : Fin 18,
    prefixCheck 18 (by decide) periodicWord0
      (periodicCaps0 4) 4 s 18 0 0 = true := by
  decide +kernel

theorem periodicCertificate0 :
    WordCertificate 18 (by decide) periodicWord0 periodicCaps0 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan0_0
  · exact periodicScan0_1
  · exact periodicScan0_2
  · exact periodicScan0_3
  · exact periodicScan0_4

theorem schedulable_word0 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 0) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps0 r := by
    simpa only [periodicCaps0_eq] using hr
  exact ⟨periodic 18 (by decide) periodicWord0,
    validRates_periodic_of_wordCertificate (by decide) periodicWord0
      periodicCertificate0 hc⟩

-- Case 1: F0094; period 18.
def periodicArray1 : Array (Fin 5) := #[0, 0, 0, 3, 0, 2, 0, 1, 0, 0, 4, 0, 0, 3, 0, 2, 0, 1]
def periodicWord1 (k : Fin 18) : Fin 5 :=
  periodicArray1[k.val]
def periodicCaps1 : Fin 5 → RateCap
  | 0 => { bound := (3/5 : ℚ), closed := false }
  | 1 => { bound := (1/9 : ℚ), closed := false }
  | 2 => { bound := (1/9 : ℚ), closed := false }
  | 3 => { bound := (1/9 : ℚ), closed := false }
  | 4 => { bound := (1/18 : ℚ), closed := true }

theorem periodicArray1_toList :
    periodicArray1.toList = words 1 := by rfl
theorem periodicCaps1_eq : periodicCaps1 = wordCaps 1 := by rfl

theorem periodicScan1_0 : ∀ s : Fin 18,
    prefixCheck 18 (by decide) periodicWord1
      (periodicCaps1 0) 0 s 18 0 0 = true := by
  decide +kernel

theorem periodicScan1_1 : ∀ s : Fin 18,
    prefixCheck 18 (by decide) periodicWord1
      (periodicCaps1 1) 1 s 18 0 0 = true := by
  decide +kernel

theorem periodicScan1_2 : ∀ s : Fin 18,
    prefixCheck 18 (by decide) periodicWord1
      (periodicCaps1 2) 2 s 18 0 0 = true := by
  decide +kernel

theorem periodicScan1_3 : ∀ s : Fin 18,
    prefixCheck 18 (by decide) periodicWord1
      (periodicCaps1 3) 3 s 18 0 0 = true := by
  decide +kernel

theorem periodicScan1_4 : ∀ s : Fin 18,
    prefixCheck 18 (by decide) periodicWord1
      (periodicCaps1 4) 4 s 18 0 0 = true := by
  decide +kernel

theorem periodicCertificate1 :
    WordCertificate 18 (by decide) periodicWord1 periodicCaps1 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan1_0
  · exact periodicScan1_1
  · exact periodicScan1_2
  · exact periodicScan1_3
  · exact periodicScan1_4

theorem schedulable_word1 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 1) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps1 r := by
    simpa only [periodicCaps1_eq] using hr
  exact ⟨periodic 18 (by decide) periodicWord1,
    validRates_periodic_of_wordCertificate (by decide) periodicWord1
      periodicCertificate1 hc⟩

-- Case 2: F0113; period 19.
def periodicArray2 : Array (Fin 5) := #[0, 0, 1, 0, 2, 0, 0, 3, 0, 1, 0, 4, 0, 0, 2, 0, 1, 0, 3]
def periodicWord2 (k : Fin 19) : Fin 5 :=
  periodicArray2[k.val]
def periodicCaps2 : Fin 5 → RateCap
  | 0 => { bound := (11/19 : ℚ), closed := true }
  | 1 => { bound := (2/13 : ℚ), closed := false }
  | 2 => { bound := (2/19 : ℚ), closed := true }
  | 3 => { bound := (1/10 : ℚ), closed := false }
  | 4 => { bound := (1/19 : ℚ), closed := true }

theorem periodicArray2_toList :
    periodicArray2.toList = words 2 := by rfl
theorem periodicCaps2_eq : periodicCaps2 = wordCaps 2 := by rfl

theorem periodicScan2_0 : ∀ s : Fin 19,
    prefixCheck 19 (by decide) periodicWord2
      (periodicCaps2 0) 0 s 19 0 0 = true := by
  decide +kernel

theorem periodicScan2_1 : ∀ s : Fin 19,
    prefixCheck 19 (by decide) periodicWord2
      (periodicCaps2 1) 1 s 19 0 0 = true := by
  decide +kernel

theorem periodicScan2_2 : ∀ s : Fin 19,
    prefixCheck 19 (by decide) periodicWord2
      (periodicCaps2 2) 2 s 19 0 0 = true := by
  decide +kernel

theorem periodicScan2_3 : ∀ s : Fin 19,
    prefixCheck 19 (by decide) periodicWord2
      (periodicCaps2 3) 3 s 19 0 0 = true := by
  decide +kernel

theorem periodicScan2_4 : ∀ s : Fin 19,
    prefixCheck 19 (by decide) periodicWord2
      (periodicCaps2 4) 4 s 19 0 0 = true := by
  decide +kernel

theorem periodicCertificate2 :
    WordCertificate 19 (by decide) periodicWord2 periodicCaps2 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan2_0
  · exact periodicScan2_1
  · exact periodicScan2_2
  · exact periodicScan2_3
  · exact periodicScan2_4

theorem schedulable_word2 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 2) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps2 r := by
    simpa only [periodicCaps2_eq] using hr
  exact ⟨periodic 19 (by decide) periodicWord2,
    validRates_periodic_of_wordCertificate (by decide) periodicWord2
      periodicCertificate2 hc⟩

-- Case 3: F0160; period 18.
def periodicArray3 : Array (Fin 5) := #[0, 0, 1, 0, 2, 0, 3, 0, 1, 0, 0, 4, 0, 2, 0, 1, 0, 3]
def periodicWord3 (k : Fin 18) : Fin 5 :=
  periodicArray3[k.val]
def periodicCaps3 : Fin 5 → RateCap
  | 0 => { bound := (5/9 : ℚ), closed := true }
  | 1 => { bound := (1/6 : ℚ), closed := false }
  | 2 => { bound := (1/9 : ℚ), closed := true }
  | 3 => { bound := (1/10 : ℚ), closed := false }
  | 4 => { bound := (1/18 : ℚ), closed := true }

theorem periodicArray3_toList :
    periodicArray3.toList = words 3 := by rfl
theorem periodicCaps3_eq : periodicCaps3 = wordCaps 3 := by rfl

theorem periodicScan3_0 : ∀ s : Fin 18,
    prefixCheck 18 (by decide) periodicWord3
      (periodicCaps3 0) 0 s 18 0 0 = true := by
  decide +kernel

theorem periodicScan3_1 : ∀ s : Fin 18,
    prefixCheck 18 (by decide) periodicWord3
      (periodicCaps3 1) 1 s 18 0 0 = true := by
  decide +kernel

theorem periodicScan3_2 : ∀ s : Fin 18,
    prefixCheck 18 (by decide) periodicWord3
      (periodicCaps3 2) 2 s 18 0 0 = true := by
  decide +kernel

theorem periodicScan3_3 : ∀ s : Fin 18,
    prefixCheck 18 (by decide) periodicWord3
      (periodicCaps3 3) 3 s 18 0 0 = true := by
  decide +kernel

theorem periodicScan3_4 : ∀ s : Fin 18,
    prefixCheck 18 (by decide) periodicWord3
      (periodicCaps3 4) 4 s 18 0 0 = true := by
  decide +kernel

theorem periodicCertificate3 :
    WordCertificate 18 (by decide) periodicWord3 periodicCaps3 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan3_0
  · exact periodicScan3_1
  · exact periodicScan3_2
  · exact periodicScan3_3
  · exact periodicScan3_4

theorem schedulable_word3 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 3) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps3 r := by
    simpa only [periodicCaps3_eq] using hr
  exact ⟨periodic 18 (by decide) periodicWord3,
    validRates_periodic_of_wordCertificate (by decide) periodicWord3
      periodicCertificate3 hc⟩

-- Case 4: F0167; period 44.
def periodicArray4 : Array (Fin 5) := #[0, 0, 2, 0, 1, 0, 0, 2, 0, 1, 0, 0, 2, 0, 1, 0, 3, 0, 2, 0, 1, 0, 0, 4, 0, 1, 0, 2, 0, 1, 0, 0, 2, 0, 1, 0, 0, 3, 0, 1, 0, 2, 0, 1]
def periodicWord4 (k : Fin 44) : Fin 5 :=
  periodicArray4[k.val]
def periodicCaps4 : Fin 5 → RateCap
  | 0 => { bound := (5/9 : ℚ), closed := false }
  | 1 => { bound := (1/5 : ℚ), closed := false }
  | 2 => { bound := (1/8 : ℚ), closed := false }
  | 3 => { bound := (1/22 : ℚ), closed := false }
  | 4 => { bound := (1/44 : ℚ), closed := true }

theorem periodicArray4_toList :
    periodicArray4.toList = words 4 := by rfl
theorem periodicCaps4_eq : periodicCaps4 = wordCaps 4 := by rfl

theorem periodicScan4_0 : ∀ s : Fin 44,
    prefixCheck 44 (by decide) periodicWord4
      (periodicCaps4 0) 0 s 44 0 0 = true := by
  decide +kernel

theorem periodicScan4_1 : ∀ s : Fin 44,
    prefixCheck 44 (by decide) periodicWord4
      (periodicCaps4 1) 1 s 44 0 0 = true := by
  decide +kernel

theorem periodicScan4_2 : ∀ s : Fin 44,
    prefixCheck 44 (by decide) periodicWord4
      (periodicCaps4 2) 2 s 44 0 0 = true := by
  decide +kernel

theorem periodicScan4_3 : ∀ s : Fin 44,
    prefixCheck 44 (by decide) periodicWord4
      (periodicCaps4 3) 3 s 44 0 0 = true := by
  decide +kernel

theorem periodicScan4_4 : ∀ s : Fin 44,
    prefixCheck 44 (by decide) periodicWord4
      (periodicCaps4 4) 4 s 44 0 0 = true := by
  decide +kernel

theorem periodicCertificate4 :
    WordCertificate 44 (by decide) periodicWord4 periodicCaps4 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan4_0
  · exact periodicScan4_1
  · exact periodicScan4_2
  · exact periodicScan4_3
  · exact periodicScan4_4

theorem schedulable_word4 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 4) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps4 r := by
    simpa only [periodicCaps4_eq] using hr
  exact ⟨periodic 44 (by decide) periodicWord4,
    validRates_periodic_of_wordCertificate (by decide) periodicWord4
      periodicCertificate4 hc⟩

-- Case 5: F0169; period 28.
def periodicArray5 : Array (Fin 5) := #[0, 0, 0, 1, 0, 2, 0, 1, 0, 0, 3, 0, 1, 0, 2, 0, 1, 0, 0, 4, 0, 1, 0, 2, 0, 3, 0, 1]
def periodicWord5 (k : Fin 28) : Fin 5 :=
  periodicArray5[k.val]
def periodicCaps5 : Fin 5 → RateCap
  | 0 => { bound := (5/9 : ℚ), closed := false }
  | 1 => { bound := (1/5 : ℚ), closed := false }
  | 2 => { bound := (3/28 : ℚ), closed := true }
  | 3 => { bound := (1/14 : ℚ), closed := false }
  | 4 => { bound := (1/28 : ℚ), closed := true }

theorem periodicArray5_toList :
    periodicArray5.toList = words 5 := by rfl
theorem periodicCaps5_eq : periodicCaps5 = wordCaps 5 := by rfl

theorem periodicScan5_0 : ∀ s : Fin 28,
    prefixCheck 28 (by decide) periodicWord5
      (periodicCaps5 0) 0 s 28 0 0 = true := by
  decide +kernel

theorem periodicScan5_1 : ∀ s : Fin 28,
    prefixCheck 28 (by decide) periodicWord5
      (periodicCaps5 1) 1 s 28 0 0 = true := by
  decide +kernel

theorem periodicScan5_2 : ∀ s : Fin 28,
    prefixCheck 28 (by decide) periodicWord5
      (periodicCaps5 2) 2 s 28 0 0 = true := by
  decide +kernel

theorem periodicScan5_3 : ∀ s : Fin 28,
    prefixCheck 28 (by decide) periodicWord5
      (periodicCaps5 3) 3 s 28 0 0 = true := by
  decide +kernel

theorem periodicScan5_4 : ∀ s : Fin 28,
    prefixCheck 28 (by decide) periodicWord5
      (periodicCaps5 4) 4 s 28 0 0 = true := by
  decide +kernel

theorem periodicCertificate5 :
    WordCertificate 28 (by decide) periodicWord5 periodicCaps5 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan5_0
  · exact periodicScan5_1
  · exact periodicScan5_2
  · exact periodicScan5_3
  · exact periodicScan5_4

theorem schedulable_word5 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 5) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps5 r := by
    simpa only [periodicCaps5_eq] using hr
  exact ⟨periodic 28 (by decide) periodicWord5,
    validRates_periodic_of_wordCertificate (by decide) periodicWord5
      periodicCertificate5 hc⟩

-- Case 6: F0223; period 15.
def periodicArray6 : Array (Fin 5) := #[0, 0, 1, 0, 2, 0, 4, 0, 1, 0, 3, 0, 2, 0, 1]
def periodicWord6 (k : Fin 15) : Fin 5 :=
  periodicArray6[k.val]
def periodicCaps6 : Fin 5 → RateCap
  | 0 => { bound := (8/15 : ℚ), closed := true }
  | 1 => { bound := (2/11 : ℚ), closed := false }
  | 2 => { bound := (2/15 : ℚ), closed := true }
  | 3 => { bound := (1/15 : ℚ), closed := true }
  | 4 => { bound := (1/15 : ℚ), closed := true }

theorem periodicArray6_toList :
    periodicArray6.toList = words 6 := by rfl
theorem periodicCaps6_eq : periodicCaps6 = wordCaps 6 := by rfl

theorem periodicScan6_0 : ∀ s : Fin 15,
    prefixCheck 15 (by decide) periodicWord6
      (periodicCaps6 0) 0 s 15 0 0 = true := by
  decide +kernel

theorem periodicScan6_1 : ∀ s : Fin 15,
    prefixCheck 15 (by decide) periodicWord6
      (periodicCaps6 1) 1 s 15 0 0 = true := by
  decide +kernel

theorem periodicScan6_2 : ∀ s : Fin 15,
    prefixCheck 15 (by decide) periodicWord6
      (periodicCaps6 2) 2 s 15 0 0 = true := by
  decide +kernel

theorem periodicScan6_3 : ∀ s : Fin 15,
    prefixCheck 15 (by decide) periodicWord6
      (periodicCaps6 3) 3 s 15 0 0 = true := by
  decide +kernel

theorem periodicScan6_4 : ∀ s : Fin 15,
    prefixCheck 15 (by decide) periodicWord6
      (periodicCaps6 4) 4 s 15 0 0 = true := by
  decide +kernel

theorem periodicCertificate6 :
    WordCertificate 15 (by decide) periodicWord6 periodicCaps6 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan6_0
  · exact periodicScan6_1
  · exact periodicScan6_2
  · exact periodicScan6_3
  · exact periodicScan6_4

theorem schedulable_word6 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 6) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps6 r := by
    simpa only [periodicCaps6_eq] using hr
  exact ⟨periodic 15 (by decide) periodicWord6,
    validRates_periodic_of_wordCertificate (by decide) periodicWord6
      periodicCertificate6 hc⟩

-- Case 7: F0227; period 33.
def periodicArray7 : Array (Fin 5) := #[0, 0, 2, 0, 1, 0, 0, 2, 0, 1, 0, 3, 0, 2, 0, 1, 0, 0, 2, 0, 1, 0, 4, 0, 2, 0, 1, 0, 3, 0, 2, 0, 1]
def periodicWord7 (k : Fin 33) : Fin 5 :=
  periodicArray7[k.val]
def periodicCaps7 : Fin 5 → RateCap
  | 0 => { bound := (8/15 : ℚ), closed := false }
  | 1 => { bound := (2/11 : ℚ), closed := false }
  | 2 => { bound := (2/11 : ℚ), closed := false }
  | 3 => { bound := (2/33 : ℚ), closed := true }
  | 4 => { bound := (1/33 : ℚ), closed := true }

theorem periodicArray7_toList :
    periodicArray7.toList = words 7 := by rfl
theorem periodicCaps7_eq : periodicCaps7 = wordCaps 7 := by rfl

theorem periodicScan7_0 : ∀ s : Fin 33,
    prefixCheck 33 (by decide) periodicWord7
      (periodicCaps7 0) 0 s 33 0 0 = true := by
  decide +kernel

theorem periodicScan7_1 : ∀ s : Fin 33,
    prefixCheck 33 (by decide) periodicWord7
      (periodicCaps7 1) 1 s 33 0 0 = true := by
  decide +kernel

theorem periodicScan7_2 : ∀ s : Fin 33,
    prefixCheck 33 (by decide) periodicWord7
      (periodicCaps7 2) 2 s 33 0 0 = true := by
  decide +kernel

theorem periodicScan7_3 : ∀ s : Fin 33,
    prefixCheck 33 (by decide) periodicWord7
      (periodicCaps7 3) 3 s 33 0 0 = true := by
  decide +kernel

theorem periodicScan7_4 : ∀ s : Fin 33,
    prefixCheck 33 (by decide) periodicWord7
      (periodicCaps7 4) 4 s 33 0 0 = true := by
  decide +kernel

theorem periodicCertificate7 :
    WordCertificate 33 (by decide) periodicWord7 periodicCaps7 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan7_0
  · exact periodicScan7_1
  · exact periodicScan7_2
  · exact periodicScan7_3
  · exact periodicScan7_4

theorem schedulable_word7 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 7) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps7 r := by
    simpa only [periodicCaps7_eq] using hr
  exact ⟨periodic 33 (by decide) periodicWord7,
    validRates_periodic_of_wordCertificate (by decide) periodicWord7
      periodicCertificate7 hc⟩

-- Case 8: F0236; period 20.
def periodicArray8 : Array (Fin 5) := #[0, 0, 0, 1, 0, 3, 0, 2, 0, 1, 0, 4, 0, 1, 0, 3, 0, 2, 0, 1]
def periodicWord8 (k : Fin 20) : Fin 5 :=
  periodicArray8[k.val]
def periodicCaps8 : Fin 5 → RateCap
  | 0 => { bound := (9/17 : ℚ), closed := false }
  | 1 => { bound := (1/5 : ℚ), closed := false }
  | 2 => { bound := (1/10 : ℚ), closed := true }
  | 3 => { bound := (1/10 : ℚ), closed := true }
  | 4 => { bound := (1/20 : ℚ), closed := true }

theorem periodicArray8_toList :
    periodicArray8.toList = words 8 := by rfl
theorem periodicCaps8_eq : periodicCaps8 = wordCaps 8 := by rfl

theorem periodicScan8_0 : ∀ s : Fin 20,
    prefixCheck 20 (by decide) periodicWord8
      (periodicCaps8 0) 0 s 20 0 0 = true := by
  decide +kernel

theorem periodicScan8_1 : ∀ s : Fin 20,
    prefixCheck 20 (by decide) periodicWord8
      (periodicCaps8 1) 1 s 20 0 0 = true := by
  decide +kernel

theorem periodicScan8_2 : ∀ s : Fin 20,
    prefixCheck 20 (by decide) periodicWord8
      (periodicCaps8 2) 2 s 20 0 0 = true := by
  decide +kernel

theorem periodicScan8_3 : ∀ s : Fin 20,
    prefixCheck 20 (by decide) periodicWord8
      (periodicCaps8 3) 3 s 20 0 0 = true := by
  decide +kernel

theorem periodicScan8_4 : ∀ s : Fin 20,
    prefixCheck 20 (by decide) periodicWord8
      (periodicCaps8 4) 4 s 20 0 0 = true := by
  decide +kernel

theorem periodicCertificate8 :
    WordCertificate 20 (by decide) periodicWord8 periodicCaps8 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan8_0
  · exact periodicScan8_1
  · exact periodicScan8_2
  · exact periodicScan8_3
  · exact periodicScan8_4

theorem schedulable_word8 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 8) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps8 r := by
    simpa only [periodicCaps8_eq] using hr
  exact ⟨periodic 20 (by decide) periodicWord8,
    validRates_periodic_of_wordCertificate (by decide) periodicWord8
      periodicCertificate8 hc⟩

-- Case 9: F0240; period 19.
def periodicArray9 : Array (Fin 5) := #[0, 0, 2, 0, 3, 0, 1, 0, 2, 0, 4, 0, 1, 0, 3, 0, 2, 0, 1]
def periodicWord9 (k : Fin 19) : Fin 5 :=
  periodicArray9[k.val]
def periodicCaps9 : Fin 5 → RateCap
  | 0 => { bound := (10/19 : ℚ), closed := true }
  | 1 => { bound := (3/19 : ℚ), closed := true }
  | 2 => { bound := (1/7 : ℚ), closed := false }
  | 3 => { bound := (2/19 : ℚ), closed := true }
  | 4 => { bound := (1/19 : ℚ), closed := true }

theorem periodicArray9_toList :
    periodicArray9.toList = words 9 := by rfl
theorem periodicCaps9_eq : periodicCaps9 = wordCaps 9 := by rfl

theorem periodicScan9_0 : ∀ s : Fin 19,
    prefixCheck 19 (by decide) periodicWord9
      (periodicCaps9 0) 0 s 19 0 0 = true := by
  decide +kernel

theorem periodicScan9_1 : ∀ s : Fin 19,
    prefixCheck 19 (by decide) periodicWord9
      (periodicCaps9 1) 1 s 19 0 0 = true := by
  decide +kernel

theorem periodicScan9_2 : ∀ s : Fin 19,
    prefixCheck 19 (by decide) periodicWord9
      (periodicCaps9 2) 2 s 19 0 0 = true := by
  decide +kernel

theorem periodicScan9_3 : ∀ s : Fin 19,
    prefixCheck 19 (by decide) periodicWord9
      (periodicCaps9 3) 3 s 19 0 0 = true := by
  decide +kernel

theorem periodicScan9_4 : ∀ s : Fin 19,
    prefixCheck 19 (by decide) periodicWord9
      (periodicCaps9 4) 4 s 19 0 0 = true := by
  decide +kernel

theorem periodicCertificate9 :
    WordCertificate 19 (by decide) periodicWord9 periodicCaps9 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan9_0
  · exact periodicScan9_1
  · exact periodicScan9_2
  · exact periodicScan9_3
  · exact periodicScan9_4

theorem schedulable_word9 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 9) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps9 r := by
    simpa only [periodicCaps9_eq] using hr
  exact ⟨periodic 19 (by decide) periodicWord9,
    validRates_periodic_of_wordCertificate (by decide) periodicWord9
      periodicCertificate9 hc⟩

-- Case 10: F0266; period 42.
def periodicArray10 : Array (Fin 5) := #[0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1]
def periodicWord10 (k : Fin 42) : Fin 5 :=
  periodicArray10[k.val]
def periodicCaps10 : Fin 5 → RateCap
  | 0 => { bound := (13/25 : ℚ), closed := false }
  | 1 => { bound := (6/23 : ℚ), closed := false }
  | 2 => { bound := (1/11 : ℚ), closed := false }
  | 3 => { bound := (2/29 : ℚ), closed := false }
  | 4 => { bound := (1/42 : ℚ), closed := true }

theorem periodicArray10_toList :
    periodicArray10.toList = words 10 := by rfl
theorem periodicCaps10_eq : periodicCaps10 = wordCaps 10 := by rfl

theorem periodicScan10_0 : ∀ s : Fin 42,
    prefixCheck 42 (by decide) periodicWord10
      (periodicCaps10 0) 0 s 42 0 0 = true := by
  decide +kernel

theorem periodicScan10_1 : ∀ s : Fin 42,
    prefixCheck 42 (by decide) periodicWord10
      (periodicCaps10 1) 1 s 42 0 0 = true := by
  decide +kernel

theorem periodicScan10_2 : ∀ s : Fin 42,
    prefixCheck 42 (by decide) periodicWord10
      (periodicCaps10 2) 2 s 42 0 0 = true := by
  decide +kernel

theorem periodicScan10_3 : ∀ s : Fin 42,
    prefixCheck 42 (by decide) periodicWord10
      (periodicCaps10 3) 3 s 42 0 0 = true := by
  decide +kernel

theorem periodicScan10_4 : ∀ s : Fin 42,
    prefixCheck 42 (by decide) periodicWord10
      (periodicCaps10 4) 4 s 42 0 0 = true := by
  decide +kernel

theorem periodicCertificate10 :
    WordCertificate 42 (by decide) periodicWord10 periodicCaps10 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan10_0
  · exact periodicScan10_1
  · exact periodicScan10_2
  · exact periodicScan10_3
  · exact periodicScan10_4

theorem schedulable_word10 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 10) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps10 r := by
    simpa only [periodicCaps10_eq] using hr
  exact ⟨periodic 42 (by decide) periodicWord10,
    validRates_periodic_of_wordCertificate (by decide) periodicWord10
      periodicCertificate10 hc⟩

-- Case 11: F0330; period 18.
def periodicArray11 : Array (Fin 5) := #[0, 1, 0, 2, 0, 3, 0, 1, 0, 2, 0, 4, 0, 1, 0, 3, 0, 2]
def periodicWord11 (k : Fin 18) : Fin 5 :=
  periodicArray11[k.val]
def periodicCaps11 : Fin 5 → RateCap
  | 0 => { bound := (1/2 : ℚ), closed := true }
  | 1 => { bound := (1/6 : ℚ), closed := true }
  | 2 => { bound := (1/7 : ℚ), closed := false }
  | 3 => { bound := (1/9 : ℚ), closed := false }
  | 4 => { bound := (1/18 : ℚ), closed := true }

theorem periodicArray11_toList :
    periodicArray11.toList = words 11 := by rfl
theorem periodicCaps11_eq : periodicCaps11 = wordCaps 11 := by rfl

theorem periodicScan11_0 : ∀ s : Fin 18,
    prefixCheck 18 (by decide) periodicWord11
      (periodicCaps11 0) 0 s 18 0 0 = true := by
  decide +kernel

theorem periodicScan11_1 : ∀ s : Fin 18,
    prefixCheck 18 (by decide) periodicWord11
      (periodicCaps11 1) 1 s 18 0 0 = true := by
  decide +kernel

theorem periodicScan11_2 : ∀ s : Fin 18,
    prefixCheck 18 (by decide) periodicWord11
      (periodicCaps11 2) 2 s 18 0 0 = true := by
  decide +kernel

theorem periodicScan11_3 : ∀ s : Fin 18,
    prefixCheck 18 (by decide) periodicWord11
      (periodicCaps11 3) 3 s 18 0 0 = true := by
  decide +kernel

theorem periodicScan11_4 : ∀ s : Fin 18,
    prefixCheck 18 (by decide) periodicWord11
      (periodicCaps11 4) 4 s 18 0 0 = true := by
  decide +kernel

theorem periodicCertificate11 :
    WordCertificate 18 (by decide) periodicWord11 periodicCaps11 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan11_0
  · exact periodicScan11_1
  · exact periodicScan11_2
  · exact periodicScan11_3
  · exact periodicScan11_4

theorem schedulable_word11 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 11) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps11 r := by
    simpa only [periodicCaps11_eq] using hr
  exact ⟨periodic 18 (by decide) periodicWord11,
    validRates_periodic_of_wordCertificate (by decide) periodicWord11
      periodicCertificate11 hc⟩

-- Case 12: F0346; period 20.
def periodicArray12 : Array (Fin 5) := #[0, 0, 1, 0, 2, 0, 1, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1, 0, 3, 1]
def periodicWord12 (k : Fin 20) : Fin 5 :=
  periodicArray12[k.val]
def periodicCaps12 : Fin 5 → RateCap
  | 0 => { bound := (1/2 : ℚ), closed := false }
  | 1 => { bound := (2/7 : ℚ), closed := false }
  | 2 => { bound := (1/10 : ℚ), closed := true }
  | 3 => { bound := (1/20 : ℚ), closed := true }
  | 4 => { bound := (1/20 : ℚ), closed := true }

theorem periodicArray12_toList :
    periodicArray12.toList = words 12 := by rfl
theorem periodicCaps12_eq : periodicCaps12 = wordCaps 12 := by rfl

theorem periodicScan12_0 : ∀ s : Fin 20,
    prefixCheck 20 (by decide) periodicWord12
      (periodicCaps12 0) 0 s 20 0 0 = true := by
  decide +kernel

theorem periodicScan12_1 : ∀ s : Fin 20,
    prefixCheck 20 (by decide) periodicWord12
      (periodicCaps12 1) 1 s 20 0 0 = true := by
  decide +kernel

theorem periodicScan12_2 : ∀ s : Fin 20,
    prefixCheck 20 (by decide) periodicWord12
      (periodicCaps12 2) 2 s 20 0 0 = true := by
  decide +kernel

theorem periodicScan12_3 : ∀ s : Fin 20,
    prefixCheck 20 (by decide) periodicWord12
      (periodicCaps12 3) 3 s 20 0 0 = true := by
  decide +kernel

theorem periodicScan12_4 : ∀ s : Fin 20,
    prefixCheck 20 (by decide) periodicWord12
      (periodicCaps12 4) 4 s 20 0 0 = true := by
  decide +kernel

theorem periodicCertificate12 :
    WordCertificate 20 (by decide) periodicWord12 periodicCaps12 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan12_0
  · exact periodicScan12_1
  · exact periodicScan12_2
  · exact periodicScan12_3
  · exact periodicScan12_4

theorem schedulable_word12 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 12) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps12 r := by
    simpa only [periodicCaps12_eq] using hr
  exact ⟨periodic 20 (by decide) periodicWord12,
    validRates_periodic_of_wordCertificate (by decide) periodicWord12
      periodicCertificate12 hc⟩

-- Case 13: F0350; period 18.
def periodicArray13 : Array (Fin 5) := #[0, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 1]
def periodicWord13 (k : Fin 18) : Fin 5 :=
  periodicArray13[k.val]
def periodicCaps13 : Fin 5 → RateCap
  | 0 => { bound := (1/2 : ℚ), closed := false }
  | 1 => { bound := (3/11 : ℚ), closed := false }
  | 2 => { bound := (1/9 : ℚ), closed := false }
  | 3 => { bound := (1/18 : ℚ), closed := true }
  | 4 => { bound := (1/18 : ℚ), closed := true }

theorem periodicArray13_toList :
    periodicArray13.toList = words 13 := by rfl
theorem periodicCaps13_eq : periodicCaps13 = wordCaps 13 := by rfl

theorem periodicScan13_0 : ∀ s : Fin 18,
    prefixCheck 18 (by decide) periodicWord13
      (periodicCaps13 0) 0 s 18 0 0 = true := by
  decide +kernel

theorem periodicScan13_1 : ∀ s : Fin 18,
    prefixCheck 18 (by decide) periodicWord13
      (periodicCaps13 1) 1 s 18 0 0 = true := by
  decide +kernel

theorem periodicScan13_2 : ∀ s : Fin 18,
    prefixCheck 18 (by decide) periodicWord13
      (periodicCaps13 2) 2 s 18 0 0 = true := by
  decide +kernel

theorem periodicScan13_3 : ∀ s : Fin 18,
    prefixCheck 18 (by decide) periodicWord13
      (periodicCaps13 3) 3 s 18 0 0 = true := by
  decide +kernel

theorem periodicScan13_4 : ∀ s : Fin 18,
    prefixCheck 18 (by decide) periodicWord13
      (periodicCaps13 4) 4 s 18 0 0 = true := by
  decide +kernel

theorem periodicCertificate13 :
    WordCertificate 18 (by decide) periodicWord13 periodicCaps13 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan13_0
  · exact periodicScan13_1
  · exact periodicScan13_2
  · exact periodicScan13_3
  · exact periodicScan13_4

theorem schedulable_word13 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 13) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps13 r := by
    simpa only [periodicCaps13_eq] using hr
  exact ⟨periodic 18 (by decide) periodicWord13,
    validRates_periodic_of_wordCertificate (by decide) periodicWord13
      periodicCertificate13 hc⟩

-- Case 14: F0392; period 24.
def periodicArray14 : Array (Fin 5) := #[0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 2, 1, 0, 0, 4, 0, 2, 1, 0, 0, 3, 0, 1, 2]
def periodicWord14 (k : Fin 24) : Fin 5 :=
  periodicArray14[k.val]
def periodicCaps14 : Fin 5 → RateCap
  | 0 => { bound := (1/2 : ℚ), closed := false }
  | 1 => { bound := (1/5 : ℚ), closed := false }
  | 2 => { bound := (1/6 : ℚ), closed := false }
  | 3 => { bound := (1/12 : ℚ), closed := true }
  | 4 => { bound := (1/24 : ℚ), closed := true }

theorem periodicArray14_toList :
    periodicArray14.toList = words 14 := by rfl
theorem periodicCaps14_eq : periodicCaps14 = wordCaps 14 := by rfl

theorem periodicScan14_0 : ∀ s : Fin 24,
    prefixCheck 24 (by decide) periodicWord14
      (periodicCaps14 0) 0 s 24 0 0 = true := by
  decide +kernel

theorem periodicScan14_1 : ∀ s : Fin 24,
    prefixCheck 24 (by decide) periodicWord14
      (periodicCaps14 1) 1 s 24 0 0 = true := by
  decide +kernel

theorem periodicScan14_2 : ∀ s : Fin 24,
    prefixCheck 24 (by decide) periodicWord14
      (periodicCaps14 2) 2 s 24 0 0 = true := by
  decide +kernel

theorem periodicScan14_3 : ∀ s : Fin 24,
    prefixCheck 24 (by decide) periodicWord14
      (periodicCaps14 3) 3 s 24 0 0 = true := by
  decide +kernel

theorem periodicScan14_4 : ∀ s : Fin 24,
    prefixCheck 24 (by decide) periodicWord14
      (periodicCaps14 4) 4 s 24 0 0 = true := by
  decide +kernel

theorem periodicCertificate14 :
    WordCertificate 24 (by decide) periodicWord14 periodicCaps14 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan14_0
  · exact periodicScan14_1
  · exact periodicScan14_2
  · exact periodicScan14_3
  · exact periodicScan14_4

theorem schedulable_word14 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 14) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps14 r := by
    simpa only [periodicCaps14_eq] using hr
  exact ⟨periodic 24 (by decide) periodicWord14,
    validRates_periodic_of_wordCertificate (by decide) periodicWord14
      periodicCertificate14 hc⟩

-- Case 15: F0474; period 49.
def periodicArray15 : Array (Fin 5) := #[0, 0, 1, 0, 1, 0, 2, 0, 1, 0, 3, 1, 0, 0, 1, 0, 2, 0, 1, 0, 4, 1, 0, 0, 1, 0, 2, 0, 1, 3, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 2, 1]
def periodicWord15 (k : Fin 49) : Fin 5 :=
  periodicArray15[k.val]
def periodicCaps15 : Fin 5 → RateCap
  | 0 => { bound := (10/21 : ℚ), closed := false }
  | 1 => { bound := (7/23 : ℚ), closed := false }
  | 2 => { bound := (1/11 : ℚ), closed := false }
  | 3 => { bound := (1/18 : ℚ), closed := false }
  | 4 => { bound := (1/49 : ℚ), closed := true }

theorem periodicArray15_toList :
    periodicArray15.toList = words 15 := by rfl
theorem periodicCaps15_eq : periodicCaps15 = wordCaps 15 := by rfl

theorem periodicScan15_0 : ∀ s : Fin 49,
    prefixCheck 49 (by decide) periodicWord15
      (periodicCaps15 0) 0 s 49 0 0 = true := by
  decide +kernel

theorem periodicScan15_1 : ∀ s : Fin 49,
    prefixCheck 49 (by decide) periodicWord15
      (periodicCaps15 1) 1 s 49 0 0 = true := by
  decide +kernel

theorem periodicScan15_2 : ∀ s : Fin 49,
    prefixCheck 49 (by decide) periodicWord15
      (periodicCaps15 2) 2 s 49 0 0 = true := by
  decide +kernel

theorem periodicScan15_3 : ∀ s : Fin 49,
    prefixCheck 49 (by decide) periodicWord15
      (periodicCaps15 3) 3 s 49 0 0 = true := by
  decide +kernel

theorem periodicScan15_4 : ∀ s : Fin 49,
    prefixCheck 49 (by decide) periodicWord15
      (periodicCaps15 4) 4 s 49 0 0 = true := by
  decide +kernel

theorem periodicCertificate15 :
    WordCertificate 49 (by decide) periodicWord15 periodicCaps15 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan15_0
  · exact periodicScan15_1
  · exact periodicScan15_2
  · exact periodicScan15_3
  · exact periodicScan15_4

theorem schedulable_word15 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 15) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps15 r := by
    simpa only [periodicCaps15_eq] using hr
  exact ⟨periodic 49 (by decide) periodicWord15,
    validRates_periodic_of_wordCertificate (by decide) periodicWord15
      periodicCertificate15 hc⟩

-- Case 16: F0500; period 17.
def periodicArray16 : Array (Fin 5) := #[0, 1, 0, 2, 0, 3, 0, 1, 0, 2, 0, 4, 0, 1, 3, 0, 2]
def periodicWord16 (k : Fin 17) : Fin 5 :=
  periodicArray16[k.val]
def periodicCaps16 : Fin 5 → RateCap
  | 0 => { bound := (8/17 : ℚ), closed := true }
  | 1 => { bound := (3/17 : ℚ), closed := true }
  | 2 => { bound := (1/6 : ℚ), closed := false }
  | 3 => { bound := (2/17 : ℚ), closed := true }
  | 4 => { bound := (1/17 : ℚ), closed := true }

theorem periodicArray16_toList :
    periodicArray16.toList = words 16 := by rfl
theorem periodicCaps16_eq : periodicCaps16 = wordCaps 16 := by rfl

theorem periodicScan16_0 : ∀ s : Fin 17,
    prefixCheck 17 (by decide) periodicWord16
      (periodicCaps16 0) 0 s 17 0 0 = true := by
  decide +kernel

theorem periodicScan16_1 : ∀ s : Fin 17,
    prefixCheck 17 (by decide) periodicWord16
      (periodicCaps16 1) 1 s 17 0 0 = true := by
  decide +kernel

theorem periodicScan16_2 : ∀ s : Fin 17,
    prefixCheck 17 (by decide) periodicWord16
      (periodicCaps16 2) 2 s 17 0 0 = true := by
  decide +kernel

theorem periodicScan16_3 : ∀ s : Fin 17,
    prefixCheck 17 (by decide) periodicWord16
      (periodicCaps16 3) 3 s 17 0 0 = true := by
  decide +kernel

theorem periodicScan16_4 : ∀ s : Fin 17,
    prefixCheck 17 (by decide) periodicWord16
      (periodicCaps16 4) 4 s 17 0 0 = true := by
  decide +kernel

theorem periodicCertificate16 :
    WordCertificate 17 (by decide) periodicWord16 periodicCaps16 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan16_0
  · exact periodicScan16_1
  · exact periodicScan16_2
  · exact periodicScan16_3
  · exact periodicScan16_4

theorem schedulable_word16 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 16) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps16 r := by
    simpa only [periodicCaps16_eq] using hr
  exact ⟨periodic 17 (by decide) periodicWord16,
    validRates_periodic_of_wordCertificate (by decide) periodicWord16
      periodicCertificate16 hc⟩

-- Case 17: F0541; period 13.
def periodicArray17 : Array (Fin 5) := #[0, 1, 0, 3, 0, 2, 0, 1, 4, 0, 3, 0, 2]
def periodicWord17 (k : Fin 13) : Fin 5 :=
  periodicArray17[k.val]
def periodicCaps17 : Fin 5 → RateCap
  | 0 => { bound := (6/13 : ℚ), closed := true }
  | 1 => { bound := (2/13 : ℚ), closed := true }
  | 2 => { bound := (2/13 : ℚ), closed := true }
  | 3 => { bound := (2/13 : ℚ), closed := true }
  | 4 => { bound := (1/13 : ℚ), closed := true }

theorem periodicArray17_toList :
    periodicArray17.toList = words 17 := by rfl
theorem periodicCaps17_eq : periodicCaps17 = wordCaps 17 := by rfl

theorem periodicScan17_0 : ∀ s : Fin 13,
    prefixCheck 13 (by decide) periodicWord17
      (periodicCaps17 0) 0 s 13 0 0 = true := by
  decide +kernel

theorem periodicScan17_1 : ∀ s : Fin 13,
    prefixCheck 13 (by decide) periodicWord17
      (periodicCaps17 1) 1 s 13 0 0 = true := by
  decide +kernel

theorem periodicScan17_2 : ∀ s : Fin 13,
    prefixCheck 13 (by decide) periodicWord17
      (periodicCaps17 2) 2 s 13 0 0 = true := by
  decide +kernel

theorem periodicScan17_3 : ∀ s : Fin 13,
    prefixCheck 13 (by decide) periodicWord17
      (periodicCaps17 3) 3 s 13 0 0 = true := by
  decide +kernel

theorem periodicScan17_4 : ∀ s : Fin 13,
    prefixCheck 13 (by decide) periodicWord17
      (periodicCaps17 4) 4 s 13 0 0 = true := by
  decide +kernel

theorem periodicCertificate17 :
    WordCertificate 13 (by decide) periodicWord17 periodicCaps17 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan17_0
  · exact periodicScan17_1
  · exact periodicScan17_2
  · exact periodicScan17_3
  · exact periodicScan17_4

theorem schedulable_word17 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 17) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps17 r := by
    simpa only [periodicCaps17_eq] using hr
  exact ⟨periodic 13 (by decide) periodicWord17,
    validRates_periodic_of_wordCertificate (by decide) periodicWord17
      periodicCertificate17 hc⟩

-- Case 18: F0605; period 35.
def periodicArray18 : Array (Fin 5) := #[0, 0, 1, 0, 3, 1, 0, 2, 0, 1, 0, 1, 0, 4, 1, 0, 2, 0, 1, 0, 1, 0, 3, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 1]
def periodicWord18 (k : Fin 35) : Fin 5 :=
  periodicArray18[k.val]
def periodicCaps18 : Fin 5 → RateCap
  | 0 => { bound := (9/20 : ℚ), closed := false }
  | 1 => { bound := (1/3 : ℚ), closed := false }
  | 2 => { bound := (4/35 : ℚ), closed := true }
  | 3 => { bound := (2/35 : ℚ), closed := true }
  | 4 => { bound := (1/35 : ℚ), closed := true }

theorem periodicArray18_toList :
    periodicArray18.toList = words 18 := by rfl
theorem periodicCaps18_eq : periodicCaps18 = wordCaps 18 := by rfl

theorem periodicScan18_0 : ∀ s : Fin 35,
    prefixCheck 35 (by decide) periodicWord18
      (periodicCaps18 0) 0 s 35 0 0 = true := by
  decide +kernel

theorem periodicScan18_1 : ∀ s : Fin 35,
    prefixCheck 35 (by decide) periodicWord18
      (periodicCaps18 1) 1 s 35 0 0 = true := by
  decide +kernel

theorem periodicScan18_2 : ∀ s : Fin 35,
    prefixCheck 35 (by decide) periodicWord18
      (periodicCaps18 2) 2 s 35 0 0 = true := by
  decide +kernel

theorem periodicScan18_3 : ∀ s : Fin 35,
    prefixCheck 35 (by decide) periodicWord18
      (periodicCaps18 3) 3 s 35 0 0 = true := by
  decide +kernel

theorem periodicScan18_4 : ∀ s : Fin 35,
    prefixCheck 35 (by decide) periodicWord18
      (periodicCaps18 4) 4 s 35 0 0 = true := by
  decide +kernel

theorem periodicCertificate18 :
    WordCertificate 35 (by decide) periodicWord18 periodicCaps18 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan18_0
  · exact periodicScan18_1
  · exact periodicScan18_2
  · exact periodicScan18_3
  · exact periodicScan18_4

theorem schedulable_word18 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 18) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps18 r := by
    simpa only [periodicCaps18_eq] using hr
  exact ⟨periodic 35 (by decide) periodicWord18,
    validRates_periodic_of_wordCertificate (by decide) periodicWord18
      periodicCertificate18 hc⟩

-- Case 19: F0615; period 30.
def periodicArray19 : Array (Fin 5) := #[0, 0, 1, 0, 1, 0, 3, 1, 0, 2, 0, 1, 0, 1, 0, 4, 1, 0, 2, 0, 1, 0, 3, 1, 0, 0, 1, 0, 2, 1]
def periodicWord19 (k : Fin 30) : Fin 5 :=
  periodicArray19[k.val]
def periodicCaps19 : Fin 5 → RateCap
  | 0 => { bound := (4/9 : ℚ), closed := false }
  | 1 => { bound := (1/3 : ℚ), closed := false }
  | 2 => { bound := (1/10 : ℚ), closed := false }
  | 3 => { bound := (1/15 : ℚ), closed := false }
  | 4 => { bound := (1/30 : ℚ), closed := true }

theorem periodicArray19_toList :
    periodicArray19.toList = words 19 := by rfl
theorem periodicCaps19_eq : periodicCaps19 = wordCaps 19 := by rfl

theorem periodicScan19_0 : ∀ s : Fin 30,
    prefixCheck 30 (by decide) periodicWord19
      (periodicCaps19 0) 0 s 30 0 0 = true := by
  decide +kernel

theorem periodicScan19_1 : ∀ s : Fin 30,
    prefixCheck 30 (by decide) periodicWord19
      (periodicCaps19 1) 1 s 30 0 0 = true := by
  decide +kernel

theorem periodicScan19_2 : ∀ s : Fin 30,
    prefixCheck 30 (by decide) periodicWord19
      (periodicCaps19 2) 2 s 30 0 0 = true := by
  decide +kernel

theorem periodicScan19_3 : ∀ s : Fin 30,
    prefixCheck 30 (by decide) periodicWord19
      (periodicCaps19 3) 3 s 30 0 0 = true := by
  decide +kernel

theorem periodicScan19_4 : ∀ s : Fin 30,
    prefixCheck 30 (by decide) periodicWord19
      (periodicCaps19 4) 4 s 30 0 0 = true := by
  decide +kernel

theorem periodicCertificate19 :
    WordCertificate 30 (by decide) periodicWord19 periodicCaps19 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan19_0
  · exact periodicScan19_1
  · exact periodicScan19_2
  · exact periodicScan19_3
  · exact periodicScan19_4

theorem schedulable_word19 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 19) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps19 r := by
    simpa only [periodicCaps19_eq] using hr
  exact ⟨periodic 30 (by decide) periodicWord19,
    validRates_periodic_of_wordCertificate (by decide) periodicWord19
      periodicCertificate19 hc⟩

-- Case 20: F0630; period 18.
def periodicArray20 : Array (Fin 5) := #[0, 1, 0, 2, 0, 1, 4, 0, 1, 0, 3, 0, 1, 2, 0, 1, 0, 3]
def periodicWord20 (k : Fin 18) : Fin 5 :=
  periodicArray20[k.val]
def periodicCaps20 : Fin 5 → RateCap
  | 0 => { bound := (4/9 : ℚ), closed := false }
  | 1 => { bound := (5/18 : ℚ), closed := true }
  | 2 => { bound := (1/9 : ℚ), closed := false }
  | 3 => { bound := (1/10 : ℚ), closed := false }
  | 4 => { bound := (1/18 : ℚ), closed := true }

theorem periodicArray20_toList :
    periodicArray20.toList = words 20 := by rfl
theorem periodicCaps20_eq : periodicCaps20 = wordCaps 20 := by rfl

theorem periodicScan20_0 : ∀ s : Fin 18,
    prefixCheck 18 (by decide) periodicWord20
      (periodicCaps20 0) 0 s 18 0 0 = true := by
  decide +kernel

theorem periodicScan20_1 : ∀ s : Fin 18,
    prefixCheck 18 (by decide) periodicWord20
      (periodicCaps20 1) 1 s 18 0 0 = true := by
  decide +kernel

theorem periodicScan20_2 : ∀ s : Fin 18,
    prefixCheck 18 (by decide) periodicWord20
      (periodicCaps20 2) 2 s 18 0 0 = true := by
  decide +kernel

theorem periodicScan20_3 : ∀ s : Fin 18,
    prefixCheck 18 (by decide) periodicWord20
      (periodicCaps20 3) 3 s 18 0 0 = true := by
  decide +kernel

theorem periodicScan20_4 : ∀ s : Fin 18,
    prefixCheck 18 (by decide) periodicWord20
      (periodicCaps20 4) 4 s 18 0 0 = true := by
  decide +kernel

theorem periodicCertificate20 :
    WordCertificate 18 (by decide) periodicWord20 periodicCaps20 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan20_0
  · exact periodicScan20_1
  · exact periodicScan20_2
  · exact periodicScan20_3
  · exact periodicScan20_4

theorem schedulable_word20 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 20) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps20 r := by
    simpa only [periodicCaps20_eq] using hr
  exact ⟨periodic 18 (by decide) periodicWord20,
    validRates_periodic_of_wordCertificate (by decide) periodicWord20
      periodicCertificate20 hc⟩

-- Case 21: F0648; period 18.
def periodicArray21 : Array (Fin 5) := #[0, 1, 0, 2, 0, 1, 0, 3, 0, 2, 1, 0, 4, 0, 1, 0, 2, 3]
def periodicWord21 (k : Fin 18) : Fin 5 :=
  periodicArray21[k.val]
def periodicCaps21 : Fin 5 → RateCap
  | 0 => { bound := (4/9 : ℚ), closed := false }
  | 1 => { bound := (2/9 : ℚ), closed := true }
  | 2 => { bound := (1/6 : ℚ), closed := false }
  | 3 => { bound := (1/9 : ℚ), closed := false }
  | 4 => { bound := (1/18 : ℚ), closed := true }

theorem periodicArray21_toList :
    periodicArray21.toList = words 21 := by rfl
theorem periodicCaps21_eq : periodicCaps21 = wordCaps 21 := by rfl

theorem periodicScan21_0 : ∀ s : Fin 18,
    prefixCheck 18 (by decide) periodicWord21
      (periodicCaps21 0) 0 s 18 0 0 = true := by
  decide +kernel

theorem periodicScan21_1 : ∀ s : Fin 18,
    prefixCheck 18 (by decide) periodicWord21
      (periodicCaps21 1) 1 s 18 0 0 = true := by
  decide +kernel

theorem periodicScan21_2 : ∀ s : Fin 18,
    prefixCheck 18 (by decide) periodicWord21
      (periodicCaps21 2) 2 s 18 0 0 = true := by
  decide +kernel

theorem periodicScan21_3 : ∀ s : Fin 18,
    prefixCheck 18 (by decide) periodicWord21
      (periodicCaps21 3) 3 s 18 0 0 = true := by
  decide +kernel

theorem periodicScan21_4 : ∀ s : Fin 18,
    prefixCheck 18 (by decide) periodicWord21
      (periodicCaps21 4) 4 s 18 0 0 = true := by
  decide +kernel

theorem periodicCertificate21 :
    WordCertificate 18 (by decide) periodicWord21 periodicCaps21 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan21_0
  · exact periodicScan21_1
  · exact periodicScan21_2
  · exact periodicScan21_3
  · exact periodicScan21_4

theorem schedulable_word21 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 21) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps21 r := by
    simpa only [periodicCaps21_eq] using hr
  exact ⟨periodic 18 (by decide) periodicWord21,
    validRates_periodic_of_wordCertificate (by decide) periodicWord21
      periodicCertificate21 hc⟩

-- Case 22: F0700; period 30.
def periodicArray22 : Array (Fin 5) := #[0, 1, 0, 2, 0, 3, 1, 0, 4, 0, 2, 0, 1, 3, 0, 2, 0, 1, 0, 3, 0, 1, 2, 0, 3, 0, 1, 0, 2, 3]
def periodicWord22 (k : Fin 30) : Fin 5 :=
  periodicArray22[k.val]
def periodicCaps22 : Fin 5 → RateCap
  | 0 => { bound := (13/30 : ℚ), closed := true }
  | 1 => { bound := (1/5 : ℚ), closed := false }
  | 2 => { bound := (1/6 : ℚ), closed := false }
  | 3 => { bound := (1/7 : ℚ), closed := false }
  | 4 => { bound := (1/30 : ℚ), closed := true }

theorem periodicArray22_toList :
    periodicArray22.toList = words 22 := by rfl
theorem periodicCaps22_eq : periodicCaps22 = wordCaps 22 := by rfl

theorem periodicScan22_0 : ∀ s : Fin 30,
    prefixCheck 30 (by decide) periodicWord22
      (periodicCaps22 0) 0 s 30 0 0 = true := by
  decide +kernel

theorem periodicScan22_1 : ∀ s : Fin 30,
    prefixCheck 30 (by decide) periodicWord22
      (periodicCaps22 1) 1 s 30 0 0 = true := by
  decide +kernel

theorem periodicScan22_2 : ∀ s : Fin 30,
    prefixCheck 30 (by decide) periodicWord22
      (periodicCaps22 2) 2 s 30 0 0 = true := by
  decide +kernel

theorem periodicScan22_3 : ∀ s : Fin 30,
    prefixCheck 30 (by decide) periodicWord22
      (periodicCaps22 3) 3 s 30 0 0 = true := by
  decide +kernel

theorem periodicScan22_4 : ∀ s : Fin 30,
    prefixCheck 30 (by decide) periodicWord22
      (periodicCaps22 4) 4 s 30 0 0 = true := by
  decide +kernel

theorem periodicCertificate22 :
    WordCertificate 30 (by decide) periodicWord22 periodicCaps22 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan22_0
  · exact periodicScan22_1
  · exact periodicScan22_2
  · exact periodicScan22_3
  · exact periodicScan22_4

theorem schedulable_word22 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 22) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps22 r := by
    simpa only [periodicCaps22_eq] using hr
  exact ⟨periodic 30 (by decide) periodicWord22,
    validRates_periodic_of_wordCertificate (by decide) periodicWord22
      periodicCertificate22 hc⟩

-- Case 23: F0712; period 42.
def periodicArray23 : Array (Fin 5) := #[0, 1, 0, 1, 0, 2, 1, 0, 1, 0, 1, 0, 2, 1, 0, 1, 0, 3, 1, 0, 2, 0, 1, 0, 1, 0, 2, 1, 0, 4, 0, 1, 0, 2, 1, 0, 1, 0, 3, 1, 0, 2]
def periodicWord23 (k : Fin 42) : Fin 5 :=
  periodicArray23[k.val]
def periodicCaps23 : Fin 5 → RateCap
  | 0 => { bound := (3/7 : ℚ), closed := false }
  | 1 => { bound := (1/3 : ℚ), closed := false }
  | 2 => { bound := (1/7 : ℚ), closed := false }
  | 3 => { bound := (1/21 : ℚ), closed := true }
  | 4 => { bound := (1/42 : ℚ), closed := true }

theorem periodicArray23_toList :
    periodicArray23.toList = words 23 := by rfl
theorem periodicCaps23_eq : periodicCaps23 = wordCaps 23 := by rfl

theorem periodicScan23_0 : ∀ s : Fin 42,
    prefixCheck 42 (by decide) periodicWord23
      (periodicCaps23 0) 0 s 42 0 0 = true := by
  decide +kernel

theorem periodicScan23_1 : ∀ s : Fin 42,
    prefixCheck 42 (by decide) periodicWord23
      (periodicCaps23 1) 1 s 42 0 0 = true := by
  decide +kernel

theorem periodicScan23_2 : ∀ s : Fin 42,
    prefixCheck 42 (by decide) periodicWord23
      (periodicCaps23 2) 2 s 42 0 0 = true := by
  decide +kernel

theorem periodicScan23_3 : ∀ s : Fin 42,
    prefixCheck 42 (by decide) periodicWord23
      (periodicCaps23 3) 3 s 42 0 0 = true := by
  decide +kernel

theorem periodicScan23_4 : ∀ s : Fin 42,
    prefixCheck 42 (by decide) periodicWord23
      (periodicCaps23 4) 4 s 42 0 0 = true := by
  decide +kernel

theorem periodicCertificate23 :
    WordCertificate 42 (by decide) periodicWord23 periodicCaps23 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan23_0
  · exact periodicScan23_1
  · exact periodicScan23_2
  · exact periodicScan23_3
  · exact periodicScan23_4

theorem schedulable_word23 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 23) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps23 r := by
    simpa only [periodicCaps23_eq] using hr
  exact ⟨periodic 42 (by decide) periodicWord23,
    validRates_periodic_of_wordCertificate (by decide) periodicWord23
      periodicCertificate23 hc⟩

-- Case 24: F0730; period 34.
def periodicArray24 : Array (Fin 5) := #[0, 1, 0, 2, 0, 1, 0, 3, 0, 2, 1, 0, 1, 0, 2, 0, 1, 0, 3, 0, 2, 1, 0, 4, 0, 1, 2, 0, 1, 0, 3, 0, 2, 1]
def periodicWord24 (k : Fin 34) : Fin 5 :=
  periodicArray24[k.val]
def periodicCaps24 : Fin 5 → RateCap
  | 0 => { bound := (3/7 : ℚ), closed := false }
  | 1 => { bound := (1/4 : ℚ), closed := false }
  | 2 => { bound := (3/17 : ℚ), closed := false }
  | 3 => { bound := (3/34 : ℚ), closed := true }
  | 4 => { bound := (1/34 : ℚ), closed := true }

theorem periodicArray24_toList :
    periodicArray24.toList = words 24 := by rfl
theorem periodicCaps24_eq : periodicCaps24 = wordCaps 24 := by rfl

theorem periodicScan24_0 : ∀ s : Fin 34,
    prefixCheck 34 (by decide) periodicWord24
      (periodicCaps24 0) 0 s 34 0 0 = true := by
  decide +kernel

theorem periodicScan24_1 : ∀ s : Fin 34,
    prefixCheck 34 (by decide) periodicWord24
      (periodicCaps24 1) 1 s 34 0 0 = true := by
  decide +kernel

theorem periodicScan24_2 : ∀ s : Fin 34,
    prefixCheck 34 (by decide) periodicWord24
      (periodicCaps24 2) 2 s 34 0 0 = true := by
  decide +kernel

theorem periodicScan24_3 : ∀ s : Fin 34,
    prefixCheck 34 (by decide) periodicWord24
      (periodicCaps24 3) 3 s 34 0 0 = true := by
  decide +kernel

theorem periodicScan24_4 : ∀ s : Fin 34,
    prefixCheck 34 (by decide) periodicWord24
      (periodicCaps24 4) 4 s 34 0 0 = true := by
  decide +kernel

theorem periodicCertificate24 :
    WordCertificate 34 (by decide) periodicWord24 periodicCaps24 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan24_0
  · exact periodicScan24_1
  · exact periodicScan24_2
  · exact periodicScan24_3
  · exact periodicScan24_4

theorem schedulable_word24 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 24) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps24 r := by
    simpa only [periodicCaps24_eq] using hr
  exact ⟨periodic 34 (by decide) periodicWord24,
    validRates_periodic_of_wordCertificate (by decide) periodicWord24
      periodicCertificate24 hc⟩

-- Case 25: F0812; period 24.
def periodicArray25 : Array (Fin 5) := #[0, 1, 0, 3, 1, 0, 2, 0, 1, 0, 3, 1, 0, 2, 0, 1, 0, 4, 1, 0, 3, 0, 1, 2]
def periodicWord25 (k : Fin 24) : Fin 5 :=
  periodicArray25[k.val]
def periodicCaps25 : Fin 5 → RateCap
  | 0 => { bound := (5/12 : ℚ), closed := false }
  | 1 => { bound := (7/24 : ℚ), closed := true }
  | 2 => { bound := (1/9 : ℚ), closed := false }
  | 3 => { bound := (1/9 : ℚ), closed := false }
  | 4 => { bound := (1/24 : ℚ), closed := true }

theorem periodicArray25_toList :
    periodicArray25.toList = words 25 := by rfl
theorem periodicCaps25_eq : periodicCaps25 = wordCaps 25 := by rfl

theorem periodicScan25_0 : ∀ s : Fin 24,
    prefixCheck 24 (by decide) periodicWord25
      (periodicCaps25 0) 0 s 24 0 0 = true := by
  decide +kernel

theorem periodicScan25_1 : ∀ s : Fin 24,
    prefixCheck 24 (by decide) periodicWord25
      (periodicCaps25 1) 1 s 24 0 0 = true := by
  decide +kernel

theorem periodicScan25_2 : ∀ s : Fin 24,
    prefixCheck 24 (by decide) periodicWord25
      (periodicCaps25 2) 2 s 24 0 0 = true := by
  decide +kernel

theorem periodicScan25_3 : ∀ s : Fin 24,
    prefixCheck 24 (by decide) periodicWord25
      (periodicCaps25 3) 3 s 24 0 0 = true := by
  decide +kernel

theorem periodicScan25_4 : ∀ s : Fin 24,
    prefixCheck 24 (by decide) periodicWord25
      (periodicCaps25 4) 4 s 24 0 0 = true := by
  decide +kernel

theorem periodicCertificate25 :
    WordCertificate 24 (by decide) periodicWord25 periodicCaps25 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan25_0
  · exact periodicScan25_1
  · exact periodicScan25_2
  · exact periodicScan25_3
  · exact periodicScan25_4

theorem schedulable_word25 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 25) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps25 r := by
    simpa only [periodicCaps25_eq] using hr
  exact ⟨periodic 24 (by decide) periodicWord25,
    validRates_periodic_of_wordCertificate (by decide) periodicWord25
      periodicCertificate25 hc⟩

-- Case 26: F0873; period 15.
def periodicArray26 : Array (Fin 5) := #[0, 1, 2, 0, 3, 0, 1, 4, 0, 2, 0, 1, 3, 0, 4]
def periodicWord26 (k : Fin 15) : Fin 5 :=
  periodicArray26[k.val]
def periodicCaps26 : Fin 5 → RateCap
  | 0 => { bound := (2/5 : ℚ), closed := true }
  | 1 => { bound := (1/5 : ℚ), closed := true }
  | 2 => { bound := (2/15 : ℚ), closed := true }
  | 3 => { bound := (2/15 : ℚ), closed := true }
  | 4 => { bound := (2/15 : ℚ), closed := true }

theorem periodicArray26_toList :
    periodicArray26.toList = words 26 := by rfl
theorem periodicCaps26_eq : periodicCaps26 = wordCaps 26 := by rfl

theorem periodicScan26_0 : ∀ s : Fin 15,
    prefixCheck 15 (by decide) periodicWord26
      (periodicCaps26 0) 0 s 15 0 0 = true := by
  decide +kernel

theorem periodicScan26_1 : ∀ s : Fin 15,
    prefixCheck 15 (by decide) periodicWord26
      (periodicCaps26 1) 1 s 15 0 0 = true := by
  decide +kernel

theorem periodicScan26_2 : ∀ s : Fin 15,
    prefixCheck 15 (by decide) periodicWord26
      (periodicCaps26 2) 2 s 15 0 0 = true := by
  decide +kernel

theorem periodicScan26_3 : ∀ s : Fin 15,
    prefixCheck 15 (by decide) periodicWord26
      (periodicCaps26 3) 3 s 15 0 0 = true := by
  decide +kernel

theorem periodicScan26_4 : ∀ s : Fin 15,
    prefixCheck 15 (by decide) periodicWord26
      (periodicCaps26 4) 4 s 15 0 0 = true := by
  decide +kernel

theorem periodicCertificate26 :
    WordCertificate 15 (by decide) periodicWord26 periodicCaps26 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan26_0
  · exact periodicScan26_1
  · exact periodicScan26_2
  · exact periodicScan26_3
  · exact periodicScan26_4

theorem schedulable_word26 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 26) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps26 r := by
    simpa only [periodicCaps26_eq] using hr
  exact ⟨periodic 15 (by decide) periodicWord26,
    validRates_periodic_of_wordCertificate (by decide) periodicWord26
      periodicCertificate26 hc⟩

-- Case 27: F0874; period 50.
def periodicArray27 : Array (Fin 5) := #[0, 1, 2, 0, 3, 0, 1, 2, 0, 3, 0, 1, 2, 0, 3, 0, 1, 2, 0, 4, 0, 3, 1, 0, 2, 0, 1, 3, 0, 2, 0, 1, 3, 0, 2, 0, 1, 3, 0, 2, 0, 1, 3, 0, 4, 0, 2, 1, 0, 3]
def periodicWord27 (k : Fin 50) : Fin 5 :=
  periodicArray27[k.val]
def periodicCaps27 : Fin 5 → RateCap
  | 0 => { bound := (2/5 : ℚ), closed := true }
  | 1 => { bound := (1/5 : ℚ), closed := false }
  | 2 => { bound := (1/6 : ℚ), closed := false }
  | 3 => { bound := (1/6 : ℚ), closed := false }
  | 4 => { bound := (1/25 : ℚ), closed := true }

theorem periodicArray27_toList :
    periodicArray27.toList = words 27 := by rfl
theorem periodicCaps27_eq : periodicCaps27 = wordCaps 27 := by rfl

theorem periodicScan27_0 : ∀ s : Fin 50,
    prefixCheck 50 (by decide) periodicWord27
      (periodicCaps27 0) 0 s 50 0 0 = true := by
  decide +kernel

theorem periodicScan27_1 : ∀ s : Fin 50,
    prefixCheck 50 (by decide) periodicWord27
      (periodicCaps27 1) 1 s 50 0 0 = true := by
  decide +kernel

theorem periodicScan27_2 : ∀ s : Fin 50,
    prefixCheck 50 (by decide) periodicWord27
      (periodicCaps27 2) 2 s 50 0 0 = true := by
  decide +kernel

theorem periodicScan27_3 : ∀ s : Fin 50,
    prefixCheck 50 (by decide) periodicWord27
      (periodicCaps27 3) 3 s 50 0 0 = true := by
  decide +kernel

theorem periodicScan27_4 : ∀ s : Fin 50,
    prefixCheck 50 (by decide) periodicWord27
      (periodicCaps27 4) 4 s 50 0 0 = true := by
  decide +kernel

theorem periodicCertificate27 :
    WordCertificate 50 (by decide) periodicWord27 periodicCaps27 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan27_0
  · exact periodicScan27_1
  · exact periodicScan27_2
  · exact periodicScan27_3
  · exact periodicScan27_4

theorem schedulable_word27 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 27) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps27 r := by
    simpa only [periodicCaps27_eq] using hr
  exact ⟨periodic 50 (by decide) periodicWord27,
    validRates_periodic_of_wordCertificate (by decide) periodicWord27
      periodicCertificate27 hc⟩

-- Case 28: F0897; period 20.
def periodicArray28 : Array (Fin 5) := #[0, 1, 0, 1, 0, 3, 1, 0, 2, 1, 0, 4, 0, 1, 0, 3, 1, 0, 2, 1]
def periodicWord28 (k : Fin 20) : Fin 5 :=
  periodicArray28[k.val]
def periodicCaps28 : Fin 5 → RateCap
  | 0 => { bound := (2/5 : ℚ), closed := false }
  | 1 => { bound := (1/3 : ℚ), closed := false }
  | 2 => { bound := (1/10 : ℚ), closed := true }
  | 3 => { bound := (1/10 : ℚ), closed := true }
  | 4 => { bound := (1/20 : ℚ), closed := true }

theorem periodicArray28_toList :
    periodicArray28.toList = words 28 := by rfl
theorem periodicCaps28_eq : periodicCaps28 = wordCaps 28 := by rfl

theorem periodicScan28_0 : ∀ s : Fin 20,
    prefixCheck 20 (by decide) periodicWord28
      (periodicCaps28 0) 0 s 20 0 0 = true := by
  decide +kernel

theorem periodicScan28_1 : ∀ s : Fin 20,
    prefixCheck 20 (by decide) periodicWord28
      (periodicCaps28 1) 1 s 20 0 0 = true := by
  decide +kernel

theorem periodicScan28_2 : ∀ s : Fin 20,
    prefixCheck 20 (by decide) periodicWord28
      (periodicCaps28 2) 2 s 20 0 0 = true := by
  decide +kernel

theorem periodicScan28_3 : ∀ s : Fin 20,
    prefixCheck 20 (by decide) periodicWord28
      (periodicCaps28 3) 3 s 20 0 0 = true := by
  decide +kernel

theorem periodicScan28_4 : ∀ s : Fin 20,
    prefixCheck 20 (by decide) periodicWord28
      (periodicCaps28 4) 4 s 20 0 0 = true := by
  decide +kernel

theorem periodicCertificate28 :
    WordCertificate 20 (by decide) periodicWord28 periodicCaps28 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan28_0
  · exact periodicScan28_1
  · exact periodicScan28_2
  · exact periodicScan28_3
  · exact periodicScan28_4

theorem schedulable_word28 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 28) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps28 r := by
    simpa only [periodicCaps28_eq] using hr
  exact ⟨periodic 20 (by decide) periodicWord28,
    validRates_periodic_of_wordCertificate (by decide) periodicWord28
      periodicCertificate28 hc⟩

-- Case 29: F0900; period 35.
def periodicArray29 : Array (Fin 5) := #[0, 1, 0, 2, 1, 0, 1, 0, 2, 1, 0, 3, 1, 0, 2, 0, 1, 0, 2, 1, 0, 4, 1, 0, 2, 0, 1, 0, 2, 1, 0, 3, 1, 0, 2]
def periodicWord29 (k : Fin 35) : Fin 5 :=
  periodicArray29[k.val]
def periodicCaps29 : Fin 5 → RateCap
  | 0 => { bound := (2/5 : ℚ), closed := false }
  | 1 => { bound := (7/23 : ℚ), closed := false }
  | 2 => { bound := (1/5 : ℚ), closed := false }
  | 3 => { bound := (1/19 : ℚ), closed := false }
  | 4 => { bound := (1/35 : ℚ), closed := true }

theorem periodicArray29_toList :
    periodicArray29.toList = words 29 := by rfl
theorem periodicCaps29_eq : periodicCaps29 = wordCaps 29 := by rfl

theorem periodicScan29_0 : ∀ s : Fin 35,
    prefixCheck 35 (by decide) periodicWord29
      (periodicCaps29 0) 0 s 35 0 0 = true := by
  decide +kernel

theorem periodicScan29_1 : ∀ s : Fin 35,
    prefixCheck 35 (by decide) periodicWord29
      (periodicCaps29 1) 1 s 35 0 0 = true := by
  decide +kernel

theorem periodicScan29_2 : ∀ s : Fin 35,
    prefixCheck 35 (by decide) periodicWord29
      (periodicCaps29 2) 2 s 35 0 0 = true := by
  decide +kernel

theorem periodicScan29_3 : ∀ s : Fin 35,
    prefixCheck 35 (by decide) periodicWord29
      (periodicCaps29 3) 3 s 35 0 0 = true := by
  decide +kernel

theorem periodicScan29_4 : ∀ s : Fin 35,
    prefixCheck 35 (by decide) periodicWord29
      (periodicCaps29 4) 4 s 35 0 0 = true := by
  decide +kernel

theorem periodicCertificate29 :
    WordCertificate 35 (by decide) periodicWord29 periodicCaps29 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan29_0
  · exact periodicScan29_1
  · exact periodicScan29_2
  · exact periodicScan29_3
  · exact periodicScan29_4

theorem schedulable_word29 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 29) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps29 r := by
    simpa only [periodicCaps29_eq] using hr
  exact ⟨periodic 35 (by decide) periodicWord29,
    validRates_periodic_of_wordCertificate (by decide) periodicWord29
      periodicCertificate29 hc⟩

-- Case 30: F0903; period 20.
def periodicArray30 : Array (Fin 5) := #[0, 1, 0, 1, 2, 0, 3, 1, 0, 4, 0, 1, 2, 0, 1, 0, 3, 1, 0, 2]
def periodicWord30 (k : Fin 20) : Fin 5 :=
  periodicArray30[k.val]
def periodicCaps30 : Fin 5 → RateCap
  | 0 => { bound := (2/5 : ℚ), closed := false }
  | 1 => { bound := (2/7 : ℚ), closed := false }
  | 2 => { bound := (1/7 : ℚ), closed := false }
  | 3 => { bound := (1/10 : ℚ), closed := true }
  | 4 => { bound := (1/20 : ℚ), closed := true }

theorem periodicArray30_toList :
    periodicArray30.toList = words 30 := by rfl
theorem periodicCaps30_eq : periodicCaps30 = wordCaps 30 := by rfl

theorem periodicScan30_0 : ∀ s : Fin 20,
    prefixCheck 20 (by decide) periodicWord30
      (periodicCaps30 0) 0 s 20 0 0 = true := by
  decide +kernel

theorem periodicScan30_1 : ∀ s : Fin 20,
    prefixCheck 20 (by decide) periodicWord30
      (periodicCaps30 1) 1 s 20 0 0 = true := by
  decide +kernel

theorem periodicScan30_2 : ∀ s : Fin 20,
    prefixCheck 20 (by decide) periodicWord30
      (periodicCaps30 2) 2 s 20 0 0 = true := by
  decide +kernel

theorem periodicScan30_3 : ∀ s : Fin 20,
    prefixCheck 20 (by decide) periodicWord30
      (periodicCaps30 3) 3 s 20 0 0 = true := by
  decide +kernel

theorem periodicScan30_4 : ∀ s : Fin 20,
    prefixCheck 20 (by decide) periodicWord30
      (periodicCaps30 4) 4 s 20 0 0 = true := by
  decide +kernel

theorem periodicCertificate30 :
    WordCertificate 20 (by decide) periodicWord30 periodicCaps30 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan30_0
  · exact periodicScan30_1
  · exact periodicScan30_2
  · exact periodicScan30_3
  · exact periodicScan30_4

theorem schedulable_word30 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 30) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps30 r := by
    simpa only [periodicCaps30_eq] using hr
  exact ⟨periodic 20 (by decide) periodicWord30,
    validRates_periodic_of_wordCertificate (by decide) periodicWord30
      periodicCertificate30 hc⟩

-- Case 31: F0915; period 15.
def periodicArray31 : Array (Fin 5) := #[0, 1, 0, 2, 1, 0, 4, 0, 1, 2, 0, 3, 1, 0, 2]
def periodicWord31 (k : Fin 15) : Fin 5 :=
  periodicArray31[k.val]
def periodicCaps31 : Fin 5 → RateCap
  | 0 => { bound := (2/5 : ℚ), closed := false }
  | 1 => { bound := (4/15 : ℚ), closed := true }
  | 2 => { bound := (1/5 : ℚ), closed := false }
  | 3 => { bound := (1/15 : ℚ), closed := true }
  | 4 => { bound := (1/15 : ℚ), closed := true }

theorem periodicArray31_toList :
    periodicArray31.toList = words 31 := by rfl
theorem periodicCaps31_eq : periodicCaps31 = wordCaps 31 := by rfl

theorem periodicScan31_0 : ∀ s : Fin 15,
    prefixCheck 15 (by decide) periodicWord31
      (periodicCaps31 0) 0 s 15 0 0 = true := by
  decide +kernel

theorem periodicScan31_1 : ∀ s : Fin 15,
    prefixCheck 15 (by decide) periodicWord31
      (periodicCaps31 1) 1 s 15 0 0 = true := by
  decide +kernel

theorem periodicScan31_2 : ∀ s : Fin 15,
    prefixCheck 15 (by decide) periodicWord31
      (periodicCaps31 2) 2 s 15 0 0 = true := by
  decide +kernel

theorem periodicScan31_3 : ∀ s : Fin 15,
    prefixCheck 15 (by decide) periodicWord31
      (periodicCaps31 3) 3 s 15 0 0 = true := by
  decide +kernel

theorem periodicScan31_4 : ∀ s : Fin 15,
    prefixCheck 15 (by decide) periodicWord31
      (periodicCaps31 4) 4 s 15 0 0 = true := by
  decide +kernel

theorem periodicCertificate31 :
    WordCertificate 15 (by decide) periodicWord31 periodicCaps31 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan31_0
  · exact periodicScan31_1
  · exact periodicScan31_2
  · exact periodicScan31_3
  · exact periodicScan31_4

theorem schedulable_word31 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 31) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps31 r := by
    simpa only [periodicCaps31_eq] using hr
  exact ⟨periodic 15 (by decide) periodicWord31,
    validRates_periodic_of_wordCertificate (by decide) periodicWord31
      periodicCertificate31 hc⟩

-- Case 32: F0916; period 15.
def periodicArray32 : Array (Fin 5) := #[0, 1, 0, 2, 0, 1, 3, 0, 4, 1, 0, 2, 0, 1, 3]
def periodicWord32 (k : Fin 15) : Fin 5 :=
  periodicArray32[k.val]
def periodicCaps32 : Fin 5 → RateCap
  | 0 => { bound := (2/5 : ℚ), closed := false }
  | 1 => { bound := (4/15 : ℚ), closed := true }
  | 2 => { bound := (2/15 : ℚ), closed := true }
  | 3 => { bound := (2/15 : ℚ), closed := true }
  | 4 => { bound := (1/15 : ℚ), closed := true }

theorem periodicArray32_toList :
    periodicArray32.toList = words 32 := by rfl
theorem periodicCaps32_eq : periodicCaps32 = wordCaps 32 := by rfl

theorem periodicScan32_0 : ∀ s : Fin 15,
    prefixCheck 15 (by decide) periodicWord32
      (periodicCaps32 0) 0 s 15 0 0 = true := by
  decide +kernel

theorem periodicScan32_1 : ∀ s : Fin 15,
    prefixCheck 15 (by decide) periodicWord32
      (periodicCaps32 1) 1 s 15 0 0 = true := by
  decide +kernel

theorem periodicScan32_2 : ∀ s : Fin 15,
    prefixCheck 15 (by decide) periodicWord32
      (periodicCaps32 2) 2 s 15 0 0 = true := by
  decide +kernel

theorem periodicScan32_3 : ∀ s : Fin 15,
    prefixCheck 15 (by decide) periodicWord32
      (periodicCaps32 3) 3 s 15 0 0 = true := by
  decide +kernel

theorem periodicScan32_4 : ∀ s : Fin 15,
    prefixCheck 15 (by decide) periodicWord32
      (periodicCaps32 4) 4 s 15 0 0 = true := by
  decide +kernel

theorem periodicCertificate32 :
    WordCertificate 15 (by decide) periodicWord32 periodicCaps32 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan32_0
  · exact periodicScan32_1
  · exact periodicScan32_2
  · exact periodicScan32_3
  · exact periodicScan32_4

theorem schedulable_word32 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 32) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps32 r := by
    simpa only [periodicCaps32_eq] using hr
  exact ⟨periodic 15 (by decide) periodicWord32,
    validRates_periodic_of_wordCertificate (by decide) periodicWord32
      periodicCertificate32 hc⟩

-- Case 33: F0933; period 20.
def periodicArray33 : Array (Fin 5) := #[0, 1, 0, 3, 0, 1, 2, 0, 4, 1, 0, 3, 0, 2, 1, 0, 3, 0, 1, 2]
def periodicWord33 (k : Fin 20) : Fin 5 :=
  periodicArray33[k.val]
def periodicCaps33 : Fin 5 → RateCap
  | 0 => { bound := (2/5 : ℚ), closed := false }
  | 1 => { bound := (1/4 : ℚ), closed := false }
  | 2 => { bound := (3/20 : ℚ), closed := true }
  | 3 => { bound := (1/7 : ℚ), closed := false }
  | 4 => { bound := (1/20 : ℚ), closed := true }

theorem periodicArray33_toList :
    periodicArray33.toList = words 33 := by rfl
theorem periodicCaps33_eq : periodicCaps33 = wordCaps 33 := by rfl

theorem periodicScan33_0 : ∀ s : Fin 20,
    prefixCheck 20 (by decide) periodicWord33
      (periodicCaps33 0) 0 s 20 0 0 = true := by
  decide +kernel

theorem periodicScan33_1 : ∀ s : Fin 20,
    prefixCheck 20 (by decide) periodicWord33
      (periodicCaps33 1) 1 s 20 0 0 = true := by
  decide +kernel

theorem periodicScan33_2 : ∀ s : Fin 20,
    prefixCheck 20 (by decide) periodicWord33
      (periodicCaps33 2) 2 s 20 0 0 = true := by
  decide +kernel

theorem periodicScan33_3 : ∀ s : Fin 20,
    prefixCheck 20 (by decide) periodicWord33
      (periodicCaps33 3) 3 s 20 0 0 = true := by
  decide +kernel

theorem periodicScan33_4 : ∀ s : Fin 20,
    prefixCheck 20 (by decide) periodicWord33
      (periodicCaps33 4) 4 s 20 0 0 = true := by
  decide +kernel

theorem periodicCertificate33 :
    WordCertificate 20 (by decide) periodicWord33 periodicCaps33 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan33_0
  · exact periodicScan33_1
  · exact periodicScan33_2
  · exact periodicScan33_3
  · exact periodicScan33_4

theorem schedulable_word33 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 33) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps33 r := by
    simpa only [periodicCaps33_eq] using hr
  exact ⟨periodic 20 (by decide) periodicWord33,
    validRates_periodic_of_wordCertificate (by decide) periodicWord33
      periodicCertificate33 hc⟩

-- Case 34: F0989; period 52.
def periodicArray34 : Array (Fin 5) := #[0, 1, 0, 1, 0, 2, 1, 0, 1, 0, 2, 1, 0, 3, 1, 0, 2, 0, 1, 0, 1, 0, 2, 1, 0, 4, 1, 0, 2, 0, 1, 3, 0, 1, 0, 2, 1, 0, 1, 0, 2, 1, 0, 1, 0, 2, 1, 0, 3, 1, 0, 2]
def periodicWord34 (k : Fin 52) : Fin 5 :=
  periodicArray34[k.val]
def periodicCaps34 : Fin 5 → RateCap
  | 0 => { bound := (11/28 : ℚ), closed := false }
  | 1 => { bound := (1/3 : ℚ), closed := false }
  | 2 => { bound := (1/6 : ℚ), closed := false }
  | 3 => { bound := (3/52 : ℚ), closed := true }
  | 4 => { bound := (1/52 : ℚ), closed := true }

theorem periodicArray34_toList :
    periodicArray34.toList = words 34 := by rfl
theorem periodicCaps34_eq : periodicCaps34 = wordCaps 34 := by rfl

theorem periodicScan34_0 : ∀ s : Fin 52,
    prefixCheck 52 (by decide) periodicWord34
      (periodicCaps34 0) 0 s 52 0 0 = true := by
  decide +kernel

theorem periodicScan34_1 : ∀ s : Fin 52,
    prefixCheck 52 (by decide) periodicWord34
      (periodicCaps34 1) 1 s 52 0 0 = true := by
  decide +kernel

theorem periodicScan34_2 : ∀ s : Fin 52,
    prefixCheck 52 (by decide) periodicWord34
      (periodicCaps34 2) 2 s 52 0 0 = true := by
  decide +kernel

theorem periodicScan34_3 : ∀ s : Fin 52,
    prefixCheck 52 (by decide) periodicWord34
      (periodicCaps34 3) 3 s 52 0 0 = true := by
  decide +kernel

theorem periodicScan34_4 : ∀ s : Fin 52,
    prefixCheck 52 (by decide) periodicWord34
      (periodicCaps34 4) 4 s 52 0 0 = true := by
  decide +kernel

theorem periodicCertificate34 :
    WordCertificate 52 (by decide) periodicWord34 periodicCaps34 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan34_0
  · exact periodicScan34_1
  · exact periodicScan34_2
  · exact periodicScan34_3
  · exact periodicScan34_4

theorem schedulable_word34 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 34) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps34 r := by
    simpa only [periodicCaps34_eq] using hr
  exact ⟨periodic 52 (by decide) periodicWord34,
    validRates_periodic_of_wordCertificate (by decide) periodicWord34
      periodicCertificate34 hc⟩

-- Case 35: F1015; period 13.
def periodicArray35 : Array (Fin 5) := #[0, 1, 2, 0, 4, 1, 0, 3, 0, 2, 1, 0, 3]
def periodicWord35 (k : Fin 13) : Fin 5 :=
  periodicArray35[k.val]
def periodicCaps35 : Fin 5 → RateCap
  | 0 => { bound := (5/13 : ℚ), closed := true }
  | 1 => { bound := (3/13 : ℚ), closed := true }
  | 2 => { bound := (2/13 : ℚ), closed := true }
  | 3 => { bound := (1/7 : ℚ), closed := false }
  | 4 => { bound := (1/13 : ℚ), closed := true }

theorem periodicArray35_toList :
    periodicArray35.toList = words 35 := by rfl
theorem periodicCaps35_eq : periodicCaps35 = wordCaps 35 := by rfl

theorem periodicScan35_0 : ∀ s : Fin 13,
    prefixCheck 13 (by decide) periodicWord35
      (periodicCaps35 0) 0 s 13 0 0 = true := by
  decide +kernel

theorem periodicScan35_1 : ∀ s : Fin 13,
    prefixCheck 13 (by decide) periodicWord35
      (periodicCaps35 1) 1 s 13 0 0 = true := by
  decide +kernel

theorem periodicScan35_2 : ∀ s : Fin 13,
    prefixCheck 13 (by decide) periodicWord35
      (periodicCaps35 2) 2 s 13 0 0 = true := by
  decide +kernel

theorem periodicScan35_3 : ∀ s : Fin 13,
    prefixCheck 13 (by decide) periodicWord35
      (periodicCaps35 3) 3 s 13 0 0 = true := by
  decide +kernel

theorem periodicScan35_4 : ∀ s : Fin 13,
    prefixCheck 13 (by decide) periodicWord35
      (periodicCaps35 4) 4 s 13 0 0 = true := by
  decide +kernel

theorem periodicCertificate35 :
    WordCertificate 13 (by decide) periodicWord35 periodicCaps35 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan35_0
  · exact periodicScan35_1
  · exact periodicScan35_2
  · exact periodicScan35_3
  · exact periodicScan35_4

theorem schedulable_word35 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 35) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps35 r := by
    simpa only [periodicCaps35_eq] using hr
  exact ⟨periodic 13 (by decide) periodicWord35,
    validRates_periodic_of_wordCertificate (by decide) periodicWord35
      periodicCertificate35 hc⟩

-- Case 36: F1026; period 45.
def periodicArray36 : Array (Fin 5) := #[0, 1, 0, 2, 0, 1, 2, 0, 1, 0, 2, 0, 1, 2, 0, 3, 1, 0, 2, 0, 1, 2, 0, 4, 1, 0, 2, 0, 1, 2, 0, 1, 0, 2, 0, 1, 2, 0, 3, 1, 0, 2, 0, 1, 2]
def periodicWord36 (k : Fin 45) : Fin 5 :=
  periodicArray36[k.val]
def periodicCaps36 : Fin 5 → RateCap
  | 0 => { bound := (5/13 : ℚ), closed := false }
  | 1 => { bound := (5/19 : ℚ), closed := false }
  | 2 => { bound := (1/4 : ℚ), closed := false }
  | 3 => { bound := (2/45 : ℚ), closed := true }
  | 4 => { bound := (1/45 : ℚ), closed := true }

theorem periodicArray36_toList :
    periodicArray36.toList = words 36 := by rfl
theorem periodicCaps36_eq : periodicCaps36 = wordCaps 36 := by rfl

theorem periodicScan36_0 : ∀ s : Fin 45,
    prefixCheck 45 (by decide) periodicWord36
      (periodicCaps36 0) 0 s 45 0 0 = true := by
  decide +kernel

theorem periodicScan36_1 : ∀ s : Fin 45,
    prefixCheck 45 (by decide) periodicWord36
      (periodicCaps36 1) 1 s 45 0 0 = true := by
  decide +kernel

theorem periodicScan36_2 : ∀ s : Fin 45,
    prefixCheck 45 (by decide) periodicWord36
      (periodicCaps36 2) 2 s 45 0 0 = true := by
  decide +kernel

theorem periodicScan36_3 : ∀ s : Fin 45,
    prefixCheck 45 (by decide) periodicWord36
      (periodicCaps36 3) 3 s 45 0 0 = true := by
  decide +kernel

theorem periodicScan36_4 : ∀ s : Fin 45,
    prefixCheck 45 (by decide) periodicWord36
      (periodicCaps36 4) 4 s 45 0 0 = true := by
  decide +kernel

theorem periodicCertificate36 :
    WordCertificate 45 (by decide) periodicWord36 periodicCaps36 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan36_0
  · exact periodicScan36_1
  · exact periodicScan36_2
  · exact periodicScan36_3
  · exact periodicScan36_4

theorem schedulable_word36 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 36) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps36 r := by
    simpa only [periodicCaps36_eq] using hr
  exact ⟨periodic 45 (by decide) periodicWord36,
    validRates_periodic_of_wordCertificate (by decide) periodicWord36
      periodicCertificate36 hc⟩

-- Case 37: F1055; period 46.
def periodicArray37 : Array (Fin 5) := #[0, 1, 0, 2, 0, 1, 2, 0, 3, 1, 0, 2, 0, 1, 2, 0, 1, 0, 2, 0, 1, 2, 0, 3, 1, 0, 2, 0, 1, 2, 0, 4, 1, 0, 2, 0, 1, 2, 0, 3, 1, 0, 2, 0, 1, 2]
def periodicWord37 (k : Fin 46) : Fin 5 :=
  periodicArray37[k.val]
def periodicCaps37 : Fin 5 → RateCap
  | 0 => { bound := (8/21 : ℚ), closed := false }
  | 1 => { bound := (7/27 : ℚ), closed := false }
  | 2 => { bound := (1/4 : ℚ), closed := false }
  | 3 => { bound := (3/46 : ℚ), closed := true }
  | 4 => { bound := (1/46 : ℚ), closed := true }

theorem periodicArray37_toList :
    periodicArray37.toList = words 37 := by rfl
theorem periodicCaps37_eq : periodicCaps37 = wordCaps 37 := by rfl

theorem periodicScan37_0 : ∀ s : Fin 46,
    prefixCheck 46 (by decide) periodicWord37
      (periodicCaps37 0) 0 s 46 0 0 = true := by
  decide +kernel

theorem periodicScan37_1 : ∀ s : Fin 46,
    prefixCheck 46 (by decide) periodicWord37
      (periodicCaps37 1) 1 s 46 0 0 = true := by
  decide +kernel

theorem periodicScan37_2 : ∀ s : Fin 46,
    prefixCheck 46 (by decide) periodicWord37
      (periodicCaps37 2) 2 s 46 0 0 = true := by
  decide +kernel

theorem periodicScan37_3 : ∀ s : Fin 46,
    prefixCheck 46 (by decide) periodicWord37
      (periodicCaps37 3) 3 s 46 0 0 = true := by
  decide +kernel

theorem periodicScan37_4 : ∀ s : Fin 46,
    prefixCheck 46 (by decide) periodicWord37
      (periodicCaps37 4) 4 s 46 0 0 = true := by
  decide +kernel

theorem periodicCertificate37 :
    WordCertificate 46 (by decide) periodicWord37 periodicCaps37 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan37_0
  · exact periodicScan37_1
  · exact periodicScan37_2
  · exact periodicScan37_3
  · exact periodicScan37_4

theorem schedulable_word37 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 37) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps37 r := by
    simpa only [periodicCaps37_eq] using hr
  exact ⟨periodic 46 (by decide) periodicWord37,
    validRates_periodic_of_wordCertificate (by decide) periodicWord37
      periodicCertificate37 hc⟩

-- Case 38: F1064; period 32.
def periodicArray38 : Array (Fin 5) := #[0, 1, 0, 3, 1, 0, 2, 1, 0, 1, 0, 3, 1, 0, 2, 1, 0, 1, 0, 3, 1, 0, 2, 1, 0, 4, 0, 1, 3, 0, 1, 2]
def periodicWord38 (k : Fin 32) : Fin 5 :=
  periodicArray38[k.val]
def periodicCaps38 : Fin 5 → RateCap
  | 0 => { bound := (3/8 : ℚ), closed := true }
  | 1 => { bound := (1/3 : ℚ), closed := false }
  | 2 => { bound := (1/8 : ℚ), closed := false }
  | 3 => { bound := (1/8 : ℚ), closed := false }
  | 4 => { bound := (1/32 : ℚ), closed := true }

theorem periodicArray38_toList :
    periodicArray38.toList = words 38 := by rfl
theorem periodicCaps38_eq : periodicCaps38 = wordCaps 38 := by rfl

theorem periodicScan38_0 : ∀ s : Fin 32,
    prefixCheck 32 (by decide) periodicWord38
      (periodicCaps38 0) 0 s 32 0 0 = true := by
  decide +kernel

theorem periodicScan38_1 : ∀ s : Fin 32,
    prefixCheck 32 (by decide) periodicWord38
      (periodicCaps38 1) 1 s 32 0 0 = true := by
  decide +kernel

theorem periodicScan38_2 : ∀ s : Fin 32,
    prefixCheck 32 (by decide) periodicWord38
      (periodicCaps38 2) 2 s 32 0 0 = true := by
  decide +kernel

theorem periodicScan38_3 : ∀ s : Fin 32,
    prefixCheck 32 (by decide) periodicWord38
      (periodicCaps38 3) 3 s 32 0 0 = true := by
  decide +kernel

theorem periodicScan38_4 : ∀ s : Fin 32,
    prefixCheck 32 (by decide) periodicWord38
      (periodicCaps38 4) 4 s 32 0 0 = true := by
  decide +kernel

theorem periodicCertificate38 :
    WordCertificate 32 (by decide) periodicWord38 periodicCaps38 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan38_0
  · exact periodicScan38_1
  · exact periodicScan38_2
  · exact periodicScan38_3
  · exact periodicScan38_4

theorem schedulable_word38 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 38) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps38 r := by
    simpa only [periodicCaps38_eq] using hr
  exact ⟨periodic 32 (by decide) periodicWord38,
    validRates_periodic_of_wordCertificate (by decide) periodicWord38
      periodicCertificate38 hc⟩

-- Case 39: F1082; period 32.
def periodicArray39 : Array (Fin 5) := #[0, 1, 0, 2, 1, 0, 1, 0, 2, 1, 0, 3, 1, 0, 2, 1, 0, 4, 0, 1, 2, 0, 1, 0, 2, 1, 0, 3, 1, 0, 2, 1]
def periodicWord39 (k : Fin 32) : Fin 5 :=
  periodicArray39[k.val]
def periodicCaps39 : Fin 5 → RateCap
  | 0 => { bound := (3/8 : ℚ), closed := false }
  | 1 => { bound := (1/3 : ℚ), closed := false }
  | 2 => { bound := (2/11 : ℚ), closed := false }
  | 3 => { bound := (1/16 : ℚ), closed := true }
  | 4 => { bound := (1/32 : ℚ), closed := true }

theorem periodicArray39_toList :
    periodicArray39.toList = words 39 := by rfl
theorem periodicCaps39_eq : periodicCaps39 = wordCaps 39 := by rfl

theorem periodicScan39_0 : ∀ s : Fin 32,
    prefixCheck 32 (by decide) periodicWord39
      (periodicCaps39 0) 0 s 32 0 0 = true := by
  decide +kernel

theorem periodicScan39_1 : ∀ s : Fin 32,
    prefixCheck 32 (by decide) periodicWord39
      (periodicCaps39 1) 1 s 32 0 0 = true := by
  decide +kernel

theorem periodicScan39_2 : ∀ s : Fin 32,
    prefixCheck 32 (by decide) periodicWord39
      (periodicCaps39 2) 2 s 32 0 0 = true := by
  decide +kernel

theorem periodicScan39_3 : ∀ s : Fin 32,
    prefixCheck 32 (by decide) periodicWord39
      (periodicCaps39 3) 3 s 32 0 0 = true := by
  decide +kernel

theorem periodicScan39_4 : ∀ s : Fin 32,
    prefixCheck 32 (by decide) periodicWord39
      (periodicCaps39 4) 4 s 32 0 0 = true := by
  decide +kernel

theorem periodicCertificate39 :
    WordCertificate 32 (by decide) periodicWord39 periodicCaps39 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan39_0
  · exact periodicScan39_1
  · exact periodicScan39_2
  · exact periodicScan39_3
  · exact periodicScan39_4

theorem schedulable_word39 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 39) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps39 r := by
    simpa only [periodicCaps39_eq] using hr
  exact ⟨periodic 32 (by decide) periodicWord39,
    validRates_periodic_of_wordCertificate (by decide) periodicWord39
      periodicCertificate39 hc⟩

-- Case 40: F1099; period 24.
def periodicArray40 : Array (Fin 5) := #[0, 1, 0, 2, 1, 0, 2, 0, 1, 3, 0, 2, 1, 0, 4, 2, 0, 1, 0, 2, 1, 0, 3, 2]
def periodicWord40 (k : Fin 24) : Fin 5 :=
  periodicArray40[k.val]
def periodicCaps40 : Fin 5 → RateCap
  | 0 => { bound := (3/8 : ℚ), closed := false }
  | 1 => { bound := (1/4 : ℚ), closed := false }
  | 2 => { bound := (1/4 : ℚ), closed := false }
  | 3 => { bound := (1/12 : ℚ), closed := false }
  | 4 => { bound := (1/24 : ℚ), closed := true }

theorem periodicArray40_toList :
    periodicArray40.toList = words 40 := by rfl
theorem periodicCaps40_eq : periodicCaps40 = wordCaps 40 := by rfl

theorem periodicScan40_0 : ∀ s : Fin 24,
    prefixCheck 24 (by decide) periodicWord40
      (periodicCaps40 0) 0 s 24 0 0 = true := by
  decide +kernel

theorem periodicScan40_1 : ∀ s : Fin 24,
    prefixCheck 24 (by decide) periodicWord40
      (periodicCaps40 1) 1 s 24 0 0 = true := by
  decide +kernel

theorem periodicScan40_2 : ∀ s : Fin 24,
    prefixCheck 24 (by decide) periodicWord40
      (periodicCaps40 2) 2 s 24 0 0 = true := by
  decide +kernel

theorem periodicScan40_3 : ∀ s : Fin 24,
    prefixCheck 24 (by decide) periodicWord40
      (periodicCaps40 3) 3 s 24 0 0 = true := by
  decide +kernel

theorem periodicScan40_4 : ∀ s : Fin 24,
    prefixCheck 24 (by decide) periodicWord40
      (periodicCaps40 4) 4 s 24 0 0 = true := by
  decide +kernel

theorem periodicCertificate40 :
    WordCertificate 24 (by decide) periodicWord40 periodicCaps40 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan40_0
  · exact periodicScan40_1
  · exact periodicScan40_2
  · exact periodicScan40_3
  · exact periodicScan40_4

theorem schedulable_word40 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 40) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps40 r := by
    simpa only [periodicCaps40_eq] using hr
  exact ⟨periodic 24 (by decide) periodicWord40,
    validRates_periodic_of_wordCertificate (by decide) periodicWord40
      periodicCertificate40 hc⟩

-- Case 41: F1109; period 16.
def periodicArray41 : Array (Fin 5) := #[0, 1, 0, 2, 1, 0, 3, 0, 1, 2, 0, 4, 1, 0, 3, 2]
def periodicWord41 (k : Fin 16) : Fin 5 :=
  periodicArray41[k.val]
def periodicCaps41 : Fin 5 → RateCap
  | 0 => { bound := (3/8 : ℚ), closed := false }
  | 1 => { bound := (1/4 : ℚ), closed := false }
  | 2 => { bound := (2/11 : ℚ), closed := false }
  | 3 => { bound := (1/8 : ℚ), closed := true }
  | 4 => { bound := (1/16 : ℚ), closed := true }

theorem periodicArray41_toList :
    periodicArray41.toList = words 41 := by rfl
theorem periodicCaps41_eq : periodicCaps41 = wordCaps 41 := by rfl

theorem periodicScan41_0 : ∀ s : Fin 16,
    prefixCheck 16 (by decide) periodicWord41
      (periodicCaps41 0) 0 s 16 0 0 = true := by
  decide +kernel

theorem periodicScan41_1 : ∀ s : Fin 16,
    prefixCheck 16 (by decide) periodicWord41
      (periodicCaps41 1) 1 s 16 0 0 = true := by
  decide +kernel

theorem periodicScan41_2 : ∀ s : Fin 16,
    prefixCheck 16 (by decide) periodicWord41
      (periodicCaps41 2) 2 s 16 0 0 = true := by
  decide +kernel

theorem periodicScan41_3 : ∀ s : Fin 16,
    prefixCheck 16 (by decide) periodicWord41
      (periodicCaps41 3) 3 s 16 0 0 = true := by
  decide +kernel

theorem periodicScan41_4 : ∀ s : Fin 16,
    prefixCheck 16 (by decide) periodicWord41
      (periodicCaps41 4) 4 s 16 0 0 = true := by
  decide +kernel

theorem periodicCertificate41 :
    WordCertificate 16 (by decide) periodicWord41 periodicCaps41 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan41_0
  · exact periodicScan41_1
  · exact periodicScan41_2
  · exact periodicScan41_3
  · exact periodicScan41_4

theorem schedulable_word41 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 41) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps41 r := by
    simpa only [periodicCaps41_eq] using hr
  exact ⟨periodic 16 (by decide) periodicWord41,
    validRates_periodic_of_wordCertificate (by decide) periodicWord41
      periodicCertificate41 hc⟩

-- Case 42: F1186; period 22.
def periodicArray42 : Array (Fin 5) := #[0, 1, 2, 0, 1, 3, 0, 2, 1, 0, 4, 0, 1, 2, 0, 3, 1, 0, 2, 1, 0, 3]
def periodicWord42 (k : Fin 22) : Fin 5 :=
  periodicArray42[k.val]
def periodicCaps42 : Fin 5 → RateCap
  | 0 => { bound := (4/11 : ℚ), closed := true }
  | 1 => { bound := (3/11 : ℚ), closed := false }
  | 2 => { bound := (2/11 : ℚ), closed := true }
  | 3 => { bound := (1/9 : ℚ), closed := false }
  | 4 => { bound := (1/22 : ℚ), closed := true }

theorem periodicArray42_toList :
    periodicArray42.toList = words 42 := by rfl
theorem periodicCaps42_eq : periodicCaps42 = wordCaps 42 := by rfl

theorem periodicScan42_0 : ∀ s : Fin 22,
    prefixCheck 22 (by decide) periodicWord42
      (periodicCaps42 0) 0 s 22 0 0 = true := by
  decide +kernel

theorem periodicScan42_1 : ∀ s : Fin 22,
    prefixCheck 22 (by decide) periodicWord42
      (periodicCaps42 1) 1 s 22 0 0 = true := by
  decide +kernel

theorem periodicScan42_2 : ∀ s : Fin 22,
    prefixCheck 22 (by decide) periodicWord42
      (periodicCaps42 2) 2 s 22 0 0 = true := by
  decide +kernel

theorem periodicScan42_3 : ∀ s : Fin 22,
    prefixCheck 22 (by decide) periodicWord42
      (periodicCaps42 3) 3 s 22 0 0 = true := by
  decide +kernel

theorem periodicScan42_4 : ∀ s : Fin 22,
    prefixCheck 22 (by decide) periodicWord42
      (periodicCaps42 4) 4 s 22 0 0 = true := by
  decide +kernel

theorem periodicCertificate42 :
    WordCertificate 22 (by decide) periodicWord42 periodicCaps42 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan42_0
  · exact periodicScan42_1
  · exact periodicScan42_2
  · exact periodicScan42_3
  · exact periodicScan42_4

theorem schedulable_word42 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 42) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps42 r := by
    simpa only [periodicCaps42_eq] using hr
  exact ⟨periodic 22 (by decide) periodicWord42,
    validRates_periodic_of_wordCertificate (by decide) periodicWord42
      periodicCertificate42 hc⟩

-- Case 43: F1205; period 22.
def periodicArray43 : Array (Fin 5) := #[0, 1, 2, 0, 3, 1, 0, 2, 0, 3, 1, 0, 4, 2, 0, 1, 3, 0, 2, 1, 0, 3]
def periodicWord43 (k : Fin 22) : Fin 5 :=
  periodicArray43[k.val]
def periodicCaps43 : Fin 5 → RateCap
  | 0 => { bound := (4/11 : ℚ), closed := false }
  | 1 => { bound := (2/9 : ℚ), closed := false }
  | 2 => { bound := (2/11 : ℚ), closed := true }
  | 3 => { bound := (1/6 : ℚ), closed := false }
  | 4 => { bound := (1/22 : ℚ), closed := true }

theorem periodicArray43_toList :
    periodicArray43.toList = words 43 := by rfl
theorem periodicCaps43_eq : periodicCaps43 = wordCaps 43 := by rfl

theorem periodicScan43_0 : ∀ s : Fin 22,
    prefixCheck 22 (by decide) periodicWord43
      (periodicCaps43 0) 0 s 22 0 0 = true := by
  decide +kernel

theorem periodicScan43_1 : ∀ s : Fin 22,
    prefixCheck 22 (by decide) periodicWord43
      (periodicCaps43 1) 1 s 22 0 0 = true := by
  decide +kernel

theorem periodicScan43_2 : ∀ s : Fin 22,
    prefixCheck 22 (by decide) periodicWord43
      (periodicCaps43 2) 2 s 22 0 0 = true := by
  decide +kernel

theorem periodicScan43_3 : ∀ s : Fin 22,
    prefixCheck 22 (by decide) periodicWord43
      (periodicCaps43 3) 3 s 22 0 0 = true := by
  decide +kernel

theorem periodicScan43_4 : ∀ s : Fin 22,
    prefixCheck 22 (by decide) periodicWord43
      (periodicCaps43 4) 4 s 22 0 0 = true := by
  decide +kernel

theorem periodicCertificate43 :
    WordCertificate 22 (by decide) periodicWord43 periodicCaps43 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan43_0
  · exact periodicScan43_1
  · exact periodicScan43_2
  · exact periodicScan43_3
  · exact periodicScan43_4

theorem schedulable_word43 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 43) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps43 r := by
    simpa only [periodicCaps43_eq] using hr
  exact ⟨periodic 22 (by decide) periodicWord43,
    validRates_periodic_of_wordCertificate (by decide) periodicWord43
      periodicCertificate43 hc⟩

-- Case 44: F1212; period 36.
def periodicArray44 : Array (Fin 5) := #[0, 1, 0, 2, 3, 0, 1, 2, 0, 3, 1, 0, 2, 0, 1, 3, 0, 2, 1, 0, 3, 2, 0, 1, 0, 2, 3, 0, 1, 2, 0, 4, 1, 0, 3, 2]
def periodicWord44 (k : Fin 36) : Fin 5 :=
  periodicArray44[k.val]
def periodicCaps44 : Fin 5 → RateCap
  | 0 => { bound := (13/36 : ℚ), closed := true }
  | 1 => { bound := (5/23 : ℚ), closed := false }
  | 2 => { bound := (1/5 : ℚ), closed := false }
  | 3 => { bound := (1/7 : ℚ), closed := false }
  | 4 => { bound := (1/36 : ℚ), closed := true }

theorem periodicArray44_toList :
    periodicArray44.toList = words 44 := by rfl
theorem periodicCaps44_eq : periodicCaps44 = wordCaps 44 := by rfl

theorem periodicScan44_0 : ∀ s : Fin 36,
    prefixCheck 36 (by decide) periodicWord44
      (periodicCaps44 0) 0 s 36 0 0 = true := by
  decide +kernel

theorem periodicScan44_1 : ∀ s : Fin 36,
    prefixCheck 36 (by decide) periodicWord44
      (periodicCaps44 1) 1 s 36 0 0 = true := by
  decide +kernel

theorem periodicScan44_2 : ∀ s : Fin 36,
    prefixCheck 36 (by decide) periodicWord44
      (periodicCaps44 2) 2 s 36 0 0 = true := by
  decide +kernel

theorem periodicScan44_3 : ∀ s : Fin 36,
    prefixCheck 36 (by decide) periodicWord44
      (periodicCaps44 3) 3 s 36 0 0 = true := by
  decide +kernel

theorem periodicScan44_4 : ∀ s : Fin 36,
    prefixCheck 36 (by decide) periodicWord44
      (periodicCaps44 4) 4 s 36 0 0 = true := by
  decide +kernel

theorem periodicCertificate44 :
    WordCertificate 36 (by decide) periodicWord44 periodicCaps44 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan44_0
  · exact periodicScan44_1
  · exact periodicScan44_2
  · exact periodicScan44_3
  · exact periodicScan44_4

theorem schedulable_word44 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 44) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps44 r := by
    simpa only [periodicCaps44_eq] using hr
  exact ⟨periodic 36 (by decide) periodicWord44,
    validRates_periodic_of_wordCertificate (by decide) periodicWord44
      periodicCertificate44 hc⟩

-- Case 45: F1222; period 14.
def periodicArray45 : Array (Fin 5) := #[0, 1, 2, 0, 1, 3, 0, 1, 4, 0, 2, 1, 0, 3]
def periodicWord45 (k : Fin 14) : Fin 5 :=
  periodicArray45[k.val]
def periodicCaps45 : Fin 5 → RateCap
  | 0 => { bound := (5/14 : ℚ), closed := true }
  | 1 => { bound := (2/7 : ℚ), closed := false }
  | 2 => { bound := (1/7 : ℚ), closed := false }
  | 3 => { bound := (1/7 : ℚ), closed := false }
  | 4 => { bound := (1/14 : ℚ), closed := true }

theorem periodicArray45_toList :
    periodicArray45.toList = words 45 := by rfl
theorem periodicCaps45_eq : periodicCaps45 = wordCaps 45 := by rfl

theorem periodicScan45_0 : ∀ s : Fin 14,
    prefixCheck 14 (by decide) periodicWord45
      (periodicCaps45 0) 0 s 14 0 0 = true := by
  decide +kernel

theorem periodicScan45_1 : ∀ s : Fin 14,
    prefixCheck 14 (by decide) periodicWord45
      (periodicCaps45 1) 1 s 14 0 0 = true := by
  decide +kernel

theorem periodicScan45_2 : ∀ s : Fin 14,
    prefixCheck 14 (by decide) periodicWord45
      (periodicCaps45 2) 2 s 14 0 0 = true := by
  decide +kernel

theorem periodicScan45_3 : ∀ s : Fin 14,
    prefixCheck 14 (by decide) periodicWord45
      (periodicCaps45 3) 3 s 14 0 0 = true := by
  decide +kernel

theorem periodicScan45_4 : ∀ s : Fin 14,
    prefixCheck 14 (by decide) periodicWord45
      (periodicCaps45 4) 4 s 14 0 0 = true := by
  decide +kernel

theorem periodicCertificate45 :
    WordCertificate 14 (by decide) periodicWord45 periodicCaps45 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan45_0
  · exact periodicScan45_1
  · exact periodicScan45_2
  · exact periodicScan45_3
  · exact periodicScan45_4

theorem schedulable_word45 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 45) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps45 r := by
    simpa only [periodicCaps45_eq] using hr
  exact ⟨periodic 14 (by decide) periodicWord45,
    validRates_periodic_of_wordCertificate (by decide) periodicWord45
      periodicCertificate45 hc⟩

-- Case 46: F1267; period 34.
def periodicArray46 : Array (Fin 5) := #[0, 1, 3, 0, 2, 1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 0, 2, 0, 1, 4, 0, 2, 1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 0, 2]
def periodicWord46 (k : Fin 34) : Fin 5 :=
  periodicArray46[k.val]
def periodicCaps46 : Fin 5 → RateCap
  | 0 => { bound := (6/17 : ℚ), closed := true }
  | 1 => { bound := (2/7 : ℚ), closed := false }
  | 2 => { bound := (1/4 : ℚ), closed := false }
  | 3 => { bound := (1/34 : ℚ), closed := true }
  | 4 => { bound := (1/34 : ℚ), closed := true }

theorem periodicArray46_toList :
    periodicArray46.toList = words 46 := by rfl
theorem periodicCaps46_eq : periodicCaps46 = wordCaps 46 := by rfl

theorem periodicScan46_0 : ∀ s : Fin 34,
    prefixCheck 34 (by decide) periodicWord46
      (periodicCaps46 0) 0 s 34 0 0 = true := by
  decide +kernel

theorem periodicScan46_1 : ∀ s : Fin 34,
    prefixCheck 34 (by decide) periodicWord46
      (periodicCaps46 1) 1 s 34 0 0 = true := by
  decide +kernel

theorem periodicScan46_2 : ∀ s : Fin 34,
    prefixCheck 34 (by decide) periodicWord46
      (periodicCaps46 2) 2 s 34 0 0 = true := by
  decide +kernel

theorem periodicScan46_3 : ∀ s : Fin 34,
    prefixCheck 34 (by decide) periodicWord46
      (periodicCaps46 3) 3 s 34 0 0 = true := by
  decide +kernel

theorem periodicScan46_4 : ∀ s : Fin 34,
    prefixCheck 34 (by decide) periodicWord46
      (periodicCaps46 4) 4 s 34 0 0 = true := by
  decide +kernel

theorem periodicCertificate46 :
    WordCertificate 34 (by decide) periodicWord46 periodicCaps46 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan46_0
  · exact periodicScan46_1
  · exact periodicScan46_2
  · exact periodicScan46_3
  · exact periodicScan46_4

theorem schedulable_word46 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 46) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps46 r := by
    simpa only [periodicCaps46_eq] using hr
  exact ⟨periodic 34 (by decide) periodicWord46,
    validRates_periodic_of_wordCertificate (by decide) periodicWord46
      periodicCertificate46 hc⟩

-- Case 47: F1303; period 37.
def periodicArray47 : Array (Fin 5) := #[0, 1, 0, 2, 1, 0, 1, 2, 0, 1, 3, 0, 2, 1, 0, 4, 1, 0, 2, 1, 0, 1, 2, 0, 1, 0, 2, 1, 0, 3, 1, 0, 2, 1, 0, 1, 2]
def periodicWord47 (k : Fin 37) : Fin 5 :=
  periodicArray47[k.val]
def periodicCaps47 : Fin 5 → RateCap
  | 0 => { bound := (7/20 : ℚ), closed := false }
  | 1 => { bound := (1/3 : ℚ), closed := false }
  | 2 => { bound := (1/5 : ℚ), closed := false }
  | 3 => { bound := (2/37 : ℚ), closed := true }
  | 4 => { bound := (1/37 : ℚ), closed := true }

theorem periodicArray47_toList :
    periodicArray47.toList = words 47 := by rfl
theorem periodicCaps47_eq : periodicCaps47 = wordCaps 47 := by rfl

theorem periodicScan47_0 : ∀ s : Fin 37,
    prefixCheck 37 (by decide) periodicWord47
      (periodicCaps47 0) 0 s 37 0 0 = true := by
  decide +kernel

theorem periodicScan47_1 : ∀ s : Fin 37,
    prefixCheck 37 (by decide) periodicWord47
      (periodicCaps47 1) 1 s 37 0 0 = true := by
  decide +kernel

theorem periodicScan47_2 : ∀ s : Fin 37,
    prefixCheck 37 (by decide) periodicWord47
      (periodicCaps47 2) 2 s 37 0 0 = true := by
  decide +kernel

theorem periodicScan47_3 : ∀ s : Fin 37,
    prefixCheck 37 (by decide) periodicWord47
      (periodicCaps47 3) 3 s 37 0 0 = true := by
  decide +kernel

theorem periodicScan47_4 : ∀ s : Fin 37,
    prefixCheck 37 (by decide) periodicWord47
      (periodicCaps47 4) 4 s 37 0 0 = true := by
  decide +kernel

theorem periodicCertificate47 :
    WordCertificate 37 (by decide) periodicWord47 periodicCaps47 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan47_0
  · exact periodicScan47_1
  · exact periodicScan47_2
  · exact periodicScan47_3
  · exact periodicScan47_4

theorem schedulable_word47 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 47) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps47 r := by
    simpa only [periodicCaps47_eq] using hr
  exact ⟨periodic 37 (by decide) periodicWord47,
    validRates_periodic_of_wordCertificate (by decide) periodicWord47
      periodicCertificate47 hc⟩

-- Case 48: F1393; period 15.
def periodicArray48 : Array (Fin 5) := #[0, 1, 3, 0, 2, 1, 0, 3, 4, 0, 2, 1, 0, 3, 2]
def periodicWord48 (k : Fin 15) : Fin 5 :=
  periodicArray48[k.val]
def periodicCaps48 : Fin 5 → RateCap
  | 0 => { bound := (1/3 : ℚ), closed := true }
  | 1 => { bound := (1/5 : ℚ), closed := false }
  | 2 => { bound := (1/5 : ℚ), closed := false }
  | 3 => { bound := (1/5 : ℚ), closed := false }
  | 4 => { bound := (1/15 : ℚ), closed := true }

theorem periodicArray48_toList :
    periodicArray48.toList = words 48 := by rfl
theorem periodicCaps48_eq : periodicCaps48 = wordCaps 48 := by rfl

theorem periodicScan48_0 : ∀ s : Fin 15,
    prefixCheck 15 (by decide) periodicWord48
      (periodicCaps48 0) 0 s 15 0 0 = true := by
  decide +kernel

theorem periodicScan48_1 : ∀ s : Fin 15,
    prefixCheck 15 (by decide) periodicWord48
      (periodicCaps48 1) 1 s 15 0 0 = true := by
  decide +kernel

theorem periodicScan48_2 : ∀ s : Fin 15,
    prefixCheck 15 (by decide) periodicWord48
      (periodicCaps48 2) 2 s 15 0 0 = true := by
  decide +kernel

theorem periodicScan48_3 : ∀ s : Fin 15,
    prefixCheck 15 (by decide) periodicWord48
      (periodicCaps48 3) 3 s 15 0 0 = true := by
  decide +kernel

theorem periodicScan48_4 : ∀ s : Fin 15,
    prefixCheck 15 (by decide) periodicWord48
      (periodicCaps48 4) 4 s 15 0 0 = true := by
  decide +kernel

theorem periodicCertificate48 :
    WordCertificate 15 (by decide) periodicWord48 periodicCaps48 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan48_0
  · exact periodicScan48_1
  · exact periodicScan48_2
  · exact periodicScan48_3
  · exact periodicScan48_4

theorem schedulable_word48 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 48) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps48 r := by
    simpa only [periodicCaps48_eq] using hr
  exact ⟨periodic 15 (by decide) periodicWord48,
    validRates_periodic_of_wordCertificate (by decide) periodicWord48
      periodicCertificate48 hc⟩

-- Case 49: F1420; period 60.
def periodicArray49 : Array (Fin 5) := #[0, 0, 1, 2, 0, 1, 2, 0, 3, 1, 0, 2, 1, 0, 2, 1, 4, 0, 2, 1, 0, 0, 1, 2, 3, 0, 1, 2, 0, 1, 0, 2, 1, 0, 2, 1, 0, 3, 2, 1, 0, 0, 1, 2, 0, 1, 4, 2, 0, 1, 0, 2, 1, 3, 0, 2, 1, 0, 2, 1]
def periodicWord49 (k : Fin 60) : Fin 5 :=
  periodicArray49[k.val]
def periodicCaps49 : Fin 5 → RateCap
  | 0 => { bound := (1/3 : ℚ), closed := false }
  | 1 => { bound := (3/10 : ℚ), closed := false }
  | 2 => { bound := (1/4 : ℚ), closed := false }
  | 3 => { bound := (3/46 : ℚ), closed := false }
  | 4 => { bound := (1/30 : ℚ), closed := true }

theorem periodicArray49_toList :
    periodicArray49.toList = words 49 := by rfl
theorem periodicCaps49_eq : periodicCaps49 = wordCaps 49 := by rfl

theorem periodicScan49_0 : ∀ s : Fin 60,
    prefixCheck 60 (by decide) periodicWord49
      (periodicCaps49 0) 0 s 60 0 0 = true := by
  decide +kernel

theorem periodicScan49_1 : ∀ s : Fin 60,
    prefixCheck 60 (by decide) periodicWord49
      (periodicCaps49 1) 1 s 60 0 0 = true := by
  decide +kernel

theorem periodicScan49_2 : ∀ s : Fin 60,
    prefixCheck 60 (by decide) periodicWord49
      (periodicCaps49 2) 2 s 60 0 0 = true := by
  decide +kernel

theorem periodicScan49_3 : ∀ s : Fin 60,
    prefixCheck 60 (by decide) periodicWord49
      (periodicCaps49 3) 3 s 60 0 0 = true := by
  decide +kernel

theorem periodicScan49_4 : ∀ s : Fin 60,
    prefixCheck 60 (by decide) periodicWord49
      (periodicCaps49 4) 4 s 60 0 0 = true := by
  decide +kernel

theorem periodicCertificate49 :
    WordCertificate 60 (by decide) periodicWord49 periodicCaps49 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan49_0
  · exact periodicScan49_1
  · exact periodicScan49_2
  · exact periodicScan49_3
  · exact periodicScan49_4

theorem schedulable_word49 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 49) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps49 r := by
    simpa only [periodicCaps49_eq] using hr
  exact ⟨periodic 60 (by decide) periodicWord49,
    validRates_periodic_of_wordCertificate (by decide) periodicWord49
      periodicCertificate49 hc⟩

-- Case 50: F1456; period 36.
def periodicArray50 : Array (Fin 5) := #[0, 1, 2, 0, 1, 2, 0, 3, 1, 0, 2, 1, 0, 4, 2, 1, 0, 2, 0, 1, 3, 0, 2, 1, 0, 2, 1, 0, 2, 1, 0, 3, 2, 1, 0, 2]
def periodicWord50 (k : Fin 36) : Fin 5 :=
  periodicArray50[k.val]
def periodicCaps50 : Fin 5 → RateCap
  | 0 => { bound := (1/3 : ℚ), closed := false }
  | 1 => { bound := (3/11 : ℚ), closed := false }
  | 2 => { bound := (1/4 : ℚ), closed := false }
  | 3 => { bound := (1/12 : ℚ), closed := false }
  | 4 => { bound := (1/36 : ℚ), closed := true }

theorem periodicArray50_toList :
    periodicArray50.toList = words 50 := by rfl
theorem periodicCaps50_eq : periodicCaps50 = wordCaps 50 := by rfl

theorem periodicScan50_0 : ∀ s : Fin 36,
    prefixCheck 36 (by decide) periodicWord50
      (periodicCaps50 0) 0 s 36 0 0 = true := by
  decide +kernel

theorem periodicScan50_1 : ∀ s : Fin 36,
    prefixCheck 36 (by decide) periodicWord50
      (periodicCaps50 1) 1 s 36 0 0 = true := by
  decide +kernel

theorem periodicScan50_2 : ∀ s : Fin 36,
    prefixCheck 36 (by decide) periodicWord50
      (periodicCaps50 2) 2 s 36 0 0 = true := by
  decide +kernel

theorem periodicScan50_3 : ∀ s : Fin 36,
    prefixCheck 36 (by decide) periodicWord50
      (periodicCaps50 3) 3 s 36 0 0 = true := by
  decide +kernel

theorem periodicScan50_4 : ∀ s : Fin 36,
    prefixCheck 36 (by decide) periodicWord50
      (periodicCaps50 4) 4 s 36 0 0 = true := by
  decide +kernel

theorem periodicCertificate50 :
    WordCertificate 36 (by decide) periodicWord50 periodicCaps50 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan50_0
  · exact periodicScan50_1
  · exact periodicScan50_2
  · exact periodicScan50_3
  · exact periodicScan50_4

theorem schedulable_word50 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 50) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps50 r := by
    simpa only [periodicCaps50_eq] using hr
  exact ⟨periodic 36 (by decide) periodicWord50,
    validRates_periodic_of_wordCertificate (by decide) periodicWord50
      periodicCertificate50 hc⟩

-- Case 51: F1458; period 18.
def periodicArray51 : Array (Fin 5) := #[0, 1, 0, 2, 3, 1, 0, 2, 0, 1, 4, 0, 2, 1, 3, 0, 1, 2]
def periodicWord51 (k : Fin 18) : Fin 5 :=
  periodicArray51[k.val]
def periodicCaps51 : Fin 5 → RateCap
  | 0 => { bound := (1/3 : ℚ), closed := false }
  | 1 => { bound := (3/11 : ℚ), closed := false }
  | 2 => { bound := (2/9 : ℚ), closed := false }
  | 3 => { bound := (1/9 : ℚ), closed := false }
  | 4 => { bound := (1/18 : ℚ), closed := true }

theorem periodicArray51_toList :
    periodicArray51.toList = words 51 := by rfl
theorem periodicCaps51_eq : periodicCaps51 = wordCaps 51 := by rfl

theorem periodicScan51_0 : ∀ s : Fin 18,
    prefixCheck 18 (by decide) periodicWord51
      (periodicCaps51 0) 0 s 18 0 0 = true := by
  decide +kernel

theorem periodicScan51_1 : ∀ s : Fin 18,
    prefixCheck 18 (by decide) periodicWord51
      (periodicCaps51 1) 1 s 18 0 0 = true := by
  decide +kernel

theorem periodicScan51_2 : ∀ s : Fin 18,
    prefixCheck 18 (by decide) periodicWord51
      (periodicCaps51 2) 2 s 18 0 0 = true := by
  decide +kernel

theorem periodicScan51_3 : ∀ s : Fin 18,
    prefixCheck 18 (by decide) periodicWord51
      (periodicCaps51 3) 3 s 18 0 0 = true := by
  decide +kernel

theorem periodicScan51_4 : ∀ s : Fin 18,
    prefixCheck 18 (by decide) periodicWord51
      (periodicCaps51 4) 4 s 18 0 0 = true := by
  decide +kernel

theorem periodicCertificate51 :
    WordCertificate 18 (by decide) periodicWord51 periodicCaps51 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan51_0
  · exact periodicScan51_1
  · exact periodicScan51_2
  · exact periodicScan51_3
  · exact periodicScan51_4

theorem schedulable_word51 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 51) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps51 r := by
    simpa only [periodicCaps51_eq] using hr
  exact ⟨periodic 18 (by decide) periodicWord51,
    validRates_periodic_of_wordCertificate (by decide) periodicWord51
      periodicCertificate51 hc⟩

-- Case 52: F1471; period 15.
def periodicArray52 : Array (Fin 5) := #[0, 1, 0, 2, 1, 0, 3, 2, 1, 0, 4, 0, 1, 2, 3]
def periodicWord52 (k : Fin 15) : Fin 5 :=
  periodicArray52[k.val]
def periodicCaps52 : Fin 5 → RateCap
  | 0 => { bound := (1/3 : ℚ), closed := false }
  | 1 => { bound := (4/15 : ℚ), closed := true }
  | 2 => { bound := (1/5 : ℚ), closed := false }
  | 3 => { bound := (2/15 : ℚ), closed := true }
  | 4 => { bound := (1/15 : ℚ), closed := true }

theorem periodicArray52_toList :
    periodicArray52.toList = words 52 := by rfl
theorem periodicCaps52_eq : periodicCaps52 = wordCaps 52 := by rfl

theorem periodicScan52_0 : ∀ s : Fin 15,
    prefixCheck 15 (by decide) periodicWord52
      (periodicCaps52 0) 0 s 15 0 0 = true := by
  decide +kernel

theorem periodicScan52_1 : ∀ s : Fin 15,
    prefixCheck 15 (by decide) periodicWord52
      (periodicCaps52 1) 1 s 15 0 0 = true := by
  decide +kernel

theorem periodicScan52_2 : ∀ s : Fin 15,
    prefixCheck 15 (by decide) periodicWord52
      (periodicCaps52 2) 2 s 15 0 0 = true := by
  decide +kernel

theorem periodicScan52_3 : ∀ s : Fin 15,
    prefixCheck 15 (by decide) periodicWord52
      (periodicCaps52 3) 3 s 15 0 0 = true := by
  decide +kernel

theorem periodicScan52_4 : ∀ s : Fin 15,
    prefixCheck 15 (by decide) periodicWord52
      (periodicCaps52 4) 4 s 15 0 0 = true := by
  decide +kernel

theorem periodicCertificate52 :
    WordCertificate 15 (by decide) periodicWord52 periodicCaps52 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan52_0
  · exact periodicScan52_1
  · exact periodicScan52_2
  · exact periodicScan52_3
  · exact periodicScan52_4

theorem schedulable_word52 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 52) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps52 r := by
    simpa only [periodicCaps52_eq] using hr
  exact ⟨periodic 15 (by decide) periodicWord52,
    validRates_periodic_of_wordCertificate (by decide) periodicWord52
      periodicCertificate52 hc⟩

-- Case 53: F1494; period 24.
def periodicArray53 : Array (Fin 5) := #[0, 1, 2, 0, 3, 1, 0, 2, 0, 1, 3, 0, 2, 1, 0, 3, 2, 1, 0, 4, 0, 2, 1, 3]
def periodicWord53 (k : Fin 24) : Fin 5 :=
  periodicArray53[k.val]
def periodicCaps53 : Fin 5 → RateCap
  | 0 => { bound := (1/3 : ℚ), closed := false }
  | 1 => { bound := (1/4 : ℚ), closed := false }
  | 2 => { bound := (5/24 : ℚ), closed := true }
  | 3 => { bound := (1/7 : ℚ), closed := false }
  | 4 => { bound := (1/24 : ℚ), closed := true }

theorem periodicArray53_toList :
    periodicArray53.toList = words 53 := by rfl
theorem periodicCaps53_eq : periodicCaps53 = wordCaps 53 := by rfl

theorem periodicScan53_0 : ∀ s : Fin 24,
    prefixCheck 24 (by decide) periodicWord53
      (periodicCaps53 0) 0 s 24 0 0 = true := by
  decide +kernel

theorem periodicScan53_1 : ∀ s : Fin 24,
    prefixCheck 24 (by decide) periodicWord53
      (periodicCaps53 1) 1 s 24 0 0 = true := by
  decide +kernel

theorem periodicScan53_2 : ∀ s : Fin 24,
    prefixCheck 24 (by decide) periodicWord53
      (periodicCaps53 2) 2 s 24 0 0 = true := by
  decide +kernel

theorem periodicScan53_3 : ∀ s : Fin 24,
    prefixCheck 24 (by decide) periodicWord53
      (periodicCaps53 3) 3 s 24 0 0 = true := by
  decide +kernel

theorem periodicScan53_4 : ∀ s : Fin 24,
    prefixCheck 24 (by decide) periodicWord53
      (periodicCaps53 4) 4 s 24 0 0 = true := by
  decide +kernel

theorem periodicCertificate53 :
    WordCertificate 24 (by decide) periodicWord53 periodicCaps53 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan53_0
  · exact periodicScan53_1
  · exact periodicScan53_2
  · exact periodicScan53_3
  · exact periodicScan53_4

theorem schedulable_word53 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 53) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps53 r := by
    simpa only [periodicCaps53_eq] using hr
  exact ⟨periodic 24 (by decide) periodicWord53,
    validRates_periodic_of_wordCertificate (by decide) periodicWord53
      periodicCertificate53 hc⟩

-- Case 54: F1496; period 30.
def periodicArray54 : Array (Fin 5) := #[0, 1, 0, 3, 2, 1, 0, 1, 2, 0, 3, 1, 0, 2, 0, 1, 3, 0, 2, 1, 0, 3, 1, 2, 0, 4, 1, 0, 3, 2]
def periodicWord54 (k : Fin 30) : Fin 5 :=
  periodicArray54[k.val]
def periodicCaps54 : Fin 5 → RateCap
  | 0 => { bound := (1/3 : ℚ), closed := false }
  | 1 => { bound := (1/4 : ℚ), closed := false }
  | 2 => { bound := (1/5 : ℚ), closed := false }
  | 3 => { bound := (1/6 : ℚ), closed := false }
  | 4 => { bound := (1/30 : ℚ), closed := true }

theorem periodicArray54_toList :
    periodicArray54.toList = words 54 := by rfl
theorem periodicCaps54_eq : periodicCaps54 = wordCaps 54 := by rfl

theorem periodicScan54_0 : ∀ s : Fin 30,
    prefixCheck 30 (by decide) periodicWord54
      (periodicCaps54 0) 0 s 30 0 0 = true := by
  decide +kernel

theorem periodicScan54_1 : ∀ s : Fin 30,
    prefixCheck 30 (by decide) periodicWord54
      (periodicCaps54 1) 1 s 30 0 0 = true := by
  decide +kernel

theorem periodicScan54_2 : ∀ s : Fin 30,
    prefixCheck 30 (by decide) periodicWord54
      (periodicCaps54 2) 2 s 30 0 0 = true := by
  decide +kernel

theorem periodicScan54_3 : ∀ s : Fin 30,
    prefixCheck 30 (by decide) periodicWord54
      (periodicCaps54 3) 3 s 30 0 0 = true := by
  decide +kernel

theorem periodicScan54_4 : ∀ s : Fin 30,
    prefixCheck 30 (by decide) periodicWord54
      (periodicCaps54 4) 4 s 30 0 0 = true := by
  decide +kernel

theorem periodicCertificate54 :
    WordCertificate 30 (by decide) periodicWord54 periodicCaps54 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan54_0
  · exact periodicScan54_1
  · exact periodicScan54_2
  · exact periodicScan54_3
  · exact periodicScan54_4

theorem schedulable_word54 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 54) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps54 r := by
    simpa only [periodicCaps54_eq] using hr
  exact ⟨periodic 30 (by decide) periodicWord54,
    validRates_periodic_of_wordCertificate (by decide) periodicWord54
      periodicCertificate54 hc⟩

-- Case 55: F1518; period 18.
def periodicArray55 : Array (Fin 5) := #[0, 1, 2, 0, 4, 3, 1, 0, 2, 0, 1, 3, 0, 4, 2, 1, 0, 3]
def periodicWord55 (k : Fin 18) : Fin 5 :=
  periodicArray55[k.val]
def periodicCaps55 : Fin 5 → RateCap
  | 0 => { bound := (1/3 : ℚ), closed := false }
  | 1 => { bound := (2/9 : ℚ), closed := true }
  | 2 => { bound := (1/6 : ℚ), closed := true }
  | 3 => { bound := (1/6 : ℚ), closed := true }
  | 4 => { bound := (1/9 : ℚ), closed := true }

theorem periodicArray55_toList :
    periodicArray55.toList = words 55 := by rfl
theorem periodicCaps55_eq : periodicCaps55 = wordCaps 55 := by rfl

theorem periodicScan55_0 : ∀ s : Fin 18,
    prefixCheck 18 (by decide) periodicWord55
      (periodicCaps55 0) 0 s 18 0 0 = true := by
  decide +kernel

theorem periodicScan55_1 : ∀ s : Fin 18,
    prefixCheck 18 (by decide) periodicWord55
      (periodicCaps55 1) 1 s 18 0 0 = true := by
  decide +kernel

theorem periodicScan55_2 : ∀ s : Fin 18,
    prefixCheck 18 (by decide) periodicWord55
      (periodicCaps55 2) 2 s 18 0 0 = true := by
  decide +kernel

theorem periodicScan55_3 : ∀ s : Fin 18,
    prefixCheck 18 (by decide) periodicWord55
      (periodicCaps55 3) 3 s 18 0 0 = true := by
  decide +kernel

theorem periodicScan55_4 : ∀ s : Fin 18,
    prefixCheck 18 (by decide) periodicWord55
      (periodicCaps55 4) 4 s 18 0 0 = true := by
  decide +kernel

theorem periodicCertificate55 :
    WordCertificate 18 (by decide) periodicWord55 periodicCaps55 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan55_0
  · exact periodicScan55_1
  · exact periodicScan55_2
  · exact periodicScan55_3
  · exact periodicScan55_4

theorem schedulable_word55 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 55) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps55 r := by
    simpa only [periodicCaps55_eq] using hr
  exact ⟨periodic 18 (by decide) periodicWord55,
    validRates_periodic_of_wordCertificate (by decide) periodicWord55
      periodicCertificate55 hc⟩

-- Case 56: F1529; period 24.
def periodicArray56 : Array (Fin 5) := #[0, 1, 0, 3, 2, 0, 1, 4, 0, 2, 3, 1, 0, 2, 0, 1, 3, 0, 2, 4, 1, 0, 3, 2]
def periodicWord56 (k : Fin 24) : Fin 5 :=
  periodicArray56[k.val]
def periodicCaps56 : Fin 5 → RateCap
  | 0 => { bound := (1/3 : ℚ), closed := false }
  | 1 => { bound := (5/24 : ℚ), closed := true }
  | 2 => { bound := (5/24 : ℚ), closed := true }
  | 3 => { bound := (1/6 : ℚ), closed := false }
  | 4 => { bound := (1/12 : ℚ), closed := true }

theorem periodicArray56_toList :
    periodicArray56.toList = words 56 := by rfl
theorem periodicCaps56_eq : periodicCaps56 = wordCaps 56 := by rfl

theorem periodicScan56_0 : ∀ s : Fin 24,
    prefixCheck 24 (by decide) periodicWord56
      (periodicCaps56 0) 0 s 24 0 0 = true := by
  decide +kernel

theorem periodicScan56_1 : ∀ s : Fin 24,
    prefixCheck 24 (by decide) periodicWord56
      (periodicCaps56 1) 1 s 24 0 0 = true := by
  decide +kernel

theorem periodicScan56_2 : ∀ s : Fin 24,
    prefixCheck 24 (by decide) periodicWord56
      (periodicCaps56 2) 2 s 24 0 0 = true := by
  decide +kernel

theorem periodicScan56_3 : ∀ s : Fin 24,
    prefixCheck 24 (by decide) periodicWord56
      (periodicCaps56 3) 3 s 24 0 0 = true := by
  decide +kernel

theorem periodicScan56_4 : ∀ s : Fin 24,
    prefixCheck 24 (by decide) periodicWord56
      (periodicCaps56 4) 4 s 24 0 0 = true := by
  decide +kernel

theorem periodicCertificate56 :
    WordCertificate 24 (by decide) periodicWord56 periodicCaps56 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan56_0
  · exact periodicScan56_1
  · exact periodicScan56_2
  · exact periodicScan56_3
  · exact periodicScan56_4

theorem schedulable_word56 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 56) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps56 r := by
    simpa only [periodicCaps56_eq] using hr
  exact ⟨periodic 24 (by decide) periodicWord56,
    validRates_periodic_of_wordCertificate (by decide) periodicWord56
      periodicCertificate56 hc⟩

-- Case 57: F1570; period 28.
def periodicArray57 : Array (Fin 5) := #[0, 1, 2, 0, 3, 1, 0, 2, 3, 0, 1, 2, 0, 3, 1, 0, 2, 3, 0, 1, 4, 2, 0, 3, 1, 0, 2, 3]
def periodicWord57 (k : Fin 28) : Fin 5 :=
  periodicArray57[k.val]
def periodicCaps57 : Fin 5 → RateCap
  | 0 => { bound := (9/28 : ℚ), closed := true }
  | 1 => { bound := (3/14 : ℚ), closed := false }
  | 2 => { bound := (3/14 : ℚ), closed := false }
  | 3 => { bound := (1/5 : ℚ), closed := false }
  | 4 => { bound := (1/28 : ℚ), closed := true }

theorem periodicArray57_toList :
    periodicArray57.toList = words 57 := by rfl
theorem periodicCaps57_eq : periodicCaps57 = wordCaps 57 := by rfl

theorem periodicScan57_0 : ∀ s : Fin 28,
    prefixCheck 28 (by decide) periodicWord57
      (periodicCaps57 0) 0 s 28 0 0 = true := by
  decide +kernel

theorem periodicScan57_1 : ∀ s : Fin 28,
    prefixCheck 28 (by decide) periodicWord57
      (periodicCaps57 1) 1 s 28 0 0 = true := by
  decide +kernel

theorem periodicScan57_2 : ∀ s : Fin 28,
    prefixCheck 28 (by decide) periodicWord57
      (periodicCaps57 2) 2 s 28 0 0 = true := by
  decide +kernel

theorem periodicScan57_3 : ∀ s : Fin 28,
    prefixCheck 28 (by decide) periodicWord57
      (periodicCaps57 3) 3 s 28 0 0 = true := by
  decide +kernel

theorem periodicScan57_4 : ∀ s : Fin 28,
    prefixCheck 28 (by decide) periodicWord57
      (periodicCaps57 4) 4 s 28 0 0 = true := by
  decide +kernel

theorem periodicCertificate57 :
    WordCertificate 28 (by decide) periodicWord57 periodicCaps57 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan57_0
  · exact periodicScan57_1
  · exact periodicScan57_2
  · exact periodicScan57_3
  · exact periodicScan57_4

theorem schedulable_word57 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 57) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps57 r := by
    simpa only [periodicCaps57_eq] using hr
  exact ⟨periodic 28 (by decide) periodicWord57,
    validRates_periodic_of_wordCertificate (by decide) periodicWord57
      periodicCertificate57 hc⟩

-- Case 58: F1620; period 16.
def periodicArray58 : Array (Fin 5) := #[0, 1, 2, 0, 1, 2, 0, 3, 1, 0, 2, 4, 1, 0, 2, 3]
def periodicWord58 (k : Fin 16) : Fin 5 :=
  periodicArray58[k.val]
def periodicCaps58 : Fin 5 → RateCap
  | 0 => { bound := (5/16 : ℚ), closed := true }
  | 1 => { bound := (1/4 : ℚ), closed := false }
  | 2 => { bound := (1/4 : ℚ), closed := false }
  | 3 => { bound := (1/8 : ℚ), closed := true }
  | 4 => { bound := (1/16 : ℚ), closed := true }

theorem periodicArray58_toList :
    periodicArray58.toList = words 58 := by rfl
theorem periodicCaps58_eq : periodicCaps58 = wordCaps 58 := by rfl

theorem periodicScan58_0 : ∀ s : Fin 16,
    prefixCheck 16 (by decide) periodicWord58
      (periodicCaps58 0) 0 s 16 0 0 = true := by
  decide +kernel

theorem periodicScan58_1 : ∀ s : Fin 16,
    prefixCheck 16 (by decide) periodicWord58
      (periodicCaps58 1) 1 s 16 0 0 = true := by
  decide +kernel

theorem periodicScan58_2 : ∀ s : Fin 16,
    prefixCheck 16 (by decide) periodicWord58
      (periodicCaps58 2) 2 s 16 0 0 = true := by
  decide +kernel

theorem periodicScan58_3 : ∀ s : Fin 16,
    prefixCheck 16 (by decide) periodicWord58
      (periodicCaps58 3) 3 s 16 0 0 = true := by
  decide +kernel

theorem periodicScan58_4 : ∀ s : Fin 16,
    prefixCheck 16 (by decide) periodicWord58
      (periodicCaps58 4) 4 s 16 0 0 = true := by
  decide +kernel

theorem periodicCertificate58 :
    WordCertificate 16 (by decide) periodicWord58 periodicCaps58 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan58_0
  · exact periodicScan58_1
  · exact periodicScan58_2
  · exact periodicScan58_3
  · exact periodicScan58_4

theorem schedulable_word58 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 58) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps58 r := by
    simpa only [periodicCaps58_eq] using hr
  exact ⟨periodic 16 (by decide) periodicWord58,
    validRates_periodic_of_wordCertificate (by decide) periodicWord58
      periodicCertificate58 hc⟩

-- Case 59: F1692; period 20.
def periodicArray59 : Array (Fin 5) := #[0, 1, 2, 0, 1, 3, 0, 2, 1, 0, 1, 3, 2, 0, 1, 4, 0, 1, 2, 3]
def periodicWord59 (k : Fin 20) : Fin 5 :=
  periodicArray59[k.val]
def periodicCaps59 : Fin 5 → RateCap
  | 0 => { bound := (3/10 : ℚ), closed := false }
  | 1 => { bound := (5/17 : ℚ), closed := false }
  | 2 => { bound := (1/5 : ℚ), closed := false }
  | 3 => { bound := (1/7 : ℚ), closed := false }
  | 4 => { bound := (1/20 : ℚ), closed := true }

theorem periodicArray59_toList :
    periodicArray59.toList = words 59 := by rfl
theorem periodicCaps59_eq : periodicCaps59 = wordCaps 59 := by rfl

theorem periodicScan59_0 : ∀ s : Fin 20,
    prefixCheck 20 (by decide) periodicWord59
      (periodicCaps59 0) 0 s 20 0 0 = true := by
  decide +kernel

theorem periodicScan59_1 : ∀ s : Fin 20,
    prefixCheck 20 (by decide) periodicWord59
      (periodicCaps59 1) 1 s 20 0 0 = true := by
  decide +kernel

theorem periodicScan59_2 : ∀ s : Fin 20,
    prefixCheck 20 (by decide) periodicWord59
      (periodicCaps59 2) 2 s 20 0 0 = true := by
  decide +kernel

theorem periodicScan59_3 : ∀ s : Fin 20,
    prefixCheck 20 (by decide) periodicWord59
      (periodicCaps59 3) 3 s 20 0 0 = true := by
  decide +kernel

theorem periodicScan59_4 : ∀ s : Fin 20,
    prefixCheck 20 (by decide) periodicWord59
      (periodicCaps59 4) 4 s 20 0 0 = true := by
  decide +kernel

theorem periodicCertificate59 :
    WordCertificate 20 (by decide) periodicWord59 periodicCaps59 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan59_0
  · exact periodicScan59_1
  · exact periodicScan59_2
  · exact periodicScan59_3
  · exact periodicScan59_4

theorem schedulable_word59 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 59) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps59 r := by
    simpa only [periodicCaps59_eq] using hr
  exact ⟨periodic 20 (by decide) periodicWord59,
    validRates_periodic_of_wordCertificate (by decide) periodicWord59
      periodicCertificate59 hc⟩

-- Case 60: F1708; period 23.
def periodicArray60 : Array (Fin 5) := #[0, 1, 2, 0, 3, 1, 0, 4, 2, 1, 0, 3, 1, 0, 2, 3, 1, 0, 4, 2, 0, 1, 3]
def periodicWord60 (k : Fin 23) : Fin 5 :=
  periodicArray60[k.val]
def periodicCaps60 : Fin 5 → RateCap
  | 0 => { bound := (3/10 : ℚ), closed := false }
  | 1 => { bound := (1/4 : ℚ), closed := false }
  | 2 => { bound := (4/23 : ℚ), closed := true }
  | 3 => { bound := (1/6 : ℚ), closed := false }
  | 4 => { bound := (2/23 : ℚ), closed := true }

theorem periodicArray60_toList :
    periodicArray60.toList = words 60 := by rfl
theorem periodicCaps60_eq : periodicCaps60 = wordCaps 60 := by rfl

theorem periodicScan60_0 : ∀ s : Fin 23,
    prefixCheck 23 (by decide) periodicWord60
      (periodicCaps60 0) 0 s 23 0 0 = true := by
  decide +kernel

theorem periodicScan60_1 : ∀ s : Fin 23,
    prefixCheck 23 (by decide) periodicWord60
      (periodicCaps60 1) 1 s 23 0 0 = true := by
  decide +kernel

theorem periodicScan60_2 : ∀ s : Fin 23,
    prefixCheck 23 (by decide) periodicWord60
      (periodicCaps60 2) 2 s 23 0 0 = true := by
  decide +kernel

theorem periodicScan60_3 : ∀ s : Fin 23,
    prefixCheck 23 (by decide) periodicWord60
      (periodicCaps60 3) 3 s 23 0 0 = true := by
  decide +kernel

theorem periodicScan60_4 : ∀ s : Fin 23,
    prefixCheck 23 (by decide) periodicWord60
      (periodicCaps60 4) 4 s 23 0 0 = true := by
  decide +kernel

theorem periodicCertificate60 :
    WordCertificate 23 (by decide) periodicWord60 periodicCaps60 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan60_0
  · exact periodicScan60_1
  · exact periodicScan60_2
  · exact periodicScan60_3
  · exact periodicScan60_4

theorem schedulable_word60 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 60) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps60 r := by
    simpa only [periodicCaps60_eq] using hr
  exact ⟨periodic 23 (by decide) periodicWord60,
    validRates_periodic_of_wordCertificate (by decide) periodicWord60
      periodicCertificate60 hc⟩

-- Case 61: F1766; period 21.
def periodicArray61 : Array (Fin 5) := #[0, 1, 2, 0, 3, 1, 0, 2, 1, 3, 0, 4, 1, 2, 0, 3, 1, 0, 2, 1, 3]
def periodicWord61 (k : Fin 21) : Fin 5 :=
  periodicArray61[k.val]
def periodicCaps61 : Fin 5 → RateCap
  | 0 => { bound := (2/7 : ℚ), closed := false }
  | 1 => { bound := (2/7 : ℚ), closed := false }
  | 2 => { bound := (4/21 : ℚ), closed := true }
  | 3 => { bound := (4/21 : ℚ), closed := true }
  | 4 => { bound := (1/21 : ℚ), closed := true }

theorem periodicArray61_toList :
    periodicArray61.toList = words 61 := by rfl
theorem periodicCaps61_eq : periodicCaps61 = wordCaps 61 := by rfl

theorem periodicScan61_0 : ∀ s : Fin 21,
    prefixCheck 21 (by decide) periodicWord61
      (periodicCaps61 0) 0 s 21 0 0 = true := by
  decide +kernel

theorem periodicScan61_1 : ∀ s : Fin 21,
    prefixCheck 21 (by decide) periodicWord61
      (periodicCaps61 1) 1 s 21 0 0 = true := by
  decide +kernel

theorem periodicScan61_2 : ∀ s : Fin 21,
    prefixCheck 21 (by decide) periodicWord61
      (periodicCaps61 2) 2 s 21 0 0 = true := by
  decide +kernel

theorem periodicScan61_3 : ∀ s : Fin 21,
    prefixCheck 21 (by decide) periodicWord61
      (periodicCaps61 3) 3 s 21 0 0 = true := by
  decide +kernel

theorem periodicScan61_4 : ∀ s : Fin 21,
    prefixCheck 21 (by decide) periodicWord61
      (periodicCaps61 4) 4 s 21 0 0 = true := by
  decide +kernel

theorem periodicCertificate61 :
    WordCertificate 21 (by decide) periodicWord61 periodicCaps61 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan61_0
  · exact periodicScan61_1
  · exact periodicScan61_2
  · exact periodicScan61_3
  · exact periodicScan61_4

theorem schedulable_word61 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 61) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps61 r := by
    simpa only [periodicCaps61_eq] using hr
  exact ⟨periodic 21 (by decide) periodicWord61,
    validRates_periodic_of_wordCertificate (by decide) periodicWord61
      periodicCertificate61 hc⟩

-- Case 62: F1787; period 24.
def periodicArray62 : Array (Fin 5) := #[0, 1, 2, 0, 1, 3, 0, 2, 1, 4, 0, 3, 2, 1, 0, 2, 1, 0, 3, 2, 1, 0, 2, 3]
def periodicWord62 (k : Fin 24) : Fin 5 :=
  periodicArray62[k.val]
def periodicCaps62 : Fin 5 → RateCap
  | 0 => { bound := (2/7 : ℚ), closed := false }
  | 1 => { bound := (1/4 : ℚ), closed := false }
  | 2 => { bound := (2/9 : ℚ), closed := false }
  | 3 => { bound := (1/6 : ℚ), closed := false }
  | 4 => { bound := (1/24 : ℚ), closed := true }

theorem periodicArray62_toList :
    periodicArray62.toList = words 62 := by rfl
theorem periodicCaps62_eq : periodicCaps62 = wordCaps 62 := by rfl

theorem periodicScan62_0 : ∀ s : Fin 24,
    prefixCheck 24 (by decide) periodicWord62
      (periodicCaps62 0) 0 s 24 0 0 = true := by
  decide +kernel

theorem periodicScan62_1 : ∀ s : Fin 24,
    prefixCheck 24 (by decide) periodicWord62
      (periodicCaps62 1) 1 s 24 0 0 = true := by
  decide +kernel

theorem periodicScan62_2 : ∀ s : Fin 24,
    prefixCheck 24 (by decide) periodicWord62
      (periodicCaps62 2) 2 s 24 0 0 = true := by
  decide +kernel

theorem periodicScan62_3 : ∀ s : Fin 24,
    prefixCheck 24 (by decide) periodicWord62
      (periodicCaps62 3) 3 s 24 0 0 = true := by
  decide +kernel

theorem periodicScan62_4 : ∀ s : Fin 24,
    prefixCheck 24 (by decide) periodicWord62
      (periodicCaps62 4) 4 s 24 0 0 = true := by
  decide +kernel

theorem periodicCertificate62 :
    WordCertificate 24 (by decide) periodicWord62 periodicCaps62 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan62_0
  · exact periodicScan62_1
  · exact periodicScan62_2
  · exact periodicScan62_3
  · exact periodicScan62_4

theorem schedulable_word62 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 62) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps62 r := by
    simpa only [periodicCaps62_eq] using hr
  exact ⟨periodic 24 (by decide) periodicWord62,
    validRates_periodic_of_wordCertificate (by decide) periodicWord62
      periodicCertificate62 hc⟩

-- Case 63: F1848; period 18.
def periodicArray63 : Array (Fin 5) := #[0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 4, 2, 0, 3, 1, 0, 2, 3]
def periodicWord63 (k : Fin 18) : Fin 5 :=
  periodicArray63[k.val]
def periodicCaps63 : Fin 5 → RateCap
  | 0 => { bound := (3/11 : ℚ), closed := false }
  | 1 => { bound := (2/9 : ℚ), closed := false }
  | 2 => { bound := (2/9 : ℚ), closed := false }
  | 3 => { bound := (1/5 : ℚ), closed := false }
  | 4 => { bound := (1/18 : ℚ), closed := true }

theorem periodicArray63_toList :
    periodicArray63.toList = words 63 := by rfl
theorem periodicCaps63_eq : periodicCaps63 = wordCaps 63 := by rfl

theorem periodicScan63_0 : ∀ s : Fin 18,
    prefixCheck 18 (by decide) periodicWord63
      (periodicCaps63 0) 0 s 18 0 0 = true := by
  decide +kernel

theorem periodicScan63_1 : ∀ s : Fin 18,
    prefixCheck 18 (by decide) periodicWord63
      (periodicCaps63 1) 1 s 18 0 0 = true := by
  decide +kernel

theorem periodicScan63_2 : ∀ s : Fin 18,
    prefixCheck 18 (by decide) periodicWord63
      (periodicCaps63 2) 2 s 18 0 0 = true := by
  decide +kernel

theorem periodicScan63_3 : ∀ s : Fin 18,
    prefixCheck 18 (by decide) periodicWord63
      (periodicCaps63 3) 3 s 18 0 0 = true := by
  decide +kernel

theorem periodicScan63_4 : ∀ s : Fin 18,
    prefixCheck 18 (by decide) periodicWord63
      (periodicCaps63 4) 4 s 18 0 0 = true := by
  decide +kernel

theorem periodicCertificate63 :
    WordCertificate 18 (by decide) periodicWord63 periodicCaps63 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan63_0
  · exact periodicScan63_1
  · exact periodicScan63_2
  · exact periodicScan63_3
  · exact periodicScan63_4

theorem schedulable_word63 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 63) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps63 r := by
    simpa only [periodicCaps63_eq] using hr
  exact ⟨periodic 18 (by decide) periodicWord63,
    validRates_periodic_of_wordCertificate (by decide) periodicWord63
      periodicCertificate63 hc⟩

-- Case 64: F1870; period 19.
def periodicArray64 : Array (Fin 5) := #[0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 4, 2, 0, 3, 1, 0, 2, 1, 3]
def periodicWord64 (k : Fin 19) : Fin 5 :=
  periodicArray64[k.val]
def periodicCaps64 : Fin 5 → RateCap
  | 0 => { bound := (5/19 : ℚ), closed := true }
  | 1 => { bound := (1/4 : ℚ), closed := false }
  | 2 => { bound := (4/19 : ℚ), closed := true }
  | 3 => { bound := (1/5 : ℚ), closed := false }
  | 4 => { bound := (1/19 : ℚ), closed := true }

theorem periodicArray64_toList :
    periodicArray64.toList = words 64 := by rfl
theorem periodicCaps64_eq : periodicCaps64 = wordCaps 64 := by rfl

theorem periodicScan64_0 : ∀ s : Fin 19,
    prefixCheck 19 (by decide) periodicWord64
      (periodicCaps64 0) 0 s 19 0 0 = true := by
  decide +kernel

theorem periodicScan64_1 : ∀ s : Fin 19,
    prefixCheck 19 (by decide) periodicWord64
      (periodicCaps64 1) 1 s 19 0 0 = true := by
  decide +kernel

theorem periodicScan64_2 : ∀ s : Fin 19,
    prefixCheck 19 (by decide) periodicWord64
      (periodicCaps64 2) 2 s 19 0 0 = true := by
  decide +kernel

theorem periodicScan64_3 : ∀ s : Fin 19,
    prefixCheck 19 (by decide) periodicWord64
      (periodicCaps64 3) 3 s 19 0 0 = true := by
  decide +kernel

theorem periodicScan64_4 : ∀ s : Fin 19,
    prefixCheck 19 (by decide) periodicWord64
      (periodicCaps64 4) 4 s 19 0 0 = true := by
  decide +kernel

theorem periodicCertificate64 :
    WordCertificate 19 (by decide) periodicWord64 periodicCaps64 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan64_0
  · exact periodicScan64_1
  · exact periodicScan64_2
  · exact periodicScan64_3
  · exact periodicScan64_4

theorem schedulable_word64 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 64) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps64 r := by
    simpa only [periodicCaps64_eq] using hr
  exact ⟨periodic 19 (by decide) periodicWord64,
    validRates_periodic_of_wordCertificate (by decide) periodicWord64
      periodicCertificate64 hc⟩

-- Case 65: F1887; period 12.
def periodicArray65 : Array (Fin 5) := #[0, 2, 3, 1, 0, 2, 4, 1, 0, 3, 2, 1]
def periodicWord65 (k : Fin 12) : Fin 5 :=
  periodicArray65[k.val]
def periodicCaps65 : Fin 5 → RateCap
  | 0 => { bound := (1/4 : ℚ), closed := true }
  | 1 => { bound := (1/4 : ℚ), closed := true }
  | 2 => { bound := (1/4 : ℚ), closed := false }
  | 3 => { bound := (1/6 : ℚ), closed := false }
  | 4 => { bound := (1/12 : ℚ), closed := true }

theorem periodicArray65_toList :
    periodicArray65.toList = words 65 := by rfl
theorem periodicCaps65_eq : periodicCaps65 = wordCaps 65 := by rfl

theorem periodicScan65_0 : ∀ s : Fin 12,
    prefixCheck 12 (by decide) periodicWord65
      (periodicCaps65 0) 0 s 12 0 0 = true := by
  decide +kernel

theorem periodicScan65_1 : ∀ s : Fin 12,
    prefixCheck 12 (by decide) periodicWord65
      (periodicCaps65 1) 1 s 12 0 0 = true := by
  decide +kernel

theorem periodicScan65_2 : ∀ s : Fin 12,
    prefixCheck 12 (by decide) periodicWord65
      (periodicCaps65 2) 2 s 12 0 0 = true := by
  decide +kernel

theorem periodicScan65_3 : ∀ s : Fin 12,
    prefixCheck 12 (by decide) periodicWord65
      (periodicCaps65 3) 3 s 12 0 0 = true := by
  decide +kernel

theorem periodicScan65_4 : ∀ s : Fin 12,
    prefixCheck 12 (by decide) periodicWord65
      (periodicCaps65 4) 4 s 12 0 0 = true := by
  decide +kernel

theorem periodicCertificate65 :
    WordCertificate 12 (by decide) periodicWord65 periodicCaps65 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan65_0
  · exact periodicScan65_1
  · exact periodicScan65_2
  · exact periodicScan65_3
  · exact periodicScan65_4

theorem schedulable_word65 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 65) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps65 r := by
    simpa only [periodicCaps65_eq] using hr
  exact ⟨periodic 12 (by decide) periodicWord65,
    validRates_periodic_of_wordCertificate (by decide) periodicWord65
      periodicCertificate65 hc⟩

-- Case 66: Q02_4; period 100.
def periodicArray66 : Array (Fin 5) := #[0, 0, 0, 1, 0, 2, 0, 0, 1, 0, 1, 0, 2, 0, 0, 1, 0, 0, 2, 0, 1, 0, 0, 2, 0, 1, 0, 0, 2, 0, 1, 0, 0, 1, 0, 2, 0, 0, 1, 0, 2, 0, 3, 0, 1, 0, 0, 2, 0, 1, 0, 0, 0, 1, 0, 2, 0, 0, 1, 0, 1, 0, 2, 0, 0, 1, 0, 0, 2, 0, 1, 0, 0, 2, 0, 1, 0, 0, 2, 0, 1, 0, 0, 1, 0, 2, 0, 0, 1, 0, 2, 0, 4, 0, 1, 0, 0, 2, 0, 1]
def periodicWord66 (k : Fin 100) : Fin 5 :=
  periodicArray66[k.val]
def periodicCaps66 : Fin 5 → RateCap
  | 0 => { bound := (4/7 : ℚ), closed := false }
  | 1 => { bound := (1/5 : ℚ), closed := false }
  | 2 => { bound := (1/7 : ℚ), closed := false }
  | 3 => { bound := (1/100 : ℚ), closed := true }
  | 4 => { bound := (1/100 : ℚ), closed := true }

theorem periodicArray66_toList :
    periodicArray66.toList = words 66 := by rfl
theorem periodicCaps66_eq : periodicCaps66 = wordCaps 66 := by rfl

theorem periodicScan66_0 : ∀ s : Fin 100,
    prefixCheck 100 (by decide) periodicWord66
      (periodicCaps66 0) 0 s 100 0 0 = true := by
  decide +kernel

theorem periodicScan66_1 : ∀ s : Fin 100,
    prefixCheck 100 (by decide) periodicWord66
      (periodicCaps66 1) 1 s 100 0 0 = true := by
  decide +kernel

theorem periodicScan66_2 : ∀ s : Fin 100,
    prefixCheck 100 (by decide) periodicWord66
      (periodicCaps66 2) 2 s 100 0 0 = true := by
  decide +kernel

theorem periodicScan66_3 : ∀ s : Fin 100,
    prefixCheck 100 (by decide) periodicWord66
      (periodicCaps66 3) 3 s 100 0 0 = true := by
  decide +kernel

theorem periodicScan66_4 : ∀ s : Fin 100,
    prefixCheck 100 (by decide) periodicWord66
      (periodicCaps66 4) 4 s 100 0 0 = true := by
  decide +kernel

theorem periodicCertificate66 :
    WordCertificate 100 (by decide) periodicWord66 periodicCaps66 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan66_0
  · exact periodicScan66_1
  · exact periodicScan66_2
  · exact periodicScan66_3
  · exact periodicScan66_4

theorem schedulable_word66 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 66) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps66 r := by
    simpa only [periodicCaps66_eq] using hr
  exact ⟨periodic 100 (by decide) periodicWord66,
    validRates_periodic_of_wordCertificate (by decide) periodicWord66
      periodicCertificate66 hc⟩

-- Case 67: Q04_3; period 22.
def periodicArray67 : Array (Fin 5) := #[0, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1]
def periodicWord67 (k : Fin 22) : Fin 5 :=
  periodicArray67[k.val]
def periodicCaps67 : Fin 5 → RateCap
  | 0 => { bound := (6/11 : ℚ), closed := true }
  | 1 => { bound := (3/11 : ℚ), closed := true }
  | 2 => { bound := (1/11 : ℚ), closed := true }
  | 3 => { bound := (1/22 : ℚ), closed := true }
  | 4 => { bound := (1/22 : ℚ), closed := true }

theorem periodicArray67_toList :
    periodicArray67.toList = words 67 := by rfl
theorem periodicCaps67_eq : periodicCaps67 = wordCaps 67 := by rfl

theorem periodicScan67_0 : ∀ s : Fin 22,
    prefixCheck 22 (by decide) periodicWord67
      (periodicCaps67 0) 0 s 22 0 0 = true := by
  decide +kernel

theorem periodicScan67_1 : ∀ s : Fin 22,
    prefixCheck 22 (by decide) periodicWord67
      (periodicCaps67 1) 1 s 22 0 0 = true := by
  decide +kernel

theorem periodicScan67_2 : ∀ s : Fin 22,
    prefixCheck 22 (by decide) periodicWord67
      (periodicCaps67 2) 2 s 22 0 0 = true := by
  decide +kernel

theorem periodicScan67_3 : ∀ s : Fin 22,
    prefixCheck 22 (by decide) periodicWord67
      (periodicCaps67 3) 3 s 22 0 0 = true := by
  decide +kernel

theorem periodicScan67_4 : ∀ s : Fin 22,
    prefixCheck 22 (by decide) periodicWord67
      (periodicCaps67 4) 4 s 22 0 0 = true := by
  decide +kernel

theorem periodicCertificate67 :
    WordCertificate 22 (by decide) periodicWord67 periodicCaps67 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan67_0
  · exact periodicScan67_1
  · exact periodicScan67_2
  · exact periodicScan67_3
  · exact periodicScan67_4

theorem schedulable_word67 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 67) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps67 r := by
    simpa only [periodicCaps67_eq] using hr
  exact ⟨periodic 22 (by decide) periodicWord67,
    validRates_periodic_of_wordCertificate (by decide) periodicWord67
      periodicCertificate67 hc⟩

-- Case 68: Q05_4; period 30.
def periodicArray68 : Array (Fin 5) := #[0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 0, 1, 0, 2, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1]
def periodicWord68 (k : Fin 30) : Fin 5 :=
  periodicArray68[k.val]
def periodicCaps68 : Fin 5 → RateCap
  | 0 => { bound := (8/15 : ℚ), closed := true }
  | 1 => { bound := (4/15 : ℚ), closed := true }
  | 2 => { bound := (2/15 : ℚ), closed := true }
  | 3 => { bound := (1/30 : ℚ), closed := true }
  | 4 => { bound := (1/30 : ℚ), closed := true }

theorem periodicArray68_toList :
    periodicArray68.toList = words 68 := by rfl
theorem periodicCaps68_eq : periodicCaps68 = wordCaps 68 := by rfl

theorem periodicScan68_0 : ∀ s : Fin 30,
    prefixCheck 30 (by decide) periodicWord68
      (periodicCaps68 0) 0 s 30 0 0 = true := by
  decide +kernel

theorem periodicScan68_1 : ∀ s : Fin 30,
    prefixCheck 30 (by decide) periodicWord68
      (periodicCaps68 1) 1 s 30 0 0 = true := by
  decide +kernel

theorem periodicScan68_2 : ∀ s : Fin 30,
    prefixCheck 30 (by decide) periodicWord68
      (periodicCaps68 2) 2 s 30 0 0 = true := by
  decide +kernel

theorem periodicScan68_3 : ∀ s : Fin 30,
    prefixCheck 30 (by decide) periodicWord68
      (periodicCaps68 3) 3 s 30 0 0 = true := by
  decide +kernel

theorem periodicScan68_4 : ∀ s : Fin 30,
    prefixCheck 30 (by decide) periodicWord68
      (periodicCaps68 4) 4 s 30 0 0 = true := by
  decide +kernel

theorem periodicCertificate68 :
    WordCertificate 30 (by decide) periodicWord68 periodicCaps68 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan68_0
  · exact periodicScan68_1
  · exact periodicScan68_2
  · exact periodicScan68_3
  · exact periodicScan68_4

theorem schedulable_word68 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 68) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps68 r := by
    simpa only [periodicCaps68_eq] using hr
  exact ⟨periodic 30 (by decide) periodicWord68,
    validRates_periodic_of_wordCertificate (by decide) periodicWord68
      periodicCertificate68 hc⟩

-- Case 69: Q06_3; period 24.
def periodicArray69 : Array (Fin 5) := #[0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 4]
def periodicWord69 (k : Fin 24) : Fin 5 :=
  periodicArray69[k.val]
def periodicCaps69 : Fin 5 → RateCap
  | 0 => { bound := (1/2 : ℚ), closed := true }
  | 1 => { bound := (1/3 : ℚ), closed := false }
  | 2 => { bound := (1/12 : ℚ), closed := true }
  | 3 => { bound := (1/24 : ℚ), closed := true }
  | 4 => { bound := (1/24 : ℚ), closed := true }

theorem periodicArray69_toList :
    periodicArray69.toList = words 69 := by rfl
theorem periodicCaps69_eq : periodicCaps69 = wordCaps 69 := by rfl

theorem periodicScan69_0 : ∀ s : Fin 24,
    prefixCheck 24 (by decide) periodicWord69
      (periodicCaps69 0) 0 s 24 0 0 = true := by
  decide +kernel

theorem periodicScan69_1 : ∀ s : Fin 24,
    prefixCheck 24 (by decide) periodicWord69
      (periodicCaps69 1) 1 s 24 0 0 = true := by
  decide +kernel

theorem periodicScan69_2 : ∀ s : Fin 24,
    prefixCheck 24 (by decide) periodicWord69
      (periodicCaps69 2) 2 s 24 0 0 = true := by
  decide +kernel

theorem periodicScan69_3 : ∀ s : Fin 24,
    prefixCheck 24 (by decide) periodicWord69
      (periodicCaps69 3) 3 s 24 0 0 = true := by
  decide +kernel

theorem periodicScan69_4 : ∀ s : Fin 24,
    prefixCheck 24 (by decide) periodicWord69
      (periodicCaps69 4) 4 s 24 0 0 = true := by
  decide +kernel

theorem periodicCertificate69 :
    WordCertificate 24 (by decide) periodicWord69 periodicCaps69 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan69_0
  · exact periodicScan69_1
  · exact periodicScan69_2
  · exact periodicScan69_3
  · exact periodicScan69_4

theorem schedulable_word69 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 69) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps69 r := by
    simpa only [periodicCaps69_eq] using hr
  exact ⟨periodic 24 (by decide) periodicWord69,
    validRates_periodic_of_wordCertificate (by decide) periodicWord69
      periodicCertificate69 hc⟩

-- Case 70: Q21_4; period 50.
def periodicArray70 : Array (Fin 5) := #[0, 0, 1, 2, 0, 1, 0, 1, 2, 0, 1, 0, 2, 0, 1, 2, 0, 1, 2, 0, 1, 3, 0, 2, 1, 0, 0, 1, 2, 0, 1, 0, 1, 2, 0, 1, 0, 2, 0, 1, 2, 0, 1, 2, 0, 1, 4, 0, 2, 1]
def periodicWord70 (k : Fin 50) : Fin 5 :=
  periodicArray70[k.val]
def periodicCaps70 : Fin 5 → RateCap
  | 0 => { bound := (4/11 : ℚ), closed := false }
  | 1 => { bound := (4/13 : ℚ), closed := false }
  | 2 => { bound := (3/14 : ℚ), closed := false }
  | 3 => { bound := (1/50 : ℚ), closed := true }
  | 4 => { bound := (1/50 : ℚ), closed := true }

theorem periodicArray70_toList :
    periodicArray70.toList = words 70 := by rfl
theorem periodicCaps70_eq : periodicCaps70 = wordCaps 70 := by rfl

theorem periodicScan70_0 : ∀ s : Fin 50,
    prefixCheck 50 (by decide) periodicWord70
      (periodicCaps70 0) 0 s 50 0 0 = true := by
  decide +kernel

theorem periodicScan70_1 : ∀ s : Fin 50,
    prefixCheck 50 (by decide) periodicWord70
      (periodicCaps70 1) 1 s 50 0 0 = true := by
  decide +kernel

theorem periodicScan70_2 : ∀ s : Fin 50,
    prefixCheck 50 (by decide) periodicWord70
      (periodicCaps70 2) 2 s 50 0 0 = true := by
  decide +kernel

theorem periodicScan70_3 : ∀ s : Fin 50,
    prefixCheck 50 (by decide) periodicWord70
      (periodicCaps70 3) 3 s 50 0 0 = true := by
  decide +kernel

theorem periodicScan70_4 : ∀ s : Fin 50,
    prefixCheck 50 (by decide) periodicWord70
      (periodicCaps70 4) 4 s 50 0 0 = true := by
  decide +kernel

theorem periodicCertificate70 :
    WordCertificate 50 (by decide) periodicWord70 periodicCaps70 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan70_0
  · exact periodicScan70_1
  · exact periodicScan70_2
  · exact periodicScan70_3
  · exact periodicScan70_4

theorem schedulable_word70 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 70) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps70 r := by
    simpa only [periodicCaps70_eq] using hr
  exact ⟨periodic 50 (by decide) periodicWord70,
    validRates_periodic_of_wordCertificate (by decide) periodicWord70
      periodicCertificate70 hc⟩

-- Case 71: Q25_4; period 26.
def periodicArray71 : Array (Fin 5) := #[0, 1, 0, 1, 0, 2, 0, 1, 3, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 4, 0, 1, 0, 2]
def periodicWord71 (k : Fin 26) : Fin 5 :=
  periodicArray71[k.val]
def periodicCaps71 : Fin 5 → RateCap
  | 0 => { bound := (6/13 : ℚ), closed := true }
  | 1 => { bound := (3/10 : ℚ), closed := false }
  | 2 => { bound := (2/13 : ℚ), closed := true }
  | 3 => { bound := (1/26 : ℚ), closed := true }
  | 4 => { bound := (1/26 : ℚ), closed := true }

theorem periodicArray71_toList :
    periodicArray71.toList = words 71 := by rfl
theorem periodicCaps71_eq : periodicCaps71 = wordCaps 71 := by rfl

theorem periodicScan71_0 : ∀ s : Fin 26,
    prefixCheck 26 (by decide) periodicWord71
      (periodicCaps71 0) 0 s 26 0 0 = true := by
  decide +kernel

theorem periodicScan71_1 : ∀ s : Fin 26,
    prefixCheck 26 (by decide) periodicWord71
      (periodicCaps71 1) 1 s 26 0 0 = true := by
  decide +kernel

theorem periodicScan71_2 : ∀ s : Fin 26,
    prefixCheck 26 (by decide) periodicWord71
      (periodicCaps71 2) 2 s 26 0 0 = true := by
  decide +kernel

theorem periodicScan71_3 : ∀ s : Fin 26,
    prefixCheck 26 (by decide) periodicWord71
      (periodicCaps71 3) 3 s 26 0 0 = true := by
  decide +kernel

theorem periodicScan71_4 : ∀ s : Fin 26,
    prefixCheck 26 (by decide) periodicWord71
      (periodicCaps71 4) 4 s 26 0 0 = true := by
  decide +kernel

theorem periodicCertificate71 :
    WordCertificate 26 (by decide) periodicWord71 periodicCaps71 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan71_0
  · exact periodicScan71_1
  · exact periodicScan71_2
  · exact periodicScan71_3
  · exact periodicScan71_4

theorem schedulable_word71 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 71) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps71 r := by
    simpa only [periodicCaps71_eq] using hr
  exact ⟨periodic 26 (by decide) periodicWord71,
    validRates_periodic_of_wordCertificate (by decide) periodicWord71
      periodicCertificate71 hc⟩

-- Case 72: Q32_2; period 22.
def periodicArray72 : Array (Fin 5) := #[0, 1, 0, 2, 0, 1, 0, 3, 4, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 4, 0, 3]
def periodicWord72 (k : Fin 22) : Fin 5 :=
  periodicArray72[k.val]
def periodicCaps72 : Fin 5 → RateCap
  | 0 => { bound := (5/11 : ℚ), closed := true }
  | 1 => { bound := (1/6 : ℚ), closed := false }
  | 2 => { bound := (3/22 : ℚ), closed := true }
  | 3 => { bound := (3/22 : ℚ), closed := true }
  | 4 => { bound := (1/11 : ℚ), closed := true }

theorem periodicArray72_toList :
    periodicArray72.toList = words 72 := by rfl
theorem periodicCaps72_eq : periodicCaps72 = wordCaps 72 := by rfl

theorem periodicScan72_0 : ∀ s : Fin 22,
    prefixCheck 22 (by decide) periodicWord72
      (periodicCaps72 0) 0 s 22 0 0 = true := by
  decide +kernel

theorem periodicScan72_1 : ∀ s : Fin 22,
    prefixCheck 22 (by decide) periodicWord72
      (periodicCaps72 1) 1 s 22 0 0 = true := by
  decide +kernel

theorem periodicScan72_2 : ∀ s : Fin 22,
    prefixCheck 22 (by decide) periodicWord72
      (periodicCaps72 2) 2 s 22 0 0 = true := by
  decide +kernel

theorem periodicScan72_3 : ∀ s : Fin 22,
    prefixCheck 22 (by decide) periodicWord72
      (periodicCaps72 3) 3 s 22 0 0 = true := by
  decide +kernel

theorem periodicScan72_4 : ∀ s : Fin 22,
    prefixCheck 22 (by decide) periodicWord72
      (periodicCaps72 4) 4 s 22 0 0 = true := by
  decide +kernel

theorem periodicCertificate72 :
    WordCertificate 22 (by decide) periodicWord72 periodicCaps72 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan72_0
  · exact periodicScan72_1
  · exact periodicScan72_2
  · exact periodicScan72_3
  · exact periodicScan72_4

theorem schedulable_word72 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 72) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps72 r := by
    simpa only [periodicCaps72_eq] using hr
  exact ⟨periodic 22 (by decide) periodicWord72,
    validRates_periodic_of_wordCertificate (by decide) periodicWord72
      periodicCertificate72 hc⟩

-- Case 73: Q32_4; period 22.
def periodicArray73 : Array (Fin 5) := #[0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 3, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 4]
def periodicWord73 (k : Fin 22) : Fin 5 :=
  periodicArray73[k.val]
def periodicCaps73 : Fin 5 → RateCap
  | 0 => { bound := (5/11 : ℚ), closed := true }
  | 1 => { bound := (3/11 : ℚ), closed := true }
  | 2 => { bound := (1/6 : ℚ), closed := false }
  | 3 => { bound := (1/22 : ℚ), closed := true }
  | 4 => { bound := (1/22 : ℚ), closed := true }

theorem periodicArray73_toList :
    periodicArray73.toList = words 73 := by rfl
theorem periodicCaps73_eq : periodicCaps73 = wordCaps 73 := by rfl

theorem periodicScan73_0 : ∀ s : Fin 22,
    prefixCheck 22 (by decide) periodicWord73
      (periodicCaps73 0) 0 s 22 0 0 = true := by
  decide +kernel

theorem periodicScan73_1 : ∀ s : Fin 22,
    prefixCheck 22 (by decide) periodicWord73
      (periodicCaps73 1) 1 s 22 0 0 = true := by
  decide +kernel

theorem periodicScan73_2 : ∀ s : Fin 22,
    prefixCheck 22 (by decide) periodicWord73
      (periodicCaps73 2) 2 s 22 0 0 = true := by
  decide +kernel

theorem periodicScan73_3 : ∀ s : Fin 22,
    prefixCheck 22 (by decide) periodicWord73
      (periodicCaps73 3) 3 s 22 0 0 = true := by
  decide +kernel

theorem periodicScan73_4 : ∀ s : Fin 22,
    prefixCheck 22 (by decide) periodicWord73
      (periodicCaps73 4) 4 s 22 0 0 = true := by
  decide +kernel

theorem periodicCertificate73 :
    WordCertificate 22 (by decide) periodicWord73 periodicCaps73 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan73_0
  · exact periodicScan73_1
  · exact periodicScan73_2
  · exact periodicScan73_3
  · exact periodicScan73_4

theorem schedulable_word73 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 73) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps73 r := by
    simpa only [periodicCaps73_eq] using hr
  exact ⟨periodic 22 (by decide) periodicWord73,
    validRates_periodic_of_wordCertificate (by decide) periodicWord73
      periodicCertificate73 hc⟩

-- Case 74: Q52_4; period 25.
def periodicArray74 : Array (Fin 5) := #[0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 4, 0, 1, 0, 2]
def periodicWord74 (k : Fin 25) : Fin 5 :=
  periodicArray74[k.val]
def periodicCaps74 : Fin 5 → RateCap
  | 0 => { bound := (13/25 : ℚ), closed := true }
  | 1 => { bound := (1/5 : ℚ), closed := false }
  | 2 => { bound := (3/16 : ℚ), closed := false }
  | 3 => { bound := (1/25 : ℚ), closed := true }
  | 4 => { bound := (1/25 : ℚ), closed := true }

theorem periodicArray74_toList :
    periodicArray74.toList = words 74 := by rfl
theorem periodicCaps74_eq : periodicCaps74 = wordCaps 74 := by rfl

theorem periodicScan74_0 : ∀ s : Fin 25,
    prefixCheck 25 (by decide) periodicWord74
      (periodicCaps74 0) 0 s 25 0 0 = true := by
  decide +kernel

theorem periodicScan74_1 : ∀ s : Fin 25,
    prefixCheck 25 (by decide) periodicWord74
      (periodicCaps74 1) 1 s 25 0 0 = true := by
  decide +kernel

theorem periodicScan74_2 : ∀ s : Fin 25,
    prefixCheck 25 (by decide) periodicWord74
      (periodicCaps74 2) 2 s 25 0 0 = true := by
  decide +kernel

theorem periodicScan74_3 : ∀ s : Fin 25,
    prefixCheck 25 (by decide) periodicWord74
      (periodicCaps74 3) 3 s 25 0 0 = true := by
  decide +kernel

theorem periodicScan74_4 : ∀ s : Fin 25,
    prefixCheck 25 (by decide) periodicWord74
      (periodicCaps74 4) 4 s 25 0 0 = true := by
  decide +kernel

theorem periodicCertificate74 :
    WordCertificate 25 (by decide) periodicWord74 periodicCaps74 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan74_0
  · exact periodicScan74_1
  · exact periodicScan74_2
  · exact periodicScan74_3
  · exact periodicScan74_4

theorem schedulable_word74 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 74) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps74 r := by
    simpa only [periodicCaps74_eq] using hr
  exact ⟨periodic 25 (by decide) periodicWord74,
    validRates_periodic_of_wordCertificate (by decide) periodicWord74
      periodicCertificate74 hc⟩

-- Case 75: Q56_4; period 50.
def periodicArray75 : Array (Fin 5) := #[0, 0, 1, 2, 0, 1, 0, 1, 0, 2, 1, 0, 0, 2, 1, 0, 3, 0, 1, 2, 0, 1, 0, 2, 1, 0, 0, 1, 2, 0, 1, 0, 1, 0, 2, 1, 0, 0, 2, 1, 0, 4, 0, 1, 2, 0, 1, 0, 2, 1]
def periodicWord75 (k : Fin 50) : Fin 5 :=
  periodicArray75[k.val]
def periodicCaps75 : Fin 5 → RateCap
  | 0 => { bound := (5/12 : ℚ), closed := false }
  | 1 => { bound := (2/7 : ℚ), closed := false }
  | 2 => { bound := (1/5 : ℚ), closed := false }
  | 3 => { bound := (1/50 : ℚ), closed := true }
  | 4 => { bound := (1/50 : ℚ), closed := true }

theorem periodicArray75_toList :
    periodicArray75.toList = words 75 := by rfl
theorem periodicCaps75_eq : periodicCaps75 = wordCaps 75 := by rfl

theorem periodicScan75_0 : ∀ s : Fin 50,
    prefixCheck 50 (by decide) periodicWord75
      (periodicCaps75 0) 0 s 50 0 0 = true := by
  decide +kernel

theorem periodicScan75_1 : ∀ s : Fin 50,
    prefixCheck 50 (by decide) periodicWord75
      (periodicCaps75 1) 1 s 50 0 0 = true := by
  decide +kernel

theorem periodicScan75_2 : ∀ s : Fin 50,
    prefixCheck 50 (by decide) periodicWord75
      (periodicCaps75 2) 2 s 50 0 0 = true := by
  decide +kernel

theorem periodicScan75_3 : ∀ s : Fin 50,
    prefixCheck 50 (by decide) periodicWord75
      (periodicCaps75 3) 3 s 50 0 0 = true := by
  decide +kernel

theorem periodicScan75_4 : ∀ s : Fin 50,
    prefixCheck 50 (by decide) periodicWord75
      (periodicCaps75 4) 4 s 50 0 0 = true := by
  decide +kernel

theorem periodicCertificate75 :
    WordCertificate 50 (by decide) periodicWord75 periodicCaps75 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan75_0
  · exact periodicScan75_1
  · exact periodicScan75_2
  · exact periodicScan75_3
  · exact periodicScan75_4

theorem schedulable_word75 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 75) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps75 r := by
    simpa only [periodicCaps75_eq] using hr
  exact ⟨periodic 50 (by decide) periodicWord75,
    validRates_periodic_of_wordCertificate (by decide) periodicWord75
      periodicCertificate75 hc⟩

-- Case 76: Q59_3; period 30.
def periodicArray76 : Array (Fin 5) := #[0, 0, 1, 0, 1, 0, 0, 3, 0, 1, 0, 0, 1, 0, 2, 0, 0, 1, 0, 1, 0, 0, 4, 0, 1, 0, 0, 1, 0, 2]
def periodicWord76 (k : Fin 30) : Fin 5 :=
  periodicArray76[k.val]
def periodicCaps76 : Fin 5 → RateCap
  | 0 => { bound := (3/5 : ℚ), closed := true }
  | 1 => { bound := (1/4 : ℚ), closed := false }
  | 2 => { bound := (1/15 : ℚ), closed := true }
  | 3 => { bound := (1/30 : ℚ), closed := true }
  | 4 => { bound := (1/30 : ℚ), closed := true }

theorem periodicArray76_toList :
    periodicArray76.toList = words 76 := by rfl
theorem periodicCaps76_eq : periodicCaps76 = wordCaps 76 := by rfl

theorem periodicScan76_0 : ∀ s : Fin 30,
    prefixCheck 30 (by decide) periodicWord76
      (periodicCaps76 0) 0 s 30 0 0 = true := by
  decide +kernel

theorem periodicScan76_1 : ∀ s : Fin 30,
    prefixCheck 30 (by decide) periodicWord76
      (periodicCaps76 1) 1 s 30 0 0 = true := by
  decide +kernel

theorem periodicScan76_2 : ∀ s : Fin 30,
    prefixCheck 30 (by decide) periodicWord76
      (periodicCaps76 2) 2 s 30 0 0 = true := by
  decide +kernel

theorem periodicScan76_3 : ∀ s : Fin 30,
    prefixCheck 30 (by decide) periodicWord76
      (periodicCaps76 3) 3 s 30 0 0 = true := by
  decide +kernel

theorem periodicScan76_4 : ∀ s : Fin 30,
    prefixCheck 30 (by decide) periodicWord76
      (periodicCaps76 4) 4 s 30 0 0 = true := by
  decide +kernel

theorem periodicCertificate76 :
    WordCertificate 30 (by decide) periodicWord76 periodicCaps76 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan76_0
  · exact periodicScan76_1
  · exact periodicScan76_2
  · exact periodicScan76_3
  · exact periodicScan76_4

theorem schedulable_word76 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 76) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps76 r := by
    simpa only [periodicCaps76_eq] using hr
  exact ⟨periodic 30 (by decide) periodicWord76,
    validRates_periodic_of_wordCertificate (by decide) periodicWord76
      periodicCertificate76 hc⟩

-- Case 77: Q60_3; period 26.
def periodicArray77 : Array (Fin 5) := #[0, 0, 1, 0, 2, 0, 1, 0, 1, 0, 3, 0, 1, 0, 0, 1, 0, 2, 0, 1, 0, 1, 0, 4, 0, 1]
def periodicWord77 (k : Fin 26) : Fin 5 :=
  periodicArray77[k.val]
def periodicCaps77 : Fin 5 → RateCap
  | 0 => { bound := (7/13 : ℚ), closed := true }
  | 1 => { bound := (3/10 : ℚ), closed := false }
  | 2 => { bound := (1/13 : ℚ), closed := true }
  | 3 => { bound := (1/26 : ℚ), closed := true }
  | 4 => { bound := (1/26 : ℚ), closed := true }

theorem periodicArray77_toList :
    periodicArray77.toList = words 77 := by rfl
theorem periodicCaps77_eq : periodicCaps77 = wordCaps 77 := by rfl

theorem periodicScan77_0 : ∀ s : Fin 26,
    prefixCheck 26 (by decide) periodicWord77
      (periodicCaps77 0) 0 s 26 0 0 = true := by
  decide +kernel

theorem periodicScan77_1 : ∀ s : Fin 26,
    prefixCheck 26 (by decide) periodicWord77
      (periodicCaps77 1) 1 s 26 0 0 = true := by
  decide +kernel

theorem periodicScan77_2 : ∀ s : Fin 26,
    prefixCheck 26 (by decide) periodicWord77
      (periodicCaps77 2) 2 s 26 0 0 = true := by
  decide +kernel

theorem periodicScan77_3 : ∀ s : Fin 26,
    prefixCheck 26 (by decide) periodicWord77
      (periodicCaps77 3) 3 s 26 0 0 = true := by
  decide +kernel

theorem periodicScan77_4 : ∀ s : Fin 26,
    prefixCheck 26 (by decide) periodicWord77
      (periodicCaps77 4) 4 s 26 0 0 = true := by
  decide +kernel

theorem periodicCertificate77 :
    WordCertificate 26 (by decide) periodicWord77 periodicCaps77 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan77_0
  · exact periodicScan77_1
  · exact periodicScan77_2
  · exact periodicScan77_3
  · exact periodicScan77_4

theorem schedulable_word77 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 77) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps77 r := by
    simpa only [periodicCaps77_eq] using hr
  exact ⟨periodic 26 (by decide) periodicWord77,
    validRates_periodic_of_wordCertificate (by decide) periodicWord77
      periodicCertificate77 hc⟩

-- Case 78: Q63_4; period 26.
def periodicArray78 : Array (Fin 5) := #[0, 1, 0, 2, 1, 0, 1, 2, 0, 3, 1, 0, 2, 0, 1, 0, 2, 1, 0, 1, 2, 0, 4, 1, 0, 2]
def periodicWord78 (k : Fin 26) : Fin 5 :=
  periodicArray78[k.val]
def periodicCaps78 : Fin 5 → RateCap
  | 0 => { bound := (3/8 : ℚ), closed := false }
  | 1 => { bound := (2/7 : ℚ), closed := false }
  | 2 => { bound := (3/13 : ℚ), closed := true }
  | 3 => { bound := (1/26 : ℚ), closed := true }
  | 4 => { bound := (1/26 : ℚ), closed := true }

theorem periodicArray78_toList :
    periodicArray78.toList = words 78 := by rfl
theorem periodicCaps78_eq : periodicCaps78 = wordCaps 78 := by rfl

theorem periodicScan78_0 : ∀ s : Fin 26,
    prefixCheck 26 (by decide) periodicWord78
      (periodicCaps78 0) 0 s 26 0 0 = true := by
  decide +kernel

theorem periodicScan78_1 : ∀ s : Fin 26,
    prefixCheck 26 (by decide) periodicWord78
      (periodicCaps78 1) 1 s 26 0 0 = true := by
  decide +kernel

theorem periodicScan78_2 : ∀ s : Fin 26,
    prefixCheck 26 (by decide) periodicWord78
      (periodicCaps78 2) 2 s 26 0 0 = true := by
  decide +kernel

theorem periodicScan78_3 : ∀ s : Fin 26,
    prefixCheck 26 (by decide) periodicWord78
      (periodicCaps78 3) 3 s 26 0 0 = true := by
  decide +kernel

theorem periodicScan78_4 : ∀ s : Fin 26,
    prefixCheck 26 (by decide) periodicWord78
      (periodicCaps78 4) 4 s 26 0 0 = true := by
  decide +kernel

theorem periodicCertificate78 :
    WordCertificate 26 (by decide) periodicWord78 periodicCaps78 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan78_0
  · exact periodicScan78_1
  · exact periodicScan78_2
  · exact periodicScan78_3
  · exact periodicScan78_4

theorem schedulable_word78 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 78) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps78 r := by
    simpa only [periodicCaps78_eq] using hr
  exact ⟨periodic 26 (by decide) periodicWord78,
    validRates_periodic_of_wordCertificate (by decide) periodicWord78
      periodicCertificate78 hc⟩

-- Case 79: T1_3_3; period 36.
def periodicArray79 : Array (Fin 5) := #[0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 4]
def periodicWord79 (k : Fin 36) : Fin 5 :=
  periodicArray79[k.val]
def periodicCaps79 : Fin 5 → RateCap
  | 0 => { bound := (2/3 : ℚ), closed := true }
  | 1 => { bound := (1/5 : ℚ), closed := false }
  | 2 => { bound := (1/18 : ℚ), closed := true }
  | 3 => { bound := (1/36 : ℚ), closed := true }
  | 4 => { bound := (1/36 : ℚ), closed := true }

theorem periodicArray79_toList :
    periodicArray79.toList = words 79 := by rfl
theorem periodicCaps79_eq : periodicCaps79 = wordCaps 79 := by rfl

theorem periodicScan79_0 : ∀ s : Fin 36,
    prefixCheck 36 (by decide) periodicWord79
      (periodicCaps79 0) 0 s 36 0 0 = true := by
  decide +kernel

theorem periodicScan79_1 : ∀ s : Fin 36,
    prefixCheck 36 (by decide) periodicWord79
      (periodicCaps79 1) 1 s 36 0 0 = true := by
  decide +kernel

theorem periodicScan79_2 : ∀ s : Fin 36,
    prefixCheck 36 (by decide) periodicWord79
      (periodicCaps79 2) 2 s 36 0 0 = true := by
  decide +kernel

theorem periodicScan79_3 : ∀ s : Fin 36,
    prefixCheck 36 (by decide) periodicWord79
      (periodicCaps79 3) 3 s 36 0 0 = true := by
  decide +kernel

theorem periodicScan79_4 : ∀ s : Fin 36,
    prefixCheck 36 (by decide) periodicWord79
      (periodicCaps79 4) 4 s 36 0 0 = true := by
  decide +kernel

theorem periodicCertificate79 :
    WordCertificate 36 (by decide) periodicWord79 periodicCaps79 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan79_0
  · exact periodicScan79_1
  · exact periodicScan79_2
  · exact periodicScan79_3
  · exact periodicScan79_4

theorem schedulable_word79 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 79) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps79 r := by
    simpa only [periodicCaps79_eq] using hr
  exact ⟨periodic 36 (by decide) periodicWord79,
    validRates_periodic_of_wordCertificate (by decide) periodicWord79
      periodicCertificate79 hc⟩

-- Case 80: T2_3_3; period 44.
def periodicArray80 : Array (Fin 5) := #[0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 4]
def periodicWord80 (k : Fin 44) : Fin 5 :=
  periodicArray80[k.val]
def periodicCaps80 : Fin 5 → RateCap
  | 0 => { bound := (7/11 : ℚ), closed := true }
  | 1 => { bound := (1/4 : ℚ), closed := false }
  | 2 => { bound := (1/22 : ℚ), closed := true }
  | 3 => { bound := (1/44 : ℚ), closed := true }
  | 4 => { bound := (1/44 : ℚ), closed := true }

theorem periodicArray80_toList :
    periodicArray80.toList = words 80 := by rfl
theorem periodicCaps80_eq : periodicCaps80 = wordCaps 80 := by rfl

theorem periodicScan80_0 : ∀ s : Fin 44,
    prefixCheck 44 (by decide) periodicWord80
      (periodicCaps80 0) 0 s 44 0 0 = true := by
  decide +kernel

theorem periodicScan80_1 : ∀ s : Fin 44,
    prefixCheck 44 (by decide) periodicWord80
      (periodicCaps80 1) 1 s 44 0 0 = true := by
  decide +kernel

theorem periodicScan80_2 : ∀ s : Fin 44,
    prefixCheck 44 (by decide) periodicWord80
      (periodicCaps80 2) 2 s 44 0 0 = true := by
  decide +kernel

theorem periodicScan80_3 : ∀ s : Fin 44,
    prefixCheck 44 (by decide) periodicWord80
      (periodicCaps80 3) 3 s 44 0 0 = true := by
  decide +kernel

theorem periodicScan80_4 : ∀ s : Fin 44,
    prefixCheck 44 (by decide) periodicWord80
      (periodicCaps80 4) 4 s 44 0 0 = true := by
  decide +kernel

theorem periodicCertificate80 :
    WordCertificate 44 (by decide) periodicWord80 periodicCaps80 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan80_0
  · exact periodicScan80_1
  · exact periodicScan80_2
  · exact periodicScan80_3
  · exact periodicScan80_4

theorem schedulable_word80 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 80) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps80 r := by
    simpa only [periodicCaps80_eq] using hr
  exact ⟨periodic 44 (by decide) periodicWord80,
    validRates_periodic_of_wordCertificate (by decide) periodicWord80
      periodicCertificate80 hc⟩

-- Case 81: T3_2_2; period 12.
def periodicArray81 : Array (Fin 5) := #[0, 0, 1, 0, 3, 0, 2, 0, 0, 1, 0, 4]
def periodicWord81 (k : Fin 12) : Fin 5 :=
  periodicArray81[k.val]
def periodicCaps81 : Fin 5 → RateCap
  | 0 => { bound := (7/12 : ℚ), closed := true }
  | 1 => { bound := (1/6 : ℚ), closed := false }
  | 2 => { bound := (1/12 : ℚ), closed := true }
  | 3 => { bound := (1/12 : ℚ), closed := true }
  | 4 => { bound := (1/12 : ℚ), closed := true }

theorem periodicArray81_toList :
    periodicArray81.toList = words 81 := by rfl
theorem periodicCaps81_eq : periodicCaps81 = wordCaps 81 := by rfl

theorem periodicScan81_0 : ∀ s : Fin 12,
    prefixCheck 12 (by decide) periodicWord81
      (periodicCaps81 0) 0 s 12 0 0 = true := by
  decide +kernel

theorem periodicScan81_1 : ∀ s : Fin 12,
    prefixCheck 12 (by decide) periodicWord81
      (periodicCaps81 1) 1 s 12 0 0 = true := by
  decide +kernel

theorem periodicScan81_2 : ∀ s : Fin 12,
    prefixCheck 12 (by decide) periodicWord81
      (periodicCaps81 2) 2 s 12 0 0 = true := by
  decide +kernel

theorem periodicScan81_3 : ∀ s : Fin 12,
    prefixCheck 12 (by decide) periodicWord81
      (periodicCaps81 3) 3 s 12 0 0 = true := by
  decide +kernel

theorem periodicScan81_4 : ∀ s : Fin 12,
    prefixCheck 12 (by decide) periodicWord81
      (periodicCaps81 4) 4 s 12 0 0 = true := by
  decide +kernel

theorem periodicCertificate81 :
    WordCertificate 12 (by decide) periodicWord81 periodicCaps81 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan81_0
  · exact periodicScan81_1
  · exact periodicScan81_2
  · exact periodicScan81_3
  · exact periodicScan81_4

theorem schedulable_word81 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 81) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps81 r := by
    simpa only [periodicCaps81_eq] using hr
  exact ⟨periodic 12 (by decide) periodicWord81,
    validRates_periodic_of_wordCertificate (by decide) periodicWord81
      periodicCertificate81 hc⟩

-- Case 82: T3_2_3; period 24.
def periodicArray82 : Array (Fin 5) := #[0, 0, 2, 0, 1, 0, 0, 2, 0, 3, 0, 1, 0, 0, 2, 0, 1, 0, 0, 2, 0, 4, 0, 1]
def periodicWord82 (k : Fin 24) : Fin 5 :=
  periodicArray82[k.val]
def periodicCaps82 : Fin 5 → RateCap
  | 0 => { bound := (7/12 : ℚ), closed := true }
  | 1 => { bound := (1/6 : ℚ), closed := false }
  | 2 => { bound := (1/6 : ℚ), closed := false }
  | 3 => { bound := (1/24 : ℚ), closed := true }
  | 4 => { bound := (1/24 : ℚ), closed := true }

theorem periodicArray82_toList :
    periodicArray82.toList = words 82 := by rfl
theorem periodicCaps82_eq : periodicCaps82 = wordCaps 82 := by rfl

theorem periodicScan82_0 : ∀ s : Fin 24,
    prefixCheck 24 (by decide) periodicWord82
      (periodicCaps82 0) 0 s 24 0 0 = true := by
  decide +kernel

theorem periodicScan82_1 : ∀ s : Fin 24,
    prefixCheck 24 (by decide) periodicWord82
      (periodicCaps82 1) 1 s 24 0 0 = true := by
  decide +kernel

theorem periodicScan82_2 : ∀ s : Fin 24,
    prefixCheck 24 (by decide) periodicWord82
      (periodicCaps82 2) 2 s 24 0 0 = true := by
  decide +kernel

theorem periodicScan82_3 : ∀ s : Fin 24,
    prefixCheck 24 (by decide) periodicWord82
      (periodicCaps82 3) 3 s 24 0 0 = true := by
  decide +kernel

theorem periodicScan82_4 : ∀ s : Fin 24,
    prefixCheck 24 (by decide) periodicWord82
      (periodicCaps82 4) 4 s 24 0 0 = true := by
  decide +kernel

theorem periodicCertificate82 :
    WordCertificate 24 (by decide) periodicWord82 periodicCaps82 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan82_0
  · exact periodicScan82_1
  · exact periodicScan82_2
  · exact periodicScan82_3
  · exact periodicScan82_4

theorem schedulable_word82 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 82) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps82 r := by
    simpa only [periodicCaps82_eq] using hr
  exact ⟨periodic 24 (by decide) periodicWord82,
    validRates_periodic_of_wordCertificate (by decide) periodicWord82
      periodicCertificate82 hc⟩

-- Case 83: T3_3_3; period 48.
def periodicArray83 : Array (Fin 5) := #[0, 0, 1, 0, 1, 0, 0, 1, 0, 2, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 3, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 2, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 4, 0, 1]
def periodicWord83 (k : Fin 48) : Fin 5 :=
  periodicArray83[k.val]
def periodicCaps83 : Fin 5 → RateCap
  | 0 => { bound := (7/12 : ℚ), closed := true }
  | 1 => { bound := (1/3 : ℚ), closed := false }
  | 2 => { bound := (1/24 : ℚ), closed := true }
  | 3 => { bound := (1/48 : ℚ), closed := true }
  | 4 => { bound := (1/48 : ℚ), closed := true }

theorem periodicArray83_toList :
    periodicArray83.toList = words 83 := by rfl
theorem periodicCaps83_eq : periodicCaps83 = wordCaps 83 := by rfl

theorem periodicScan83_0 : ∀ s : Fin 48,
    prefixCheck 48 (by decide) periodicWord83
      (periodicCaps83 0) 0 s 48 0 0 = true := by
  decide +kernel

theorem periodicScan83_1 : ∀ s : Fin 48,
    prefixCheck 48 (by decide) periodicWord83
      (periodicCaps83 1) 1 s 48 0 0 = true := by
  decide +kernel

theorem periodicScan83_2 : ∀ s : Fin 48,
    prefixCheck 48 (by decide) periodicWord83
      (periodicCaps83 2) 2 s 48 0 0 = true := by
  decide +kernel

theorem periodicScan83_3 : ∀ s : Fin 48,
    prefixCheck 48 (by decide) periodicWord83
      (periodicCaps83 3) 3 s 48 0 0 = true := by
  decide +kernel

theorem periodicScan83_4 : ∀ s : Fin 48,
    prefixCheck 48 (by decide) periodicWord83
      (periodicCaps83 4) 4 s 48 0 0 = true := by
  decide +kernel

theorem periodicCertificate83 :
    WordCertificate 48 (by decide) periodicWord83 periodicCaps83 := by
  apply wordCertificate_of_prefixChecks
  intro i
  fin_cases i
  · exact periodicScan83_0
  · exact periodicScan83_1
  · exact periodicScan83_2
  · exact periodicScan83_3
  · exact periodicScan83_4

theorem schedulable_word83 (r : Fin 5 → ℝ)
    (hr : CapsHold (wordCaps 83) r) : SchedulableRates r := by
  have hc : CapsHold periodicCaps83 r := by
    simpa only [periodicCaps83_eq] using hr
  exact ⟨periodic 48 (by decide) periodicWord83,
    validRates_periodic_of_wordCertificate (by decide) periodicWord83
      periodicCertificate83 hc⟩

end Catalogue

theorem periodic_catalogue_schedulable (j : Fin 84) (r : Fin 5 → ℝ)
    (hr : CapsHold (Catalogue.wordCaps j) r) : SchedulableRates r := by
  fin_cases j
  · exact Catalogue.schedulable_word0 r hr
  · exact Catalogue.schedulable_word1 r hr
  · exact Catalogue.schedulable_word2 r hr
  · exact Catalogue.schedulable_word3 r hr
  · exact Catalogue.schedulable_word4 r hr
  · exact Catalogue.schedulable_word5 r hr
  · exact Catalogue.schedulable_word6 r hr
  · exact Catalogue.schedulable_word7 r hr
  · exact Catalogue.schedulable_word8 r hr
  · exact Catalogue.schedulable_word9 r hr
  · exact Catalogue.schedulable_word10 r hr
  · exact Catalogue.schedulable_word11 r hr
  · exact Catalogue.schedulable_word12 r hr
  · exact Catalogue.schedulable_word13 r hr
  · exact Catalogue.schedulable_word14 r hr
  · exact Catalogue.schedulable_word15 r hr
  · exact Catalogue.schedulable_word16 r hr
  · exact Catalogue.schedulable_word17 r hr
  · exact Catalogue.schedulable_word18 r hr
  · exact Catalogue.schedulable_word19 r hr
  · exact Catalogue.schedulable_word20 r hr
  · exact Catalogue.schedulable_word21 r hr
  · exact Catalogue.schedulable_word22 r hr
  · exact Catalogue.schedulable_word23 r hr
  · exact Catalogue.schedulable_word24 r hr
  · exact Catalogue.schedulable_word25 r hr
  · exact Catalogue.schedulable_word26 r hr
  · exact Catalogue.schedulable_word27 r hr
  · exact Catalogue.schedulable_word28 r hr
  · exact Catalogue.schedulable_word29 r hr
  · exact Catalogue.schedulable_word30 r hr
  · exact Catalogue.schedulable_word31 r hr
  · exact Catalogue.schedulable_word32 r hr
  · exact Catalogue.schedulable_word33 r hr
  · exact Catalogue.schedulable_word34 r hr
  · exact Catalogue.schedulable_word35 r hr
  · exact Catalogue.schedulable_word36 r hr
  · exact Catalogue.schedulable_word37 r hr
  · exact Catalogue.schedulable_word38 r hr
  · exact Catalogue.schedulable_word39 r hr
  · exact Catalogue.schedulable_word40 r hr
  · exact Catalogue.schedulable_word41 r hr
  · exact Catalogue.schedulable_word42 r hr
  · exact Catalogue.schedulable_word43 r hr
  · exact Catalogue.schedulable_word44 r hr
  · exact Catalogue.schedulable_word45 r hr
  · exact Catalogue.schedulable_word46 r hr
  · exact Catalogue.schedulable_word47 r hr
  · exact Catalogue.schedulable_word48 r hr
  · exact Catalogue.schedulable_word49 r hr
  · exact Catalogue.schedulable_word50 r hr
  · exact Catalogue.schedulable_word51 r hr
  · exact Catalogue.schedulable_word52 r hr
  · exact Catalogue.schedulable_word53 r hr
  · exact Catalogue.schedulable_word54 r hr
  · exact Catalogue.schedulable_word55 r hr
  · exact Catalogue.schedulable_word56 r hr
  · exact Catalogue.schedulable_word57 r hr
  · exact Catalogue.schedulable_word58 r hr
  · exact Catalogue.schedulable_word59 r hr
  · exact Catalogue.schedulable_word60 r hr
  · exact Catalogue.schedulable_word61 r hr
  · exact Catalogue.schedulable_word62 r hr
  · exact Catalogue.schedulable_word63 r hr
  · exact Catalogue.schedulable_word64 r hr
  · exact Catalogue.schedulable_word65 r hr
  · exact Catalogue.schedulable_word66 r hr
  · exact Catalogue.schedulable_word67 r hr
  · exact Catalogue.schedulable_word68 r hr
  · exact Catalogue.schedulable_word69 r hr
  · exact Catalogue.schedulable_word70 r hr
  · exact Catalogue.schedulable_word71 r hr
  · exact Catalogue.schedulable_word72 r hr
  · exact Catalogue.schedulable_word73 r hr
  · exact Catalogue.schedulable_word74 r hr
  · exact Catalogue.schedulable_word75 r hr
  · exact Catalogue.schedulable_word76 r hr
  · exact Catalogue.schedulable_word77 r hr
  · exact Catalogue.schedulable_word78 r hr
  · exact Catalogue.schedulable_word79 r hr
  · exact Catalogue.schedulable_word80 r hr
  · exact Catalogue.schedulable_word81 r hr
  · exact Catalogue.schedulable_word82 r hr
  · exact Catalogue.schedulable_word83 r hr

end RealPinwheel
