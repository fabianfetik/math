import Pinwheel.WeakSevenBandData.Words
import Pinwheel.WeakSevenBandData.RateOrder
import Pinwheel.WeakServiceTransport
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Cap-plateau lifting and monotone weak-word adapters. -/

namespace RealPinwheel.WeakSevenBandData

noncomputable def ws7WordCap0 (i : Fin 7) : ℝ :=
  (ws7WordP0 i : ℝ) / (ws7WordQ0 i : ℝ)

def ws7WordRep0 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 0
  | 2 => 2
  | 3 => 2
  | 4 => 2
  | 5 => 2
  | 6 => 2
  | _ => 0

theorem ws7Word0WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep0 i) ≤ ws7WordCap0 (ws7WordRep0 i)) :
    WeakValidRates r
      (periodic ws7Word0.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word0)) := by
  have hrepLe : ∀ i, (ws7WordRep0 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap0 (ws7WordRep0 i) = ws7WordCap0 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap0, ws7WordRep0, ws7WordP0, ws7WordQ0]
  have hall := caps_of_representatives ws7WordRep0 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word0Weak
  intro i
  simpa [ws7WordCap0, ws7WordP0, ws7WordQ0] using hall i

noncomputable def ws7WordCap1 (i : Fin 7) : ℝ :=
  (ws7WordP1 i : ℝ) / (ws7WordQ1 i : ℝ)

def ws7WordRep1 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 2
  | 5 => 2
  | 6 => 2
  | _ => 0

theorem ws7Word1WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep1 i) ≤ ws7WordCap1 (ws7WordRep1 i)) :
    WeakValidRates r
      (periodic ws7Word1.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word1)) := by
  have hrepLe : ∀ i, (ws7WordRep1 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap1 (ws7WordRep1 i) = ws7WordCap1 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap1, ws7WordRep1, ws7WordP1, ws7WordQ1]
  have hall := caps_of_representatives ws7WordRep1 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word1Weak
  intro i
  simpa [ws7WordCap1, ws7WordP1, ws7WordQ1] using hall i

noncomputable def ws7WordCap2 (i : Fin 7) : ℝ :=
  (ws7WordP2 i : ℝ) / (ws7WordQ2 i : ℝ)

def ws7WordRep2 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 0
  | 2 => 2
  | 3 => 2
  | 4 => 2
  | 5 => 2
  | 6 => 2
  | _ => 0

theorem ws7Word2WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep2 i) ≤ ws7WordCap2 (ws7WordRep2 i)) :
    WeakValidRates r
      (periodic ws7Word2.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word2)) := by
  have hrepLe : ∀ i, (ws7WordRep2 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap2 (ws7WordRep2 i) = ws7WordCap2 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap2, ws7WordRep2, ws7WordP2, ws7WordQ2]
  have hall := caps_of_representatives ws7WordRep2 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word2Weak
  intro i
  simpa [ws7WordCap2, ws7WordP2, ws7WordQ2] using hall i

noncomputable def ws7WordCap3 (i : Fin 7) : ℝ :=
  (ws7WordP3 i : ℝ) / (ws7WordQ3 i : ℝ)

def ws7WordRep3 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 2
  | 5 => 2
  | 6 => 2
  | _ => 0

theorem ws7Word3WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep3 i) ≤ ws7WordCap3 (ws7WordRep3 i)) :
    WeakValidRates r
      (periodic ws7Word3.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word3)) := by
  have hrepLe : ∀ i, (ws7WordRep3 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap3 (ws7WordRep3 i) = ws7WordCap3 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap3, ws7WordRep3, ws7WordP3, ws7WordQ3]
  have hall := caps_of_representatives ws7WordRep3 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word3Weak
  intro i
  simpa [ws7WordCap3, ws7WordP3, ws7WordQ3] using hall i

noncomputable def ws7WordCap4 (i : Fin 7) : ℝ :=
  (ws7WordP4 i : ℝ) / (ws7WordQ4 i : ℝ)

def ws7WordRep4 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word4WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep4 i) ≤ ws7WordCap4 (ws7WordRep4 i)) :
    WeakValidRates r
      (periodic ws7Word4.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word4)) := by
  have hrepLe : ∀ i, (ws7WordRep4 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap4 (ws7WordRep4 i) = ws7WordCap4 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap4, ws7WordRep4, ws7WordP4, ws7WordQ4]
  have hall := caps_of_representatives ws7WordRep4 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word4Weak
  intro i
  simpa [ws7WordCap4, ws7WordP4, ws7WordQ4] using hall i

noncomputable def ws7WordCap5 (i : Fin 7) : ℝ :=
  (ws7WordP5 i : ℝ) / (ws7WordQ5 i : ℝ)

def ws7WordRep5 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 0
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 3
  | 6 => 3
  | _ => 0

theorem ws7Word5WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep5 i) ≤ ws7WordCap5 (ws7WordRep5 i)) :
    WeakValidRates r
      (periodic ws7Word5.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word5)) := by
  have hrepLe : ∀ i, (ws7WordRep5 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap5 (ws7WordRep5 i) = ws7WordCap5 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap5, ws7WordRep5, ws7WordP5, ws7WordQ5]
  have hall := caps_of_representatives ws7WordRep5 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word5Weak
  intro i
  simpa [ws7WordCap5, ws7WordP5, ws7WordQ5] using hall i

noncomputable def ws7WordCap6 (i : Fin 7) : ℝ :=
  (ws7WordP6 i : ℝ) / (ws7WordQ6 i : ℝ)

def ws7WordRep6 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 6
  | _ => 0

theorem ws7Word6WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep6 i) ≤ ws7WordCap6 (ws7WordRep6 i)) :
    WeakValidRates r
      (periodic ws7Word6.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word6)) := by
  have hrepLe : ∀ i, (ws7WordRep6 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap6 (ws7WordRep6 i) = ws7WordCap6 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap6, ws7WordRep6, ws7WordP6, ws7WordQ6]
  have hall := caps_of_representatives ws7WordRep6 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word6Weak
  intro i
  simpa [ws7WordCap6, ws7WordP6, ws7WordQ6] using hall i

noncomputable def ws7WordCap7 (i : Fin 7) : ℝ :=
  (ws7WordP7 i : ℝ) / (ws7WordQ7 i : ℝ)

def ws7WordRep7 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 6
  | _ => 0

theorem ws7Word7WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep7 i) ≤ ws7WordCap7 (ws7WordRep7 i)) :
    WeakValidRates r
      (periodic ws7Word7.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word7)) := by
  have hrepLe : ∀ i, (ws7WordRep7 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap7 (ws7WordRep7 i) = ws7WordCap7 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap7, ws7WordRep7, ws7WordP7, ws7WordQ7]
  have hall := caps_of_representatives ws7WordRep7 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word7Weak
  intro i
  simpa [ws7WordCap7, ws7WordP7, ws7WordQ7] using hall i

noncomputable def ws7WordCap8 (i : Fin 7) : ℝ :=
  (ws7WordP8 i : ℝ) / (ws7WordQ8 i : ℝ)

def ws7WordRep8 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

theorem ws7Word8WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep8 i) ≤ ws7WordCap8 (ws7WordRep8 i)) :
    WeakValidRates r
      (periodic ws7Word8.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word8)) := by
  have hrepLe : ∀ i, (ws7WordRep8 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap8 (ws7WordRep8 i) = ws7WordCap8 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap8, ws7WordRep8, ws7WordP8, ws7WordQ8]
  have hall := caps_of_representatives ws7WordRep8 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word8Weak
  intro i
  simpa [ws7WordCap8, ws7WordP8, ws7WordQ8] using hall i

noncomputable def ws7WordCap9 (i : Fin 7) : ℝ :=
  (ws7WordP9 i : ℝ) / (ws7WordQ9 i : ℝ)

def ws7WordRep9 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

theorem ws7Word9WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep9 i) ≤ ws7WordCap9 (ws7WordRep9 i)) :
    WeakValidRates r
      (periodic ws7Word9.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word9)) := by
  have hrepLe : ∀ i, (ws7WordRep9 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap9 (ws7WordRep9 i) = ws7WordCap9 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap9, ws7WordRep9, ws7WordP9, ws7WordQ9]
  have hall := caps_of_representatives ws7WordRep9 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word9Weak
  intro i
  simpa [ws7WordCap9, ws7WordP9, ws7WordQ9] using hall i

noncomputable def ws7WordCap10 (i : Fin 7) : ℝ :=
  (ws7WordP10 i : ℝ) / (ws7WordQ10 i : ℝ)

def ws7WordRep10 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 2
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word10WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep10 i) ≤ ws7WordCap10 (ws7WordRep10 i)) :
    WeakValidRates r
      (periodic ws7Word10.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word10)) := by
  have hrepLe : ∀ i, (ws7WordRep10 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap10 (ws7WordRep10 i) = ws7WordCap10 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap10, ws7WordRep10, ws7WordP10, ws7WordQ10]
  have hall := caps_of_representatives ws7WordRep10 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word10Weak
  intro i
  simpa [ws7WordCap10, ws7WordP10, ws7WordQ10] using hall i

noncomputable def ws7WordCap11 (i : Fin 7) : ℝ :=
  (ws7WordP11 i : ℝ) / (ws7WordQ11 i : ℝ)

def ws7WordRep11 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

theorem ws7Word11WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep11 i) ≤ ws7WordCap11 (ws7WordRep11 i)) :
    WeakValidRates r
      (periodic ws7Word11.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word11)) := by
  have hrepLe : ∀ i, (ws7WordRep11 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap11 (ws7WordRep11 i) = ws7WordCap11 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap11, ws7WordRep11, ws7WordP11, ws7WordQ11]
  have hall := caps_of_representatives ws7WordRep11 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word11Weak
  intro i
  simpa [ws7WordCap11, ws7WordP11, ws7WordQ11] using hall i

noncomputable def ws7WordCap12 (i : Fin 7) : ℝ :=
  (ws7WordP12 i : ℝ) / (ws7WordQ12 i : ℝ)

def ws7WordRep12 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

theorem ws7Word12WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep12 i) ≤ ws7WordCap12 (ws7WordRep12 i)) :
    WeakValidRates r
      (periodic ws7Word12.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word12)) := by
  have hrepLe : ∀ i, (ws7WordRep12 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap12 (ws7WordRep12 i) = ws7WordCap12 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap12, ws7WordRep12, ws7WordP12, ws7WordQ12]
  have hall := caps_of_representatives ws7WordRep12 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word12Weak
  intro i
  simpa [ws7WordCap12, ws7WordP12, ws7WordQ12] using hall i

noncomputable def ws7WordCap13 (i : Fin 7) : ℝ :=
  (ws7WordP13 i : ℝ) / (ws7WordQ13 i : ℝ)

def ws7WordRep13 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 2
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word13WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep13 i) ≤ ws7WordCap13 (ws7WordRep13 i)) :
    WeakValidRates r
      (periodic ws7Word13.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word13)) := by
  have hrepLe : ∀ i, (ws7WordRep13 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap13 (ws7WordRep13 i) = ws7WordCap13 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap13, ws7WordRep13, ws7WordP13, ws7WordQ13]
  have hall := caps_of_representatives ws7WordRep13 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word13Weak
  intro i
  simpa [ws7WordCap13, ws7WordP13, ws7WordQ13] using hall i

noncomputable def ws7WordCap14 (i : Fin 7) : ℝ :=
  (ws7WordP14 i : ℝ) / (ws7WordQ14 i : ℝ)

def ws7WordRep14 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 2
  | 5 => 2
  | 6 => 2
  | _ => 0

theorem ws7Word14WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep14 i) ≤ ws7WordCap14 (ws7WordRep14 i)) :
    WeakValidRates r
      (periodic ws7Word14.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word14)) := by
  have hrepLe : ∀ i, (ws7WordRep14 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap14 (ws7WordRep14 i) = ws7WordCap14 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap14, ws7WordRep14, ws7WordP14, ws7WordQ14]
  have hall := caps_of_representatives ws7WordRep14 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word14Weak
  intro i
  simpa [ws7WordCap14, ws7WordP14, ws7WordQ14] using hall i

noncomputable def ws7WordCap15 (i : Fin 7) : ℝ :=
  (ws7WordP15 i : ℝ) / (ws7WordQ15 i : ℝ)

def ws7WordRep15 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 6
  | _ => 0

theorem ws7Word15WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep15 i) ≤ ws7WordCap15 (ws7WordRep15 i)) :
    WeakValidRates r
      (periodic ws7Word15.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word15)) := by
  have hrepLe : ∀ i, (ws7WordRep15 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap15 (ws7WordRep15 i) = ws7WordCap15 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap15, ws7WordRep15, ws7WordP15, ws7WordQ15]
  have hall := caps_of_representatives ws7WordRep15 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word15Weak
  intro i
  simpa [ws7WordCap15, ws7WordP15, ws7WordQ15] using hall i

noncomputable def ws7WordCap16 (i : Fin 7) : ℝ :=
  (ws7WordP16 i : ℝ) / (ws7WordQ16 i : ℝ)

def ws7WordRep16 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 3
  | 6 => 3
  | _ => 0

theorem ws7Word16WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep16 i) ≤ ws7WordCap16 (ws7WordRep16 i)) :
    WeakValidRates r
      (periodic ws7Word16.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word16)) := by
  have hrepLe : ∀ i, (ws7WordRep16 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap16 (ws7WordRep16 i) = ws7WordCap16 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap16, ws7WordRep16, ws7WordP16, ws7WordQ16]
  have hall := caps_of_representatives ws7WordRep16 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word16Weak
  intro i
  simpa [ws7WordCap16, ws7WordP16, ws7WordQ16] using hall i

noncomputable def ws7WordCap17 (i : Fin 7) : ℝ :=
  (ws7WordP17 i : ℝ) / (ws7WordQ17 i : ℝ)

def ws7WordRep17 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word17WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep17 i) ≤ ws7WordCap17 (ws7WordRep17 i)) :
    WeakValidRates r
      (periodic ws7Word17.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word17)) := by
  have hrepLe : ∀ i, (ws7WordRep17 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap17 (ws7WordRep17 i) = ws7WordCap17 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap17, ws7WordRep17, ws7WordP17, ws7WordQ17]
  have hall := caps_of_representatives ws7WordRep17 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word17Weak
  intro i
  simpa [ws7WordCap17, ws7WordP17, ws7WordQ17] using hall i

noncomputable def ws7WordCap18 (i : Fin 7) : ℝ :=
  (ws7WordP18 i : ℝ) / (ws7WordQ18 i : ℝ)

def ws7WordRep18 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 4
  | 5 => 4
  | 6 => 6
  | _ => 0

theorem ws7Word18WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep18 i) ≤ ws7WordCap18 (ws7WordRep18 i)) :
    WeakValidRates r
      (periodic ws7Word18.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word18)) := by
  have hrepLe : ∀ i, (ws7WordRep18 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap18 (ws7WordRep18 i) = ws7WordCap18 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap18, ws7WordRep18, ws7WordP18, ws7WordQ18]
  have hall := caps_of_representatives ws7WordRep18 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word18Weak
  intro i
  simpa [ws7WordCap18, ws7WordP18, ws7WordQ18] using hall i

noncomputable def ws7WordCap19 (i : Fin 7) : ℝ :=
  (ws7WordP19 i : ℝ) / (ws7WordQ19 i : ℝ)

def ws7WordRep19 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 3
  | 6 => 6
  | _ => 0

theorem ws7Word19WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep19 i) ≤ ws7WordCap19 (ws7WordRep19 i)) :
    WeakValidRates r
      (periodic ws7Word19.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word19)) := by
  have hrepLe : ∀ i, (ws7WordRep19 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap19 (ws7WordRep19 i) = ws7WordCap19 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap19, ws7WordRep19, ws7WordP19, ws7WordQ19]
  have hall := caps_of_representatives ws7WordRep19 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word19Weak
  intro i
  simpa [ws7WordCap19, ws7WordP19, ws7WordQ19] using hall i

noncomputable def ws7WordCap20 (i : Fin 7) : ℝ :=
  (ws7WordP20 i : ℝ) / (ws7WordQ20 i : ℝ)

def ws7WordRep20 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

theorem ws7Word20WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep20 i) ≤ ws7WordCap20 (ws7WordRep20 i)) :
    WeakValidRates r
      (periodic ws7Word20.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word20)) := by
  have hrepLe : ∀ i, (ws7WordRep20 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap20 (ws7WordRep20 i) = ws7WordCap20 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap20, ws7WordRep20, ws7WordP20, ws7WordQ20]
  have hall := caps_of_representatives ws7WordRep20 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word20Weak
  intro i
  simpa [ws7WordCap20, ws7WordP20, ws7WordQ20] using hall i

noncomputable def ws7WordCap21 (i : Fin 7) : ℝ :=
  (ws7WordP21 i : ℝ) / (ws7WordQ21 i : ℝ)

def ws7WordRep21 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word21WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep21 i) ≤ ws7WordCap21 (ws7WordRep21 i)) :
    WeakValidRates r
      (periodic ws7Word21.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word21)) := by
  have hrepLe : ∀ i, (ws7WordRep21 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap21 (ws7WordRep21 i) = ws7WordCap21 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap21, ws7WordRep21, ws7WordP21, ws7WordQ21]
  have hall := caps_of_representatives ws7WordRep21 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word21Weak
  intro i
  simpa [ws7WordCap21, ws7WordP21, ws7WordQ21] using hall i

noncomputable def ws7WordCap22 (i : Fin 7) : ℝ :=
  (ws7WordP22 i : ℝ) / (ws7WordQ22 i : ℝ)

def ws7WordRep22 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 6
  | _ => 0

theorem ws7Word22WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep22 i) ≤ ws7WordCap22 (ws7WordRep22 i)) :
    WeakValidRates r
      (periodic ws7Word22.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word22)) := by
  have hrepLe : ∀ i, (ws7WordRep22 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap22 (ws7WordRep22 i) = ws7WordCap22 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap22, ws7WordRep22, ws7WordP22, ws7WordQ22]
  have hall := caps_of_representatives ws7WordRep22 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word22Weak
  intro i
  simpa [ws7WordCap22, ws7WordP22, ws7WordQ22] using hall i

noncomputable def ws7WordCap23 (i : Fin 7) : ℝ :=
  (ws7WordP23 i : ℝ) / (ws7WordQ23 i : ℝ)

def ws7WordRep23 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

theorem ws7Word23WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep23 i) ≤ ws7WordCap23 (ws7WordRep23 i)) :
    WeakValidRates r
      (periodic ws7Word23.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word23)) := by
  have hrepLe : ∀ i, (ws7WordRep23 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap23 (ws7WordRep23 i) = ws7WordCap23 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap23, ws7WordRep23, ws7WordP23, ws7WordQ23]
  have hall := caps_of_representatives ws7WordRep23 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word23Weak
  intro i
  simpa [ws7WordCap23, ws7WordP23, ws7WordQ23] using hall i

noncomputable def ws7WordCap24 (i : Fin 7) : ℝ :=
  (ws7WordP24 i : ℝ) / (ws7WordQ24 i : ℝ)

def ws7WordRep24 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 3
  | 6 => 6
  | _ => 0

theorem ws7Word24WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep24 i) ≤ ws7WordCap24 (ws7WordRep24 i)) :
    WeakValidRates r
      (periodic ws7Word24.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word24)) := by
  have hrepLe : ∀ i, (ws7WordRep24 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap24 (ws7WordRep24 i) = ws7WordCap24 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap24, ws7WordRep24, ws7WordP24, ws7WordQ24]
  have hall := caps_of_representatives ws7WordRep24 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word24Weak
  intro i
  simpa [ws7WordCap24, ws7WordP24, ws7WordQ24] using hall i

noncomputable def ws7WordCap25 (i : Fin 7) : ℝ :=
  (ws7WordP25 i : ℝ) / (ws7WordQ25 i : ℝ)

def ws7WordRep25 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 3
  | 6 => 3
  | _ => 0

theorem ws7Word25WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep25 i) ≤ ws7WordCap25 (ws7WordRep25 i)) :
    WeakValidRates r
      (periodic ws7Word25.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word25)) := by
  have hrepLe : ∀ i, (ws7WordRep25 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap25 (ws7WordRep25 i) = ws7WordCap25 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap25, ws7WordRep25, ws7WordP25, ws7WordQ25]
  have hall := caps_of_representatives ws7WordRep25 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word25Weak
  intro i
  simpa [ws7WordCap25, ws7WordP25, ws7WordQ25] using hall i

noncomputable def ws7WordCap26 (i : Fin 7) : ℝ :=
  (ws7WordP26 i : ℝ) / (ws7WordQ26 i : ℝ)

def ws7WordRep26 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 3
  | 6 => 3
  | _ => 0

theorem ws7Word26WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep26 i) ≤ ws7WordCap26 (ws7WordRep26 i)) :
    WeakValidRates r
      (periodic ws7Word26.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word26)) := by
  have hrepLe : ∀ i, (ws7WordRep26 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap26 (ws7WordRep26 i) = ws7WordCap26 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap26, ws7WordRep26, ws7WordP26, ws7WordQ26]
  have hall := caps_of_representatives ws7WordRep26 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word26Weak
  intro i
  simpa [ws7WordCap26, ws7WordP26, ws7WordQ26] using hall i

noncomputable def ws7WordCap27 (i : Fin 7) : ℝ :=
  (ws7WordP27 i : ℝ) / (ws7WordQ27 i : ℝ)

def ws7WordRep27 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 3
  | 6 => 3
  | _ => 0

theorem ws7Word27WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep27 i) ≤ ws7WordCap27 (ws7WordRep27 i)) :
    WeakValidRates r
      (periodic ws7Word27.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word27)) := by
  have hrepLe : ∀ i, (ws7WordRep27 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap27 (ws7WordRep27 i) = ws7WordCap27 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap27, ws7WordRep27, ws7WordP27, ws7WordQ27]
  have hall := caps_of_representatives ws7WordRep27 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word27Weak
  intro i
  simpa [ws7WordCap27, ws7WordP27, ws7WordQ27] using hall i

noncomputable def ws7WordCap28 (i : Fin 7) : ℝ :=
  (ws7WordP28 i : ℝ) / (ws7WordQ28 i : ℝ)

def ws7WordRep28 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

theorem ws7Word28WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep28 i) ≤ ws7WordCap28 (ws7WordRep28 i)) :
    WeakValidRates r
      (periodic ws7Word28.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word28)) := by
  have hrepLe : ∀ i, (ws7WordRep28 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap28 (ws7WordRep28 i) = ws7WordCap28 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap28, ws7WordRep28, ws7WordP28, ws7WordQ28]
  have hall := caps_of_representatives ws7WordRep28 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word28Weak
  intro i
  simpa [ws7WordCap28, ws7WordP28, ws7WordQ28] using hall i

noncomputable def ws7WordCap29 (i : Fin 7) : ℝ :=
  (ws7WordP29 i : ℝ) / (ws7WordQ29 i : ℝ)

def ws7WordRep29 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 3
  | 4 => 3
  | 5 => 3
  | 6 => 6
  | _ => 0

theorem ws7Word29WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep29 i) ≤ ws7WordCap29 (ws7WordRep29 i)) :
    WeakValidRates r
      (periodic ws7Word29.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word29)) := by
  have hrepLe : ∀ i, (ws7WordRep29 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap29 (ws7WordRep29 i) = ws7WordCap29 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap29, ws7WordRep29, ws7WordP29, ws7WordQ29]
  have hall := caps_of_representatives ws7WordRep29 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word29Weak
  intro i
  simpa [ws7WordCap29, ws7WordP29, ws7WordQ29] using hall i

noncomputable def ws7WordCap30 (i : Fin 7) : ℝ :=
  (ws7WordP30 i : ℝ) / (ws7WordQ30 i : ℝ)

def ws7WordRep30 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word30WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep30 i) ≤ ws7WordCap30 (ws7WordRep30 i)) :
    WeakValidRates r
      (periodic ws7Word30.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word30)) := by
  have hrepLe : ∀ i, (ws7WordRep30 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap30 (ws7WordRep30 i) = ws7WordCap30 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap30, ws7WordRep30, ws7WordP30, ws7WordQ30]
  have hall := caps_of_representatives ws7WordRep30 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word30Weak
  intro i
  simpa [ws7WordCap30, ws7WordP30, ws7WordQ30] using hall i

noncomputable def ws7WordCap31 (i : Fin 7) : ℝ :=
  (ws7WordP31 i : ℝ) / (ws7WordQ31 i : ℝ)

def ws7WordRep31 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word31WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep31 i) ≤ ws7WordCap31 (ws7WordRep31 i)) :
    WeakValidRates r
      (periodic ws7Word31.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word31)) := by
  have hrepLe : ∀ i, (ws7WordRep31 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap31 (ws7WordRep31 i) = ws7WordCap31 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap31, ws7WordRep31, ws7WordP31, ws7WordQ31]
  have hall := caps_of_representatives ws7WordRep31 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word31Weak
  intro i
  simpa [ws7WordCap31, ws7WordP31, ws7WordQ31] using hall i

noncomputable def ws7WordCap32 (i : Fin 7) : ℝ :=
  (ws7WordP32 i : ℝ) / (ws7WordQ32 i : ℝ)

def ws7WordRep32 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

theorem ws7Word32WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep32 i) ≤ ws7WordCap32 (ws7WordRep32 i)) :
    WeakValidRates r
      (periodic ws7Word32.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word32)) := by
  have hrepLe : ∀ i, (ws7WordRep32 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap32 (ws7WordRep32 i) = ws7WordCap32 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap32, ws7WordRep32, ws7WordP32, ws7WordQ32]
  have hall := caps_of_representatives ws7WordRep32 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word32Weak
  intro i
  simpa [ws7WordCap32, ws7WordP32, ws7WordQ32] using hall i

noncomputable def ws7WordCap33 (i : Fin 7) : ℝ :=
  (ws7WordP33 i : ℝ) / (ws7WordQ33 i : ℝ)

def ws7WordRep33 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word33WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep33 i) ≤ ws7WordCap33 (ws7WordRep33 i)) :
    WeakValidRates r
      (periodic ws7Word33.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word33)) := by
  have hrepLe : ∀ i, (ws7WordRep33 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap33 (ws7WordRep33 i) = ws7WordCap33 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap33, ws7WordRep33, ws7WordP33, ws7WordQ33]
  have hall := caps_of_representatives ws7WordRep33 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word33Weak
  intro i
  simpa [ws7WordCap33, ws7WordP33, ws7WordQ33] using hall i

noncomputable def ws7WordCap34 (i : Fin 7) : ℝ :=
  (ws7WordP34 i : ℝ) / (ws7WordQ34 i : ℝ)

def ws7WordRep34 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

theorem ws7Word34WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep34 i) ≤ ws7WordCap34 (ws7WordRep34 i)) :
    WeakValidRates r
      (periodic ws7Word34.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word34)) := by
  have hrepLe : ∀ i, (ws7WordRep34 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap34 (ws7WordRep34 i) = ws7WordCap34 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap34, ws7WordRep34, ws7WordP34, ws7WordQ34]
  have hall := caps_of_representatives ws7WordRep34 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word34Weak
  intro i
  simpa [ws7WordCap34, ws7WordP34, ws7WordQ34] using hall i

noncomputable def ws7WordCap35 (i : Fin 7) : ℝ :=
  (ws7WordP35 i : ℝ) / (ws7WordQ35 i : ℝ)

def ws7WordRep35 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word35WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep35 i) ≤ ws7WordCap35 (ws7WordRep35 i)) :
    WeakValidRates r
      (periodic ws7Word35.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word35)) := by
  have hrepLe : ∀ i, (ws7WordRep35 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap35 (ws7WordRep35 i) = ws7WordCap35 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap35, ws7WordRep35, ws7WordP35, ws7WordQ35]
  have hall := caps_of_representatives ws7WordRep35 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word35Weak
  intro i
  simpa [ws7WordCap35, ws7WordP35, ws7WordQ35] using hall i

noncomputable def ws7WordCap36 (i : Fin 7) : ℝ :=
  (ws7WordP36 i : ℝ) / (ws7WordQ36 i : ℝ)

def ws7WordRep36 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word36WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep36 i) ≤ ws7WordCap36 (ws7WordRep36 i)) :
    WeakValidRates r
      (periodic ws7Word36.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word36)) := by
  have hrepLe : ∀ i, (ws7WordRep36 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap36 (ws7WordRep36 i) = ws7WordCap36 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap36, ws7WordRep36, ws7WordP36, ws7WordQ36]
  have hall := caps_of_representatives ws7WordRep36 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word36Weak
  intro i
  simpa [ws7WordCap36, ws7WordP36, ws7WordQ36] using hall i

noncomputable def ws7WordCap37 (i : Fin 7) : ℝ :=
  (ws7WordP37 i : ℝ) / (ws7WordQ37 i : ℝ)

def ws7WordRep37 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

theorem ws7Word37WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep37 i) ≤ ws7WordCap37 (ws7WordRep37 i)) :
    WeakValidRates r
      (periodic ws7Word37.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word37)) := by
  have hrepLe : ∀ i, (ws7WordRep37 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap37 (ws7WordRep37 i) = ws7WordCap37 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap37, ws7WordRep37, ws7WordP37, ws7WordQ37]
  have hall := caps_of_representatives ws7WordRep37 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word37Weak
  intro i
  simpa [ws7WordCap37, ws7WordP37, ws7WordQ37] using hall i

noncomputable def ws7WordCap38 (i : Fin 7) : ℝ :=
  (ws7WordP38 i : ℝ) / (ws7WordQ38 i : ℝ)

def ws7WordRep38 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 6
  | _ => 0

theorem ws7Word38WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep38 i) ≤ ws7WordCap38 (ws7WordRep38 i)) :
    WeakValidRates r
      (periodic ws7Word38.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word38)) := by
  have hrepLe : ∀ i, (ws7WordRep38 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap38 (ws7WordRep38 i) = ws7WordCap38 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap38, ws7WordRep38, ws7WordP38, ws7WordQ38]
  have hall := caps_of_representatives ws7WordRep38 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word38Weak
  intro i
  simpa [ws7WordCap38, ws7WordP38, ws7WordQ38] using hall i

noncomputable def ws7WordCap39 (i : Fin 7) : ℝ :=
  (ws7WordP39 i : ℝ) / (ws7WordQ39 i : ℝ)

def ws7WordRep39 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

theorem ws7Word39WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep39 i) ≤ ws7WordCap39 (ws7WordRep39 i)) :
    WeakValidRates r
      (periodic ws7Word39.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word39)) := by
  have hrepLe : ∀ i, (ws7WordRep39 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap39 (ws7WordRep39 i) = ws7WordCap39 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap39, ws7WordRep39, ws7WordP39, ws7WordQ39]
  have hall := caps_of_representatives ws7WordRep39 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word39Weak
  intro i
  simpa [ws7WordCap39, ws7WordP39, ws7WordQ39] using hall i

noncomputable def ws7WordCap40 (i : Fin 7) : ℝ :=
  (ws7WordP40 i : ℝ) / (ws7WordQ40 i : ℝ)

def ws7WordRep40 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 3
  | 6 => 3
  | _ => 0

theorem ws7Word40WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep40 i) ≤ ws7WordCap40 (ws7WordRep40 i)) :
    WeakValidRates r
      (periodic ws7Word40.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word40)) := by
  have hrepLe : ∀ i, (ws7WordRep40 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap40 (ws7WordRep40 i) = ws7WordCap40 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap40, ws7WordRep40, ws7WordP40, ws7WordQ40]
  have hall := caps_of_representatives ws7WordRep40 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word40Weak
  intro i
  simpa [ws7WordCap40, ws7WordP40, ws7WordQ40] using hall i

noncomputable def ws7WordCap41 (i : Fin 7) : ℝ :=
  (ws7WordP41 i : ℝ) / (ws7WordQ41 i : ℝ)

def ws7WordRep41 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word41WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep41 i) ≤ ws7WordCap41 (ws7WordRep41 i)) :
    WeakValidRates r
      (periodic ws7Word41.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word41)) := by
  have hrepLe : ∀ i, (ws7WordRep41 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap41 (ws7WordRep41 i) = ws7WordCap41 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap41, ws7WordRep41, ws7WordP41, ws7WordQ41]
  have hall := caps_of_representatives ws7WordRep41 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word41Weak
  intro i
  simpa [ws7WordCap41, ws7WordP41, ws7WordQ41] using hall i

noncomputable def ws7WordCap42 (i : Fin 7) : ℝ :=
  (ws7WordP42 i : ℝ) / (ws7WordQ42 i : ℝ)

def ws7WordRep42 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

theorem ws7Word42WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep42 i) ≤ ws7WordCap42 (ws7WordRep42 i)) :
    WeakValidRates r
      (periodic ws7Word42.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word42)) := by
  have hrepLe : ∀ i, (ws7WordRep42 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap42 (ws7WordRep42 i) = ws7WordCap42 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap42, ws7WordRep42, ws7WordP42, ws7WordQ42]
  have hall := caps_of_representatives ws7WordRep42 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word42Weak
  intro i
  simpa [ws7WordCap42, ws7WordP42, ws7WordQ42] using hall i

noncomputable def ws7WordCap43 (i : Fin 7) : ℝ :=
  (ws7WordP43 i : ℝ) / (ws7WordQ43 i : ℝ)

def ws7WordRep43 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word43WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep43 i) ≤ ws7WordCap43 (ws7WordRep43 i)) :
    WeakValidRates r
      (periodic ws7Word43.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word43)) := by
  have hrepLe : ∀ i, (ws7WordRep43 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap43 (ws7WordRep43 i) = ws7WordCap43 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap43, ws7WordRep43, ws7WordP43, ws7WordQ43]
  have hall := caps_of_representatives ws7WordRep43 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word43Weak
  intro i
  simpa [ws7WordCap43, ws7WordP43, ws7WordQ43] using hall i

noncomputable def ws7WordCap44 (i : Fin 7) : ℝ :=
  (ws7WordP44 i : ℝ) / (ws7WordQ44 i : ℝ)

def ws7WordRep44 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word44WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep44 i) ≤ ws7WordCap44 (ws7WordRep44 i)) :
    WeakValidRates r
      (periodic ws7Word44.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word44)) := by
  have hrepLe : ∀ i, (ws7WordRep44 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap44 (ws7WordRep44 i) = ws7WordCap44 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap44, ws7WordRep44, ws7WordP44, ws7WordQ44]
  have hall := caps_of_representatives ws7WordRep44 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word44Weak
  intro i
  simpa [ws7WordCap44, ws7WordP44, ws7WordQ44] using hall i

noncomputable def ws7WordCap45 (i : Fin 7) : ℝ :=
  (ws7WordP45 i : ℝ) / (ws7WordQ45 i : ℝ)

def ws7WordRep45 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 2
  | 5 => 2
  | 6 => 2
  | _ => 0

theorem ws7Word45WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep45 i) ≤ ws7WordCap45 (ws7WordRep45 i)) :
    WeakValidRates r
      (periodic ws7Word45.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word45)) := by
  have hrepLe : ∀ i, (ws7WordRep45 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap45 (ws7WordRep45 i) = ws7WordCap45 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap45, ws7WordRep45, ws7WordP45, ws7WordQ45]
  have hall := caps_of_representatives ws7WordRep45 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word45Weak
  intro i
  simpa [ws7WordCap45, ws7WordP45, ws7WordQ45] using hall i

noncomputable def ws7WordCap46 (i : Fin 7) : ℝ :=
  (ws7WordP46 i : ℝ) / (ws7WordQ46 i : ℝ)

def ws7WordRep46 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 3
  | 4 => 3
  | 5 => 3
  | 6 => 3
  | _ => 0

theorem ws7Word46WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep46 i) ≤ ws7WordCap46 (ws7WordRep46 i)) :
    WeakValidRates r
      (periodic ws7Word46.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word46)) := by
  have hrepLe : ∀ i, (ws7WordRep46 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap46 (ws7WordRep46 i) = ws7WordCap46 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap46, ws7WordRep46, ws7WordP46, ws7WordQ46]
  have hall := caps_of_representatives ws7WordRep46 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word46Weak
  intro i
  simpa [ws7WordCap46, ws7WordP46, ws7WordQ46] using hall i

noncomputable def ws7WordCap47 (i : Fin 7) : ℝ :=
  (ws7WordP47 i : ℝ) / (ws7WordQ47 i : ℝ)

def ws7WordRep47 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 6
  | _ => 0

theorem ws7Word47WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep47 i) ≤ ws7WordCap47 (ws7WordRep47 i)) :
    WeakValidRates r
      (periodic ws7Word47.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word47)) := by
  have hrepLe : ∀ i, (ws7WordRep47 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap47 (ws7WordRep47 i) = ws7WordCap47 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap47, ws7WordRep47, ws7WordP47, ws7WordQ47]
  have hall := caps_of_representatives ws7WordRep47 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word47Weak
  intro i
  simpa [ws7WordCap47, ws7WordP47, ws7WordQ47] using hall i

noncomputable def ws7WordCap48 (i : Fin 7) : ℝ :=
  (ws7WordP48 i : ℝ) / (ws7WordQ48 i : ℝ)

def ws7WordRep48 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

theorem ws7Word48WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep48 i) ≤ ws7WordCap48 (ws7WordRep48 i)) :
    WeakValidRates r
      (periodic ws7Word48.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word48)) := by
  have hrepLe : ∀ i, (ws7WordRep48 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap48 (ws7WordRep48 i) = ws7WordCap48 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap48, ws7WordRep48, ws7WordP48, ws7WordQ48]
  have hall := caps_of_representatives ws7WordRep48 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word48Weak
  intro i
  simpa [ws7WordCap48, ws7WordP48, ws7WordQ48] using hall i

noncomputable def ws7WordCap49 (i : Fin 7) : ℝ :=
  (ws7WordP49 i : ℝ) / (ws7WordQ49 i : ℝ)

def ws7WordRep49 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 0
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word49WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep49 i) ≤ ws7WordCap49 (ws7WordRep49 i)) :
    WeakValidRates r
      (periodic ws7Word49.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word49)) := by
  have hrepLe : ∀ i, (ws7WordRep49 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap49 (ws7WordRep49 i) = ws7WordCap49 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap49, ws7WordRep49, ws7WordP49, ws7WordQ49]
  have hall := caps_of_representatives ws7WordRep49 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word49Weak
  intro i
  simpa [ws7WordCap49, ws7WordP49, ws7WordQ49] using hall i

noncomputable def ws7WordCap50 (i : Fin 7) : ℝ :=
  (ws7WordP50 i : ℝ) / (ws7WordQ50 i : ℝ)

def ws7WordRep50 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 2
  | 5 => 2
  | 6 => 2
  | _ => 0

theorem ws7Word50WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep50 i) ≤ ws7WordCap50 (ws7WordRep50 i)) :
    WeakValidRates r
      (periodic ws7Word50.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word50)) := by
  have hrepLe : ∀ i, (ws7WordRep50 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap50 (ws7WordRep50 i) = ws7WordCap50 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap50, ws7WordRep50, ws7WordP50, ws7WordQ50]
  have hall := caps_of_representatives ws7WordRep50 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word50Weak
  intro i
  simpa [ws7WordCap50, ws7WordP50, ws7WordQ50] using hall i

noncomputable def ws7WordCap51 (i : Fin 7) : ℝ :=
  (ws7WordP51 i : ℝ) / (ws7WordQ51 i : ℝ)

def ws7WordRep51 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

theorem ws7Word51WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep51 i) ≤ ws7WordCap51 (ws7WordRep51 i)) :
    WeakValidRates r
      (periodic ws7Word51.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word51)) := by
  have hrepLe : ∀ i, (ws7WordRep51 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap51 (ws7WordRep51 i) = ws7WordCap51 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap51, ws7WordRep51, ws7WordP51, ws7WordQ51]
  have hall := caps_of_representatives ws7WordRep51 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word51Weak
  intro i
  simpa [ws7WordCap51, ws7WordP51, ws7WordQ51] using hall i

noncomputable def ws7WordCap52 (i : Fin 7) : ℝ :=
  (ws7WordP52 i : ℝ) / (ws7WordQ52 i : ℝ)

def ws7WordRep52 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 6
  | _ => 0

theorem ws7Word52WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep52 i) ≤ ws7WordCap52 (ws7WordRep52 i)) :
    WeakValidRates r
      (periodic ws7Word52.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word52)) := by
  have hrepLe : ∀ i, (ws7WordRep52 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap52 (ws7WordRep52 i) = ws7WordCap52 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap52, ws7WordRep52, ws7WordP52, ws7WordQ52]
  have hall := caps_of_representatives ws7WordRep52 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word52Weak
  intro i
  simpa [ws7WordCap52, ws7WordP52, ws7WordQ52] using hall i

noncomputable def ws7WordCap53 (i : Fin 7) : ℝ :=
  (ws7WordP53 i : ℝ) / (ws7WordQ53 i : ℝ)

def ws7WordRep53 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 6
  | _ => 0

theorem ws7Word53WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep53 i) ≤ ws7WordCap53 (ws7WordRep53 i)) :
    WeakValidRates r
      (periodic ws7Word53.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word53)) := by
  have hrepLe : ∀ i, (ws7WordRep53 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap53 (ws7WordRep53 i) = ws7WordCap53 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap53, ws7WordRep53, ws7WordP53, ws7WordQ53]
  have hall := caps_of_representatives ws7WordRep53 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word53Weak
  intro i
  simpa [ws7WordCap53, ws7WordP53, ws7WordQ53] using hall i

noncomputable def ws7WordCap54 (i : Fin 7) : ℝ :=
  (ws7WordP54 i : ℝ) / (ws7WordQ54 i : ℝ)

def ws7WordRep54 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word54WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep54 i) ≤ ws7WordCap54 (ws7WordRep54 i)) :
    WeakValidRates r
      (periodic ws7Word54.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word54)) := by
  have hrepLe : ∀ i, (ws7WordRep54 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap54 (ws7WordRep54 i) = ws7WordCap54 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap54, ws7WordRep54, ws7WordP54, ws7WordQ54]
  have hall := caps_of_representatives ws7WordRep54 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word54Weak
  intro i
  simpa [ws7WordCap54, ws7WordP54, ws7WordQ54] using hall i

noncomputable def ws7WordCap55 (i : Fin 7) : ℝ :=
  (ws7WordP55 i : ℝ) / (ws7WordQ55 i : ℝ)

def ws7WordRep55 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word55WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep55 i) ≤ ws7WordCap55 (ws7WordRep55 i)) :
    WeakValidRates r
      (periodic ws7Word55.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word55)) := by
  have hrepLe : ∀ i, (ws7WordRep55 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap55 (ws7WordRep55 i) = ws7WordCap55 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap55, ws7WordRep55, ws7WordP55, ws7WordQ55]
  have hall := caps_of_representatives ws7WordRep55 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word55Weak
  intro i
  simpa [ws7WordCap55, ws7WordP55, ws7WordQ55] using hall i

noncomputable def ws7WordCap56 (i : Fin 7) : ℝ :=
  (ws7WordP56 i : ℝ) / (ws7WordQ56 i : ℝ)

def ws7WordRep56 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 2
  | 5 => 2
  | 6 => 2
  | _ => 0

theorem ws7Word56WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep56 i) ≤ ws7WordCap56 (ws7WordRep56 i)) :
    WeakValidRates r
      (periodic ws7Word56.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word56)) := by
  have hrepLe : ∀ i, (ws7WordRep56 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap56 (ws7WordRep56 i) = ws7WordCap56 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap56, ws7WordRep56, ws7WordP56, ws7WordQ56]
  have hall := caps_of_representatives ws7WordRep56 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word56Weak
  intro i
  simpa [ws7WordCap56, ws7WordP56, ws7WordQ56] using hall i

noncomputable def ws7WordCap57 (i : Fin 7) : ℝ :=
  (ws7WordP57 i : ℝ) / (ws7WordQ57 i : ℝ)

def ws7WordRep57 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

theorem ws7Word57WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep57 i) ≤ ws7WordCap57 (ws7WordRep57 i)) :
    WeakValidRates r
      (periodic ws7Word57.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word57)) := by
  have hrepLe : ∀ i, (ws7WordRep57 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap57 (ws7WordRep57 i) = ws7WordCap57 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap57, ws7WordRep57, ws7WordP57, ws7WordQ57]
  have hall := caps_of_representatives ws7WordRep57 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word57Weak
  intro i
  simpa [ws7WordCap57, ws7WordP57, ws7WordQ57] using hall i

noncomputable def ws7WordCap58 (i : Fin 7) : ℝ :=
  (ws7WordP58 i : ℝ) / (ws7WordQ58 i : ℝ)

def ws7WordRep58 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 2
  | 5 => 2
  | 6 => 2
  | _ => 0

theorem ws7Word58WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep58 i) ≤ ws7WordCap58 (ws7WordRep58 i)) :
    WeakValidRates r
      (periodic ws7Word58.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word58)) := by
  have hrepLe : ∀ i, (ws7WordRep58 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap58 (ws7WordRep58 i) = ws7WordCap58 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap58, ws7WordRep58, ws7WordP58, ws7WordQ58]
  have hall := caps_of_representatives ws7WordRep58 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word58Weak
  intro i
  simpa [ws7WordCap58, ws7WordP58, ws7WordQ58] using hall i

noncomputable def ws7WordCap59 (i : Fin 7) : ℝ :=
  (ws7WordP59 i : ℝ) / (ws7WordQ59 i : ℝ)

def ws7WordRep59 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word59WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep59 i) ≤ ws7WordCap59 (ws7WordRep59 i)) :
    WeakValidRates r
      (periodic ws7Word59.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word59)) := by
  have hrepLe : ∀ i, (ws7WordRep59 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap59 (ws7WordRep59 i) = ws7WordCap59 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap59, ws7WordRep59, ws7WordP59, ws7WordQ59]
  have hall := caps_of_representatives ws7WordRep59 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word59Weak
  intro i
  simpa [ws7WordCap59, ws7WordP59, ws7WordQ59] using hall i

noncomputable def ws7WordCap60 (i : Fin 7) : ℝ :=
  (ws7WordP60 i : ℝ) / (ws7WordQ60 i : ℝ)

def ws7WordRep60 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word60WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep60 i) ≤ ws7WordCap60 (ws7WordRep60 i)) :
    WeakValidRates r
      (periodic ws7Word60.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word60)) := by
  have hrepLe : ∀ i, (ws7WordRep60 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap60 (ws7WordRep60 i) = ws7WordCap60 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap60, ws7WordRep60, ws7WordP60, ws7WordQ60]
  have hall := caps_of_representatives ws7WordRep60 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word60Weak
  intro i
  simpa [ws7WordCap60, ws7WordP60, ws7WordQ60] using hall i

noncomputable def ws7WordCap61 (i : Fin 7) : ℝ :=
  (ws7WordP61 i : ℝ) / (ws7WordQ61 i : ℝ)

def ws7WordRep61 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word61WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep61 i) ≤ ws7WordCap61 (ws7WordRep61 i)) :
    WeakValidRates r
      (periodic ws7Word61.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word61)) := by
  have hrepLe : ∀ i, (ws7WordRep61 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap61 (ws7WordRep61 i) = ws7WordCap61 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap61, ws7WordRep61, ws7WordP61, ws7WordQ61]
  have hall := caps_of_representatives ws7WordRep61 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word61Weak
  intro i
  simpa [ws7WordCap61, ws7WordP61, ws7WordQ61] using hall i

noncomputable def ws7WordCap62 (i : Fin 7) : ℝ :=
  (ws7WordP62 i : ℝ) / (ws7WordQ62 i : ℝ)

def ws7WordRep62 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word62WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep62 i) ≤ ws7WordCap62 (ws7WordRep62 i)) :
    WeakValidRates r
      (periodic ws7Word62.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word62)) := by
  have hrepLe : ∀ i, (ws7WordRep62 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap62 (ws7WordRep62 i) = ws7WordCap62 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap62, ws7WordRep62, ws7WordP62, ws7WordQ62]
  have hall := caps_of_representatives ws7WordRep62 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word62Weak
  intro i
  simpa [ws7WordCap62, ws7WordP62, ws7WordQ62] using hall i

noncomputable def ws7WordCap63 (i : Fin 7) : ℝ :=
  (ws7WordP63 i : ℝ) / (ws7WordQ63 i : ℝ)

def ws7WordRep63 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 3
  | 6 => 6
  | _ => 0

theorem ws7Word63WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep63 i) ≤ ws7WordCap63 (ws7WordRep63 i)) :
    WeakValidRates r
      (periodic ws7Word63.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word63)) := by
  have hrepLe : ∀ i, (ws7WordRep63 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap63 (ws7WordRep63 i) = ws7WordCap63 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap63, ws7WordRep63, ws7WordP63, ws7WordQ63]
  have hall := caps_of_representatives ws7WordRep63 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word63Weak
  intro i
  simpa [ws7WordCap63, ws7WordP63, ws7WordQ63] using hall i

noncomputable def ws7WordCap64 (i : Fin 7) : ℝ :=
  (ws7WordP64 i : ℝ) / (ws7WordQ64 i : ℝ)

def ws7WordRep64 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 4
  | 5 => 4
  | 6 => 6
  | _ => 0

theorem ws7Word64WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep64 i) ≤ ws7WordCap64 (ws7WordRep64 i)) :
    WeakValidRates r
      (periodic ws7Word64.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word64)) := by
  have hrepLe : ∀ i, (ws7WordRep64 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap64 (ws7WordRep64 i) = ws7WordCap64 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap64, ws7WordRep64, ws7WordP64, ws7WordQ64]
  have hall := caps_of_representatives ws7WordRep64 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word64Weak
  intro i
  simpa [ws7WordCap64, ws7WordP64, ws7WordQ64] using hall i

noncomputable def ws7WordCap65 (i : Fin 7) : ℝ :=
  (ws7WordP65 i : ℝ) / (ws7WordQ65 i : ℝ)

def ws7WordRep65 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word65WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep65 i) ≤ ws7WordCap65 (ws7WordRep65 i)) :
    WeakValidRates r
      (periodic ws7Word65.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word65)) := by
  have hrepLe : ∀ i, (ws7WordRep65 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap65 (ws7WordRep65 i) = ws7WordCap65 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap65, ws7WordRep65, ws7WordP65, ws7WordQ65]
  have hall := caps_of_representatives ws7WordRep65 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word65Weak
  intro i
  simpa [ws7WordCap65, ws7WordP65, ws7WordQ65] using hall i

noncomputable def ws7WordCap66 (i : Fin 7) : ℝ :=
  (ws7WordP66 i : ℝ) / (ws7WordQ66 i : ℝ)

def ws7WordRep66 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word66WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep66 i) ≤ ws7WordCap66 (ws7WordRep66 i)) :
    WeakValidRates r
      (periodic ws7Word66.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word66)) := by
  have hrepLe : ∀ i, (ws7WordRep66 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap66 (ws7WordRep66 i) = ws7WordCap66 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap66, ws7WordRep66, ws7WordP66, ws7WordQ66]
  have hall := caps_of_representatives ws7WordRep66 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word66Weak
  intro i
  simpa [ws7WordCap66, ws7WordP66, ws7WordQ66] using hall i

noncomputable def ws7WordCap67 (i : Fin 7) : ℝ :=
  (ws7WordP67 i : ℝ) / (ws7WordQ67 i : ℝ)

def ws7WordRep67 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 6
  | _ => 0

theorem ws7Word67WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep67 i) ≤ ws7WordCap67 (ws7WordRep67 i)) :
    WeakValidRates r
      (periodic ws7Word67.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word67)) := by
  have hrepLe : ∀ i, (ws7WordRep67 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap67 (ws7WordRep67 i) = ws7WordCap67 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap67, ws7WordRep67, ws7WordP67, ws7WordQ67]
  have hall := caps_of_representatives ws7WordRep67 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word67Weak
  intro i
  simpa [ws7WordCap67, ws7WordP67, ws7WordQ67] using hall i

noncomputable def ws7WordCap68 (i : Fin 7) : ℝ :=
  (ws7WordP68 i : ℝ) / (ws7WordQ68 i : ℝ)

def ws7WordRep68 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

theorem ws7Word68WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep68 i) ≤ ws7WordCap68 (ws7WordRep68 i)) :
    WeakValidRates r
      (periodic ws7Word68.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word68)) := by
  have hrepLe : ∀ i, (ws7WordRep68 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap68 (ws7WordRep68 i) = ws7WordCap68 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap68, ws7WordRep68, ws7WordP68, ws7WordQ68]
  have hall := caps_of_representatives ws7WordRep68 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word68Weak
  intro i
  simpa [ws7WordCap68, ws7WordP68, ws7WordQ68] using hall i

noncomputable def ws7WordCap69 (i : Fin 7) : ℝ :=
  (ws7WordP69 i : ℝ) / (ws7WordQ69 i : ℝ)

def ws7WordRep69 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word69WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep69 i) ≤ ws7WordCap69 (ws7WordRep69 i)) :
    WeakValidRates r
      (periodic ws7Word69.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word69)) := by
  have hrepLe : ∀ i, (ws7WordRep69 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap69 (ws7WordRep69 i) = ws7WordCap69 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap69, ws7WordRep69, ws7WordP69, ws7WordQ69]
  have hall := caps_of_representatives ws7WordRep69 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word69Weak
  intro i
  simpa [ws7WordCap69, ws7WordP69, ws7WordQ69] using hall i

noncomputable def ws7WordCap70 (i : Fin 7) : ℝ :=
  (ws7WordP70 i : ℝ) / (ws7WordQ70 i : ℝ)

def ws7WordRep70 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word70WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep70 i) ≤ ws7WordCap70 (ws7WordRep70 i)) :
    WeakValidRates r
      (periodic ws7Word70.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word70)) := by
  have hrepLe : ∀ i, (ws7WordRep70 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap70 (ws7WordRep70 i) = ws7WordCap70 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap70, ws7WordRep70, ws7WordP70, ws7WordQ70]
  have hall := caps_of_representatives ws7WordRep70 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word70Weak
  intro i
  simpa [ws7WordCap70, ws7WordP70, ws7WordQ70] using hall i

noncomputable def ws7WordCap71 (i : Fin 7) : ℝ :=
  (ws7WordP71 i : ℝ) / (ws7WordQ71 i : ℝ)

def ws7WordRep71 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 6
  | _ => 0

theorem ws7Word71WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep71 i) ≤ ws7WordCap71 (ws7WordRep71 i)) :
    WeakValidRates r
      (periodic ws7Word71.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word71)) := by
  have hrepLe : ∀ i, (ws7WordRep71 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap71 (ws7WordRep71 i) = ws7WordCap71 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap71, ws7WordRep71, ws7WordP71, ws7WordQ71]
  have hall := caps_of_representatives ws7WordRep71 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word71Weak
  intro i
  simpa [ws7WordCap71, ws7WordP71, ws7WordQ71] using hall i

noncomputable def ws7WordCap72 (i : Fin 7) : ℝ :=
  (ws7WordP72 i : ℝ) / (ws7WordQ72 i : ℝ)

def ws7WordRep72 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word72WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep72 i) ≤ ws7WordCap72 (ws7WordRep72 i)) :
    WeakValidRates r
      (periodic ws7Word72.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word72)) := by
  have hrepLe : ∀ i, (ws7WordRep72 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap72 (ws7WordRep72 i) = ws7WordCap72 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap72, ws7WordRep72, ws7WordP72, ws7WordQ72]
  have hall := caps_of_representatives ws7WordRep72 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word72Weak
  intro i
  simpa [ws7WordCap72, ws7WordP72, ws7WordQ72] using hall i

noncomputable def ws7WordCap73 (i : Fin 7) : ℝ :=
  (ws7WordP73 i : ℝ) / (ws7WordQ73 i : ℝ)

def ws7WordRep73 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word73WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep73 i) ≤ ws7WordCap73 (ws7WordRep73 i)) :
    WeakValidRates r
      (periodic ws7Word73.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word73)) := by
  have hrepLe : ∀ i, (ws7WordRep73 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap73 (ws7WordRep73 i) = ws7WordCap73 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap73, ws7WordRep73, ws7WordP73, ws7WordQ73]
  have hall := caps_of_representatives ws7WordRep73 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word73Weak
  intro i
  simpa [ws7WordCap73, ws7WordP73, ws7WordQ73] using hall i

noncomputable def ws7WordCap74 (i : Fin 7) : ℝ :=
  (ws7WordP74 i : ℝ) / (ws7WordQ74 i : ℝ)

def ws7WordRep74 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word74WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep74 i) ≤ ws7WordCap74 (ws7WordRep74 i)) :
    WeakValidRates r
      (periodic ws7Word74.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word74)) := by
  have hrepLe : ∀ i, (ws7WordRep74 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap74 (ws7WordRep74 i) = ws7WordCap74 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap74, ws7WordRep74, ws7WordP74, ws7WordQ74]
  have hall := caps_of_representatives ws7WordRep74 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word74Weak
  intro i
  simpa [ws7WordCap74, ws7WordP74, ws7WordQ74] using hall i

noncomputable def ws7WordCap75 (i : Fin 7) : ℝ :=
  (ws7WordP75 i : ℝ) / (ws7WordQ75 i : ℝ)

def ws7WordRep75 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word75WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep75 i) ≤ ws7WordCap75 (ws7WordRep75 i)) :
    WeakValidRates r
      (periodic ws7Word75.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word75)) := by
  have hrepLe : ∀ i, (ws7WordRep75 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap75 (ws7WordRep75 i) = ws7WordCap75 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap75, ws7WordRep75, ws7WordP75, ws7WordQ75]
  have hall := caps_of_representatives ws7WordRep75 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word75Weak
  intro i
  simpa [ws7WordCap75, ws7WordP75, ws7WordQ75] using hall i

noncomputable def ws7WordCap76 (i : Fin 7) : ℝ :=
  (ws7WordP76 i : ℝ) / (ws7WordQ76 i : ℝ)

def ws7WordRep76 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word76WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep76 i) ≤ ws7WordCap76 (ws7WordRep76 i)) :
    WeakValidRates r
      (periodic ws7Word76.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word76)) := by
  have hrepLe : ∀ i, (ws7WordRep76 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap76 (ws7WordRep76 i) = ws7WordCap76 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap76, ws7WordRep76, ws7WordP76, ws7WordQ76]
  have hall := caps_of_representatives ws7WordRep76 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word76Weak
  intro i
  simpa [ws7WordCap76, ws7WordP76, ws7WordQ76] using hall i

noncomputable def ws7WordCap77 (i : Fin 7) : ℝ :=
  (ws7WordP77 i : ℝ) / (ws7WordQ77 i : ℝ)

def ws7WordRep77 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word77WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep77 i) ≤ ws7WordCap77 (ws7WordRep77 i)) :
    WeakValidRates r
      (periodic ws7Word77.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word77)) := by
  have hrepLe : ∀ i, (ws7WordRep77 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap77 (ws7WordRep77 i) = ws7WordCap77 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap77, ws7WordRep77, ws7WordP77, ws7WordQ77]
  have hall := caps_of_representatives ws7WordRep77 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word77Weak
  intro i
  simpa [ws7WordCap77, ws7WordP77, ws7WordQ77] using hall i

noncomputable def ws7WordCap78 (i : Fin 7) : ℝ :=
  (ws7WordP78 i : ℝ) / (ws7WordQ78 i : ℝ)

def ws7WordRep78 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 6
  | _ => 0

theorem ws7Word78WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep78 i) ≤ ws7WordCap78 (ws7WordRep78 i)) :
    WeakValidRates r
      (periodic ws7Word78.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word78)) := by
  have hrepLe : ∀ i, (ws7WordRep78 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap78 (ws7WordRep78 i) = ws7WordCap78 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap78, ws7WordRep78, ws7WordP78, ws7WordQ78]
  have hall := caps_of_representatives ws7WordRep78 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word78Weak
  intro i
  simpa [ws7WordCap78, ws7WordP78, ws7WordQ78] using hall i

noncomputable def ws7WordCap79 (i : Fin 7) : ℝ :=
  (ws7WordP79 i : ℝ) / (ws7WordQ79 i : ℝ)

def ws7WordRep79 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word79WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep79 i) ≤ ws7WordCap79 (ws7WordRep79 i)) :
    WeakValidRates r
      (periodic ws7Word79.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word79)) := by
  have hrepLe : ∀ i, (ws7WordRep79 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap79 (ws7WordRep79 i) = ws7WordCap79 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap79, ws7WordRep79, ws7WordP79, ws7WordQ79]
  have hall := caps_of_representatives ws7WordRep79 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word79Weak
  intro i
  simpa [ws7WordCap79, ws7WordP79, ws7WordQ79] using hall i

noncomputable def ws7WordCap80 (i : Fin 7) : ℝ :=
  (ws7WordP80 i : ℝ) / (ws7WordQ80 i : ℝ)

def ws7WordRep80 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 3
  | 6 => 3
  | _ => 0

theorem ws7Word80WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep80 i) ≤ ws7WordCap80 (ws7WordRep80 i)) :
    WeakValidRates r
      (periodic ws7Word80.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word80)) := by
  have hrepLe : ∀ i, (ws7WordRep80 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap80 (ws7WordRep80 i) = ws7WordCap80 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap80, ws7WordRep80, ws7WordP80, ws7WordQ80]
  have hall := caps_of_representatives ws7WordRep80 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word80Weak
  intro i
  simpa [ws7WordCap80, ws7WordP80, ws7WordQ80] using hall i

noncomputable def ws7WordCap81 (i : Fin 7) : ℝ :=
  (ws7WordP81 i : ℝ) / (ws7WordQ81 i : ℝ)

def ws7WordRep81 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word81WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep81 i) ≤ ws7WordCap81 (ws7WordRep81 i)) :
    WeakValidRates r
      (periodic ws7Word81.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word81)) := by
  have hrepLe : ∀ i, (ws7WordRep81 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap81 (ws7WordRep81 i) = ws7WordCap81 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap81, ws7WordRep81, ws7WordP81, ws7WordQ81]
  have hall := caps_of_representatives ws7WordRep81 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word81Weak
  intro i
  simpa [ws7WordCap81, ws7WordP81, ws7WordQ81] using hall i

noncomputable def ws7WordCap82 (i : Fin 7) : ℝ :=
  (ws7WordP82 i : ℝ) / (ws7WordQ82 i : ℝ)

def ws7WordRep82 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word82WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep82 i) ≤ ws7WordCap82 (ws7WordRep82 i)) :
    WeakValidRates r
      (periodic ws7Word82.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word82)) := by
  have hrepLe : ∀ i, (ws7WordRep82 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap82 (ws7WordRep82 i) = ws7WordCap82 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap82, ws7WordRep82, ws7WordP82, ws7WordQ82]
  have hall := caps_of_representatives ws7WordRep82 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word82Weak
  intro i
  simpa [ws7WordCap82, ws7WordP82, ws7WordQ82] using hall i

noncomputable def ws7WordCap83 (i : Fin 7) : ℝ :=
  (ws7WordP83 i : ℝ) / (ws7WordQ83 i : ℝ)

def ws7WordRep83 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 2
  | 5 => 2
  | 6 => 2
  | _ => 0

theorem ws7Word83WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep83 i) ≤ ws7WordCap83 (ws7WordRep83 i)) :
    WeakValidRates r
      (periodic ws7Word83.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word83)) := by
  have hrepLe : ∀ i, (ws7WordRep83 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap83 (ws7WordRep83 i) = ws7WordCap83 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap83, ws7WordRep83, ws7WordP83, ws7WordQ83]
  have hall := caps_of_representatives ws7WordRep83 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word83Weak
  intro i
  simpa [ws7WordCap83, ws7WordP83, ws7WordQ83] using hall i

noncomputable def ws7WordCap84 (i : Fin 7) : ℝ :=
  (ws7WordP84 i : ℝ) / (ws7WordQ84 i : ℝ)

def ws7WordRep84 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 0
  | 2 => 2
  | 3 => 2
  | 4 => 2
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word84WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep84 i) ≤ ws7WordCap84 (ws7WordRep84 i)) :
    WeakValidRates r
      (periodic ws7Word84.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word84)) := by
  have hrepLe : ∀ i, (ws7WordRep84 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap84 (ws7WordRep84 i) = ws7WordCap84 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap84, ws7WordRep84, ws7WordP84, ws7WordQ84]
  have hall := caps_of_representatives ws7WordRep84 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word84Weak
  intro i
  simpa [ws7WordCap84, ws7WordP84, ws7WordQ84] using hall i

noncomputable def ws7WordCap85 (i : Fin 7) : ℝ :=
  (ws7WordP85 i : ℝ) / (ws7WordQ85 i : ℝ)

def ws7WordRep85 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

theorem ws7Word85WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep85 i) ≤ ws7WordCap85 (ws7WordRep85 i)) :
    WeakValidRates r
      (periodic ws7Word85.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word85)) := by
  have hrepLe : ∀ i, (ws7WordRep85 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap85 (ws7WordRep85 i) = ws7WordCap85 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap85, ws7WordRep85, ws7WordP85, ws7WordQ85]
  have hall := caps_of_representatives ws7WordRep85 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word85Weak
  intro i
  simpa [ws7WordCap85, ws7WordP85, ws7WordQ85] using hall i

noncomputable def ws7WordCap86 (i : Fin 7) : ℝ :=
  (ws7WordP86 i : ℝ) / (ws7WordQ86 i : ℝ)

def ws7WordRep86 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 2
  | 5 => 2
  | 6 => 2
  | _ => 0

theorem ws7Word86WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep86 i) ≤ ws7WordCap86 (ws7WordRep86 i)) :
    WeakValidRates r
      (periodic ws7Word86.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word86)) := by
  have hrepLe : ∀ i, (ws7WordRep86 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap86 (ws7WordRep86 i) = ws7WordCap86 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap86, ws7WordRep86, ws7WordP86, ws7WordQ86]
  have hall := caps_of_representatives ws7WordRep86 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word86Weak
  intro i
  simpa [ws7WordCap86, ws7WordP86, ws7WordQ86] using hall i

noncomputable def ws7WordCap87 (i : Fin 7) : ℝ :=
  (ws7WordP87 i : ℝ) / (ws7WordQ87 i : ℝ)

def ws7WordRep87 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word87WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep87 i) ≤ ws7WordCap87 (ws7WordRep87 i)) :
    WeakValidRates r
      (periodic ws7Word87.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word87)) := by
  have hrepLe : ∀ i, (ws7WordRep87 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap87 (ws7WordRep87 i) = ws7WordCap87 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap87, ws7WordRep87, ws7WordP87, ws7WordQ87]
  have hall := caps_of_representatives ws7WordRep87 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word87Weak
  intro i
  simpa [ws7WordCap87, ws7WordP87, ws7WordQ87] using hall i

noncomputable def ws7WordCap88 (i : Fin 7) : ℝ :=
  (ws7WordP88 i : ℝ) / (ws7WordQ88 i : ℝ)

def ws7WordRep88 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word88WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep88 i) ≤ ws7WordCap88 (ws7WordRep88 i)) :
    WeakValidRates r
      (periodic ws7Word88.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word88)) := by
  have hrepLe : ∀ i, (ws7WordRep88 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap88 (ws7WordRep88 i) = ws7WordCap88 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap88, ws7WordRep88, ws7WordP88, ws7WordQ88]
  have hall := caps_of_representatives ws7WordRep88 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word88Weak
  intro i
  simpa [ws7WordCap88, ws7WordP88, ws7WordQ88] using hall i

noncomputable def ws7WordCap89 (i : Fin 7) : ℝ :=
  (ws7WordP89 i : ℝ) / (ws7WordQ89 i : ℝ)

def ws7WordRep89 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word89WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep89 i) ≤ ws7WordCap89 (ws7WordRep89 i)) :
    WeakValidRates r
      (periodic ws7Word89.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word89)) := by
  have hrepLe : ∀ i, (ws7WordRep89 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap89 (ws7WordRep89 i) = ws7WordCap89 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap89, ws7WordRep89, ws7WordP89, ws7WordQ89]
  have hall := caps_of_representatives ws7WordRep89 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word89Weak
  intro i
  simpa [ws7WordCap89, ws7WordP89, ws7WordQ89] using hall i

noncomputable def ws7WordCap90 (i : Fin 7) : ℝ :=
  (ws7WordP90 i : ℝ) / (ws7WordQ90 i : ℝ)

def ws7WordRep90 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 6
  | _ => 0

theorem ws7Word90WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep90 i) ≤ ws7WordCap90 (ws7WordRep90 i)) :
    WeakValidRates r
      (periodic ws7Word90.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word90)) := by
  have hrepLe : ∀ i, (ws7WordRep90 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap90 (ws7WordRep90 i) = ws7WordCap90 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap90, ws7WordRep90, ws7WordP90, ws7WordQ90]
  have hall := caps_of_representatives ws7WordRep90 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word90Weak
  intro i
  simpa [ws7WordCap90, ws7WordP90, ws7WordQ90] using hall i

noncomputable def ws7WordCap91 (i : Fin 7) : ℝ :=
  (ws7WordP91 i : ℝ) / (ws7WordQ91 i : ℝ)

def ws7WordRep91 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 3
  | 6 => 6
  | _ => 0

theorem ws7Word91WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep91 i) ≤ ws7WordCap91 (ws7WordRep91 i)) :
    WeakValidRates r
      (periodic ws7Word91.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word91)) := by
  have hrepLe : ∀ i, (ws7WordRep91 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap91 (ws7WordRep91 i) = ws7WordCap91 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap91, ws7WordRep91, ws7WordP91, ws7WordQ91]
  have hall := caps_of_representatives ws7WordRep91 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word91Weak
  intro i
  simpa [ws7WordCap91, ws7WordP91, ws7WordQ91] using hall i

noncomputable def ws7WordCap92 (i : Fin 7) : ℝ :=
  (ws7WordP92 i : ℝ) / (ws7WordQ92 i : ℝ)

def ws7WordRep92 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

theorem ws7Word92WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep92 i) ≤ ws7WordCap92 (ws7WordRep92 i)) :
    WeakValidRates r
      (periodic ws7Word92.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word92)) := by
  have hrepLe : ∀ i, (ws7WordRep92 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap92 (ws7WordRep92 i) = ws7WordCap92 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap92, ws7WordRep92, ws7WordP92, ws7WordQ92]
  have hall := caps_of_representatives ws7WordRep92 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word92Weak
  intro i
  simpa [ws7WordCap92, ws7WordP92, ws7WordQ92] using hall i

noncomputable def ws7WordCap93 (i : Fin 7) : ℝ :=
  (ws7WordP93 i : ℝ) / (ws7WordQ93 i : ℝ)

def ws7WordRep93 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word93WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep93 i) ≤ ws7WordCap93 (ws7WordRep93 i)) :
    WeakValidRates r
      (periodic ws7Word93.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word93)) := by
  have hrepLe : ∀ i, (ws7WordRep93 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap93 (ws7WordRep93 i) = ws7WordCap93 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap93, ws7WordRep93, ws7WordP93, ws7WordQ93]
  have hall := caps_of_representatives ws7WordRep93 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word93Weak
  intro i
  simpa [ws7WordCap93, ws7WordP93, ws7WordQ93] using hall i

noncomputable def ws7WordCap94 (i : Fin 7) : ℝ :=
  (ws7WordP94 i : ℝ) / (ws7WordQ94 i : ℝ)

def ws7WordRep94 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 4
  | 5 => 4
  | 6 => 6
  | _ => 0

theorem ws7Word94WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep94 i) ≤ ws7WordCap94 (ws7WordRep94 i)) :
    WeakValidRates r
      (periodic ws7Word94.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word94)) := by
  have hrepLe : ∀ i, (ws7WordRep94 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap94 (ws7WordRep94 i) = ws7WordCap94 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap94, ws7WordRep94, ws7WordP94, ws7WordQ94]
  have hall := caps_of_representatives ws7WordRep94 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word94Weak
  intro i
  simpa [ws7WordCap94, ws7WordP94, ws7WordQ94] using hall i

noncomputable def ws7WordCap95 (i : Fin 7) : ℝ :=
  (ws7WordP95 i : ℝ) / (ws7WordQ95 i : ℝ)

def ws7WordRep95 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word95WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep95 i) ≤ ws7WordCap95 (ws7WordRep95 i)) :
    WeakValidRates r
      (periodic ws7Word95.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word95)) := by
  have hrepLe : ∀ i, (ws7WordRep95 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap95 (ws7WordRep95 i) = ws7WordCap95 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap95, ws7WordRep95, ws7WordP95, ws7WordQ95]
  have hall := caps_of_representatives ws7WordRep95 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word95Weak
  intro i
  simpa [ws7WordCap95, ws7WordP95, ws7WordQ95] using hall i

noncomputable def ws7WordCap96 (i : Fin 7) : ℝ :=
  (ws7WordP96 i : ℝ) / (ws7WordQ96 i : ℝ)

def ws7WordRep96 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

theorem ws7Word96WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep96 i) ≤ ws7WordCap96 (ws7WordRep96 i)) :
    WeakValidRates r
      (periodic ws7Word96.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word96)) := by
  have hrepLe : ∀ i, (ws7WordRep96 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap96 (ws7WordRep96 i) = ws7WordCap96 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap96, ws7WordRep96, ws7WordP96, ws7WordQ96]
  have hall := caps_of_representatives ws7WordRep96 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word96Weak
  intro i
  simpa [ws7WordCap96, ws7WordP96, ws7WordQ96] using hall i

noncomputable def ws7WordCap97 (i : Fin 7) : ℝ :=
  (ws7WordP97 i : ℝ) / (ws7WordQ97 i : ℝ)

def ws7WordRep97 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

theorem ws7Word97WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep97 i) ≤ ws7WordCap97 (ws7WordRep97 i)) :
    WeakValidRates r
      (periodic ws7Word97.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word97)) := by
  have hrepLe : ∀ i, (ws7WordRep97 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap97 (ws7WordRep97 i) = ws7WordCap97 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap97, ws7WordRep97, ws7WordP97, ws7WordQ97]
  have hall := caps_of_representatives ws7WordRep97 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word97Weak
  intro i
  simpa [ws7WordCap97, ws7WordP97, ws7WordQ97] using hall i

noncomputable def ws7WordCap98 (i : Fin 7) : ℝ :=
  (ws7WordP98 i : ℝ) / (ws7WordQ98 i : ℝ)

def ws7WordRep98 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word98WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep98 i) ≤ ws7WordCap98 (ws7WordRep98 i)) :
    WeakValidRates r
      (periodic ws7Word98.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word98)) := by
  have hrepLe : ∀ i, (ws7WordRep98 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap98 (ws7WordRep98 i) = ws7WordCap98 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap98, ws7WordRep98, ws7WordP98, ws7WordQ98]
  have hall := caps_of_representatives ws7WordRep98 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word98Weak
  intro i
  simpa [ws7WordCap98, ws7WordP98, ws7WordQ98] using hall i

noncomputable def ws7WordCap99 (i : Fin 7) : ℝ :=
  (ws7WordP99 i : ℝ) / (ws7WordQ99 i : ℝ)

def ws7WordRep99 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 4
  | 5 => 4
  | 6 => 6
  | _ => 0

theorem ws7Word99WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep99 i) ≤ ws7WordCap99 (ws7WordRep99 i)) :
    WeakValidRates r
      (periodic ws7Word99.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word99)) := by
  have hrepLe : ∀ i, (ws7WordRep99 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap99 (ws7WordRep99 i) = ws7WordCap99 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap99, ws7WordRep99, ws7WordP99, ws7WordQ99]
  have hall := caps_of_representatives ws7WordRep99 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word99Weak
  intro i
  simpa [ws7WordCap99, ws7WordP99, ws7WordQ99] using hall i

noncomputable def ws7WordCap100 (i : Fin 7) : ℝ :=
  (ws7WordP100 i : ℝ) / (ws7WordQ100 i : ℝ)

def ws7WordRep100 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 3
  | 4 => 3
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word100WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep100 i) ≤ ws7WordCap100 (ws7WordRep100 i)) :
    WeakValidRates r
      (periodic ws7Word100.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word100)) := by
  have hrepLe : ∀ i, (ws7WordRep100 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap100 (ws7WordRep100 i) = ws7WordCap100 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap100, ws7WordRep100, ws7WordP100, ws7WordQ100]
  have hall := caps_of_representatives ws7WordRep100 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word100Weak
  intro i
  simpa [ws7WordCap100, ws7WordP100, ws7WordQ100] using hall i

noncomputable def ws7WordCap101 (i : Fin 7) : ℝ :=
  (ws7WordP101 i : ℝ) / (ws7WordQ101 i : ℝ)

def ws7WordRep101 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

theorem ws7Word101WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep101 i) ≤ ws7WordCap101 (ws7WordRep101 i)) :
    WeakValidRates r
      (periodic ws7Word101.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word101)) := by
  have hrepLe : ∀ i, (ws7WordRep101 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap101 (ws7WordRep101 i) = ws7WordCap101 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap101, ws7WordRep101, ws7WordP101, ws7WordQ101]
  have hall := caps_of_representatives ws7WordRep101 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word101Weak
  intro i
  simpa [ws7WordCap101, ws7WordP101, ws7WordQ101] using hall i

noncomputable def ws7WordCap102 (i : Fin 7) : ℝ :=
  (ws7WordP102 i : ℝ) / (ws7WordQ102 i : ℝ)

def ws7WordRep102 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 4
  | 5 => 4
  | 6 => 6
  | _ => 0

theorem ws7Word102WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep102 i) ≤ ws7WordCap102 (ws7WordRep102 i)) :
    WeakValidRates r
      (periodic ws7Word102.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word102)) := by
  have hrepLe : ∀ i, (ws7WordRep102 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap102 (ws7WordRep102 i) = ws7WordCap102 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap102, ws7WordRep102, ws7WordP102, ws7WordQ102]
  have hall := caps_of_representatives ws7WordRep102 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word102Weak
  intro i
  simpa [ws7WordCap102, ws7WordP102, ws7WordQ102] using hall i

noncomputable def ws7WordCap103 (i : Fin 7) : ℝ :=
  (ws7WordP103 i : ℝ) / (ws7WordQ103 i : ℝ)

def ws7WordRep103 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

theorem ws7Word103WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep103 i) ≤ ws7WordCap103 (ws7WordRep103 i)) :
    WeakValidRates r
      (periodic ws7Word103.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word103)) := by
  have hrepLe : ∀ i, (ws7WordRep103 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap103 (ws7WordRep103 i) = ws7WordCap103 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap103, ws7WordRep103, ws7WordP103, ws7WordQ103]
  have hall := caps_of_representatives ws7WordRep103 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word103Weak
  intro i
  simpa [ws7WordCap103, ws7WordP103, ws7WordQ103] using hall i

noncomputable def ws7WordCap104 (i : Fin 7) : ℝ :=
  (ws7WordP104 i : ℝ) / (ws7WordQ104 i : ℝ)

def ws7WordRep104 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 3
  | 6 => 3
  | _ => 0

theorem ws7Word104WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep104 i) ≤ ws7WordCap104 (ws7WordRep104 i)) :
    WeakValidRates r
      (periodic ws7Word104.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word104)) := by
  have hrepLe : ∀ i, (ws7WordRep104 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap104 (ws7WordRep104 i) = ws7WordCap104 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap104, ws7WordRep104, ws7WordP104, ws7WordQ104]
  have hall := caps_of_representatives ws7WordRep104 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word104Weak
  intro i
  simpa [ws7WordCap104, ws7WordP104, ws7WordQ104] using hall i

noncomputable def ws7WordCap105 (i : Fin 7) : ℝ :=
  (ws7WordP105 i : ℝ) / (ws7WordQ105 i : ℝ)

def ws7WordRep105 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word105WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep105 i) ≤ ws7WordCap105 (ws7WordRep105 i)) :
    WeakValidRates r
      (periodic ws7Word105.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word105)) := by
  have hrepLe : ∀ i, (ws7WordRep105 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap105 (ws7WordRep105 i) = ws7WordCap105 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap105, ws7WordRep105, ws7WordP105, ws7WordQ105]
  have hall := caps_of_representatives ws7WordRep105 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word105Weak
  intro i
  simpa [ws7WordCap105, ws7WordP105, ws7WordQ105] using hall i

noncomputable def ws7WordCap106 (i : Fin 7) : ℝ :=
  (ws7WordP106 i : ℝ) / (ws7WordQ106 i : ℝ)

def ws7WordRep106 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

theorem ws7Word106WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep106 i) ≤ ws7WordCap106 (ws7WordRep106 i)) :
    WeakValidRates r
      (periodic ws7Word106.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word106)) := by
  have hrepLe : ∀ i, (ws7WordRep106 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap106 (ws7WordRep106 i) = ws7WordCap106 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap106, ws7WordRep106, ws7WordP106, ws7WordQ106]
  have hall := caps_of_representatives ws7WordRep106 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word106Weak
  intro i
  simpa [ws7WordCap106, ws7WordP106, ws7WordQ106] using hall i

noncomputable def ws7WordCap107 (i : Fin 7) : ℝ :=
  (ws7WordP107 i : ℝ) / (ws7WordQ107 i : ℝ)

def ws7WordRep107 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word107WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep107 i) ≤ ws7WordCap107 (ws7WordRep107 i)) :
    WeakValidRates r
      (periodic ws7Word107.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word107)) := by
  have hrepLe : ∀ i, (ws7WordRep107 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap107 (ws7WordRep107 i) = ws7WordCap107 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap107, ws7WordRep107, ws7WordP107, ws7WordQ107]
  have hall := caps_of_representatives ws7WordRep107 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word107Weak
  intro i
  simpa [ws7WordCap107, ws7WordP107, ws7WordQ107] using hall i

noncomputable def ws7WordCap108 (i : Fin 7) : ℝ :=
  (ws7WordP108 i : ℝ) / (ws7WordQ108 i : ℝ)

def ws7WordRep108 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word108WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep108 i) ≤ ws7WordCap108 (ws7WordRep108 i)) :
    WeakValidRates r
      (periodic ws7Word108.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word108)) := by
  have hrepLe : ∀ i, (ws7WordRep108 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap108 (ws7WordRep108 i) = ws7WordCap108 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap108, ws7WordRep108, ws7WordP108, ws7WordQ108]
  have hall := caps_of_representatives ws7WordRep108 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word108Weak
  intro i
  simpa [ws7WordCap108, ws7WordP108, ws7WordQ108] using hall i

noncomputable def ws7WordCap109 (i : Fin 7) : ℝ :=
  (ws7WordP109 i : ℝ) / (ws7WordQ109 i : ℝ)

def ws7WordRep109 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 3
  | 4 => 3
  | 5 => 3
  | 6 => 3
  | _ => 0

theorem ws7Word109WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep109 i) ≤ ws7WordCap109 (ws7WordRep109 i)) :
    WeakValidRates r
      (periodic ws7Word109.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word109)) := by
  have hrepLe : ∀ i, (ws7WordRep109 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap109 (ws7WordRep109 i) = ws7WordCap109 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap109, ws7WordRep109, ws7WordP109, ws7WordQ109]
  have hall := caps_of_representatives ws7WordRep109 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word109Weak
  intro i
  simpa [ws7WordCap109, ws7WordP109, ws7WordQ109] using hall i

noncomputable def ws7WordCap110 (i : Fin 7) : ℝ :=
  (ws7WordP110 i : ℝ) / (ws7WordQ110 i : ℝ)

def ws7WordRep110 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word110WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep110 i) ≤ ws7WordCap110 (ws7WordRep110 i)) :
    WeakValidRates r
      (periodic ws7Word110.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word110)) := by
  have hrepLe : ∀ i, (ws7WordRep110 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap110 (ws7WordRep110 i) = ws7WordCap110 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap110, ws7WordRep110, ws7WordP110, ws7WordQ110]
  have hall := caps_of_representatives ws7WordRep110 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word110Weak
  intro i
  simpa [ws7WordCap110, ws7WordP110, ws7WordQ110] using hall i

noncomputable def ws7WordCap111 (i : Fin 7) : ℝ :=
  (ws7WordP111 i : ℝ) / (ws7WordQ111 i : ℝ)

def ws7WordRep111 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 4
  | 5 => 4
  | 6 => 6
  | _ => 0

theorem ws7Word111WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep111 i) ≤ ws7WordCap111 (ws7WordRep111 i)) :
    WeakValidRates r
      (periodic ws7Word111.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word111)) := by
  have hrepLe : ∀ i, (ws7WordRep111 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap111 (ws7WordRep111 i) = ws7WordCap111 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap111, ws7WordRep111, ws7WordP111, ws7WordQ111]
  have hall := caps_of_representatives ws7WordRep111 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word111Weak
  intro i
  simpa [ws7WordCap111, ws7WordP111, ws7WordQ111] using hall i

noncomputable def ws7WordCap112 (i : Fin 7) : ℝ :=
  (ws7WordP112 i : ℝ) / (ws7WordQ112 i : ℝ)

def ws7WordRep112 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 2
  | 5 => 2
  | 6 => 6
  | _ => 0

theorem ws7Word112WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep112 i) ≤ ws7WordCap112 (ws7WordRep112 i)) :
    WeakValidRates r
      (periodic ws7Word112.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word112)) := by
  have hrepLe : ∀ i, (ws7WordRep112 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap112 (ws7WordRep112 i) = ws7WordCap112 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap112, ws7WordRep112, ws7WordP112, ws7WordQ112]
  have hall := caps_of_representatives ws7WordRep112 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word112Weak
  intro i
  simpa [ws7WordCap112, ws7WordP112, ws7WordQ112] using hall i

noncomputable def ws7WordCap113 (i : Fin 7) : ℝ :=
  (ws7WordP113 i : ℝ) / (ws7WordQ113 i : ℝ)

def ws7WordRep113 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 2
  | 5 => 2
  | 6 => 2
  | _ => 0

theorem ws7Word113WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep113 i) ≤ ws7WordCap113 (ws7WordRep113 i)) :
    WeakValidRates r
      (periodic ws7Word113.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word113)) := by
  have hrepLe : ∀ i, (ws7WordRep113 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap113 (ws7WordRep113 i) = ws7WordCap113 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap113, ws7WordRep113, ws7WordP113, ws7WordQ113]
  have hall := caps_of_representatives ws7WordRep113 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word113Weak
  intro i
  simpa [ws7WordCap113, ws7WordP113, ws7WordQ113] using hall i

noncomputable def ws7WordCap114 (i : Fin 7) : ℝ :=
  (ws7WordP114 i : ℝ) / (ws7WordQ114 i : ℝ)

def ws7WordRep114 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word114WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep114 i) ≤ ws7WordCap114 (ws7WordRep114 i)) :
    WeakValidRates r
      (periodic ws7Word114.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word114)) := by
  have hrepLe : ∀ i, (ws7WordRep114 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap114 (ws7WordRep114 i) = ws7WordCap114 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap114, ws7WordRep114, ws7WordP114, ws7WordQ114]
  have hall := caps_of_representatives ws7WordRep114 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word114Weak
  intro i
  simpa [ws7WordCap114, ws7WordP114, ws7WordQ114] using hall i

noncomputable def ws7WordCap115 (i : Fin 7) : ℝ :=
  (ws7WordP115 i : ℝ) / (ws7WordQ115 i : ℝ)

def ws7WordRep115 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word115WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep115 i) ≤ ws7WordCap115 (ws7WordRep115 i)) :
    WeakValidRates r
      (periodic ws7Word115.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word115)) := by
  have hrepLe : ∀ i, (ws7WordRep115 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap115 (ws7WordRep115 i) = ws7WordCap115 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap115, ws7WordRep115, ws7WordP115, ws7WordQ115]
  have hall := caps_of_representatives ws7WordRep115 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word115Weak
  intro i
  simpa [ws7WordCap115, ws7WordP115, ws7WordQ115] using hall i

noncomputable def ws7WordCap116 (i : Fin 7) : ℝ :=
  (ws7WordP116 i : ℝ) / (ws7WordQ116 i : ℝ)

def ws7WordRep116 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word116WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep116 i) ≤ ws7WordCap116 (ws7WordRep116 i)) :
    WeakValidRates r
      (periodic ws7Word116.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word116)) := by
  have hrepLe : ∀ i, (ws7WordRep116 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap116 (ws7WordRep116 i) = ws7WordCap116 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap116, ws7WordRep116, ws7WordP116, ws7WordQ116]
  have hall := caps_of_representatives ws7WordRep116 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word116Weak
  intro i
  simpa [ws7WordCap116, ws7WordP116, ws7WordQ116] using hall i

noncomputable def ws7WordCap117 (i : Fin 7) : ℝ :=
  (ws7WordP117 i : ℝ) / (ws7WordQ117 i : ℝ)

def ws7WordRep117 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word117WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep117 i) ≤ ws7WordCap117 (ws7WordRep117 i)) :
    WeakValidRates r
      (periodic ws7Word117.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word117)) := by
  have hrepLe : ∀ i, (ws7WordRep117 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap117 (ws7WordRep117 i) = ws7WordCap117 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap117, ws7WordRep117, ws7WordP117, ws7WordQ117]
  have hall := caps_of_representatives ws7WordRep117 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word117Weak
  intro i
  simpa [ws7WordCap117, ws7WordP117, ws7WordQ117] using hall i

noncomputable def ws7WordCap118 (i : Fin 7) : ℝ :=
  (ws7WordP118 i : ℝ) / (ws7WordQ118 i : ℝ)

def ws7WordRep118 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word118WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep118 i) ≤ ws7WordCap118 (ws7WordRep118 i)) :
    WeakValidRates r
      (periodic ws7Word118.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word118)) := by
  have hrepLe : ∀ i, (ws7WordRep118 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap118 (ws7WordRep118 i) = ws7WordCap118 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap118, ws7WordRep118, ws7WordP118, ws7WordQ118]
  have hall := caps_of_representatives ws7WordRep118 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word118Weak
  intro i
  simpa [ws7WordCap118, ws7WordP118, ws7WordQ118] using hall i

noncomputable def ws7WordCap119 (i : Fin 7) : ℝ :=
  (ws7WordP119 i : ℝ) / (ws7WordQ119 i : ℝ)

def ws7WordRep119 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

theorem ws7Word119WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep119 i) ≤ ws7WordCap119 (ws7WordRep119 i)) :
    WeakValidRates r
      (periodic ws7Word119.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word119)) := by
  have hrepLe : ∀ i, (ws7WordRep119 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap119 (ws7WordRep119 i) = ws7WordCap119 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap119, ws7WordRep119, ws7WordP119, ws7WordQ119]
  have hall := caps_of_representatives ws7WordRep119 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word119Weak
  intro i
  simpa [ws7WordCap119, ws7WordP119, ws7WordQ119] using hall i

noncomputable def ws7WordCap120 (i : Fin 7) : ℝ :=
  (ws7WordP120 i : ℝ) / (ws7WordQ120 i : ℝ)

def ws7WordRep120 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 2
  | 5 => 2
  | 6 => 2
  | _ => 0

theorem ws7Word120WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep120 i) ≤ ws7WordCap120 (ws7WordRep120 i)) :
    WeakValidRates r
      (periodic ws7Word120.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word120)) := by
  have hrepLe : ∀ i, (ws7WordRep120 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap120 (ws7WordRep120 i) = ws7WordCap120 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap120, ws7WordRep120, ws7WordP120, ws7WordQ120]
  have hall := caps_of_representatives ws7WordRep120 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word120Weak
  intro i
  simpa [ws7WordCap120, ws7WordP120, ws7WordQ120] using hall i

noncomputable def ws7WordCap121 (i : Fin 7) : ℝ :=
  (ws7WordP121 i : ℝ) / (ws7WordQ121 i : ℝ)

def ws7WordRep121 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word121WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep121 i) ≤ ws7WordCap121 (ws7WordRep121 i)) :
    WeakValidRates r
      (periodic ws7Word121.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word121)) := by
  have hrepLe : ∀ i, (ws7WordRep121 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap121 (ws7WordRep121 i) = ws7WordCap121 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap121, ws7WordRep121, ws7WordP121, ws7WordQ121]
  have hall := caps_of_representatives ws7WordRep121 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word121Weak
  intro i
  simpa [ws7WordCap121, ws7WordP121, ws7WordQ121] using hall i

noncomputable def ws7WordCap122 (i : Fin 7) : ℝ :=
  (ws7WordP122 i : ℝ) / (ws7WordQ122 i : ℝ)

def ws7WordRep122 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 6
  | _ => 0

theorem ws7Word122WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep122 i) ≤ ws7WordCap122 (ws7WordRep122 i)) :
    WeakValidRates r
      (periodic ws7Word122.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word122)) := by
  have hrepLe : ∀ i, (ws7WordRep122 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap122 (ws7WordRep122 i) = ws7WordCap122 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap122, ws7WordRep122, ws7WordP122, ws7WordQ122]
  have hall := caps_of_representatives ws7WordRep122 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word122Weak
  intro i
  simpa [ws7WordCap122, ws7WordP122, ws7WordQ122] using hall i

noncomputable def ws7WordCap123 (i : Fin 7) : ℝ :=
  (ws7WordP123 i : ℝ) / (ws7WordQ123 i : ℝ)

def ws7WordRep123 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 6
  | _ => 0

theorem ws7Word123WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep123 i) ≤ ws7WordCap123 (ws7WordRep123 i)) :
    WeakValidRates r
      (periodic ws7Word123.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word123)) := by
  have hrepLe : ∀ i, (ws7WordRep123 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap123 (ws7WordRep123 i) = ws7WordCap123 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap123, ws7WordRep123, ws7WordP123, ws7WordQ123]
  have hall := caps_of_representatives ws7WordRep123 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word123Weak
  intro i
  simpa [ws7WordCap123, ws7WordP123, ws7WordQ123] using hall i

noncomputable def ws7WordCap124 (i : Fin 7) : ℝ :=
  (ws7WordP124 i : ℝ) / (ws7WordQ124 i : ℝ)

def ws7WordRep124 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word124WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep124 i) ≤ ws7WordCap124 (ws7WordRep124 i)) :
    WeakValidRates r
      (periodic ws7Word124.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word124)) := by
  have hrepLe : ∀ i, (ws7WordRep124 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap124 (ws7WordRep124 i) = ws7WordCap124 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap124, ws7WordRep124, ws7WordP124, ws7WordQ124]
  have hall := caps_of_representatives ws7WordRep124 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word124Weak
  intro i
  simpa [ws7WordCap124, ws7WordP124, ws7WordQ124] using hall i

noncomputable def ws7WordCap125 (i : Fin 7) : ℝ :=
  (ws7WordP125 i : ℝ) / (ws7WordQ125 i : ℝ)

def ws7WordRep125 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word125WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep125 i) ≤ ws7WordCap125 (ws7WordRep125 i)) :
    WeakValidRates r
      (periodic ws7Word125.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word125)) := by
  have hrepLe : ∀ i, (ws7WordRep125 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap125 (ws7WordRep125 i) = ws7WordCap125 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap125, ws7WordRep125, ws7WordP125, ws7WordQ125]
  have hall := caps_of_representatives ws7WordRep125 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word125Weak
  intro i
  simpa [ws7WordCap125, ws7WordP125, ws7WordQ125] using hall i

noncomputable def ws7WordCap126 (i : Fin 7) : ℝ :=
  (ws7WordP126 i : ℝ) / (ws7WordQ126 i : ℝ)

def ws7WordRep126 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 0
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word126WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep126 i) ≤ ws7WordCap126 (ws7WordRep126 i)) :
    WeakValidRates r
      (periodic ws7Word126.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word126)) := by
  have hrepLe : ∀ i, (ws7WordRep126 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap126 (ws7WordRep126 i) = ws7WordCap126 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap126, ws7WordRep126, ws7WordP126, ws7WordQ126]
  have hall := caps_of_representatives ws7WordRep126 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word126Weak
  intro i
  simpa [ws7WordCap126, ws7WordP126, ws7WordQ126] using hall i

noncomputable def ws7WordCap127 (i : Fin 7) : ℝ :=
  (ws7WordP127 i : ℝ) / (ws7WordQ127 i : ℝ)

def ws7WordRep127 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 2
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word127WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep127 i) ≤ ws7WordCap127 (ws7WordRep127 i)) :
    WeakValidRates r
      (periodic ws7Word127.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word127)) := by
  have hrepLe : ∀ i, (ws7WordRep127 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap127 (ws7WordRep127 i) = ws7WordCap127 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap127, ws7WordRep127, ws7WordP127, ws7WordQ127]
  have hall := caps_of_representatives ws7WordRep127 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word127Weak
  intro i
  simpa [ws7WordCap127, ws7WordP127, ws7WordQ127] using hall i

noncomputable def ws7WordCap128 (i : Fin 7) : ℝ :=
  (ws7WordP128 i : ℝ) / (ws7WordQ128 i : ℝ)

def ws7WordRep128 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 0
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 3
  | 6 => 6
  | _ => 0

theorem ws7Word128WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep128 i) ≤ ws7WordCap128 (ws7WordRep128 i)) :
    WeakValidRates r
      (periodic ws7Word128.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word128)) := by
  have hrepLe : ∀ i, (ws7WordRep128 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap128 (ws7WordRep128 i) = ws7WordCap128 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap128, ws7WordRep128, ws7WordP128, ws7WordQ128]
  have hall := caps_of_representatives ws7WordRep128 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word128Weak
  intro i
  simpa [ws7WordCap128, ws7WordP128, ws7WordQ128] using hall i

noncomputable def ws7WordCap129 (i : Fin 7) : ℝ :=
  (ws7WordP129 i : ℝ) / (ws7WordQ129 i : ℝ)

def ws7WordRep129 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

theorem ws7Word129WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep129 i) ≤ ws7WordCap129 (ws7WordRep129 i)) :
    WeakValidRates r
      (periodic ws7Word129.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word129)) := by
  have hrepLe : ∀ i, (ws7WordRep129 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap129 (ws7WordRep129 i) = ws7WordCap129 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap129, ws7WordRep129, ws7WordP129, ws7WordQ129]
  have hall := caps_of_representatives ws7WordRep129 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word129Weak
  intro i
  simpa [ws7WordCap129, ws7WordP129, ws7WordQ129] using hall i

noncomputable def ws7WordCap130 (i : Fin 7) : ℝ :=
  (ws7WordP130 i : ℝ) / (ws7WordQ130 i : ℝ)

def ws7WordRep130 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 0
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word130WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep130 i) ≤ ws7WordCap130 (ws7WordRep130 i)) :
    WeakValidRates r
      (periodic ws7Word130.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word130)) := by
  have hrepLe : ∀ i, (ws7WordRep130 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap130 (ws7WordRep130 i) = ws7WordCap130 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap130, ws7WordRep130, ws7WordP130, ws7WordQ130]
  have hall := caps_of_representatives ws7WordRep130 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word130Weak
  intro i
  simpa [ws7WordCap130, ws7WordP130, ws7WordQ130] using hall i

noncomputable def ws7WordCap131 (i : Fin 7) : ℝ :=
  (ws7WordP131 i : ℝ) / (ws7WordQ131 i : ℝ)

def ws7WordRep131 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word131WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep131 i) ≤ ws7WordCap131 (ws7WordRep131 i)) :
    WeakValidRates r
      (periodic ws7Word131.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word131)) := by
  have hrepLe : ∀ i, (ws7WordRep131 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap131 (ws7WordRep131 i) = ws7WordCap131 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap131, ws7WordRep131, ws7WordP131, ws7WordQ131]
  have hall := caps_of_representatives ws7WordRep131 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word131Weak
  intro i
  simpa [ws7WordCap131, ws7WordP131, ws7WordQ131] using hall i

noncomputable def ws7WordCap132 (i : Fin 7) : ℝ :=
  (ws7WordP132 i : ℝ) / (ws7WordQ132 i : ℝ)

def ws7WordRep132 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word132WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep132 i) ≤ ws7WordCap132 (ws7WordRep132 i)) :
    WeakValidRates r
      (periodic ws7Word132.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word132)) := by
  have hrepLe : ∀ i, (ws7WordRep132 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap132 (ws7WordRep132 i) = ws7WordCap132 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap132, ws7WordRep132, ws7WordP132, ws7WordQ132]
  have hall := caps_of_representatives ws7WordRep132 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word132Weak
  intro i
  simpa [ws7WordCap132, ws7WordP132, ws7WordQ132] using hall i

noncomputable def ws7WordCap133 (i : Fin 7) : ℝ :=
  (ws7WordP133 i : ℝ) / (ws7WordQ133 i : ℝ)

def ws7WordRep133 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word133WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep133 i) ≤ ws7WordCap133 (ws7WordRep133 i)) :
    WeakValidRates r
      (periodic ws7Word133.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word133)) := by
  have hrepLe : ∀ i, (ws7WordRep133 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap133 (ws7WordRep133 i) = ws7WordCap133 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap133, ws7WordRep133, ws7WordP133, ws7WordQ133]
  have hall := caps_of_representatives ws7WordRep133 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word133Weak
  intro i
  simpa [ws7WordCap133, ws7WordP133, ws7WordQ133] using hall i

noncomputable def ws7WordCap134 (i : Fin 7) : ℝ :=
  (ws7WordP134 i : ℝ) / (ws7WordQ134 i : ℝ)

def ws7WordRep134 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word134WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep134 i) ≤ ws7WordCap134 (ws7WordRep134 i)) :
    WeakValidRates r
      (periodic ws7Word134.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word134)) := by
  have hrepLe : ∀ i, (ws7WordRep134 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap134 (ws7WordRep134 i) = ws7WordCap134 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap134, ws7WordRep134, ws7WordP134, ws7WordQ134]
  have hall := caps_of_representatives ws7WordRep134 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word134Weak
  intro i
  simpa [ws7WordCap134, ws7WordP134, ws7WordQ134] using hall i

noncomputable def ws7WordCap135 (i : Fin 7) : ℝ :=
  (ws7WordP135 i : ℝ) / (ws7WordQ135 i : ℝ)

def ws7WordRep135 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 2
  | 5 => 2
  | 6 => 2
  | _ => 0

theorem ws7Word135WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep135 i) ≤ ws7WordCap135 (ws7WordRep135 i)) :
    WeakValidRates r
      (periodic ws7Word135.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word135)) := by
  have hrepLe : ∀ i, (ws7WordRep135 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap135 (ws7WordRep135 i) = ws7WordCap135 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap135, ws7WordRep135, ws7WordP135, ws7WordQ135]
  have hall := caps_of_representatives ws7WordRep135 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word135Weak
  intro i
  simpa [ws7WordCap135, ws7WordP135, ws7WordQ135] using hall i

noncomputable def ws7WordCap136 (i : Fin 7) : ℝ :=
  (ws7WordP136 i : ℝ) / (ws7WordQ136 i : ℝ)

def ws7WordRep136 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 3
  | 6 => 6
  | _ => 0

theorem ws7Word136WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep136 i) ≤ ws7WordCap136 (ws7WordRep136 i)) :
    WeakValidRates r
      (periodic ws7Word136.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word136)) := by
  have hrepLe : ∀ i, (ws7WordRep136 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap136 (ws7WordRep136 i) = ws7WordCap136 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap136, ws7WordRep136, ws7WordP136, ws7WordQ136]
  have hall := caps_of_representatives ws7WordRep136 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word136Weak
  intro i
  simpa [ws7WordCap136, ws7WordP136, ws7WordQ136] using hall i

noncomputable def ws7WordCap137 (i : Fin 7) : ℝ :=
  (ws7WordP137 i : ℝ) / (ws7WordQ137 i : ℝ)

def ws7WordRep137 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 6
  | _ => 0

theorem ws7Word137WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep137 i) ≤ ws7WordCap137 (ws7WordRep137 i)) :
    WeakValidRates r
      (periodic ws7Word137.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word137)) := by
  have hrepLe : ∀ i, (ws7WordRep137 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap137 (ws7WordRep137 i) = ws7WordCap137 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap137, ws7WordRep137, ws7WordP137, ws7WordQ137]
  have hall := caps_of_representatives ws7WordRep137 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word137Weak
  intro i
  simpa [ws7WordCap137, ws7WordP137, ws7WordQ137] using hall i

noncomputable def ws7WordCap138 (i : Fin 7) : ℝ :=
  (ws7WordP138 i : ℝ) / (ws7WordQ138 i : ℝ)

def ws7WordRep138 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 6
  | _ => 0

theorem ws7Word138WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep138 i) ≤ ws7WordCap138 (ws7WordRep138 i)) :
    WeakValidRates r
      (periodic ws7Word138.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word138)) := by
  have hrepLe : ∀ i, (ws7WordRep138 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap138 (ws7WordRep138 i) = ws7WordCap138 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap138, ws7WordRep138, ws7WordP138, ws7WordQ138]
  have hall := caps_of_representatives ws7WordRep138 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word138Weak
  intro i
  simpa [ws7WordCap138, ws7WordP138, ws7WordQ138] using hall i

noncomputable def ws7WordCap139 (i : Fin 7) : ℝ :=
  (ws7WordP139 i : ℝ) / (ws7WordQ139 i : ℝ)

def ws7WordRep139 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word139WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep139 i) ≤ ws7WordCap139 (ws7WordRep139 i)) :
    WeakValidRates r
      (periodic ws7Word139.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word139)) := by
  have hrepLe : ∀ i, (ws7WordRep139 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap139 (ws7WordRep139 i) = ws7WordCap139 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap139, ws7WordRep139, ws7WordP139, ws7WordQ139]
  have hall := caps_of_representatives ws7WordRep139 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word139Weak
  intro i
  simpa [ws7WordCap139, ws7WordP139, ws7WordQ139] using hall i

noncomputable def ws7WordCap140 (i : Fin 7) : ℝ :=
  (ws7WordP140 i : ℝ) / (ws7WordQ140 i : ℝ)

def ws7WordRep140 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 3
  | 6 => 3
  | _ => 0

theorem ws7Word140WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep140 i) ≤ ws7WordCap140 (ws7WordRep140 i)) :
    WeakValidRates r
      (periodic ws7Word140.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word140)) := by
  have hrepLe : ∀ i, (ws7WordRep140 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap140 (ws7WordRep140 i) = ws7WordCap140 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap140, ws7WordRep140, ws7WordP140, ws7WordQ140]
  have hall := caps_of_representatives ws7WordRep140 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word140Weak
  intro i
  simpa [ws7WordCap140, ws7WordP140, ws7WordQ140] using hall i

noncomputable def ws7WordCap141 (i : Fin 7) : ℝ :=
  (ws7WordP141 i : ℝ) / (ws7WordQ141 i : ℝ)

def ws7WordRep141 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 2
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word141WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep141 i) ≤ ws7WordCap141 (ws7WordRep141 i)) :
    WeakValidRates r
      (periodic ws7Word141.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word141)) := by
  have hrepLe : ∀ i, (ws7WordRep141 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap141 (ws7WordRep141 i) = ws7WordCap141 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap141, ws7WordRep141, ws7WordP141, ws7WordQ141]
  have hall := caps_of_representatives ws7WordRep141 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word141Weak
  intro i
  simpa [ws7WordCap141, ws7WordP141, ws7WordQ141] using hall i

noncomputable def ws7WordCap142 (i : Fin 7) : ℝ :=
  (ws7WordP142 i : ℝ) / (ws7WordQ142 i : ℝ)

def ws7WordRep142 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word142WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep142 i) ≤ ws7WordCap142 (ws7WordRep142 i)) :
    WeakValidRates r
      (periodic ws7Word142.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word142)) := by
  have hrepLe : ∀ i, (ws7WordRep142 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap142 (ws7WordRep142 i) = ws7WordCap142 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap142, ws7WordRep142, ws7WordP142, ws7WordQ142]
  have hall := caps_of_representatives ws7WordRep142 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word142Weak
  intro i
  simpa [ws7WordCap142, ws7WordP142, ws7WordQ142] using hall i

noncomputable def ws7WordCap143 (i : Fin 7) : ℝ :=
  (ws7WordP143 i : ℝ) / (ws7WordQ143 i : ℝ)

def ws7WordRep143 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 4
  | 5 => 4
  | 6 => 6
  | _ => 0

theorem ws7Word143WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep143 i) ≤ ws7WordCap143 (ws7WordRep143 i)) :
    WeakValidRates r
      (periodic ws7Word143.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word143)) := by
  have hrepLe : ∀ i, (ws7WordRep143 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap143 (ws7WordRep143 i) = ws7WordCap143 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap143, ws7WordRep143, ws7WordP143, ws7WordQ143]
  have hall := caps_of_representatives ws7WordRep143 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word143Weak
  intro i
  simpa [ws7WordCap143, ws7WordP143, ws7WordQ143] using hall i

noncomputable def ws7WordCap144 (i : Fin 7) : ℝ :=
  (ws7WordP144 i : ℝ) / (ws7WordQ144 i : ℝ)

def ws7WordRep144 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word144WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep144 i) ≤ ws7WordCap144 (ws7WordRep144 i)) :
    WeakValidRates r
      (periodic ws7Word144.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word144)) := by
  have hrepLe : ∀ i, (ws7WordRep144 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap144 (ws7WordRep144 i) = ws7WordCap144 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap144, ws7WordRep144, ws7WordP144, ws7WordQ144]
  have hall := caps_of_representatives ws7WordRep144 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word144Weak
  intro i
  simpa [ws7WordCap144, ws7WordP144, ws7WordQ144] using hall i

noncomputable def ws7WordCap145 (i : Fin 7) : ℝ :=
  (ws7WordP145 i : ℝ) / (ws7WordQ145 i : ℝ)

def ws7WordRep145 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 6
  | _ => 0

theorem ws7Word145WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep145 i) ≤ ws7WordCap145 (ws7WordRep145 i)) :
    WeakValidRates r
      (periodic ws7Word145.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word145)) := by
  have hrepLe : ∀ i, (ws7WordRep145 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap145 (ws7WordRep145 i) = ws7WordCap145 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap145, ws7WordRep145, ws7WordP145, ws7WordQ145]
  have hall := caps_of_representatives ws7WordRep145 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word145Weak
  intro i
  simpa [ws7WordCap145, ws7WordP145, ws7WordQ145] using hall i

noncomputable def ws7WordCap146 (i : Fin 7) : ℝ :=
  (ws7WordP146 i : ℝ) / (ws7WordQ146 i : ℝ)

def ws7WordRep146 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 0
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 3
  | 6 => 3
  | _ => 0

theorem ws7Word146WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep146 i) ≤ ws7WordCap146 (ws7WordRep146 i)) :
    WeakValidRates r
      (periodic ws7Word146.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word146)) := by
  have hrepLe : ∀ i, (ws7WordRep146 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap146 (ws7WordRep146 i) = ws7WordCap146 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap146, ws7WordRep146, ws7WordP146, ws7WordQ146]
  have hall := caps_of_representatives ws7WordRep146 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word146Weak
  intro i
  simpa [ws7WordCap146, ws7WordP146, ws7WordQ146] using hall i

noncomputable def ws7WordCap147 (i : Fin 7) : ℝ :=
  (ws7WordP147 i : ℝ) / (ws7WordQ147 i : ℝ)

def ws7WordRep147 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word147WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep147 i) ≤ ws7WordCap147 (ws7WordRep147 i)) :
    WeakValidRates r
      (periodic ws7Word147.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word147)) := by
  have hrepLe : ∀ i, (ws7WordRep147 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap147 (ws7WordRep147 i) = ws7WordCap147 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap147, ws7WordRep147, ws7WordP147, ws7WordQ147]
  have hall := caps_of_representatives ws7WordRep147 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word147Weak
  intro i
  simpa [ws7WordCap147, ws7WordP147, ws7WordQ147] using hall i

noncomputable def ws7WordCap148 (i : Fin 7) : ℝ :=
  (ws7WordP148 i : ℝ) / (ws7WordQ148 i : ℝ)

def ws7WordRep148 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word148WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep148 i) ≤ ws7WordCap148 (ws7WordRep148 i)) :
    WeakValidRates r
      (periodic ws7Word148.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word148)) := by
  have hrepLe : ∀ i, (ws7WordRep148 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap148 (ws7WordRep148 i) = ws7WordCap148 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap148, ws7WordRep148, ws7WordP148, ws7WordQ148]
  have hall := caps_of_representatives ws7WordRep148 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word148Weak
  intro i
  simpa [ws7WordCap148, ws7WordP148, ws7WordQ148] using hall i

noncomputable def ws7WordCap149 (i : Fin 7) : ℝ :=
  (ws7WordP149 i : ℝ) / (ws7WordQ149 i : ℝ)

def ws7WordRep149 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word149WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep149 i) ≤ ws7WordCap149 (ws7WordRep149 i)) :
    WeakValidRates r
      (periodic ws7Word149.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word149)) := by
  have hrepLe : ∀ i, (ws7WordRep149 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap149 (ws7WordRep149 i) = ws7WordCap149 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap149, ws7WordRep149, ws7WordP149, ws7WordQ149]
  have hall := caps_of_representatives ws7WordRep149 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word149Weak
  intro i
  simpa [ws7WordCap149, ws7WordP149, ws7WordQ149] using hall i

noncomputable def ws7WordCap150 (i : Fin 7) : ℝ :=
  (ws7WordP150 i : ℝ) / (ws7WordQ150 i : ℝ)

def ws7WordRep150 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word150WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep150 i) ≤ ws7WordCap150 (ws7WordRep150 i)) :
    WeakValidRates r
      (periodic ws7Word150.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word150)) := by
  have hrepLe : ∀ i, (ws7WordRep150 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap150 (ws7WordRep150 i) = ws7WordCap150 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap150, ws7WordRep150, ws7WordP150, ws7WordQ150]
  have hall := caps_of_representatives ws7WordRep150 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word150Weak
  intro i
  simpa [ws7WordCap150, ws7WordP150, ws7WordQ150] using hall i

noncomputable def ws7WordCap151 (i : Fin 7) : ℝ :=
  (ws7WordP151 i : ℝ) / (ws7WordQ151 i : ℝ)

def ws7WordRep151 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 6
  | _ => 0

theorem ws7Word151WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep151 i) ≤ ws7WordCap151 (ws7WordRep151 i)) :
    WeakValidRates r
      (periodic ws7Word151.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word151)) := by
  have hrepLe : ∀ i, (ws7WordRep151 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap151 (ws7WordRep151 i) = ws7WordCap151 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap151, ws7WordRep151, ws7WordP151, ws7WordQ151]
  have hall := caps_of_representatives ws7WordRep151 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word151Weak
  intro i
  simpa [ws7WordCap151, ws7WordP151, ws7WordQ151] using hall i

noncomputable def ws7WordCap152 (i : Fin 7) : ℝ :=
  (ws7WordP152 i : ℝ) / (ws7WordQ152 i : ℝ)

def ws7WordRep152 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 4
  | 5 => 4
  | 6 => 6
  | _ => 0

theorem ws7Word152WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep152 i) ≤ ws7WordCap152 (ws7WordRep152 i)) :
    WeakValidRates r
      (periodic ws7Word152.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word152)) := by
  have hrepLe : ∀ i, (ws7WordRep152 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap152 (ws7WordRep152 i) = ws7WordCap152 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap152, ws7WordRep152, ws7WordP152, ws7WordQ152]
  have hall := caps_of_representatives ws7WordRep152 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word152Weak
  intro i
  simpa [ws7WordCap152, ws7WordP152, ws7WordQ152] using hall i

noncomputable def ws7WordCap153 (i : Fin 7) : ℝ :=
  (ws7WordP153 i : ℝ) / (ws7WordQ153 i : ℝ)

def ws7WordRep153 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word153WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep153 i) ≤ ws7WordCap153 (ws7WordRep153 i)) :
    WeakValidRates r
      (periodic ws7Word153.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word153)) := by
  have hrepLe : ∀ i, (ws7WordRep153 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap153 (ws7WordRep153 i) = ws7WordCap153 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap153, ws7WordRep153, ws7WordP153, ws7WordQ153]
  have hall := caps_of_representatives ws7WordRep153 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word153Weak
  intro i
  simpa [ws7WordCap153, ws7WordP153, ws7WordQ153] using hall i

noncomputable def ws7WordCap154 (i : Fin 7) : ℝ :=
  (ws7WordP154 i : ℝ) / (ws7WordQ154 i : ℝ)

def ws7WordRep154 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

theorem ws7Word154WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep154 i) ≤ ws7WordCap154 (ws7WordRep154 i)) :
    WeakValidRates r
      (periodic ws7Word154.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word154)) := by
  have hrepLe : ∀ i, (ws7WordRep154 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap154 (ws7WordRep154 i) = ws7WordCap154 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap154, ws7WordRep154, ws7WordP154, ws7WordQ154]
  have hall := caps_of_representatives ws7WordRep154 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word154Weak
  intro i
  simpa [ws7WordCap154, ws7WordP154, ws7WordQ154] using hall i

noncomputable def ws7WordCap155 (i : Fin 7) : ℝ :=
  (ws7WordP155 i : ℝ) / (ws7WordQ155 i : ℝ)

def ws7WordRep155 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word155WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep155 i) ≤ ws7WordCap155 (ws7WordRep155 i)) :
    WeakValidRates r
      (periodic ws7Word155.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word155)) := by
  have hrepLe : ∀ i, (ws7WordRep155 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap155 (ws7WordRep155 i) = ws7WordCap155 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap155, ws7WordRep155, ws7WordP155, ws7WordQ155]
  have hall := caps_of_representatives ws7WordRep155 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word155Weak
  intro i
  simpa [ws7WordCap155, ws7WordP155, ws7WordQ155] using hall i

noncomputable def ws7WordCap156 (i : Fin 7) : ℝ :=
  (ws7WordP156 i : ℝ) / (ws7WordQ156 i : ℝ)

def ws7WordRep156 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word156WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep156 i) ≤ ws7WordCap156 (ws7WordRep156 i)) :
    WeakValidRates r
      (periodic ws7Word156.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word156)) := by
  have hrepLe : ∀ i, (ws7WordRep156 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap156 (ws7WordRep156 i) = ws7WordCap156 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap156, ws7WordRep156, ws7WordP156, ws7WordQ156]
  have hall := caps_of_representatives ws7WordRep156 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word156Weak
  intro i
  simpa [ws7WordCap156, ws7WordP156, ws7WordQ156] using hall i

noncomputable def ws7WordCap157 (i : Fin 7) : ℝ :=
  (ws7WordP157 i : ℝ) / (ws7WordQ157 i : ℝ)

def ws7WordRep157 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word157WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep157 i) ≤ ws7WordCap157 (ws7WordRep157 i)) :
    WeakValidRates r
      (periodic ws7Word157.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word157)) := by
  have hrepLe : ∀ i, (ws7WordRep157 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap157 (ws7WordRep157 i) = ws7WordCap157 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap157, ws7WordRep157, ws7WordP157, ws7WordQ157]
  have hall := caps_of_representatives ws7WordRep157 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word157Weak
  intro i
  simpa [ws7WordCap157, ws7WordP157, ws7WordQ157] using hall i

noncomputable def ws7WordCap158 (i : Fin 7) : ℝ :=
  (ws7WordP158 i : ℝ) / (ws7WordQ158 i : ℝ)

def ws7WordRep158 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 3
  | 4 => 3
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word158WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep158 i) ≤ ws7WordCap158 (ws7WordRep158 i)) :
    WeakValidRates r
      (periodic ws7Word158.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word158)) := by
  have hrepLe : ∀ i, (ws7WordRep158 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap158 (ws7WordRep158 i) = ws7WordCap158 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap158, ws7WordRep158, ws7WordP158, ws7WordQ158]
  have hall := caps_of_representatives ws7WordRep158 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word158Weak
  intro i
  simpa [ws7WordCap158, ws7WordP158, ws7WordQ158] using hall i

noncomputable def ws7WordCap159 (i : Fin 7) : ℝ :=
  (ws7WordP159 i : ℝ) / (ws7WordQ159 i : ℝ)

def ws7WordRep159 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word159WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep159 i) ≤ ws7WordCap159 (ws7WordRep159 i)) :
    WeakValidRates r
      (periodic ws7Word159.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word159)) := by
  have hrepLe : ∀ i, (ws7WordRep159 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap159 (ws7WordRep159 i) = ws7WordCap159 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap159, ws7WordRep159, ws7WordP159, ws7WordQ159]
  have hall := caps_of_representatives ws7WordRep159 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word159Weak
  intro i
  simpa [ws7WordCap159, ws7WordP159, ws7WordQ159] using hall i

noncomputable def ws7WordCap160 (i : Fin 7) : ℝ :=
  (ws7WordP160 i : ℝ) / (ws7WordQ160 i : ℝ)

def ws7WordRep160 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word160WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep160 i) ≤ ws7WordCap160 (ws7WordRep160 i)) :
    WeakValidRates r
      (periodic ws7Word160.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word160)) := by
  have hrepLe : ∀ i, (ws7WordRep160 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap160 (ws7WordRep160 i) = ws7WordCap160 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap160, ws7WordRep160, ws7WordP160, ws7WordQ160]
  have hall := caps_of_representatives ws7WordRep160 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word160Weak
  intro i
  simpa [ws7WordCap160, ws7WordP160, ws7WordQ160] using hall i

noncomputable def ws7WordCap161 (i : Fin 7) : ℝ :=
  (ws7WordP161 i : ℝ) / (ws7WordQ161 i : ℝ)

def ws7WordRep161 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

theorem ws7Word161WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep161 i) ≤ ws7WordCap161 (ws7WordRep161 i)) :
    WeakValidRates r
      (periodic ws7Word161.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word161)) := by
  have hrepLe : ∀ i, (ws7WordRep161 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap161 (ws7WordRep161 i) = ws7WordCap161 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap161, ws7WordRep161, ws7WordP161, ws7WordQ161]
  have hall := caps_of_representatives ws7WordRep161 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word161Weak
  intro i
  simpa [ws7WordCap161, ws7WordP161, ws7WordQ161] using hall i

noncomputable def ws7WordCap162 (i : Fin 7) : ℝ :=
  (ws7WordP162 i : ℝ) / (ws7WordQ162 i : ℝ)

def ws7WordRep162 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 6
  | _ => 0

theorem ws7Word162WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep162 i) ≤ ws7WordCap162 (ws7WordRep162 i)) :
    WeakValidRates r
      (periodic ws7Word162.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word162)) := by
  have hrepLe : ∀ i, (ws7WordRep162 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap162 (ws7WordRep162 i) = ws7WordCap162 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap162, ws7WordRep162, ws7WordP162, ws7WordQ162]
  have hall := caps_of_representatives ws7WordRep162 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word162Weak
  intro i
  simpa [ws7WordCap162, ws7WordP162, ws7WordQ162] using hall i

noncomputable def ws7WordCap163 (i : Fin 7) : ℝ :=
  (ws7WordP163 i : ℝ) / (ws7WordQ163 i : ℝ)

def ws7WordRep163 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

theorem ws7Word163WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep163 i) ≤ ws7WordCap163 (ws7WordRep163 i)) :
    WeakValidRates r
      (periodic ws7Word163.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word163)) := by
  have hrepLe : ∀ i, (ws7WordRep163 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap163 (ws7WordRep163 i) = ws7WordCap163 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap163, ws7WordRep163, ws7WordP163, ws7WordQ163]
  have hall := caps_of_representatives ws7WordRep163 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word163Weak
  intro i
  simpa [ws7WordCap163, ws7WordP163, ws7WordQ163] using hall i

noncomputable def ws7WordCap164 (i : Fin 7) : ℝ :=
  (ws7WordP164 i : ℝ) / (ws7WordQ164 i : ℝ)

def ws7WordRep164 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word164WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep164 i) ≤ ws7WordCap164 (ws7WordRep164 i)) :
    WeakValidRates r
      (periodic ws7Word164.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word164)) := by
  have hrepLe : ∀ i, (ws7WordRep164 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap164 (ws7WordRep164 i) = ws7WordCap164 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap164, ws7WordRep164, ws7WordP164, ws7WordQ164]
  have hall := caps_of_representatives ws7WordRep164 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word164Weak
  intro i
  simpa [ws7WordCap164, ws7WordP164, ws7WordQ164] using hall i

noncomputable def ws7WordCap165 (i : Fin 7) : ℝ :=
  (ws7WordP165 i : ℝ) / (ws7WordQ165 i : ℝ)

def ws7WordRep165 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word165WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep165 i) ≤ ws7WordCap165 (ws7WordRep165 i)) :
    WeakValidRates r
      (periodic ws7Word165.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word165)) := by
  have hrepLe : ∀ i, (ws7WordRep165 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap165 (ws7WordRep165 i) = ws7WordCap165 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap165, ws7WordRep165, ws7WordP165, ws7WordQ165]
  have hall := caps_of_representatives ws7WordRep165 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word165Weak
  intro i
  simpa [ws7WordCap165, ws7WordP165, ws7WordQ165] using hall i

noncomputable def ws7WordCap166 (i : Fin 7) : ℝ :=
  (ws7WordP166 i : ℝ) / (ws7WordQ166 i : ℝ)

def ws7WordRep166 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 0
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 3
  | 6 => 3
  | _ => 0

theorem ws7Word166WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep166 i) ≤ ws7WordCap166 (ws7WordRep166 i)) :
    WeakValidRates r
      (periodic ws7Word166.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word166)) := by
  have hrepLe : ∀ i, (ws7WordRep166 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap166 (ws7WordRep166 i) = ws7WordCap166 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap166, ws7WordRep166, ws7WordP166, ws7WordQ166]
  have hall := caps_of_representatives ws7WordRep166 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word166Weak
  intro i
  simpa [ws7WordCap166, ws7WordP166, ws7WordQ166] using hall i

noncomputable def ws7WordCap167 (i : Fin 7) : ℝ :=
  (ws7WordP167 i : ℝ) / (ws7WordQ167 i : ℝ)

def ws7WordRep167 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 3
  | 6 => 3
  | _ => 0

theorem ws7Word167WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep167 i) ≤ ws7WordCap167 (ws7WordRep167 i)) :
    WeakValidRates r
      (periodic ws7Word167.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word167)) := by
  have hrepLe : ∀ i, (ws7WordRep167 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap167 (ws7WordRep167 i) = ws7WordCap167 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap167, ws7WordRep167, ws7WordP167, ws7WordQ167]
  have hall := caps_of_representatives ws7WordRep167 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word167Weak
  intro i
  simpa [ws7WordCap167, ws7WordP167, ws7WordQ167] using hall i

noncomputable def ws7WordCap168 (i : Fin 7) : ℝ :=
  (ws7WordP168 i : ℝ) / (ws7WordQ168 i : ℝ)

def ws7WordRep168 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word168WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep168 i) ≤ ws7WordCap168 (ws7WordRep168 i)) :
    WeakValidRates r
      (periodic ws7Word168.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word168)) := by
  have hrepLe : ∀ i, (ws7WordRep168 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap168 (ws7WordRep168 i) = ws7WordCap168 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap168, ws7WordRep168, ws7WordP168, ws7WordQ168]
  have hall := caps_of_representatives ws7WordRep168 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word168Weak
  intro i
  simpa [ws7WordCap168, ws7WordP168, ws7WordQ168] using hall i

noncomputable def ws7WordCap169 (i : Fin 7) : ℝ :=
  (ws7WordP169 i : ℝ) / (ws7WordQ169 i : ℝ)

def ws7WordRep169 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word169WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep169 i) ≤ ws7WordCap169 (ws7WordRep169 i)) :
    WeakValidRates r
      (periodic ws7Word169.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word169)) := by
  have hrepLe : ∀ i, (ws7WordRep169 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap169 (ws7WordRep169 i) = ws7WordCap169 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap169, ws7WordRep169, ws7WordP169, ws7WordQ169]
  have hall := caps_of_representatives ws7WordRep169 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word169Weak
  intro i
  simpa [ws7WordCap169, ws7WordP169, ws7WordQ169] using hall i

noncomputable def ws7WordCap170 (i : Fin 7) : ℝ :=
  (ws7WordP170 i : ℝ) / (ws7WordQ170 i : ℝ)

def ws7WordRep170 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word170WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep170 i) ≤ ws7WordCap170 (ws7WordRep170 i)) :
    WeakValidRates r
      (periodic ws7Word170.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word170)) := by
  have hrepLe : ∀ i, (ws7WordRep170 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap170 (ws7WordRep170 i) = ws7WordCap170 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap170, ws7WordRep170, ws7WordP170, ws7WordQ170]
  have hall := caps_of_representatives ws7WordRep170 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word170Weak
  intro i
  simpa [ws7WordCap170, ws7WordP170, ws7WordQ170] using hall i

noncomputable def ws7WordCap171 (i : Fin 7) : ℝ :=
  (ws7WordP171 i : ℝ) / (ws7WordQ171 i : ℝ)

def ws7WordRep171 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 3
  | 6 => 6
  | _ => 0

theorem ws7Word171WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep171 i) ≤ ws7WordCap171 (ws7WordRep171 i)) :
    WeakValidRates r
      (periodic ws7Word171.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word171)) := by
  have hrepLe : ∀ i, (ws7WordRep171 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap171 (ws7WordRep171 i) = ws7WordCap171 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap171, ws7WordRep171, ws7WordP171, ws7WordQ171]
  have hall := caps_of_representatives ws7WordRep171 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word171Weak
  intro i
  simpa [ws7WordCap171, ws7WordP171, ws7WordQ171] using hall i

noncomputable def ws7WordCap172 (i : Fin 7) : ℝ :=
  (ws7WordP172 i : ℝ) / (ws7WordQ172 i : ℝ)

def ws7WordRep172 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word172WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep172 i) ≤ ws7WordCap172 (ws7WordRep172 i)) :
    WeakValidRates r
      (periodic ws7Word172.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word172)) := by
  have hrepLe : ∀ i, (ws7WordRep172 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap172 (ws7WordRep172 i) = ws7WordCap172 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap172, ws7WordRep172, ws7WordP172, ws7WordQ172]
  have hall := caps_of_representatives ws7WordRep172 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word172Weak
  intro i
  simpa [ws7WordCap172, ws7WordP172, ws7WordQ172] using hall i

noncomputable def ws7WordCap173 (i : Fin 7) : ℝ :=
  (ws7WordP173 i : ℝ) / (ws7WordQ173 i : ℝ)

def ws7WordRep173 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word173WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep173 i) ≤ ws7WordCap173 (ws7WordRep173 i)) :
    WeakValidRates r
      (periodic ws7Word173.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word173)) := by
  have hrepLe : ∀ i, (ws7WordRep173 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap173 (ws7WordRep173 i) = ws7WordCap173 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap173, ws7WordRep173, ws7WordP173, ws7WordQ173]
  have hall := caps_of_representatives ws7WordRep173 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word173Weak
  intro i
  simpa [ws7WordCap173, ws7WordP173, ws7WordQ173] using hall i

noncomputable def ws7WordCap174 (i : Fin 7) : ℝ :=
  (ws7WordP174 i : ℝ) / (ws7WordQ174 i : ℝ)

def ws7WordRep174 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word174WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep174 i) ≤ ws7WordCap174 (ws7WordRep174 i)) :
    WeakValidRates r
      (periodic ws7Word174.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word174)) := by
  have hrepLe : ∀ i, (ws7WordRep174 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap174 (ws7WordRep174 i) = ws7WordCap174 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap174, ws7WordRep174, ws7WordP174, ws7WordQ174]
  have hall := caps_of_representatives ws7WordRep174 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word174Weak
  intro i
  simpa [ws7WordCap174, ws7WordP174, ws7WordQ174] using hall i

noncomputable def ws7WordCap175 (i : Fin 7) : ℝ :=
  (ws7WordP175 i : ℝ) / (ws7WordQ175 i : ℝ)

def ws7WordRep175 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 6
  | _ => 0

theorem ws7Word175WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep175 i) ≤ ws7WordCap175 (ws7WordRep175 i)) :
    WeakValidRates r
      (periodic ws7Word175.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word175)) := by
  have hrepLe : ∀ i, (ws7WordRep175 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap175 (ws7WordRep175 i) = ws7WordCap175 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap175, ws7WordRep175, ws7WordP175, ws7WordQ175]
  have hall := caps_of_representatives ws7WordRep175 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word175Weak
  intro i
  simpa [ws7WordCap175, ws7WordP175, ws7WordQ175] using hall i

noncomputable def ws7WordCap176 (i : Fin 7) : ℝ :=
  (ws7WordP176 i : ℝ) / (ws7WordQ176 i : ℝ)

def ws7WordRep176 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

theorem ws7Word176WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep176 i) ≤ ws7WordCap176 (ws7WordRep176 i)) :
    WeakValidRates r
      (periodic ws7Word176.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word176)) := by
  have hrepLe : ∀ i, (ws7WordRep176 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap176 (ws7WordRep176 i) = ws7WordCap176 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap176, ws7WordRep176, ws7WordP176, ws7WordQ176]
  have hall := caps_of_representatives ws7WordRep176 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word176Weak
  intro i
  simpa [ws7WordCap176, ws7WordP176, ws7WordQ176] using hall i

noncomputable def ws7WordCap177 (i : Fin 7) : ℝ :=
  (ws7WordP177 i : ℝ) / (ws7WordQ177 i : ℝ)

def ws7WordRep177 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

theorem ws7Word177WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep177 i) ≤ ws7WordCap177 (ws7WordRep177 i)) :
    WeakValidRates r
      (periodic ws7Word177.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word177)) := by
  have hrepLe : ∀ i, (ws7WordRep177 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap177 (ws7WordRep177 i) = ws7WordCap177 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap177, ws7WordRep177, ws7WordP177, ws7WordQ177]
  have hall := caps_of_representatives ws7WordRep177 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word177Weak
  intro i
  simpa [ws7WordCap177, ws7WordP177, ws7WordQ177] using hall i

noncomputable def ws7WordCap178 (i : Fin 7) : ℝ :=
  (ws7WordP178 i : ℝ) / (ws7WordQ178 i : ℝ)

def ws7WordRep178 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word178WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep178 i) ≤ ws7WordCap178 (ws7WordRep178 i)) :
    WeakValidRates r
      (periodic ws7Word178.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word178)) := by
  have hrepLe : ∀ i, (ws7WordRep178 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap178 (ws7WordRep178 i) = ws7WordCap178 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap178, ws7WordRep178, ws7WordP178, ws7WordQ178]
  have hall := caps_of_representatives ws7WordRep178 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word178Weak
  intro i
  simpa [ws7WordCap178, ws7WordP178, ws7WordQ178] using hall i

noncomputable def ws7WordCap179 (i : Fin 7) : ℝ :=
  (ws7WordP179 i : ℝ) / (ws7WordQ179 i : ℝ)

def ws7WordRep179 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word179WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep179 i) ≤ ws7WordCap179 (ws7WordRep179 i)) :
    WeakValidRates r
      (periodic ws7Word179.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word179)) := by
  have hrepLe : ∀ i, (ws7WordRep179 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap179 (ws7WordRep179 i) = ws7WordCap179 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap179, ws7WordRep179, ws7WordP179, ws7WordQ179]
  have hall := caps_of_representatives ws7WordRep179 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word179Weak
  intro i
  simpa [ws7WordCap179, ws7WordP179, ws7WordQ179] using hall i

noncomputable def ws7WordCap180 (i : Fin 7) : ℝ :=
  (ws7WordP180 i : ℝ) / (ws7WordQ180 i : ℝ)

def ws7WordRep180 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word180WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep180 i) ≤ ws7WordCap180 (ws7WordRep180 i)) :
    WeakValidRates r
      (periodic ws7Word180.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word180)) := by
  have hrepLe : ∀ i, (ws7WordRep180 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap180 (ws7WordRep180 i) = ws7WordCap180 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap180, ws7WordRep180, ws7WordP180, ws7WordQ180]
  have hall := caps_of_representatives ws7WordRep180 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word180Weak
  intro i
  simpa [ws7WordCap180, ws7WordP180, ws7WordQ180] using hall i

noncomputable def ws7WordCap181 (i : Fin 7) : ℝ :=
  (ws7WordP181 i : ℝ) / (ws7WordQ181 i : ℝ)

def ws7WordRep181 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word181WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep181 i) ≤ ws7WordCap181 (ws7WordRep181 i)) :
    WeakValidRates r
      (periodic ws7Word181.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word181)) := by
  have hrepLe : ∀ i, (ws7WordRep181 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap181 (ws7WordRep181 i) = ws7WordCap181 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap181, ws7WordRep181, ws7WordP181, ws7WordQ181]
  have hall := caps_of_representatives ws7WordRep181 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word181Weak
  intro i
  simpa [ws7WordCap181, ws7WordP181, ws7WordQ181] using hall i

noncomputable def ws7WordCap182 (i : Fin 7) : ℝ :=
  (ws7WordP182 i : ℝ) / (ws7WordQ182 i : ℝ)

def ws7WordRep182 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 6
  | _ => 0

theorem ws7Word182WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep182 i) ≤ ws7WordCap182 (ws7WordRep182 i)) :
    WeakValidRates r
      (periodic ws7Word182.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word182)) := by
  have hrepLe : ∀ i, (ws7WordRep182 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap182 (ws7WordRep182 i) = ws7WordCap182 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap182, ws7WordRep182, ws7WordP182, ws7WordQ182]
  have hall := caps_of_representatives ws7WordRep182 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word182Weak
  intro i
  simpa [ws7WordCap182, ws7WordP182, ws7WordQ182] using hall i

noncomputable def ws7WordCap183 (i : Fin 7) : ℝ :=
  (ws7WordP183 i : ℝ) / (ws7WordQ183 i : ℝ)

def ws7WordRep183 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word183WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep183 i) ≤ ws7WordCap183 (ws7WordRep183 i)) :
    WeakValidRates r
      (periodic ws7Word183.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word183)) := by
  have hrepLe : ∀ i, (ws7WordRep183 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap183 (ws7WordRep183 i) = ws7WordCap183 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap183, ws7WordRep183, ws7WordP183, ws7WordQ183]
  have hall := caps_of_representatives ws7WordRep183 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word183Weak
  intro i
  simpa [ws7WordCap183, ws7WordP183, ws7WordQ183] using hall i

noncomputable def ws7WordCap184 (i : Fin 7) : ℝ :=
  (ws7WordP184 i : ℝ) / (ws7WordQ184 i : ℝ)

def ws7WordRep184 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word184WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep184 i) ≤ ws7WordCap184 (ws7WordRep184 i)) :
    WeakValidRates r
      (periodic ws7Word184.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word184)) := by
  have hrepLe : ∀ i, (ws7WordRep184 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap184 (ws7WordRep184 i) = ws7WordCap184 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap184, ws7WordRep184, ws7WordP184, ws7WordQ184]
  have hall := caps_of_representatives ws7WordRep184 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word184Weak
  intro i
  simpa [ws7WordCap184, ws7WordP184, ws7WordQ184] using hall i

noncomputable def ws7WordCap185 (i : Fin 7) : ℝ :=
  (ws7WordP185 i : ℝ) / (ws7WordQ185 i : ℝ)

def ws7WordRep185 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word185WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep185 i) ≤ ws7WordCap185 (ws7WordRep185 i)) :
    WeakValidRates r
      (periodic ws7Word185.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word185)) := by
  have hrepLe : ∀ i, (ws7WordRep185 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap185 (ws7WordRep185 i) = ws7WordCap185 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap185, ws7WordRep185, ws7WordP185, ws7WordQ185]
  have hall := caps_of_representatives ws7WordRep185 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word185Weak
  intro i
  simpa [ws7WordCap185, ws7WordP185, ws7WordQ185] using hall i

noncomputable def ws7WordCap186 (i : Fin 7) : ℝ :=
  (ws7WordP186 i : ℝ) / (ws7WordQ186 i : ℝ)

def ws7WordRep186 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 3
  | 4 => 3
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word186WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep186 i) ≤ ws7WordCap186 (ws7WordRep186 i)) :
    WeakValidRates r
      (periodic ws7Word186.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word186)) := by
  have hrepLe : ∀ i, (ws7WordRep186 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap186 (ws7WordRep186 i) = ws7WordCap186 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap186, ws7WordRep186, ws7WordP186, ws7WordQ186]
  have hall := caps_of_representatives ws7WordRep186 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word186Weak
  intro i
  simpa [ws7WordCap186, ws7WordP186, ws7WordQ186] using hall i

noncomputable def ws7WordCap187 (i : Fin 7) : ℝ :=
  (ws7WordP187 i : ℝ) / (ws7WordQ187 i : ℝ)

def ws7WordRep187 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word187WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep187 i) ≤ ws7WordCap187 (ws7WordRep187 i)) :
    WeakValidRates r
      (periodic ws7Word187.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word187)) := by
  have hrepLe : ∀ i, (ws7WordRep187 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap187 (ws7WordRep187 i) = ws7WordCap187 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap187, ws7WordRep187, ws7WordP187, ws7WordQ187]
  have hall := caps_of_representatives ws7WordRep187 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word187Weak
  intro i
  simpa [ws7WordCap187, ws7WordP187, ws7WordQ187] using hall i

noncomputable def ws7WordCap188 (i : Fin 7) : ℝ :=
  (ws7WordP188 i : ℝ) / (ws7WordQ188 i : ℝ)

def ws7WordRep188 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

theorem ws7Word188WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep188 i) ≤ ws7WordCap188 (ws7WordRep188 i)) :
    WeakValidRates r
      (periodic ws7Word188.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word188)) := by
  have hrepLe : ∀ i, (ws7WordRep188 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap188 (ws7WordRep188 i) = ws7WordCap188 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap188, ws7WordRep188, ws7WordP188, ws7WordQ188]
  have hall := caps_of_representatives ws7WordRep188 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word188Weak
  intro i
  simpa [ws7WordCap188, ws7WordP188, ws7WordQ188] using hall i

noncomputable def ws7WordCap189 (i : Fin 7) : ℝ :=
  (ws7WordP189 i : ℝ) / (ws7WordQ189 i : ℝ)

def ws7WordRep189 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word189WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep189 i) ≤ ws7WordCap189 (ws7WordRep189 i)) :
    WeakValidRates r
      (periodic ws7Word189.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word189)) := by
  have hrepLe : ∀ i, (ws7WordRep189 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap189 (ws7WordRep189 i) = ws7WordCap189 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap189, ws7WordRep189, ws7WordP189, ws7WordQ189]
  have hall := caps_of_representatives ws7WordRep189 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word189Weak
  intro i
  simpa [ws7WordCap189, ws7WordP189, ws7WordQ189] using hall i

noncomputable def ws7WordCap190 (i : Fin 7) : ℝ :=
  (ws7WordP190 i : ℝ) / (ws7WordQ190 i : ℝ)

def ws7WordRep190 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 2
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word190WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep190 i) ≤ ws7WordCap190 (ws7WordRep190 i)) :
    WeakValidRates r
      (periodic ws7Word190.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word190)) := by
  have hrepLe : ∀ i, (ws7WordRep190 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap190 (ws7WordRep190 i) = ws7WordCap190 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap190, ws7WordRep190, ws7WordP190, ws7WordQ190]
  have hall := caps_of_representatives ws7WordRep190 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word190Weak
  intro i
  simpa [ws7WordCap190, ws7WordP190, ws7WordQ190] using hall i

noncomputable def ws7WordCap191 (i : Fin 7) : ℝ :=
  (ws7WordP191 i : ℝ) / (ws7WordQ191 i : ℝ)

def ws7WordRep191 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

theorem ws7Word191WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep191 i) ≤ ws7WordCap191 (ws7WordRep191 i)) :
    WeakValidRates r
      (periodic ws7Word191.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word191)) := by
  have hrepLe : ∀ i, (ws7WordRep191 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap191 (ws7WordRep191 i) = ws7WordCap191 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap191, ws7WordRep191, ws7WordP191, ws7WordQ191]
  have hall := caps_of_representatives ws7WordRep191 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word191Weak
  intro i
  simpa [ws7WordCap191, ws7WordP191, ws7WordQ191] using hall i

noncomputable def ws7WordCap192 (i : Fin 7) : ℝ :=
  (ws7WordP192 i : ℝ) / (ws7WordQ192 i : ℝ)

def ws7WordRep192 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 3
  | 4 => 3
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word192WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep192 i) ≤ ws7WordCap192 (ws7WordRep192 i)) :
    WeakValidRates r
      (periodic ws7Word192.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word192)) := by
  have hrepLe : ∀ i, (ws7WordRep192 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap192 (ws7WordRep192 i) = ws7WordCap192 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap192, ws7WordRep192, ws7WordP192, ws7WordQ192]
  have hall := caps_of_representatives ws7WordRep192 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word192Weak
  intro i
  simpa [ws7WordCap192, ws7WordP192, ws7WordQ192] using hall i

noncomputable def ws7WordCap193 (i : Fin 7) : ℝ :=
  (ws7WordP193 i : ℝ) / (ws7WordQ193 i : ℝ)

def ws7WordRep193 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 3
  | 6 => 3
  | _ => 0

theorem ws7Word193WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep193 i) ≤ ws7WordCap193 (ws7WordRep193 i)) :
    WeakValidRates r
      (periodic ws7Word193.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word193)) := by
  have hrepLe : ∀ i, (ws7WordRep193 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap193 (ws7WordRep193 i) = ws7WordCap193 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap193, ws7WordRep193, ws7WordP193, ws7WordQ193]
  have hall := caps_of_representatives ws7WordRep193 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word193Weak
  intro i
  simpa [ws7WordCap193, ws7WordP193, ws7WordQ193] using hall i

noncomputable def ws7WordCap194 (i : Fin 7) : ℝ :=
  (ws7WordP194 i : ℝ) / (ws7WordQ194 i : ℝ)

def ws7WordRep194 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 2
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word194WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep194 i) ≤ ws7WordCap194 (ws7WordRep194 i)) :
    WeakValidRates r
      (periodic ws7Word194.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word194)) := by
  have hrepLe : ∀ i, (ws7WordRep194 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap194 (ws7WordRep194 i) = ws7WordCap194 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap194, ws7WordRep194, ws7WordP194, ws7WordQ194]
  have hall := caps_of_representatives ws7WordRep194 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word194Weak
  intro i
  simpa [ws7WordCap194, ws7WordP194, ws7WordQ194] using hall i

noncomputable def ws7WordCap195 (i : Fin 7) : ℝ :=
  (ws7WordP195 i : ℝ) / (ws7WordQ195 i : ℝ)

def ws7WordRep195 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 2
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word195WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep195 i) ≤ ws7WordCap195 (ws7WordRep195 i)) :
    WeakValidRates r
      (periodic ws7Word195.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word195)) := by
  have hrepLe : ∀ i, (ws7WordRep195 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap195 (ws7WordRep195 i) = ws7WordCap195 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap195, ws7WordRep195, ws7WordP195, ws7WordQ195]
  have hall := caps_of_representatives ws7WordRep195 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word195Weak
  intro i
  simpa [ws7WordCap195, ws7WordP195, ws7WordQ195] using hall i

noncomputable def ws7WordCap196 (i : Fin 7) : ℝ :=
  (ws7WordP196 i : ℝ) / (ws7WordQ196 i : ℝ)

def ws7WordRep196 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 6
  | _ => 0

theorem ws7Word196WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep196 i) ≤ ws7WordCap196 (ws7WordRep196 i)) :
    WeakValidRates r
      (periodic ws7Word196.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word196)) := by
  have hrepLe : ∀ i, (ws7WordRep196 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap196 (ws7WordRep196 i) = ws7WordCap196 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap196, ws7WordRep196, ws7WordP196, ws7WordQ196]
  have hall := caps_of_representatives ws7WordRep196 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word196Weak
  intro i
  simpa [ws7WordCap196, ws7WordP196, ws7WordQ196] using hall i

noncomputable def ws7WordCap197 (i : Fin 7) : ℝ :=
  (ws7WordP197 i : ℝ) / (ws7WordQ197 i : ℝ)

def ws7WordRep197 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word197WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep197 i) ≤ ws7WordCap197 (ws7WordRep197 i)) :
    WeakValidRates r
      (periodic ws7Word197.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word197)) := by
  have hrepLe : ∀ i, (ws7WordRep197 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap197 (ws7WordRep197 i) = ws7WordCap197 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap197, ws7WordRep197, ws7WordP197, ws7WordQ197]
  have hall := caps_of_representatives ws7WordRep197 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word197Weak
  intro i
  simpa [ws7WordCap197, ws7WordP197, ws7WordQ197] using hall i

noncomputable def ws7WordCap198 (i : Fin 7) : ℝ :=
  (ws7WordP198 i : ℝ) / (ws7WordQ198 i : ℝ)

def ws7WordRep198 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word198WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep198 i) ≤ ws7WordCap198 (ws7WordRep198 i)) :
    WeakValidRates r
      (periodic ws7Word198.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word198)) := by
  have hrepLe : ∀ i, (ws7WordRep198 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap198 (ws7WordRep198 i) = ws7WordCap198 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap198, ws7WordRep198, ws7WordP198, ws7WordQ198]
  have hall := caps_of_representatives ws7WordRep198 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word198Weak
  intro i
  simpa [ws7WordCap198, ws7WordP198, ws7WordQ198] using hall i

noncomputable def ws7WordCap199 (i : Fin 7) : ℝ :=
  (ws7WordP199 i : ℝ) / (ws7WordQ199 i : ℝ)

def ws7WordRep199 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

theorem ws7Word199WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep199 i) ≤ ws7WordCap199 (ws7WordRep199 i)) :
    WeakValidRates r
      (periodic ws7Word199.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word199)) := by
  have hrepLe : ∀ i, (ws7WordRep199 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap199 (ws7WordRep199 i) = ws7WordCap199 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap199, ws7WordRep199, ws7WordP199, ws7WordQ199]
  have hall := caps_of_representatives ws7WordRep199 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word199Weak
  intro i
  simpa [ws7WordCap199, ws7WordP199, ws7WordQ199] using hall i

noncomputable def ws7WordCap200 (i : Fin 7) : ℝ :=
  (ws7WordP200 i : ℝ) / (ws7WordQ200 i : ℝ)

def ws7WordRep200 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word200WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep200 i) ≤ ws7WordCap200 (ws7WordRep200 i)) :
    WeakValidRates r
      (periodic ws7Word200.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word200)) := by
  have hrepLe : ∀ i, (ws7WordRep200 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap200 (ws7WordRep200 i) = ws7WordCap200 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap200, ws7WordRep200, ws7WordP200, ws7WordQ200]
  have hall := caps_of_representatives ws7WordRep200 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word200Weak
  intro i
  simpa [ws7WordCap200, ws7WordP200, ws7WordQ200] using hall i

noncomputable def ws7WordCap201 (i : Fin 7) : ℝ :=
  (ws7WordP201 i : ℝ) / (ws7WordQ201 i : ℝ)

def ws7WordRep201 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 3
  | 4 => 3
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word201WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep201 i) ≤ ws7WordCap201 (ws7WordRep201 i)) :
    WeakValidRates r
      (periodic ws7Word201.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word201)) := by
  have hrepLe : ∀ i, (ws7WordRep201 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap201 (ws7WordRep201 i) = ws7WordCap201 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap201, ws7WordRep201, ws7WordP201, ws7WordQ201]
  have hall := caps_of_representatives ws7WordRep201 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word201Weak
  intro i
  simpa [ws7WordCap201, ws7WordP201, ws7WordQ201] using hall i

noncomputable def ws7WordCap202 (i : Fin 7) : ℝ :=
  (ws7WordP202 i : ℝ) / (ws7WordQ202 i : ℝ)

def ws7WordRep202 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word202WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep202 i) ≤ ws7WordCap202 (ws7WordRep202 i)) :
    WeakValidRates r
      (periodic ws7Word202.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word202)) := by
  have hrepLe : ∀ i, (ws7WordRep202 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap202 (ws7WordRep202 i) = ws7WordCap202 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap202, ws7WordRep202, ws7WordP202, ws7WordQ202]
  have hall := caps_of_representatives ws7WordRep202 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word202Weak
  intro i
  simpa [ws7WordCap202, ws7WordP202, ws7WordQ202] using hall i

noncomputable def ws7WordCap203 (i : Fin 7) : ℝ :=
  (ws7WordP203 i : ℝ) / (ws7WordQ203 i : ℝ)

def ws7WordRep203 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 0
  | 2 => 2
  | 3 => 2
  | 4 => 2
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word203WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep203 i) ≤ ws7WordCap203 (ws7WordRep203 i)) :
    WeakValidRates r
      (periodic ws7Word203.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word203)) := by
  have hrepLe : ∀ i, (ws7WordRep203 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap203 (ws7WordRep203 i) = ws7WordCap203 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap203, ws7WordRep203, ws7WordP203, ws7WordQ203]
  have hall := caps_of_representatives ws7WordRep203 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word203Weak
  intro i
  simpa [ws7WordCap203, ws7WordP203, ws7WordQ203] using hall i

noncomputable def ws7WordCap204 (i : Fin 7) : ℝ :=
  (ws7WordP204 i : ℝ) / (ws7WordQ204 i : ℝ)

def ws7WordRep204 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 3
  | 6 => 3
  | _ => 0

theorem ws7Word204WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep204 i) ≤ ws7WordCap204 (ws7WordRep204 i)) :
    WeakValidRates r
      (periodic ws7Word204.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word204)) := by
  have hrepLe : ∀ i, (ws7WordRep204 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap204 (ws7WordRep204 i) = ws7WordCap204 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap204, ws7WordRep204, ws7WordP204, ws7WordQ204]
  have hall := caps_of_representatives ws7WordRep204 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word204Weak
  intro i
  simpa [ws7WordCap204, ws7WordP204, ws7WordQ204] using hall i

noncomputable def ws7WordCap205 (i : Fin 7) : ℝ :=
  (ws7WordP205 i : ℝ) / (ws7WordQ205 i : ℝ)

def ws7WordRep205 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 6
  | _ => 0

theorem ws7Word205WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep205 i) ≤ ws7WordCap205 (ws7WordRep205 i)) :
    WeakValidRates r
      (periodic ws7Word205.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word205)) := by
  have hrepLe : ∀ i, (ws7WordRep205 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap205 (ws7WordRep205 i) = ws7WordCap205 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap205, ws7WordRep205, ws7WordP205, ws7WordQ205]
  have hall := caps_of_representatives ws7WordRep205 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word205Weak
  intro i
  simpa [ws7WordCap205, ws7WordP205, ws7WordQ205] using hall i

noncomputable def ws7WordCap206 (i : Fin 7) : ℝ :=
  (ws7WordP206 i : ℝ) / (ws7WordQ206 i : ℝ)

def ws7WordRep206 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word206WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep206 i) ≤ ws7WordCap206 (ws7WordRep206 i)) :
    WeakValidRates r
      (periodic ws7Word206.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word206)) := by
  have hrepLe : ∀ i, (ws7WordRep206 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap206 (ws7WordRep206 i) = ws7WordCap206 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap206, ws7WordRep206, ws7WordP206, ws7WordQ206]
  have hall := caps_of_representatives ws7WordRep206 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word206Weak
  intro i
  simpa [ws7WordCap206, ws7WordP206, ws7WordQ206] using hall i

noncomputable def ws7WordCap207 (i : Fin 7) : ℝ :=
  (ws7WordP207 i : ℝ) / (ws7WordQ207 i : ℝ)

def ws7WordRep207 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word207WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep207 i) ≤ ws7WordCap207 (ws7WordRep207 i)) :
    WeakValidRates r
      (periodic ws7Word207.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word207)) := by
  have hrepLe : ∀ i, (ws7WordRep207 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap207 (ws7WordRep207 i) = ws7WordCap207 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap207, ws7WordRep207, ws7WordP207, ws7WordQ207]
  have hall := caps_of_representatives ws7WordRep207 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word207Weak
  intro i
  simpa [ws7WordCap207, ws7WordP207, ws7WordQ207] using hall i

noncomputable def ws7WordCap208 (i : Fin 7) : ℝ :=
  (ws7WordP208 i : ℝ) / (ws7WordQ208 i : ℝ)

def ws7WordRep208 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word208WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep208 i) ≤ ws7WordCap208 (ws7WordRep208 i)) :
    WeakValidRates r
      (periodic ws7Word208.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word208)) := by
  have hrepLe : ∀ i, (ws7WordRep208 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap208 (ws7WordRep208 i) = ws7WordCap208 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap208, ws7WordRep208, ws7WordP208, ws7WordQ208]
  have hall := caps_of_representatives ws7WordRep208 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word208Weak
  intro i
  simpa [ws7WordCap208, ws7WordP208, ws7WordQ208] using hall i

noncomputable def ws7WordCap209 (i : Fin 7) : ℝ :=
  (ws7WordP209 i : ℝ) / (ws7WordQ209 i : ℝ)

def ws7WordRep209 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

theorem ws7Word209WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep209 i) ≤ ws7WordCap209 (ws7WordRep209 i)) :
    WeakValidRates r
      (periodic ws7Word209.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word209)) := by
  have hrepLe : ∀ i, (ws7WordRep209 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap209 (ws7WordRep209 i) = ws7WordCap209 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap209, ws7WordRep209, ws7WordP209, ws7WordQ209]
  have hall := caps_of_representatives ws7WordRep209 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word209Weak
  intro i
  simpa [ws7WordCap209, ws7WordP209, ws7WordQ209] using hall i

noncomputable def ws7WordCap210 (i : Fin 7) : ℝ :=
  (ws7WordP210 i : ℝ) / (ws7WordQ210 i : ℝ)

def ws7WordRep210 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word210WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep210 i) ≤ ws7WordCap210 (ws7WordRep210 i)) :
    WeakValidRates r
      (periodic ws7Word210.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word210)) := by
  have hrepLe : ∀ i, (ws7WordRep210 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap210 (ws7WordRep210 i) = ws7WordCap210 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap210, ws7WordRep210, ws7WordP210, ws7WordQ210]
  have hall := caps_of_representatives ws7WordRep210 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word210Weak
  intro i
  simpa [ws7WordCap210, ws7WordP210, ws7WordQ210] using hall i

noncomputable def ws7WordCap211 (i : Fin 7) : ℝ :=
  (ws7WordP211 i : ℝ) / (ws7WordQ211 i : ℝ)

def ws7WordRep211 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word211WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep211 i) ≤ ws7WordCap211 (ws7WordRep211 i)) :
    WeakValidRates r
      (periodic ws7Word211.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word211)) := by
  have hrepLe : ∀ i, (ws7WordRep211 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap211 (ws7WordRep211 i) = ws7WordCap211 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap211, ws7WordRep211, ws7WordP211, ws7WordQ211]
  have hall := caps_of_representatives ws7WordRep211 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word211Weak
  intro i
  simpa [ws7WordCap211, ws7WordP211, ws7WordQ211] using hall i

noncomputable def ws7WordCap212 (i : Fin 7) : ℝ :=
  (ws7WordP212 i : ℝ) / (ws7WordQ212 i : ℝ)

def ws7WordRep212 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word212WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep212 i) ≤ ws7WordCap212 (ws7WordRep212 i)) :
    WeakValidRates r
      (periodic ws7Word212.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word212)) := by
  have hrepLe : ∀ i, (ws7WordRep212 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap212 (ws7WordRep212 i) = ws7WordCap212 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap212, ws7WordRep212, ws7WordP212, ws7WordQ212]
  have hall := caps_of_representatives ws7WordRep212 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word212Weak
  intro i
  simpa [ws7WordCap212, ws7WordP212, ws7WordQ212] using hall i

noncomputable def ws7WordCap213 (i : Fin 7) : ℝ :=
  (ws7WordP213 i : ℝ) / (ws7WordQ213 i : ℝ)

def ws7WordRep213 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word213WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep213 i) ≤ ws7WordCap213 (ws7WordRep213 i)) :
    WeakValidRates r
      (periodic ws7Word213.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word213)) := by
  have hrepLe : ∀ i, (ws7WordRep213 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap213 (ws7WordRep213 i) = ws7WordCap213 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap213, ws7WordRep213, ws7WordP213, ws7WordQ213]
  have hall := caps_of_representatives ws7WordRep213 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word213Weak
  intro i
  simpa [ws7WordCap213, ws7WordP213, ws7WordQ213] using hall i

noncomputable def ws7WordCap214 (i : Fin 7) : ℝ :=
  (ws7WordP214 i : ℝ) / (ws7WordQ214 i : ℝ)

def ws7WordRep214 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 3
  | 6 => 6
  | _ => 0

theorem ws7Word214WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep214 i) ≤ ws7WordCap214 (ws7WordRep214 i)) :
    WeakValidRates r
      (periodic ws7Word214.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word214)) := by
  have hrepLe : ∀ i, (ws7WordRep214 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap214 (ws7WordRep214 i) = ws7WordCap214 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap214, ws7WordRep214, ws7WordP214, ws7WordQ214]
  have hall := caps_of_representatives ws7WordRep214 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word214Weak
  intro i
  simpa [ws7WordCap214, ws7WordP214, ws7WordQ214] using hall i

noncomputable def ws7WordCap215 (i : Fin 7) : ℝ :=
  (ws7WordP215 i : ℝ) / (ws7WordQ215 i : ℝ)

def ws7WordRep215 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word215WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep215 i) ≤ ws7WordCap215 (ws7WordRep215 i)) :
    WeakValidRates r
      (periodic ws7Word215.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word215)) := by
  have hrepLe : ∀ i, (ws7WordRep215 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap215 (ws7WordRep215 i) = ws7WordCap215 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap215, ws7WordRep215, ws7WordP215, ws7WordQ215]
  have hall := caps_of_representatives ws7WordRep215 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word215Weak
  intro i
  simpa [ws7WordCap215, ws7WordP215, ws7WordQ215] using hall i

noncomputable def ws7WordCap216 (i : Fin 7) : ℝ :=
  (ws7WordP216 i : ℝ) / (ws7WordQ216 i : ℝ)

def ws7WordRep216 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word216WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep216 i) ≤ ws7WordCap216 (ws7WordRep216 i)) :
    WeakValidRates r
      (periodic ws7Word216.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word216)) := by
  have hrepLe : ∀ i, (ws7WordRep216 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap216 (ws7WordRep216 i) = ws7WordCap216 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap216, ws7WordRep216, ws7WordP216, ws7WordQ216]
  have hall := caps_of_representatives ws7WordRep216 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word216Weak
  intro i
  simpa [ws7WordCap216, ws7WordP216, ws7WordQ216] using hall i

noncomputable def ws7WordCap217 (i : Fin 7) : ℝ :=
  (ws7WordP217 i : ℝ) / (ws7WordQ217 i : ℝ)

def ws7WordRep217 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word217WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep217 i) ≤ ws7WordCap217 (ws7WordRep217 i)) :
    WeakValidRates r
      (periodic ws7Word217.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word217)) := by
  have hrepLe : ∀ i, (ws7WordRep217 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap217 (ws7WordRep217 i) = ws7WordCap217 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap217, ws7WordRep217, ws7WordP217, ws7WordQ217]
  have hall := caps_of_representatives ws7WordRep217 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word217Weak
  intro i
  simpa [ws7WordCap217, ws7WordP217, ws7WordQ217] using hall i

noncomputable def ws7WordCap218 (i : Fin 7) : ℝ :=
  (ws7WordP218 i : ℝ) / (ws7WordQ218 i : ℝ)

def ws7WordRep218 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word218WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep218 i) ≤ ws7WordCap218 (ws7WordRep218 i)) :
    WeakValidRates r
      (periodic ws7Word218.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word218)) := by
  have hrepLe : ∀ i, (ws7WordRep218 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap218 (ws7WordRep218 i) = ws7WordCap218 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap218, ws7WordRep218, ws7WordP218, ws7WordQ218]
  have hall := caps_of_representatives ws7WordRep218 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word218Weak
  intro i
  simpa [ws7WordCap218, ws7WordP218, ws7WordQ218] using hall i

noncomputable def ws7WordCap219 (i : Fin 7) : ℝ :=
  (ws7WordP219 i : ℝ) / (ws7WordQ219 i : ℝ)

def ws7WordRep219 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

theorem ws7Word219WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep219 i) ≤ ws7WordCap219 (ws7WordRep219 i)) :
    WeakValidRates r
      (periodic ws7Word219.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word219)) := by
  have hrepLe : ∀ i, (ws7WordRep219 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap219 (ws7WordRep219 i) = ws7WordCap219 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap219, ws7WordRep219, ws7WordP219, ws7WordQ219]
  have hall := caps_of_representatives ws7WordRep219 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word219Weak
  intro i
  simpa [ws7WordCap219, ws7WordP219, ws7WordQ219] using hall i

noncomputable def ws7WordCap220 (i : Fin 7) : ℝ :=
  (ws7WordP220 i : ℝ) / (ws7WordQ220 i : ℝ)

def ws7WordRep220 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 6
  | _ => 0

theorem ws7Word220WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep220 i) ≤ ws7WordCap220 (ws7WordRep220 i)) :
    WeakValidRates r
      (periodic ws7Word220.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word220)) := by
  have hrepLe : ∀ i, (ws7WordRep220 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap220 (ws7WordRep220 i) = ws7WordCap220 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap220, ws7WordRep220, ws7WordP220, ws7WordQ220]
  have hall := caps_of_representatives ws7WordRep220 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word220Weak
  intro i
  simpa [ws7WordCap220, ws7WordP220, ws7WordQ220] using hall i

noncomputable def ws7WordCap221 (i : Fin 7) : ℝ :=
  (ws7WordP221 i : ℝ) / (ws7WordQ221 i : ℝ)

def ws7WordRep221 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 2
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word221WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep221 i) ≤ ws7WordCap221 (ws7WordRep221 i)) :
    WeakValidRates r
      (periodic ws7Word221.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word221)) := by
  have hrepLe : ∀ i, (ws7WordRep221 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap221 (ws7WordRep221 i) = ws7WordCap221 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap221, ws7WordRep221, ws7WordP221, ws7WordQ221]
  have hall := caps_of_representatives ws7WordRep221 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word221Weak
  intro i
  simpa [ws7WordCap221, ws7WordP221, ws7WordQ221] using hall i

noncomputable def ws7WordCap222 (i : Fin 7) : ℝ :=
  (ws7WordP222 i : ℝ) / (ws7WordQ222 i : ℝ)

def ws7WordRep222 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word222WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep222 i) ≤ ws7WordCap222 (ws7WordRep222 i)) :
    WeakValidRates r
      (periodic ws7Word222.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word222)) := by
  have hrepLe : ∀ i, (ws7WordRep222 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap222 (ws7WordRep222 i) = ws7WordCap222 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap222, ws7WordRep222, ws7WordP222, ws7WordQ222]
  have hall := caps_of_representatives ws7WordRep222 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word222Weak
  intro i
  simpa [ws7WordCap222, ws7WordP222, ws7WordQ222] using hall i

noncomputable def ws7WordCap223 (i : Fin 7) : ℝ :=
  (ws7WordP223 i : ℝ) / (ws7WordQ223 i : ℝ)

def ws7WordRep223 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word223WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep223 i) ≤ ws7WordCap223 (ws7WordRep223 i)) :
    WeakValidRates r
      (periodic ws7Word223.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word223)) := by
  have hrepLe : ∀ i, (ws7WordRep223 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap223 (ws7WordRep223 i) = ws7WordCap223 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap223, ws7WordRep223, ws7WordP223, ws7WordQ223]
  have hall := caps_of_representatives ws7WordRep223 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word223Weak
  intro i
  simpa [ws7WordCap223, ws7WordP223, ws7WordQ223] using hall i

noncomputable def ws7WordCap224 (i : Fin 7) : ℝ :=
  (ws7WordP224 i : ℝ) / (ws7WordQ224 i : ℝ)

def ws7WordRep224 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word224WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep224 i) ≤ ws7WordCap224 (ws7WordRep224 i)) :
    WeakValidRates r
      (periodic ws7Word224.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word224)) := by
  have hrepLe : ∀ i, (ws7WordRep224 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap224 (ws7WordRep224 i) = ws7WordCap224 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap224, ws7WordRep224, ws7WordP224, ws7WordQ224]
  have hall := caps_of_representatives ws7WordRep224 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word224Weak
  intro i
  simpa [ws7WordCap224, ws7WordP224, ws7WordQ224] using hall i

noncomputable def ws7WordCap225 (i : Fin 7) : ℝ :=
  (ws7WordP225 i : ℝ) / (ws7WordQ225 i : ℝ)

def ws7WordRep225 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word225WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep225 i) ≤ ws7WordCap225 (ws7WordRep225 i)) :
    WeakValidRates r
      (periodic ws7Word225.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word225)) := by
  have hrepLe : ∀ i, (ws7WordRep225 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap225 (ws7WordRep225 i) = ws7WordCap225 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap225, ws7WordRep225, ws7WordP225, ws7WordQ225]
  have hall := caps_of_representatives ws7WordRep225 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word225Weak
  intro i
  simpa [ws7WordCap225, ws7WordP225, ws7WordQ225] using hall i

noncomputable def ws7WordCap226 (i : Fin 7) : ℝ :=
  (ws7WordP226 i : ℝ) / (ws7WordQ226 i : ℝ)

def ws7WordRep226 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word226WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep226 i) ≤ ws7WordCap226 (ws7WordRep226 i)) :
    WeakValidRates r
      (periodic ws7Word226.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word226)) := by
  have hrepLe : ∀ i, (ws7WordRep226 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap226 (ws7WordRep226 i) = ws7WordCap226 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap226, ws7WordRep226, ws7WordP226, ws7WordQ226]
  have hall := caps_of_representatives ws7WordRep226 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word226Weak
  intro i
  simpa [ws7WordCap226, ws7WordP226, ws7WordQ226] using hall i

noncomputable def ws7WordCap227 (i : Fin 7) : ℝ :=
  (ws7WordP227 i : ℝ) / (ws7WordQ227 i : ℝ)

def ws7WordRep227 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word227WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep227 i) ≤ ws7WordCap227 (ws7WordRep227 i)) :
    WeakValidRates r
      (periodic ws7Word227.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word227)) := by
  have hrepLe : ∀ i, (ws7WordRep227 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap227 (ws7WordRep227 i) = ws7WordCap227 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap227, ws7WordRep227, ws7WordP227, ws7WordQ227]
  have hall := caps_of_representatives ws7WordRep227 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word227Weak
  intro i
  simpa [ws7WordCap227, ws7WordP227, ws7WordQ227] using hall i

noncomputable def ws7WordCap228 (i : Fin 7) : ℝ :=
  (ws7WordP228 i : ℝ) / (ws7WordQ228 i : ℝ)

def ws7WordRep228 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word228WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep228 i) ≤ ws7WordCap228 (ws7WordRep228 i)) :
    WeakValidRates r
      (periodic ws7Word228.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word228)) := by
  have hrepLe : ∀ i, (ws7WordRep228 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap228 (ws7WordRep228 i) = ws7WordCap228 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap228, ws7WordRep228, ws7WordP228, ws7WordQ228]
  have hall := caps_of_representatives ws7WordRep228 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word228Weak
  intro i
  simpa [ws7WordCap228, ws7WordP228, ws7WordQ228] using hall i

noncomputable def ws7WordCap229 (i : Fin 7) : ℝ :=
  (ws7WordP229 i : ℝ) / (ws7WordQ229 i : ℝ)

def ws7WordRep229 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word229WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep229 i) ≤ ws7WordCap229 (ws7WordRep229 i)) :
    WeakValidRates r
      (periodic ws7Word229.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word229)) := by
  have hrepLe : ∀ i, (ws7WordRep229 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap229 (ws7WordRep229 i) = ws7WordCap229 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap229, ws7WordRep229, ws7WordP229, ws7WordQ229]
  have hall := caps_of_representatives ws7WordRep229 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word229Weak
  intro i
  simpa [ws7WordCap229, ws7WordP229, ws7WordQ229] using hall i

noncomputable def ws7WordCap230 (i : Fin 7) : ℝ :=
  (ws7WordP230 i : ℝ) / (ws7WordQ230 i : ℝ)

def ws7WordRep230 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 0
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word230WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep230 i) ≤ ws7WordCap230 (ws7WordRep230 i)) :
    WeakValidRates r
      (periodic ws7Word230.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word230)) := by
  have hrepLe : ∀ i, (ws7WordRep230 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap230 (ws7WordRep230 i) = ws7WordCap230 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap230, ws7WordRep230, ws7WordP230, ws7WordQ230]
  have hall := caps_of_representatives ws7WordRep230 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word230Weak
  intro i
  simpa [ws7WordCap230, ws7WordP230, ws7WordQ230] using hall i

noncomputable def ws7WordCap231 (i : Fin 7) : ℝ :=
  (ws7WordP231 i : ℝ) / (ws7WordQ231 i : ℝ)

def ws7WordRep231 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word231WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep231 i) ≤ ws7WordCap231 (ws7WordRep231 i)) :
    WeakValidRates r
      (periodic ws7Word231.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word231)) := by
  have hrepLe : ∀ i, (ws7WordRep231 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap231 (ws7WordRep231 i) = ws7WordCap231 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap231, ws7WordRep231, ws7WordP231, ws7WordQ231]
  have hall := caps_of_representatives ws7WordRep231 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word231Weak
  intro i
  simpa [ws7WordCap231, ws7WordP231, ws7WordQ231] using hall i

noncomputable def ws7WordCap232 (i : Fin 7) : ℝ :=
  (ws7WordP232 i : ℝ) / (ws7WordQ232 i : ℝ)

def ws7WordRep232 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

theorem ws7Word232WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep232 i) ≤ ws7WordCap232 (ws7WordRep232 i)) :
    WeakValidRates r
      (periodic ws7Word232.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word232)) := by
  have hrepLe : ∀ i, (ws7WordRep232 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap232 (ws7WordRep232 i) = ws7WordCap232 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap232, ws7WordRep232, ws7WordP232, ws7WordQ232]
  have hall := caps_of_representatives ws7WordRep232 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word232Weak
  intro i
  simpa [ws7WordCap232, ws7WordP232, ws7WordQ232] using hall i

noncomputable def ws7WordCap233 (i : Fin 7) : ℝ :=
  (ws7WordP233 i : ℝ) / (ws7WordQ233 i : ℝ)

def ws7WordRep233 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 3
  | 6 => 3
  | _ => 0

theorem ws7Word233WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep233 i) ≤ ws7WordCap233 (ws7WordRep233 i)) :
    WeakValidRates r
      (periodic ws7Word233.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word233)) := by
  have hrepLe : ∀ i, (ws7WordRep233 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap233 (ws7WordRep233 i) = ws7WordCap233 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap233, ws7WordRep233, ws7WordP233, ws7WordQ233]
  have hall := caps_of_representatives ws7WordRep233 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word233Weak
  intro i
  simpa [ws7WordCap233, ws7WordP233, ws7WordQ233] using hall i

noncomputable def ws7WordCap234 (i : Fin 7) : ℝ :=
  (ws7WordP234 i : ℝ) / (ws7WordQ234 i : ℝ)

def ws7WordRep234 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word234WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep234 i) ≤ ws7WordCap234 (ws7WordRep234 i)) :
    WeakValidRates r
      (periodic ws7Word234.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word234)) := by
  have hrepLe : ∀ i, (ws7WordRep234 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap234 (ws7WordRep234 i) = ws7WordCap234 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap234, ws7WordRep234, ws7WordP234, ws7WordQ234]
  have hall := caps_of_representatives ws7WordRep234 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word234Weak
  intro i
  simpa [ws7WordCap234, ws7WordP234, ws7WordQ234] using hall i

noncomputable def ws7WordCap235 (i : Fin 7) : ℝ :=
  (ws7WordP235 i : ℝ) / (ws7WordQ235 i : ℝ)

def ws7WordRep235 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word235WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep235 i) ≤ ws7WordCap235 (ws7WordRep235 i)) :
    WeakValidRates r
      (periodic ws7Word235.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word235)) := by
  have hrepLe : ∀ i, (ws7WordRep235 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap235 (ws7WordRep235 i) = ws7WordCap235 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap235, ws7WordRep235, ws7WordP235, ws7WordQ235]
  have hall := caps_of_representatives ws7WordRep235 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word235Weak
  intro i
  simpa [ws7WordCap235, ws7WordP235, ws7WordQ235] using hall i

noncomputable def ws7WordCap236 (i : Fin 7) : ℝ :=
  (ws7WordP236 i : ℝ) / (ws7WordQ236 i : ℝ)

def ws7WordRep236 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word236WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep236 i) ≤ ws7WordCap236 (ws7WordRep236 i)) :
    WeakValidRates r
      (periodic ws7Word236.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word236)) := by
  have hrepLe : ∀ i, (ws7WordRep236 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap236 (ws7WordRep236 i) = ws7WordCap236 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap236, ws7WordRep236, ws7WordP236, ws7WordQ236]
  have hall := caps_of_representatives ws7WordRep236 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word236Weak
  intro i
  simpa [ws7WordCap236, ws7WordP236, ws7WordQ236] using hall i

noncomputable def ws7WordCap237 (i : Fin 7) : ℝ :=
  (ws7WordP237 i : ℝ) / (ws7WordQ237 i : ℝ)

def ws7WordRep237 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word237WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep237 i) ≤ ws7WordCap237 (ws7WordRep237 i)) :
    WeakValidRates r
      (periodic ws7Word237.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word237)) := by
  have hrepLe : ∀ i, (ws7WordRep237 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap237 (ws7WordRep237 i) = ws7WordCap237 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap237, ws7WordRep237, ws7WordP237, ws7WordQ237]
  have hall := caps_of_representatives ws7WordRep237 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word237Weak
  intro i
  simpa [ws7WordCap237, ws7WordP237, ws7WordQ237] using hall i

noncomputable def ws7WordCap238 (i : Fin 7) : ℝ :=
  (ws7WordP238 i : ℝ) / (ws7WordQ238 i : ℝ)

def ws7WordRep238 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word238WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep238 i) ≤ ws7WordCap238 (ws7WordRep238 i)) :
    WeakValidRates r
      (periodic ws7Word238.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word238)) := by
  have hrepLe : ∀ i, (ws7WordRep238 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap238 (ws7WordRep238 i) = ws7WordCap238 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap238, ws7WordRep238, ws7WordP238, ws7WordQ238]
  have hall := caps_of_representatives ws7WordRep238 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word238Weak
  intro i
  simpa [ws7WordCap238, ws7WordP238, ws7WordQ238] using hall i

noncomputable def ws7WordCap239 (i : Fin 7) : ℝ :=
  (ws7WordP239 i : ℝ) / (ws7WordQ239 i : ℝ)

def ws7WordRep239 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word239WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep239 i) ≤ ws7WordCap239 (ws7WordRep239 i)) :
    WeakValidRates r
      (periodic ws7Word239.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word239)) := by
  have hrepLe : ∀ i, (ws7WordRep239 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap239 (ws7WordRep239 i) = ws7WordCap239 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap239, ws7WordRep239, ws7WordP239, ws7WordQ239]
  have hall := caps_of_representatives ws7WordRep239 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word239Weak
  intro i
  simpa [ws7WordCap239, ws7WordP239, ws7WordQ239] using hall i

noncomputable def ws7WordCap240 (i : Fin 7) : ℝ :=
  (ws7WordP240 i : ℝ) / (ws7WordQ240 i : ℝ)

def ws7WordRep240 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word240WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep240 i) ≤ ws7WordCap240 (ws7WordRep240 i)) :
    WeakValidRates r
      (periodic ws7Word240.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word240)) := by
  have hrepLe : ∀ i, (ws7WordRep240 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap240 (ws7WordRep240 i) = ws7WordCap240 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap240, ws7WordRep240, ws7WordP240, ws7WordQ240]
  have hall := caps_of_representatives ws7WordRep240 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word240Weak
  intro i
  simpa [ws7WordCap240, ws7WordP240, ws7WordQ240] using hall i

noncomputable def ws7WordCap241 (i : Fin 7) : ℝ :=
  (ws7WordP241 i : ℝ) / (ws7WordQ241 i : ℝ)

def ws7WordRep241 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word241WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep241 i) ≤ ws7WordCap241 (ws7WordRep241 i)) :
    WeakValidRates r
      (periodic ws7Word241.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word241)) := by
  have hrepLe : ∀ i, (ws7WordRep241 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap241 (ws7WordRep241 i) = ws7WordCap241 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap241, ws7WordRep241, ws7WordP241, ws7WordQ241]
  have hall := caps_of_representatives ws7WordRep241 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word241Weak
  intro i
  simpa [ws7WordCap241, ws7WordP241, ws7WordQ241] using hall i

noncomputable def ws7WordCap242 (i : Fin 7) : ℝ :=
  (ws7WordP242 i : ℝ) / (ws7WordQ242 i : ℝ)

def ws7WordRep242 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 2
  | 5 => 2
  | 6 => 2
  | _ => 0

theorem ws7Word242WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep242 i) ≤ ws7WordCap242 (ws7WordRep242 i)) :
    WeakValidRates r
      (periodic ws7Word242.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word242)) := by
  have hrepLe : ∀ i, (ws7WordRep242 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap242 (ws7WordRep242 i) = ws7WordCap242 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap242, ws7WordRep242, ws7WordP242, ws7WordQ242]
  have hall := caps_of_representatives ws7WordRep242 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word242Weak
  intro i
  simpa [ws7WordCap242, ws7WordP242, ws7WordQ242] using hall i

noncomputable def ws7WordCap243 (i : Fin 7) : ℝ :=
  (ws7WordP243 i : ℝ) / (ws7WordQ243 i : ℝ)

def ws7WordRep243 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 6
  | _ => 0

theorem ws7Word243WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep243 i) ≤ ws7WordCap243 (ws7WordRep243 i)) :
    WeakValidRates r
      (periodic ws7Word243.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word243)) := by
  have hrepLe : ∀ i, (ws7WordRep243 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap243 (ws7WordRep243 i) = ws7WordCap243 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap243, ws7WordRep243, ws7WordP243, ws7WordQ243]
  have hall := caps_of_representatives ws7WordRep243 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word243Weak
  intro i
  simpa [ws7WordCap243, ws7WordP243, ws7WordQ243] using hall i

noncomputable def ws7WordCap244 (i : Fin 7) : ℝ :=
  (ws7WordP244 i : ℝ) / (ws7WordQ244 i : ℝ)

def ws7WordRep244 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word244WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep244 i) ≤ ws7WordCap244 (ws7WordRep244 i)) :
    WeakValidRates r
      (periodic ws7Word244.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word244)) := by
  have hrepLe : ∀ i, (ws7WordRep244 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap244 (ws7WordRep244 i) = ws7WordCap244 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap244, ws7WordRep244, ws7WordP244, ws7WordQ244]
  have hall := caps_of_representatives ws7WordRep244 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word244Weak
  intro i
  simpa [ws7WordCap244, ws7WordP244, ws7WordQ244] using hall i

noncomputable def ws7WordCap245 (i : Fin 7) : ℝ :=
  (ws7WordP245 i : ℝ) / (ws7WordQ245 i : ℝ)

def ws7WordRep245 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word245WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep245 i) ≤ ws7WordCap245 (ws7WordRep245 i)) :
    WeakValidRates r
      (periodic ws7Word245.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word245)) := by
  have hrepLe : ∀ i, (ws7WordRep245 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap245 (ws7WordRep245 i) = ws7WordCap245 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap245, ws7WordRep245, ws7WordP245, ws7WordQ245]
  have hall := caps_of_representatives ws7WordRep245 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word245Weak
  intro i
  simpa [ws7WordCap245, ws7WordP245, ws7WordQ245] using hall i

noncomputable def ws7WordCap246 (i : Fin 7) : ℝ :=
  (ws7WordP246 i : ℝ) / (ws7WordQ246 i : ℝ)

def ws7WordRep246 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word246WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep246 i) ≤ ws7WordCap246 (ws7WordRep246 i)) :
    WeakValidRates r
      (periodic ws7Word246.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word246)) := by
  have hrepLe : ∀ i, (ws7WordRep246 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap246 (ws7WordRep246 i) = ws7WordCap246 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap246, ws7WordRep246, ws7WordP246, ws7WordQ246]
  have hall := caps_of_representatives ws7WordRep246 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word246Weak
  intro i
  simpa [ws7WordCap246, ws7WordP246, ws7WordQ246] using hall i

noncomputable def ws7WordCap247 (i : Fin 7) : ℝ :=
  (ws7WordP247 i : ℝ) / (ws7WordQ247 i : ℝ)

def ws7WordRep247 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word247WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep247 i) ≤ ws7WordCap247 (ws7WordRep247 i)) :
    WeakValidRates r
      (periodic ws7Word247.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word247)) := by
  have hrepLe : ∀ i, (ws7WordRep247 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap247 (ws7WordRep247 i) = ws7WordCap247 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap247, ws7WordRep247, ws7WordP247, ws7WordQ247]
  have hall := caps_of_representatives ws7WordRep247 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word247Weak
  intro i
  simpa [ws7WordCap247, ws7WordP247, ws7WordQ247] using hall i

noncomputable def ws7WordCap248 (i : Fin 7) : ℝ :=
  (ws7WordP248 i : ℝ) / (ws7WordQ248 i : ℝ)

def ws7WordRep248 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word248WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep248 i) ≤ ws7WordCap248 (ws7WordRep248 i)) :
    WeakValidRates r
      (periodic ws7Word248.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word248)) := by
  have hrepLe : ∀ i, (ws7WordRep248 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap248 (ws7WordRep248 i) = ws7WordCap248 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap248, ws7WordRep248, ws7WordP248, ws7WordQ248]
  have hall := caps_of_representatives ws7WordRep248 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word248Weak
  intro i
  simpa [ws7WordCap248, ws7WordP248, ws7WordQ248] using hall i

noncomputable def ws7WordCap249 (i : Fin 7) : ℝ :=
  (ws7WordP249 i : ℝ) / (ws7WordQ249 i : ℝ)

def ws7WordRep249 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 3
  | 6 => 6
  | _ => 0

theorem ws7Word249WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep249 i) ≤ ws7WordCap249 (ws7WordRep249 i)) :
    WeakValidRates r
      (periodic ws7Word249.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word249)) := by
  have hrepLe : ∀ i, (ws7WordRep249 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap249 (ws7WordRep249 i) = ws7WordCap249 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap249, ws7WordRep249, ws7WordP249, ws7WordQ249]
  have hall := caps_of_representatives ws7WordRep249 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word249Weak
  intro i
  simpa [ws7WordCap249, ws7WordP249, ws7WordQ249] using hall i

noncomputable def ws7WordCap250 (i : Fin 7) : ℝ :=
  (ws7WordP250 i : ℝ) / (ws7WordQ250 i : ℝ)

def ws7WordRep250 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word250WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep250 i) ≤ ws7WordCap250 (ws7WordRep250 i)) :
    WeakValidRates r
      (periodic ws7Word250.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word250)) := by
  have hrepLe : ∀ i, (ws7WordRep250 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap250 (ws7WordRep250 i) = ws7WordCap250 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap250, ws7WordRep250, ws7WordP250, ws7WordQ250]
  have hall := caps_of_representatives ws7WordRep250 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word250Weak
  intro i
  simpa [ws7WordCap250, ws7WordP250, ws7WordQ250] using hall i

noncomputable def ws7WordCap251 (i : Fin 7) : ℝ :=
  (ws7WordP251 i : ℝ) / (ws7WordQ251 i : ℝ)

def ws7WordRep251 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word251WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep251 i) ≤ ws7WordCap251 (ws7WordRep251 i)) :
    WeakValidRates r
      (periodic ws7Word251.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word251)) := by
  have hrepLe : ∀ i, (ws7WordRep251 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap251 (ws7WordRep251 i) = ws7WordCap251 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap251, ws7WordRep251, ws7WordP251, ws7WordQ251]
  have hall := caps_of_representatives ws7WordRep251 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word251Weak
  intro i
  simpa [ws7WordCap251, ws7WordP251, ws7WordQ251] using hall i

noncomputable def ws7WordCap252 (i : Fin 7) : ℝ :=
  (ws7WordP252 i : ℝ) / (ws7WordQ252 i : ℝ)

def ws7WordRep252 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 6
  | _ => 0

theorem ws7Word252WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep252 i) ≤ ws7WordCap252 (ws7WordRep252 i)) :
    WeakValidRates r
      (periodic ws7Word252.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word252)) := by
  have hrepLe : ∀ i, (ws7WordRep252 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap252 (ws7WordRep252 i) = ws7WordCap252 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap252, ws7WordRep252, ws7WordP252, ws7WordQ252]
  have hall := caps_of_representatives ws7WordRep252 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word252Weak
  intro i
  simpa [ws7WordCap252, ws7WordP252, ws7WordQ252] using hall i

noncomputable def ws7WordCap253 (i : Fin 7) : ℝ :=
  (ws7WordP253 i : ℝ) / (ws7WordQ253 i : ℝ)

def ws7WordRep253 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 6
  | _ => 0

theorem ws7Word253WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep253 i) ≤ ws7WordCap253 (ws7WordRep253 i)) :
    WeakValidRates r
      (periodic ws7Word253.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word253)) := by
  have hrepLe : ∀ i, (ws7WordRep253 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap253 (ws7WordRep253 i) = ws7WordCap253 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap253, ws7WordRep253, ws7WordP253, ws7WordQ253]
  have hall := caps_of_representatives ws7WordRep253 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word253Weak
  intro i
  simpa [ws7WordCap253, ws7WordP253, ws7WordQ253] using hall i

noncomputable def ws7WordCap254 (i : Fin 7) : ℝ :=
  (ws7WordP254 i : ℝ) / (ws7WordQ254 i : ℝ)

def ws7WordRep254 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word254WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep254 i) ≤ ws7WordCap254 (ws7WordRep254 i)) :
    WeakValidRates r
      (periodic ws7Word254.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word254)) := by
  have hrepLe : ∀ i, (ws7WordRep254 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap254 (ws7WordRep254 i) = ws7WordCap254 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap254, ws7WordRep254, ws7WordP254, ws7WordQ254]
  have hall := caps_of_representatives ws7WordRep254 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word254Weak
  intro i
  simpa [ws7WordCap254, ws7WordP254, ws7WordQ254] using hall i

noncomputable def ws7WordCap255 (i : Fin 7) : ℝ :=
  (ws7WordP255 i : ℝ) / (ws7WordQ255 i : ℝ)

def ws7WordRep255 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 2
  | 5 => 2
  | 6 => 6
  | _ => 0

theorem ws7Word255WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep255 i) ≤ ws7WordCap255 (ws7WordRep255 i)) :
    WeakValidRates r
      (periodic ws7Word255.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word255)) := by
  have hrepLe : ∀ i, (ws7WordRep255 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap255 (ws7WordRep255 i) = ws7WordCap255 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap255, ws7WordRep255, ws7WordP255, ws7WordQ255]
  have hall := caps_of_representatives ws7WordRep255 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word255Weak
  intro i
  simpa [ws7WordCap255, ws7WordP255, ws7WordQ255] using hall i

noncomputable def ws7WordCap256 (i : Fin 7) : ℝ :=
  (ws7WordP256 i : ℝ) / (ws7WordQ256 i : ℝ)

def ws7WordRep256 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 2
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word256WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep256 i) ≤ ws7WordCap256 (ws7WordRep256 i)) :
    WeakValidRates r
      (periodic ws7Word256.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word256)) := by
  have hrepLe : ∀ i, (ws7WordRep256 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap256 (ws7WordRep256 i) = ws7WordCap256 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap256, ws7WordRep256, ws7WordP256, ws7WordQ256]
  have hall := caps_of_representatives ws7WordRep256 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word256Weak
  intro i
  simpa [ws7WordCap256, ws7WordP256, ws7WordQ256] using hall i

noncomputable def ws7WordCap257 (i : Fin 7) : ℝ :=
  (ws7WordP257 i : ℝ) / (ws7WordQ257 i : ℝ)

def ws7WordRep257 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word257WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep257 i) ≤ ws7WordCap257 (ws7WordRep257 i)) :
    WeakValidRates r
      (periodic ws7Word257.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word257)) := by
  have hrepLe : ∀ i, (ws7WordRep257 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap257 (ws7WordRep257 i) = ws7WordCap257 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap257, ws7WordRep257, ws7WordP257, ws7WordQ257]
  have hall := caps_of_representatives ws7WordRep257 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word257Weak
  intro i
  simpa [ws7WordCap257, ws7WordP257, ws7WordQ257] using hall i

noncomputable def ws7WordCap258 (i : Fin 7) : ℝ :=
  (ws7WordP258 i : ℝ) / (ws7WordQ258 i : ℝ)

def ws7WordRep258 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word258WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep258 i) ≤ ws7WordCap258 (ws7WordRep258 i)) :
    WeakValidRates r
      (periodic ws7Word258.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word258)) := by
  have hrepLe : ∀ i, (ws7WordRep258 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap258 (ws7WordRep258 i) = ws7WordCap258 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap258, ws7WordRep258, ws7WordP258, ws7WordQ258]
  have hall := caps_of_representatives ws7WordRep258 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word258Weak
  intro i
  simpa [ws7WordCap258, ws7WordP258, ws7WordQ258] using hall i

noncomputable def ws7WordCap259 (i : Fin 7) : ℝ :=
  (ws7WordP259 i : ℝ) / (ws7WordQ259 i : ℝ)

def ws7WordRep259 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word259WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep259 i) ≤ ws7WordCap259 (ws7WordRep259 i)) :
    WeakValidRates r
      (periodic ws7Word259.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word259)) := by
  have hrepLe : ∀ i, (ws7WordRep259 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap259 (ws7WordRep259 i) = ws7WordCap259 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap259, ws7WordRep259, ws7WordP259, ws7WordQ259]
  have hall := caps_of_representatives ws7WordRep259 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word259Weak
  intro i
  simpa [ws7WordCap259, ws7WordP259, ws7WordQ259] using hall i

noncomputable def ws7WordCap260 (i : Fin 7) : ℝ :=
  (ws7WordP260 i : ℝ) / (ws7WordQ260 i : ℝ)

def ws7WordRep260 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

theorem ws7Word260WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep260 i) ≤ ws7WordCap260 (ws7WordRep260 i)) :
    WeakValidRates r
      (periodic ws7Word260.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word260)) := by
  have hrepLe : ∀ i, (ws7WordRep260 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap260 (ws7WordRep260 i) = ws7WordCap260 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap260, ws7WordRep260, ws7WordP260, ws7WordQ260]
  have hall := caps_of_representatives ws7WordRep260 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word260Weak
  intro i
  simpa [ws7WordCap260, ws7WordP260, ws7WordQ260] using hall i

noncomputable def ws7WordCap261 (i : Fin 7) : ℝ :=
  (ws7WordP261 i : ℝ) / (ws7WordQ261 i : ℝ)

def ws7WordRep261 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word261WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep261 i) ≤ ws7WordCap261 (ws7WordRep261 i)) :
    WeakValidRates r
      (periodic ws7Word261.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word261)) := by
  have hrepLe : ∀ i, (ws7WordRep261 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap261 (ws7WordRep261 i) = ws7WordCap261 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap261, ws7WordRep261, ws7WordP261, ws7WordQ261]
  have hall := caps_of_representatives ws7WordRep261 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word261Weak
  intro i
  simpa [ws7WordCap261, ws7WordP261, ws7WordQ261] using hall i

noncomputable def ws7WordCap262 (i : Fin 7) : ℝ :=
  (ws7WordP262 i : ℝ) / (ws7WordQ262 i : ℝ)

def ws7WordRep262 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 6
  | _ => 0

theorem ws7Word262WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep262 i) ≤ ws7WordCap262 (ws7WordRep262 i)) :
    WeakValidRates r
      (periodic ws7Word262.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word262)) := by
  have hrepLe : ∀ i, (ws7WordRep262 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap262 (ws7WordRep262 i) = ws7WordCap262 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap262, ws7WordRep262, ws7WordP262, ws7WordQ262]
  have hall := caps_of_representatives ws7WordRep262 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word262Weak
  intro i
  simpa [ws7WordCap262, ws7WordP262, ws7WordQ262] using hall i

noncomputable def ws7WordCap263 (i : Fin 7) : ℝ :=
  (ws7WordP263 i : ℝ) / (ws7WordQ263 i : ℝ)

def ws7WordRep263 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word263WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep263 i) ≤ ws7WordCap263 (ws7WordRep263 i)) :
    WeakValidRates r
      (periodic ws7Word263.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word263)) := by
  have hrepLe : ∀ i, (ws7WordRep263 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap263 (ws7WordRep263 i) = ws7WordCap263 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap263, ws7WordRep263, ws7WordP263, ws7WordQ263]
  have hall := caps_of_representatives ws7WordRep263 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word263Weak
  intro i
  simpa [ws7WordCap263, ws7WordP263, ws7WordQ263] using hall i

noncomputable def ws7WordCap264 (i : Fin 7) : ℝ :=
  (ws7WordP264 i : ℝ) / (ws7WordQ264 i : ℝ)

def ws7WordRep264 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

theorem ws7Word264WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep264 i) ≤ ws7WordCap264 (ws7WordRep264 i)) :
    WeakValidRates r
      (periodic ws7Word264.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word264)) := by
  have hrepLe : ∀ i, (ws7WordRep264 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap264 (ws7WordRep264 i) = ws7WordCap264 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap264, ws7WordRep264, ws7WordP264, ws7WordQ264]
  have hall := caps_of_representatives ws7WordRep264 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word264Weak
  intro i
  simpa [ws7WordCap264, ws7WordP264, ws7WordQ264] using hall i

noncomputable def ws7WordCap265 (i : Fin 7) : ℝ :=
  (ws7WordP265 i : ℝ) / (ws7WordQ265 i : ℝ)

def ws7WordRep265 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

theorem ws7Word265WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep265 i) ≤ ws7WordCap265 (ws7WordRep265 i)) :
    WeakValidRates r
      (periodic ws7Word265.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word265)) := by
  have hrepLe : ∀ i, (ws7WordRep265 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap265 (ws7WordRep265 i) = ws7WordCap265 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap265, ws7WordRep265, ws7WordP265, ws7WordQ265]
  have hall := caps_of_representatives ws7WordRep265 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word265Weak
  intro i
  simpa [ws7WordCap265, ws7WordP265, ws7WordQ265] using hall i

noncomputable def ws7WordCap266 (i : Fin 7) : ℝ :=
  (ws7WordP266 i : ℝ) / (ws7WordQ266 i : ℝ)

def ws7WordRep266 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word266WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep266 i) ≤ ws7WordCap266 (ws7WordRep266 i)) :
    WeakValidRates r
      (periodic ws7Word266.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word266)) := by
  have hrepLe : ∀ i, (ws7WordRep266 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap266 (ws7WordRep266 i) = ws7WordCap266 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap266, ws7WordRep266, ws7WordP266, ws7WordQ266]
  have hall := caps_of_representatives ws7WordRep266 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word266Weak
  intro i
  simpa [ws7WordCap266, ws7WordP266, ws7WordQ266] using hall i

noncomputable def ws7WordCap267 (i : Fin 7) : ℝ :=
  (ws7WordP267 i : ℝ) / (ws7WordQ267 i : ℝ)

def ws7WordRep267 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

theorem ws7Word267WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep267 i) ≤ ws7WordCap267 (ws7WordRep267 i)) :
    WeakValidRates r
      (periodic ws7Word267.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word267)) := by
  have hrepLe : ∀ i, (ws7WordRep267 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap267 (ws7WordRep267 i) = ws7WordCap267 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap267, ws7WordRep267, ws7WordP267, ws7WordQ267]
  have hall := caps_of_representatives ws7WordRep267 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word267Weak
  intro i
  simpa [ws7WordCap267, ws7WordP267, ws7WordQ267] using hall i

noncomputable def ws7WordCap268 (i : Fin 7) : ℝ :=
  (ws7WordP268 i : ℝ) / (ws7WordQ268 i : ℝ)

def ws7WordRep268 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word268WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep268 i) ≤ ws7WordCap268 (ws7WordRep268 i)) :
    WeakValidRates r
      (periodic ws7Word268.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word268)) := by
  have hrepLe : ∀ i, (ws7WordRep268 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap268 (ws7WordRep268 i) = ws7WordCap268 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap268, ws7WordRep268, ws7WordP268, ws7WordQ268]
  have hall := caps_of_representatives ws7WordRep268 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word268Weak
  intro i
  simpa [ws7WordCap268, ws7WordP268, ws7WordQ268] using hall i

noncomputable def ws7WordCap269 (i : Fin 7) : ℝ :=
  (ws7WordP269 i : ℝ) / (ws7WordQ269 i : ℝ)

def ws7WordRep269 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word269WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep269 i) ≤ ws7WordCap269 (ws7WordRep269 i)) :
    WeakValidRates r
      (periodic ws7Word269.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word269)) := by
  have hrepLe : ∀ i, (ws7WordRep269 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap269 (ws7WordRep269 i) = ws7WordCap269 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap269, ws7WordRep269, ws7WordP269, ws7WordQ269]
  have hall := caps_of_representatives ws7WordRep269 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word269Weak
  intro i
  simpa [ws7WordCap269, ws7WordP269, ws7WordQ269] using hall i

noncomputable def ws7WordCap270 (i : Fin 7) : ℝ :=
  (ws7WordP270 i : ℝ) / (ws7WordQ270 i : ℝ)

def ws7WordRep270 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 6
  | _ => 0

theorem ws7Word270WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep270 i) ≤ ws7WordCap270 (ws7WordRep270 i)) :
    WeakValidRates r
      (periodic ws7Word270.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word270)) := by
  have hrepLe : ∀ i, (ws7WordRep270 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap270 (ws7WordRep270 i) = ws7WordCap270 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap270, ws7WordRep270, ws7WordP270, ws7WordQ270]
  have hall := caps_of_representatives ws7WordRep270 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word270Weak
  intro i
  simpa [ws7WordCap270, ws7WordP270, ws7WordQ270] using hall i

noncomputable def ws7WordCap271 (i : Fin 7) : ℝ :=
  (ws7WordP271 i : ℝ) / (ws7WordQ271 i : ℝ)

def ws7WordRep271 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word271WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep271 i) ≤ ws7WordCap271 (ws7WordRep271 i)) :
    WeakValidRates r
      (periodic ws7Word271.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word271)) := by
  have hrepLe : ∀ i, (ws7WordRep271 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap271 (ws7WordRep271 i) = ws7WordCap271 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap271, ws7WordRep271, ws7WordP271, ws7WordQ271]
  have hall := caps_of_representatives ws7WordRep271 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word271Weak
  intro i
  simpa [ws7WordCap271, ws7WordP271, ws7WordQ271] using hall i

noncomputable def ws7WordCap272 (i : Fin 7) : ℝ :=
  (ws7WordP272 i : ℝ) / (ws7WordQ272 i : ℝ)

def ws7WordRep272 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word272WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep272 i) ≤ ws7WordCap272 (ws7WordRep272 i)) :
    WeakValidRates r
      (periodic ws7Word272.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word272)) := by
  have hrepLe : ∀ i, (ws7WordRep272 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap272 (ws7WordRep272 i) = ws7WordCap272 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap272, ws7WordRep272, ws7WordP272, ws7WordQ272]
  have hall := caps_of_representatives ws7WordRep272 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word272Weak
  intro i
  simpa [ws7WordCap272, ws7WordP272, ws7WordQ272] using hall i

noncomputable def ws7WordCap273 (i : Fin 7) : ℝ :=
  (ws7WordP273 i : ℝ) / (ws7WordQ273 i : ℝ)

def ws7WordRep273 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word273WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep273 i) ≤ ws7WordCap273 (ws7WordRep273 i)) :
    WeakValidRates r
      (periodic ws7Word273.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word273)) := by
  have hrepLe : ∀ i, (ws7WordRep273 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap273 (ws7WordRep273 i) = ws7WordCap273 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap273, ws7WordRep273, ws7WordP273, ws7WordQ273]
  have hall := caps_of_representatives ws7WordRep273 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word273Weak
  intro i
  simpa [ws7WordCap273, ws7WordP273, ws7WordQ273] using hall i

noncomputable def ws7WordCap274 (i : Fin 7) : ℝ :=
  (ws7WordP274 i : ℝ) / (ws7WordQ274 i : ℝ)

def ws7WordRep274 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 4
  | 5 => 4
  | 6 => 6
  | _ => 0

theorem ws7Word274WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep274 i) ≤ ws7WordCap274 (ws7WordRep274 i)) :
    WeakValidRates r
      (periodic ws7Word274.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word274)) := by
  have hrepLe : ∀ i, (ws7WordRep274 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap274 (ws7WordRep274 i) = ws7WordCap274 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap274, ws7WordRep274, ws7WordP274, ws7WordQ274]
  have hall := caps_of_representatives ws7WordRep274 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word274Weak
  intro i
  simpa [ws7WordCap274, ws7WordP274, ws7WordQ274] using hall i

noncomputable def ws7WordCap275 (i : Fin 7) : ℝ :=
  (ws7WordP275 i : ℝ) / (ws7WordQ275 i : ℝ)

def ws7WordRep275 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word275WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep275 i) ≤ ws7WordCap275 (ws7WordRep275 i)) :
    WeakValidRates r
      (periodic ws7Word275.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word275)) := by
  have hrepLe : ∀ i, (ws7WordRep275 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap275 (ws7WordRep275 i) = ws7WordCap275 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap275, ws7WordRep275, ws7WordP275, ws7WordQ275]
  have hall := caps_of_representatives ws7WordRep275 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word275Weak
  intro i
  simpa [ws7WordCap275, ws7WordP275, ws7WordQ275] using hall i

noncomputable def ws7WordCap276 (i : Fin 7) : ℝ :=
  (ws7WordP276 i : ℝ) / (ws7WordQ276 i : ℝ)

def ws7WordRep276 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

theorem ws7Word276WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep276 i) ≤ ws7WordCap276 (ws7WordRep276 i)) :
    WeakValidRates r
      (periodic ws7Word276.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word276)) := by
  have hrepLe : ∀ i, (ws7WordRep276 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap276 (ws7WordRep276 i) = ws7WordCap276 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap276, ws7WordRep276, ws7WordP276, ws7WordQ276]
  have hall := caps_of_representatives ws7WordRep276 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word276Weak
  intro i
  simpa [ws7WordCap276, ws7WordP276, ws7WordQ276] using hall i

noncomputable def ws7WordCap277 (i : Fin 7) : ℝ :=
  (ws7WordP277 i : ℝ) / (ws7WordQ277 i : ℝ)

def ws7WordRep277 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 6
  | _ => 0

theorem ws7Word277WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep277 i) ≤ ws7WordCap277 (ws7WordRep277 i)) :
    WeakValidRates r
      (periodic ws7Word277.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word277)) := by
  have hrepLe : ∀ i, (ws7WordRep277 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap277 (ws7WordRep277 i) = ws7WordCap277 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap277, ws7WordRep277, ws7WordP277, ws7WordQ277]
  have hall := caps_of_representatives ws7WordRep277 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word277Weak
  intro i
  simpa [ws7WordCap277, ws7WordP277, ws7WordQ277] using hall i

noncomputable def ws7WordCap278 (i : Fin 7) : ℝ :=
  (ws7WordP278 i : ℝ) / (ws7WordQ278 i : ℝ)

def ws7WordRep278 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word278WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep278 i) ≤ ws7WordCap278 (ws7WordRep278 i)) :
    WeakValidRates r
      (periodic ws7Word278.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word278)) := by
  have hrepLe : ∀ i, (ws7WordRep278 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap278 (ws7WordRep278 i) = ws7WordCap278 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap278, ws7WordRep278, ws7WordP278, ws7WordQ278]
  have hall := caps_of_representatives ws7WordRep278 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word278Weak
  intro i
  simpa [ws7WordCap278, ws7WordP278, ws7WordQ278] using hall i

noncomputable def ws7WordCap279 (i : Fin 7) : ℝ :=
  (ws7WordP279 i : ℝ) / (ws7WordQ279 i : ℝ)

def ws7WordRep279 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word279WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep279 i) ≤ ws7WordCap279 (ws7WordRep279 i)) :
    WeakValidRates r
      (periodic ws7Word279.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word279)) := by
  have hrepLe : ∀ i, (ws7WordRep279 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap279 (ws7WordRep279 i) = ws7WordCap279 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap279, ws7WordRep279, ws7WordP279, ws7WordQ279]
  have hall := caps_of_representatives ws7WordRep279 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word279Weak
  intro i
  simpa [ws7WordCap279, ws7WordP279, ws7WordQ279] using hall i

noncomputable def ws7WordCap280 (i : Fin 7) : ℝ :=
  (ws7WordP280 i : ℝ) / (ws7WordQ280 i : ℝ)

def ws7WordRep280 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word280WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep280 i) ≤ ws7WordCap280 (ws7WordRep280 i)) :
    WeakValidRates r
      (periodic ws7Word280.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word280)) := by
  have hrepLe : ∀ i, (ws7WordRep280 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap280 (ws7WordRep280 i) = ws7WordCap280 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap280, ws7WordRep280, ws7WordP280, ws7WordQ280]
  have hall := caps_of_representatives ws7WordRep280 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word280Weak
  intro i
  simpa [ws7WordCap280, ws7WordP280, ws7WordQ280] using hall i

noncomputable def ws7WordCap281 (i : Fin 7) : ℝ :=
  (ws7WordP281 i : ℝ) / (ws7WordQ281 i : ℝ)

def ws7WordRep281 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word281WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep281 i) ≤ ws7WordCap281 (ws7WordRep281 i)) :
    WeakValidRates r
      (periodic ws7Word281.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word281)) := by
  have hrepLe : ∀ i, (ws7WordRep281 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap281 (ws7WordRep281 i) = ws7WordCap281 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap281, ws7WordRep281, ws7WordP281, ws7WordQ281]
  have hall := caps_of_representatives ws7WordRep281 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word281Weak
  intro i
  simpa [ws7WordCap281, ws7WordP281, ws7WordQ281] using hall i

noncomputable def ws7WordCap282 (i : Fin 7) : ℝ :=
  (ws7WordP282 i : ℝ) / (ws7WordQ282 i : ℝ)

def ws7WordRep282 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 6
  | _ => 0

theorem ws7Word282WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep282 i) ≤ ws7WordCap282 (ws7WordRep282 i)) :
    WeakValidRates r
      (periodic ws7Word282.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word282)) := by
  have hrepLe : ∀ i, (ws7WordRep282 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap282 (ws7WordRep282 i) = ws7WordCap282 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap282, ws7WordRep282, ws7WordP282, ws7WordQ282]
  have hall := caps_of_representatives ws7WordRep282 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word282Weak
  intro i
  simpa [ws7WordCap282, ws7WordP282, ws7WordQ282] using hall i

noncomputable def ws7WordCap283 (i : Fin 7) : ℝ :=
  (ws7WordP283 i : ℝ) / (ws7WordQ283 i : ℝ)

def ws7WordRep283 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word283WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep283 i) ≤ ws7WordCap283 (ws7WordRep283 i)) :
    WeakValidRates r
      (periodic ws7Word283.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word283)) := by
  have hrepLe : ∀ i, (ws7WordRep283 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap283 (ws7WordRep283 i) = ws7WordCap283 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap283, ws7WordRep283, ws7WordP283, ws7WordQ283]
  have hall := caps_of_representatives ws7WordRep283 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word283Weak
  intro i
  simpa [ws7WordCap283, ws7WordP283, ws7WordQ283] using hall i

noncomputable def ws7WordCap284 (i : Fin 7) : ℝ :=
  (ws7WordP284 i : ℝ) / (ws7WordQ284 i : ℝ)

def ws7WordRep284 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word284WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep284 i) ≤ ws7WordCap284 (ws7WordRep284 i)) :
    WeakValidRates r
      (periodic ws7Word284.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word284)) := by
  have hrepLe : ∀ i, (ws7WordRep284 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap284 (ws7WordRep284 i) = ws7WordCap284 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap284, ws7WordRep284, ws7WordP284, ws7WordQ284]
  have hall := caps_of_representatives ws7WordRep284 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word284Weak
  intro i
  simpa [ws7WordCap284, ws7WordP284, ws7WordQ284] using hall i

noncomputable def ws7WordCap285 (i : Fin 7) : ℝ :=
  (ws7WordP285 i : ℝ) / (ws7WordQ285 i : ℝ)

def ws7WordRep285 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word285WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep285 i) ≤ ws7WordCap285 (ws7WordRep285 i)) :
    WeakValidRates r
      (periodic ws7Word285.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word285)) := by
  have hrepLe : ∀ i, (ws7WordRep285 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap285 (ws7WordRep285 i) = ws7WordCap285 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap285, ws7WordRep285, ws7WordP285, ws7WordQ285]
  have hall := caps_of_representatives ws7WordRep285 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word285Weak
  intro i
  simpa [ws7WordCap285, ws7WordP285, ws7WordQ285] using hall i

noncomputable def ws7WordCap286 (i : Fin 7) : ℝ :=
  (ws7WordP286 i : ℝ) / (ws7WordQ286 i : ℝ)

def ws7WordRep286 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 6
  | _ => 0

theorem ws7Word286WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep286 i) ≤ ws7WordCap286 (ws7WordRep286 i)) :
    WeakValidRates r
      (periodic ws7Word286.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word286)) := by
  have hrepLe : ∀ i, (ws7WordRep286 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap286 (ws7WordRep286 i) = ws7WordCap286 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap286, ws7WordRep286, ws7WordP286, ws7WordQ286]
  have hall := caps_of_representatives ws7WordRep286 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word286Weak
  intro i
  simpa [ws7WordCap286, ws7WordP286, ws7WordQ286] using hall i

noncomputable def ws7WordCap287 (i : Fin 7) : ℝ :=
  (ws7WordP287 i : ℝ) / (ws7WordQ287 i : ℝ)

def ws7WordRep287 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 3
  | 6 => 6
  | _ => 0

theorem ws7Word287WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep287 i) ≤ ws7WordCap287 (ws7WordRep287 i)) :
    WeakValidRates r
      (periodic ws7Word287.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word287)) := by
  have hrepLe : ∀ i, (ws7WordRep287 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap287 (ws7WordRep287 i) = ws7WordCap287 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap287, ws7WordRep287, ws7WordP287, ws7WordQ287]
  have hall := caps_of_representatives ws7WordRep287 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word287Weak
  intro i
  simpa [ws7WordCap287, ws7WordP287, ws7WordQ287] using hall i

noncomputable def ws7WordCap288 (i : Fin 7) : ℝ :=
  (ws7WordP288 i : ℝ) / (ws7WordQ288 i : ℝ)

def ws7WordRep288 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word288WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep288 i) ≤ ws7WordCap288 (ws7WordRep288 i)) :
    WeakValidRates r
      (periodic ws7Word288.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word288)) := by
  have hrepLe : ∀ i, (ws7WordRep288 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap288 (ws7WordRep288 i) = ws7WordCap288 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap288, ws7WordRep288, ws7WordP288, ws7WordQ288]
  have hall := caps_of_representatives ws7WordRep288 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word288Weak
  intro i
  simpa [ws7WordCap288, ws7WordP288, ws7WordQ288] using hall i

noncomputable def ws7WordCap289 (i : Fin 7) : ℝ :=
  (ws7WordP289 i : ℝ) / (ws7WordQ289 i : ℝ)

def ws7WordRep289 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word289WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep289 i) ≤ ws7WordCap289 (ws7WordRep289 i)) :
    WeakValidRates r
      (periodic ws7Word289.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word289)) := by
  have hrepLe : ∀ i, (ws7WordRep289 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap289 (ws7WordRep289 i) = ws7WordCap289 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap289, ws7WordRep289, ws7WordP289, ws7WordQ289]
  have hall := caps_of_representatives ws7WordRep289 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word289Weak
  intro i
  simpa [ws7WordCap289, ws7WordP289, ws7WordQ289] using hall i

noncomputable def ws7WordCap290 (i : Fin 7) : ℝ :=
  (ws7WordP290 i : ℝ) / (ws7WordQ290 i : ℝ)

def ws7WordRep290 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word290WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep290 i) ≤ ws7WordCap290 (ws7WordRep290 i)) :
    WeakValidRates r
      (periodic ws7Word290.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word290)) := by
  have hrepLe : ∀ i, (ws7WordRep290 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap290 (ws7WordRep290 i) = ws7WordCap290 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap290, ws7WordRep290, ws7WordP290, ws7WordQ290]
  have hall := caps_of_representatives ws7WordRep290 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word290Weak
  intro i
  simpa [ws7WordCap290, ws7WordP290, ws7WordQ290] using hall i

noncomputable def ws7WordCap291 (i : Fin 7) : ℝ :=
  (ws7WordP291 i : ℝ) / (ws7WordQ291 i : ℝ)

def ws7WordRep291 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word291WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep291 i) ≤ ws7WordCap291 (ws7WordRep291 i)) :
    WeakValidRates r
      (periodic ws7Word291.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word291)) := by
  have hrepLe : ∀ i, (ws7WordRep291 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap291 (ws7WordRep291 i) = ws7WordCap291 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap291, ws7WordRep291, ws7WordP291, ws7WordQ291]
  have hall := caps_of_representatives ws7WordRep291 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word291Weak
  intro i
  simpa [ws7WordCap291, ws7WordP291, ws7WordQ291] using hall i

noncomputable def ws7WordCap292 (i : Fin 7) : ℝ :=
  (ws7WordP292 i : ℝ) / (ws7WordQ292 i : ℝ)

def ws7WordRep292 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

theorem ws7Word292WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep292 i) ≤ ws7WordCap292 (ws7WordRep292 i)) :
    WeakValidRates r
      (periodic ws7Word292.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word292)) := by
  have hrepLe : ∀ i, (ws7WordRep292 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap292 (ws7WordRep292 i) = ws7WordCap292 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap292, ws7WordRep292, ws7WordP292, ws7WordQ292]
  have hall := caps_of_representatives ws7WordRep292 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word292Weak
  intro i
  simpa [ws7WordCap292, ws7WordP292, ws7WordQ292] using hall i

noncomputable def ws7WordCap293 (i : Fin 7) : ℝ :=
  (ws7WordP293 i : ℝ) / (ws7WordQ293 i : ℝ)

def ws7WordRep293 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word293WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep293 i) ≤ ws7WordCap293 (ws7WordRep293 i)) :
    WeakValidRates r
      (periodic ws7Word293.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word293)) := by
  have hrepLe : ∀ i, (ws7WordRep293 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap293 (ws7WordRep293 i) = ws7WordCap293 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap293, ws7WordRep293, ws7WordP293, ws7WordQ293]
  have hall := caps_of_representatives ws7WordRep293 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word293Weak
  intro i
  simpa [ws7WordCap293, ws7WordP293, ws7WordQ293] using hall i

noncomputable def ws7WordCap294 (i : Fin 7) : ℝ :=
  (ws7WordP294 i : ℝ) / (ws7WordQ294 i : ℝ)

def ws7WordRep294 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word294WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep294 i) ≤ ws7WordCap294 (ws7WordRep294 i)) :
    WeakValidRates r
      (periodic ws7Word294.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word294)) := by
  have hrepLe : ∀ i, (ws7WordRep294 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap294 (ws7WordRep294 i) = ws7WordCap294 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap294, ws7WordRep294, ws7WordP294, ws7WordQ294]
  have hall := caps_of_representatives ws7WordRep294 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word294Weak
  intro i
  simpa [ws7WordCap294, ws7WordP294, ws7WordQ294] using hall i

noncomputable def ws7WordCap295 (i : Fin 7) : ℝ :=
  (ws7WordP295 i : ℝ) / (ws7WordQ295 i : ℝ)

def ws7WordRep295 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

theorem ws7Word295WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep295 i) ≤ ws7WordCap295 (ws7WordRep295 i)) :
    WeakValidRates r
      (periodic ws7Word295.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word295)) := by
  have hrepLe : ∀ i, (ws7WordRep295 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap295 (ws7WordRep295 i) = ws7WordCap295 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap295, ws7WordRep295, ws7WordP295, ws7WordQ295]
  have hall := caps_of_representatives ws7WordRep295 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word295Weak
  intro i
  simpa [ws7WordCap295, ws7WordP295, ws7WordQ295] using hall i

noncomputable def ws7WordCap296 (i : Fin 7) : ℝ :=
  (ws7WordP296 i : ℝ) / (ws7WordQ296 i : ℝ)

def ws7WordRep296 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word296WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep296 i) ≤ ws7WordCap296 (ws7WordRep296 i)) :
    WeakValidRates r
      (periodic ws7Word296.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word296)) := by
  have hrepLe : ∀ i, (ws7WordRep296 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap296 (ws7WordRep296 i) = ws7WordCap296 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap296, ws7WordRep296, ws7WordP296, ws7WordQ296]
  have hall := caps_of_representatives ws7WordRep296 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word296Weak
  intro i
  simpa [ws7WordCap296, ws7WordP296, ws7WordQ296] using hall i

noncomputable def ws7WordCap297 (i : Fin 7) : ℝ :=
  (ws7WordP297 i : ℝ) / (ws7WordQ297 i : ℝ)

def ws7WordRep297 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 6
  | _ => 0

theorem ws7Word297WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep297 i) ≤ ws7WordCap297 (ws7WordRep297 i)) :
    WeakValidRates r
      (periodic ws7Word297.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word297)) := by
  have hrepLe : ∀ i, (ws7WordRep297 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap297 (ws7WordRep297 i) = ws7WordCap297 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap297, ws7WordRep297, ws7WordP297, ws7WordQ297]
  have hall := caps_of_representatives ws7WordRep297 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word297Weak
  intro i
  simpa [ws7WordCap297, ws7WordP297, ws7WordQ297] using hall i

noncomputable def ws7WordCap298 (i : Fin 7) : ℝ :=
  (ws7WordP298 i : ℝ) / (ws7WordQ298 i : ℝ)

def ws7WordRep298 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

theorem ws7Word298WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep298 i) ≤ ws7WordCap298 (ws7WordRep298 i)) :
    WeakValidRates r
      (periodic ws7Word298.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word298)) := by
  have hrepLe : ∀ i, (ws7WordRep298 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap298 (ws7WordRep298 i) = ws7WordCap298 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap298, ws7WordRep298, ws7WordP298, ws7WordQ298]
  have hall := caps_of_representatives ws7WordRep298 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word298Weak
  intro i
  simpa [ws7WordCap298, ws7WordP298, ws7WordQ298] using hall i

noncomputable def ws7WordCap299 (i : Fin 7) : ℝ :=
  (ws7WordP299 i : ℝ) / (ws7WordQ299 i : ℝ)

def ws7WordRep299 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word299WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep299 i) ≤ ws7WordCap299 (ws7WordRep299 i)) :
    WeakValidRates r
      (periodic ws7Word299.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word299)) := by
  have hrepLe : ∀ i, (ws7WordRep299 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap299 (ws7WordRep299 i) = ws7WordCap299 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap299, ws7WordRep299, ws7WordP299, ws7WordQ299]
  have hall := caps_of_representatives ws7WordRep299 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word299Weak
  intro i
  simpa [ws7WordCap299, ws7WordP299, ws7WordQ299] using hall i

noncomputable def ws7WordCap300 (i : Fin 7) : ℝ :=
  (ws7WordP300 i : ℝ) / (ws7WordQ300 i : ℝ)

def ws7WordRep300 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word300WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep300 i) ≤ ws7WordCap300 (ws7WordRep300 i)) :
    WeakValidRates r
      (periodic ws7Word300.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word300)) := by
  have hrepLe : ∀ i, (ws7WordRep300 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap300 (ws7WordRep300 i) = ws7WordCap300 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap300, ws7WordRep300, ws7WordP300, ws7WordQ300]
  have hall := caps_of_representatives ws7WordRep300 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word300Weak
  intro i
  simpa [ws7WordCap300, ws7WordP300, ws7WordQ300] using hall i

noncomputable def ws7WordCap301 (i : Fin 7) : ℝ :=
  (ws7WordP301 i : ℝ) / (ws7WordQ301 i : ℝ)

def ws7WordRep301 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 3
  | 6 => 3
  | _ => 0

theorem ws7Word301WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep301 i) ≤ ws7WordCap301 (ws7WordRep301 i)) :
    WeakValidRates r
      (periodic ws7Word301.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word301)) := by
  have hrepLe : ∀ i, (ws7WordRep301 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap301 (ws7WordRep301 i) = ws7WordCap301 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap301, ws7WordRep301, ws7WordP301, ws7WordQ301]
  have hall := caps_of_representatives ws7WordRep301 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word301Weak
  intro i
  simpa [ws7WordCap301, ws7WordP301, ws7WordQ301] using hall i

noncomputable def ws7WordCap302 (i : Fin 7) : ℝ :=
  (ws7WordP302 i : ℝ) / (ws7WordQ302 i : ℝ)

def ws7WordRep302 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 6
  | _ => 0

theorem ws7Word302WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep302 i) ≤ ws7WordCap302 (ws7WordRep302 i)) :
    WeakValidRates r
      (periodic ws7Word302.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word302)) := by
  have hrepLe : ∀ i, (ws7WordRep302 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap302 (ws7WordRep302 i) = ws7WordCap302 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap302, ws7WordRep302, ws7WordP302, ws7WordQ302]
  have hall := caps_of_representatives ws7WordRep302 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word302Weak
  intro i
  simpa [ws7WordCap302, ws7WordP302, ws7WordQ302] using hall i

noncomputable def ws7WordCap303 (i : Fin 7) : ℝ :=
  (ws7WordP303 i : ℝ) / (ws7WordQ303 i : ℝ)

def ws7WordRep303 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word303WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep303 i) ≤ ws7WordCap303 (ws7WordRep303 i)) :
    WeakValidRates r
      (periodic ws7Word303.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word303)) := by
  have hrepLe : ∀ i, (ws7WordRep303 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap303 (ws7WordRep303 i) = ws7WordCap303 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap303, ws7WordRep303, ws7WordP303, ws7WordQ303]
  have hall := caps_of_representatives ws7WordRep303 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word303Weak
  intro i
  simpa [ws7WordCap303, ws7WordP303, ws7WordQ303] using hall i

noncomputable def ws7WordCap304 (i : Fin 7) : ℝ :=
  (ws7WordP304 i : ℝ) / (ws7WordQ304 i : ℝ)

def ws7WordRep304 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word304WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep304 i) ≤ ws7WordCap304 (ws7WordRep304 i)) :
    WeakValidRates r
      (periodic ws7Word304.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word304)) := by
  have hrepLe : ∀ i, (ws7WordRep304 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap304 (ws7WordRep304 i) = ws7WordCap304 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap304, ws7WordRep304, ws7WordP304, ws7WordQ304]
  have hall := caps_of_representatives ws7WordRep304 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word304Weak
  intro i
  simpa [ws7WordCap304, ws7WordP304, ws7WordQ304] using hall i

noncomputable def ws7WordCap305 (i : Fin 7) : ℝ :=
  (ws7WordP305 i : ℝ) / (ws7WordQ305 i : ℝ)

def ws7WordRep305 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word305WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep305 i) ≤ ws7WordCap305 (ws7WordRep305 i)) :
    WeakValidRates r
      (periodic ws7Word305.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word305)) := by
  have hrepLe : ∀ i, (ws7WordRep305 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap305 (ws7WordRep305 i) = ws7WordCap305 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap305, ws7WordRep305, ws7WordP305, ws7WordQ305]
  have hall := caps_of_representatives ws7WordRep305 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word305Weak
  intro i
  simpa [ws7WordCap305, ws7WordP305, ws7WordQ305] using hall i

noncomputable def ws7WordCap306 (i : Fin 7) : ℝ :=
  (ws7WordP306 i : ℝ) / (ws7WordQ306 i : ℝ)

def ws7WordRep306 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word306WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep306 i) ≤ ws7WordCap306 (ws7WordRep306 i)) :
    WeakValidRates r
      (periodic ws7Word306.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word306)) := by
  have hrepLe : ∀ i, (ws7WordRep306 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap306 (ws7WordRep306 i) = ws7WordCap306 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap306, ws7WordRep306, ws7WordP306, ws7WordQ306]
  have hall := caps_of_representatives ws7WordRep306 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word306Weak
  intro i
  simpa [ws7WordCap306, ws7WordP306, ws7WordQ306] using hall i

noncomputable def ws7WordCap307 (i : Fin 7) : ℝ :=
  (ws7WordP307 i : ℝ) / (ws7WordQ307 i : ℝ)

def ws7WordRep307 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word307WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep307 i) ≤ ws7WordCap307 (ws7WordRep307 i)) :
    WeakValidRates r
      (periodic ws7Word307.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word307)) := by
  have hrepLe : ∀ i, (ws7WordRep307 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap307 (ws7WordRep307 i) = ws7WordCap307 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap307, ws7WordRep307, ws7WordP307, ws7WordQ307]
  have hall := caps_of_representatives ws7WordRep307 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word307Weak
  intro i
  simpa [ws7WordCap307, ws7WordP307, ws7WordQ307] using hall i

noncomputable def ws7WordCap308 (i : Fin 7) : ℝ :=
  (ws7WordP308 i : ℝ) / (ws7WordQ308 i : ℝ)

def ws7WordRep308 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word308WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep308 i) ≤ ws7WordCap308 (ws7WordRep308 i)) :
    WeakValidRates r
      (periodic ws7Word308.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word308)) := by
  have hrepLe : ∀ i, (ws7WordRep308 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap308 (ws7WordRep308 i) = ws7WordCap308 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap308, ws7WordRep308, ws7WordP308, ws7WordQ308]
  have hall := caps_of_representatives ws7WordRep308 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word308Weak
  intro i
  simpa [ws7WordCap308, ws7WordP308, ws7WordQ308] using hall i

noncomputable def ws7WordCap309 (i : Fin 7) : ℝ :=
  (ws7WordP309 i : ℝ) / (ws7WordQ309 i : ℝ)

def ws7WordRep309 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word309WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep309 i) ≤ ws7WordCap309 (ws7WordRep309 i)) :
    WeakValidRates r
      (periodic ws7Word309.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word309)) := by
  have hrepLe : ∀ i, (ws7WordRep309 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap309 (ws7WordRep309 i) = ws7WordCap309 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap309, ws7WordRep309, ws7WordP309, ws7WordQ309]
  have hall := caps_of_representatives ws7WordRep309 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word309Weak
  intro i
  simpa [ws7WordCap309, ws7WordP309, ws7WordQ309] using hall i

noncomputable def ws7WordCap310 (i : Fin 7) : ℝ :=
  (ws7WordP310 i : ℝ) / (ws7WordQ310 i : ℝ)

def ws7WordRep310 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word310WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep310 i) ≤ ws7WordCap310 (ws7WordRep310 i)) :
    WeakValidRates r
      (periodic ws7Word310.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word310)) := by
  have hrepLe : ∀ i, (ws7WordRep310 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap310 (ws7WordRep310 i) = ws7WordCap310 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap310, ws7WordRep310, ws7WordP310, ws7WordQ310]
  have hall := caps_of_representatives ws7WordRep310 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word310Weak
  intro i
  simpa [ws7WordCap310, ws7WordP310, ws7WordQ310] using hall i

noncomputable def ws7WordCap311 (i : Fin 7) : ℝ :=
  (ws7WordP311 i : ℝ) / (ws7WordQ311 i : ℝ)

def ws7WordRep311 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

theorem ws7Word311WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep311 i) ≤ ws7WordCap311 (ws7WordRep311 i)) :
    WeakValidRates r
      (periodic ws7Word311.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word311)) := by
  have hrepLe : ∀ i, (ws7WordRep311 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap311 (ws7WordRep311 i) = ws7WordCap311 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap311, ws7WordRep311, ws7WordP311, ws7WordQ311]
  have hall := caps_of_representatives ws7WordRep311 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word311Weak
  intro i
  simpa [ws7WordCap311, ws7WordP311, ws7WordQ311] using hall i

noncomputable def ws7WordCap312 (i : Fin 7) : ℝ :=
  (ws7WordP312 i : ℝ) / (ws7WordQ312 i : ℝ)

def ws7WordRep312 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

theorem ws7Word312WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep312 i) ≤ ws7WordCap312 (ws7WordRep312 i)) :
    WeakValidRates r
      (periodic ws7Word312.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word312)) := by
  have hrepLe : ∀ i, (ws7WordRep312 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap312 (ws7WordRep312 i) = ws7WordCap312 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap312, ws7WordRep312, ws7WordP312, ws7WordQ312]
  have hall := caps_of_representatives ws7WordRep312 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word312Weak
  intro i
  simpa [ws7WordCap312, ws7WordP312, ws7WordQ312] using hall i

noncomputable def ws7WordCap313 (i : Fin 7) : ℝ :=
  (ws7WordP313 i : ℝ) / (ws7WordQ313 i : ℝ)

def ws7WordRep313 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word313WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep313 i) ≤ ws7WordCap313 (ws7WordRep313 i)) :
    WeakValidRates r
      (periodic ws7Word313.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word313)) := by
  have hrepLe : ∀ i, (ws7WordRep313 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap313 (ws7WordRep313 i) = ws7WordCap313 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap313, ws7WordRep313, ws7WordP313, ws7WordQ313]
  have hall := caps_of_representatives ws7WordRep313 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word313Weak
  intro i
  simpa [ws7WordCap313, ws7WordP313, ws7WordQ313] using hall i

noncomputable def ws7WordCap314 (i : Fin 7) : ℝ :=
  (ws7WordP314 i : ℝ) / (ws7WordQ314 i : ℝ)

def ws7WordRep314 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word314WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep314 i) ≤ ws7WordCap314 (ws7WordRep314 i)) :
    WeakValidRates r
      (periodic ws7Word314.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word314)) := by
  have hrepLe : ∀ i, (ws7WordRep314 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap314 (ws7WordRep314 i) = ws7WordCap314 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap314, ws7WordRep314, ws7WordP314, ws7WordQ314]
  have hall := caps_of_representatives ws7WordRep314 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word314Weak
  intro i
  simpa [ws7WordCap314, ws7WordP314, ws7WordQ314] using hall i

noncomputable def ws7WordCap315 (i : Fin 7) : ℝ :=
  (ws7WordP315 i : ℝ) / (ws7WordQ315 i : ℝ)

def ws7WordRep315 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word315WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep315 i) ≤ ws7WordCap315 (ws7WordRep315 i)) :
    WeakValidRates r
      (periodic ws7Word315.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word315)) := by
  have hrepLe : ∀ i, (ws7WordRep315 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap315 (ws7WordRep315 i) = ws7WordCap315 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap315, ws7WordRep315, ws7WordP315, ws7WordQ315]
  have hall := caps_of_representatives ws7WordRep315 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word315Weak
  intro i
  simpa [ws7WordCap315, ws7WordP315, ws7WordQ315] using hall i

noncomputable def ws7WordCap316 (i : Fin 7) : ℝ :=
  (ws7WordP316 i : ℝ) / (ws7WordQ316 i : ℝ)

def ws7WordRep316 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 3
  | 6 => 3
  | _ => 0

theorem ws7Word316WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep316 i) ≤ ws7WordCap316 (ws7WordRep316 i)) :
    WeakValidRates r
      (periodic ws7Word316.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word316)) := by
  have hrepLe : ∀ i, (ws7WordRep316 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap316 (ws7WordRep316 i) = ws7WordCap316 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap316, ws7WordRep316, ws7WordP316, ws7WordQ316]
  have hall := caps_of_representatives ws7WordRep316 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word316Weak
  intro i
  simpa [ws7WordCap316, ws7WordP316, ws7WordQ316] using hall i

noncomputable def ws7WordCap317 (i : Fin 7) : ℝ :=
  (ws7WordP317 i : ℝ) / (ws7WordQ317 i : ℝ)

def ws7WordRep317 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

theorem ws7Word317WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep317 i) ≤ ws7WordCap317 (ws7WordRep317 i)) :
    WeakValidRates r
      (periodic ws7Word317.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word317)) := by
  have hrepLe : ∀ i, (ws7WordRep317 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap317 (ws7WordRep317 i) = ws7WordCap317 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap317, ws7WordRep317, ws7WordP317, ws7WordQ317]
  have hall := caps_of_representatives ws7WordRep317 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word317Weak
  intro i
  simpa [ws7WordCap317, ws7WordP317, ws7WordQ317] using hall i

noncomputable def ws7WordCap318 (i : Fin 7) : ℝ :=
  (ws7WordP318 i : ℝ) / (ws7WordQ318 i : ℝ)

def ws7WordRep318 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

theorem ws7Word318WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep318 i) ≤ ws7WordCap318 (ws7WordRep318 i)) :
    WeakValidRates r
      (periodic ws7Word318.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word318)) := by
  have hrepLe : ∀ i, (ws7WordRep318 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap318 (ws7WordRep318 i) = ws7WordCap318 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap318, ws7WordRep318, ws7WordP318, ws7WordQ318]
  have hall := caps_of_representatives ws7WordRep318 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word318Weak
  intro i
  simpa [ws7WordCap318, ws7WordP318, ws7WordQ318] using hall i

noncomputable def ws7WordCap319 (i : Fin 7) : ℝ :=
  (ws7WordP319 i : ℝ) / (ws7WordQ319 i : ℝ)

def ws7WordRep319 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word319WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep319 i) ≤ ws7WordCap319 (ws7WordRep319 i)) :
    WeakValidRates r
      (periodic ws7Word319.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word319)) := by
  have hrepLe : ∀ i, (ws7WordRep319 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap319 (ws7WordRep319 i) = ws7WordCap319 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap319, ws7WordRep319, ws7WordP319, ws7WordQ319]
  have hall := caps_of_representatives ws7WordRep319 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word319Weak
  intro i
  simpa [ws7WordCap319, ws7WordP319, ws7WordQ319] using hall i

noncomputable def ws7WordCap320 (i : Fin 7) : ℝ :=
  (ws7WordP320 i : ℝ) / (ws7WordQ320 i : ℝ)

def ws7WordRep320 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word320WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep320 i) ≤ ws7WordCap320 (ws7WordRep320 i)) :
    WeakValidRates r
      (periodic ws7Word320.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word320)) := by
  have hrepLe : ∀ i, (ws7WordRep320 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap320 (ws7WordRep320 i) = ws7WordCap320 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap320, ws7WordRep320, ws7WordP320, ws7WordQ320]
  have hall := caps_of_representatives ws7WordRep320 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word320Weak
  intro i
  simpa [ws7WordCap320, ws7WordP320, ws7WordQ320] using hall i

noncomputable def ws7WordCap321 (i : Fin 7) : ℝ :=
  (ws7WordP321 i : ℝ) / (ws7WordQ321 i : ℝ)

def ws7WordRep321 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word321WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep321 i) ≤ ws7WordCap321 (ws7WordRep321 i)) :
    WeakValidRates r
      (periodic ws7Word321.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word321)) := by
  have hrepLe : ∀ i, (ws7WordRep321 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap321 (ws7WordRep321 i) = ws7WordCap321 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap321, ws7WordRep321, ws7WordP321, ws7WordQ321]
  have hall := caps_of_representatives ws7WordRep321 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word321Weak
  intro i
  simpa [ws7WordCap321, ws7WordP321, ws7WordQ321] using hall i

noncomputable def ws7WordCap322 (i : Fin 7) : ℝ :=
  (ws7WordP322 i : ℝ) / (ws7WordQ322 i : ℝ)

def ws7WordRep322 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

theorem ws7Word322WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep322 i) ≤ ws7WordCap322 (ws7WordRep322 i)) :
    WeakValidRates r
      (periodic ws7Word322.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word322)) := by
  have hrepLe : ∀ i, (ws7WordRep322 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap322 (ws7WordRep322 i) = ws7WordCap322 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap322, ws7WordRep322, ws7WordP322, ws7WordQ322]
  have hall := caps_of_representatives ws7WordRep322 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word322Weak
  intro i
  simpa [ws7WordCap322, ws7WordP322, ws7WordQ322] using hall i

noncomputable def ws7WordCap323 (i : Fin 7) : ℝ :=
  (ws7WordP323 i : ℝ) / (ws7WordQ323 i : ℝ)

def ws7WordRep323 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 3
  | 6 => 6
  | _ => 0

theorem ws7Word323WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep323 i) ≤ ws7WordCap323 (ws7WordRep323 i)) :
    WeakValidRates r
      (periodic ws7Word323.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word323)) := by
  have hrepLe : ∀ i, (ws7WordRep323 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap323 (ws7WordRep323 i) = ws7WordCap323 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap323, ws7WordRep323, ws7WordP323, ws7WordQ323]
  have hall := caps_of_representatives ws7WordRep323 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word323Weak
  intro i
  simpa [ws7WordCap323, ws7WordP323, ws7WordQ323] using hall i

noncomputable def ws7WordCap324 (i : Fin 7) : ℝ :=
  (ws7WordP324 i : ℝ) / (ws7WordQ324 i : ℝ)

def ws7WordRep324 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word324WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep324 i) ≤ ws7WordCap324 (ws7WordRep324 i)) :
    WeakValidRates r
      (periodic ws7Word324.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word324)) := by
  have hrepLe : ∀ i, (ws7WordRep324 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap324 (ws7WordRep324 i) = ws7WordCap324 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap324, ws7WordRep324, ws7WordP324, ws7WordQ324]
  have hall := caps_of_representatives ws7WordRep324 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word324Weak
  intro i
  simpa [ws7WordCap324, ws7WordP324, ws7WordQ324] using hall i

noncomputable def ws7WordCap325 (i : Fin 7) : ℝ :=
  (ws7WordP325 i : ℝ) / (ws7WordQ325 i : ℝ)

def ws7WordRep325 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word325WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep325 i) ≤ ws7WordCap325 (ws7WordRep325 i)) :
    WeakValidRates r
      (periodic ws7Word325.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word325)) := by
  have hrepLe : ∀ i, (ws7WordRep325 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap325 (ws7WordRep325 i) = ws7WordCap325 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap325, ws7WordRep325, ws7WordP325, ws7WordQ325]
  have hall := caps_of_representatives ws7WordRep325 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word325Weak
  intro i
  simpa [ws7WordCap325, ws7WordP325, ws7WordQ325] using hall i

noncomputable def ws7WordCap326 (i : Fin 7) : ℝ :=
  (ws7WordP326 i : ℝ) / (ws7WordQ326 i : ℝ)

def ws7WordRep326 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word326WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep326 i) ≤ ws7WordCap326 (ws7WordRep326 i)) :
    WeakValidRates r
      (periodic ws7Word326.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word326)) := by
  have hrepLe : ∀ i, (ws7WordRep326 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap326 (ws7WordRep326 i) = ws7WordCap326 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap326, ws7WordRep326, ws7WordP326, ws7WordQ326]
  have hall := caps_of_representatives ws7WordRep326 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word326Weak
  intro i
  simpa [ws7WordCap326, ws7WordP326, ws7WordQ326] using hall i

noncomputable def ws7WordCap327 (i : Fin 7) : ℝ :=
  (ws7WordP327 i : ℝ) / (ws7WordQ327 i : ℝ)

def ws7WordRep327 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 6
  | _ => 0

theorem ws7Word327WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep327 i) ≤ ws7WordCap327 (ws7WordRep327 i)) :
    WeakValidRates r
      (periodic ws7Word327.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word327)) := by
  have hrepLe : ∀ i, (ws7WordRep327 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap327 (ws7WordRep327 i) = ws7WordCap327 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap327, ws7WordRep327, ws7WordP327, ws7WordQ327]
  have hall := caps_of_representatives ws7WordRep327 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word327Weak
  intro i
  simpa [ws7WordCap327, ws7WordP327, ws7WordQ327] using hall i

noncomputable def ws7WordCap328 (i : Fin 7) : ℝ :=
  (ws7WordP328 i : ℝ) / (ws7WordQ328 i : ℝ)

def ws7WordRep328 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word328WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep328 i) ≤ ws7WordCap328 (ws7WordRep328 i)) :
    WeakValidRates r
      (periodic ws7Word328.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word328)) := by
  have hrepLe : ∀ i, (ws7WordRep328 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap328 (ws7WordRep328 i) = ws7WordCap328 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap328, ws7WordRep328, ws7WordP328, ws7WordQ328]
  have hall := caps_of_representatives ws7WordRep328 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word328Weak
  intro i
  simpa [ws7WordCap328, ws7WordP328, ws7WordQ328] using hall i

noncomputable def ws7WordCap329 (i : Fin 7) : ℝ :=
  (ws7WordP329 i : ℝ) / (ws7WordQ329 i : ℝ)

def ws7WordRep329 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 6
  | _ => 0

theorem ws7Word329WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep329 i) ≤ ws7WordCap329 (ws7WordRep329 i)) :
    WeakValidRates r
      (periodic ws7Word329.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word329)) := by
  have hrepLe : ∀ i, (ws7WordRep329 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap329 (ws7WordRep329 i) = ws7WordCap329 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap329, ws7WordRep329, ws7WordP329, ws7WordQ329]
  have hall := caps_of_representatives ws7WordRep329 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word329Weak
  intro i
  simpa [ws7WordCap329, ws7WordP329, ws7WordQ329] using hall i

noncomputable def ws7WordCap330 (i : Fin 7) : ℝ :=
  (ws7WordP330 i : ℝ) / (ws7WordQ330 i : ℝ)

def ws7WordRep330 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word330WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep330 i) ≤ ws7WordCap330 (ws7WordRep330 i)) :
    WeakValidRates r
      (periodic ws7Word330.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word330)) := by
  have hrepLe : ∀ i, (ws7WordRep330 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap330 (ws7WordRep330 i) = ws7WordCap330 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap330, ws7WordRep330, ws7WordP330, ws7WordQ330]
  have hall := caps_of_representatives ws7WordRep330 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word330Weak
  intro i
  simpa [ws7WordCap330, ws7WordP330, ws7WordQ330] using hall i

noncomputable def ws7WordCap331 (i : Fin 7) : ℝ :=
  (ws7WordP331 i : ℝ) / (ws7WordQ331 i : ℝ)

def ws7WordRep331 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

theorem ws7Word331WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep331 i) ≤ ws7WordCap331 (ws7WordRep331 i)) :
    WeakValidRates r
      (periodic ws7Word331.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word331)) := by
  have hrepLe : ∀ i, (ws7WordRep331 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap331 (ws7WordRep331 i) = ws7WordCap331 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap331, ws7WordRep331, ws7WordP331, ws7WordQ331]
  have hall := caps_of_representatives ws7WordRep331 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word331Weak
  intro i
  simpa [ws7WordCap331, ws7WordP331, ws7WordQ331] using hall i

noncomputable def ws7WordCap332 (i : Fin 7) : ℝ :=
  (ws7WordP332 i : ℝ) / (ws7WordQ332 i : ℝ)

def ws7WordRep332 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word332WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep332 i) ≤ ws7WordCap332 (ws7WordRep332 i)) :
    WeakValidRates r
      (periodic ws7Word332.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word332)) := by
  have hrepLe : ∀ i, (ws7WordRep332 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap332 (ws7WordRep332 i) = ws7WordCap332 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap332, ws7WordRep332, ws7WordP332, ws7WordQ332]
  have hall := caps_of_representatives ws7WordRep332 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word332Weak
  intro i
  simpa [ws7WordCap332, ws7WordP332, ws7WordQ332] using hall i

noncomputable def ws7WordCap333 (i : Fin 7) : ℝ :=
  (ws7WordP333 i : ℝ) / (ws7WordQ333 i : ℝ)

def ws7WordRep333 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word333WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep333 i) ≤ ws7WordCap333 (ws7WordRep333 i)) :
    WeakValidRates r
      (periodic ws7Word333.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word333)) := by
  have hrepLe : ∀ i, (ws7WordRep333 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap333 (ws7WordRep333 i) = ws7WordCap333 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap333, ws7WordRep333, ws7WordP333, ws7WordQ333]
  have hall := caps_of_representatives ws7WordRep333 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word333Weak
  intro i
  simpa [ws7WordCap333, ws7WordP333, ws7WordQ333] using hall i

noncomputable def ws7WordCap334 (i : Fin 7) : ℝ :=
  (ws7WordP334 i : ℝ) / (ws7WordQ334 i : ℝ)

def ws7WordRep334 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word334WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep334 i) ≤ ws7WordCap334 (ws7WordRep334 i)) :
    WeakValidRates r
      (periodic ws7Word334.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word334)) := by
  have hrepLe : ∀ i, (ws7WordRep334 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap334 (ws7WordRep334 i) = ws7WordCap334 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap334, ws7WordRep334, ws7WordP334, ws7WordQ334]
  have hall := caps_of_representatives ws7WordRep334 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word334Weak
  intro i
  simpa [ws7WordCap334, ws7WordP334, ws7WordQ334] using hall i

noncomputable def ws7WordCap335 (i : Fin 7) : ℝ :=
  (ws7WordP335 i : ℝ) / (ws7WordQ335 i : ℝ)

def ws7WordRep335 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word335WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep335 i) ≤ ws7WordCap335 (ws7WordRep335 i)) :
    WeakValidRates r
      (periodic ws7Word335.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word335)) := by
  have hrepLe : ∀ i, (ws7WordRep335 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap335 (ws7WordRep335 i) = ws7WordCap335 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap335, ws7WordRep335, ws7WordP335, ws7WordQ335]
  have hall := caps_of_representatives ws7WordRep335 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word335Weak
  intro i
  simpa [ws7WordCap335, ws7WordP335, ws7WordQ335] using hall i

noncomputable def ws7WordCap336 (i : Fin 7) : ℝ :=
  (ws7WordP336 i : ℝ) / (ws7WordQ336 i : ℝ)

def ws7WordRep336 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word336WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep336 i) ≤ ws7WordCap336 (ws7WordRep336 i)) :
    WeakValidRates r
      (periodic ws7Word336.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word336)) := by
  have hrepLe : ∀ i, (ws7WordRep336 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap336 (ws7WordRep336 i) = ws7WordCap336 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap336, ws7WordRep336, ws7WordP336, ws7WordQ336]
  have hall := caps_of_representatives ws7WordRep336 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word336Weak
  intro i
  simpa [ws7WordCap336, ws7WordP336, ws7WordQ336] using hall i

noncomputable def ws7WordCap337 (i : Fin 7) : ℝ :=
  (ws7WordP337 i : ℝ) / (ws7WordQ337 i : ℝ)

def ws7WordRep337 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word337WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep337 i) ≤ ws7WordCap337 (ws7WordRep337 i)) :
    WeakValidRates r
      (periodic ws7Word337.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word337)) := by
  have hrepLe : ∀ i, (ws7WordRep337 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap337 (ws7WordRep337 i) = ws7WordCap337 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap337, ws7WordRep337, ws7WordP337, ws7WordQ337]
  have hall := caps_of_representatives ws7WordRep337 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word337Weak
  intro i
  simpa [ws7WordCap337, ws7WordP337, ws7WordQ337] using hall i

noncomputable def ws7WordCap338 (i : Fin 7) : ℝ :=
  (ws7WordP338 i : ℝ) / (ws7WordQ338 i : ℝ)

def ws7WordRep338 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word338WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep338 i) ≤ ws7WordCap338 (ws7WordRep338 i)) :
    WeakValidRates r
      (periodic ws7Word338.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word338)) := by
  have hrepLe : ∀ i, (ws7WordRep338 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap338 (ws7WordRep338 i) = ws7WordCap338 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap338, ws7WordRep338, ws7WordP338, ws7WordQ338]
  have hall := caps_of_representatives ws7WordRep338 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word338Weak
  intro i
  simpa [ws7WordCap338, ws7WordP338, ws7WordQ338] using hall i

noncomputable def ws7WordCap339 (i : Fin 7) : ℝ :=
  (ws7WordP339 i : ℝ) / (ws7WordQ339 i : ℝ)

def ws7WordRep339 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word339WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep339 i) ≤ ws7WordCap339 (ws7WordRep339 i)) :
    WeakValidRates r
      (periodic ws7Word339.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word339)) := by
  have hrepLe : ∀ i, (ws7WordRep339 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap339 (ws7WordRep339 i) = ws7WordCap339 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap339, ws7WordRep339, ws7WordP339, ws7WordQ339]
  have hall := caps_of_representatives ws7WordRep339 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word339Weak
  intro i
  simpa [ws7WordCap339, ws7WordP339, ws7WordQ339] using hall i

noncomputable def ws7WordCap340 (i : Fin 7) : ℝ :=
  (ws7WordP340 i : ℝ) / (ws7WordQ340 i : ℝ)

def ws7WordRep340 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word340WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep340 i) ≤ ws7WordCap340 (ws7WordRep340 i)) :
    WeakValidRates r
      (periodic ws7Word340.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word340)) := by
  have hrepLe : ∀ i, (ws7WordRep340 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap340 (ws7WordRep340 i) = ws7WordCap340 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap340, ws7WordRep340, ws7WordP340, ws7WordQ340]
  have hall := caps_of_representatives ws7WordRep340 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word340Weak
  intro i
  simpa [ws7WordCap340, ws7WordP340, ws7WordQ340] using hall i

noncomputable def ws7WordCap341 (i : Fin 7) : ℝ :=
  (ws7WordP341 i : ℝ) / (ws7WordQ341 i : ℝ)

def ws7WordRep341 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word341WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep341 i) ≤ ws7WordCap341 (ws7WordRep341 i)) :
    WeakValidRates r
      (periodic ws7Word341.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word341)) := by
  have hrepLe : ∀ i, (ws7WordRep341 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap341 (ws7WordRep341 i) = ws7WordCap341 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap341, ws7WordRep341, ws7WordP341, ws7WordQ341]
  have hall := caps_of_representatives ws7WordRep341 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word341Weak
  intro i
  simpa [ws7WordCap341, ws7WordP341, ws7WordQ341] using hall i

noncomputable def ws7WordCap342 (i : Fin 7) : ℝ :=
  (ws7WordP342 i : ℝ) / (ws7WordQ342 i : ℝ)

def ws7WordRep342 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word342WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep342 i) ≤ ws7WordCap342 (ws7WordRep342 i)) :
    WeakValidRates r
      (periodic ws7Word342.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word342)) := by
  have hrepLe : ∀ i, (ws7WordRep342 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap342 (ws7WordRep342 i) = ws7WordCap342 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap342, ws7WordRep342, ws7WordP342, ws7WordQ342]
  have hall := caps_of_representatives ws7WordRep342 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word342Weak
  intro i
  simpa [ws7WordCap342, ws7WordP342, ws7WordQ342] using hall i

noncomputable def ws7WordCap343 (i : Fin 7) : ℝ :=
  (ws7WordP343 i : ℝ) / (ws7WordQ343 i : ℝ)

def ws7WordRep343 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

theorem ws7Word343WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep343 i) ≤ ws7WordCap343 (ws7WordRep343 i)) :
    WeakValidRates r
      (periodic ws7Word343.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word343)) := by
  have hrepLe : ∀ i, (ws7WordRep343 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap343 (ws7WordRep343 i) = ws7WordCap343 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap343, ws7WordRep343, ws7WordP343, ws7WordQ343]
  have hall := caps_of_representatives ws7WordRep343 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word343Weak
  intro i
  simpa [ws7WordCap343, ws7WordP343, ws7WordQ343] using hall i

noncomputable def ws7WordCap344 (i : Fin 7) : ℝ :=
  (ws7WordP344 i : ℝ) / (ws7WordQ344 i : ℝ)

def ws7WordRep344 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word344WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep344 i) ≤ ws7WordCap344 (ws7WordRep344 i)) :
    WeakValidRates r
      (periodic ws7Word344.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word344)) := by
  have hrepLe : ∀ i, (ws7WordRep344 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap344 (ws7WordRep344 i) = ws7WordCap344 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap344, ws7WordRep344, ws7WordP344, ws7WordQ344]
  have hall := caps_of_representatives ws7WordRep344 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word344Weak
  intro i
  simpa [ws7WordCap344, ws7WordP344, ws7WordQ344] using hall i

noncomputable def ws7WordCap345 (i : Fin 7) : ℝ :=
  (ws7WordP345 i : ℝ) / (ws7WordQ345 i : ℝ)

def ws7WordRep345 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word345WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep345 i) ≤ ws7WordCap345 (ws7WordRep345 i)) :
    WeakValidRates r
      (periodic ws7Word345.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word345)) := by
  have hrepLe : ∀ i, (ws7WordRep345 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap345 (ws7WordRep345 i) = ws7WordCap345 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap345, ws7WordRep345, ws7WordP345, ws7WordQ345]
  have hall := caps_of_representatives ws7WordRep345 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word345Weak
  intro i
  simpa [ws7WordCap345, ws7WordP345, ws7WordQ345] using hall i

noncomputable def ws7WordCap346 (i : Fin 7) : ℝ :=
  (ws7WordP346 i : ℝ) / (ws7WordQ346 i : ℝ)

def ws7WordRep346 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word346WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep346 i) ≤ ws7WordCap346 (ws7WordRep346 i)) :
    WeakValidRates r
      (periodic ws7Word346.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word346)) := by
  have hrepLe : ∀ i, (ws7WordRep346 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap346 (ws7WordRep346 i) = ws7WordCap346 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap346, ws7WordRep346, ws7WordP346, ws7WordQ346]
  have hall := caps_of_representatives ws7WordRep346 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word346Weak
  intro i
  simpa [ws7WordCap346, ws7WordP346, ws7WordQ346] using hall i

noncomputable def ws7WordCap347 (i : Fin 7) : ℝ :=
  (ws7WordP347 i : ℝ) / (ws7WordQ347 i : ℝ)

def ws7WordRep347 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word347WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep347 i) ≤ ws7WordCap347 (ws7WordRep347 i)) :
    WeakValidRates r
      (periodic ws7Word347.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word347)) := by
  have hrepLe : ∀ i, (ws7WordRep347 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap347 (ws7WordRep347 i) = ws7WordCap347 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap347, ws7WordRep347, ws7WordP347, ws7WordQ347]
  have hall := caps_of_representatives ws7WordRep347 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word347Weak
  intro i
  simpa [ws7WordCap347, ws7WordP347, ws7WordQ347] using hall i

noncomputable def ws7WordCap348 (i : Fin 7) : ℝ :=
  (ws7WordP348 i : ℝ) / (ws7WordQ348 i : ℝ)

def ws7WordRep348 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 3
  | 6 => 6
  | _ => 0

theorem ws7Word348WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep348 i) ≤ ws7WordCap348 (ws7WordRep348 i)) :
    WeakValidRates r
      (periodic ws7Word348.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word348)) := by
  have hrepLe : ∀ i, (ws7WordRep348 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap348 (ws7WordRep348 i) = ws7WordCap348 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap348, ws7WordRep348, ws7WordP348, ws7WordQ348]
  have hall := caps_of_representatives ws7WordRep348 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word348Weak
  intro i
  simpa [ws7WordCap348, ws7WordP348, ws7WordQ348] using hall i

noncomputable def ws7WordCap349 (i : Fin 7) : ℝ :=
  (ws7WordP349 i : ℝ) / (ws7WordQ349 i : ℝ)

def ws7WordRep349 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 6
  | _ => 0

theorem ws7Word349WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep349 i) ≤ ws7WordCap349 (ws7WordRep349 i)) :
    WeakValidRates r
      (periodic ws7Word349.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word349)) := by
  have hrepLe : ∀ i, (ws7WordRep349 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap349 (ws7WordRep349 i) = ws7WordCap349 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap349, ws7WordRep349, ws7WordP349, ws7WordQ349]
  have hall := caps_of_representatives ws7WordRep349 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word349Weak
  intro i
  simpa [ws7WordCap349, ws7WordP349, ws7WordQ349] using hall i

noncomputable def ws7WordCap350 (i : Fin 7) : ℝ :=
  (ws7WordP350 i : ℝ) / (ws7WordQ350 i : ℝ)

def ws7WordRep350 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word350WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep350 i) ≤ ws7WordCap350 (ws7WordRep350 i)) :
    WeakValidRates r
      (periodic ws7Word350.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word350)) := by
  have hrepLe : ∀ i, (ws7WordRep350 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap350 (ws7WordRep350 i) = ws7WordCap350 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap350, ws7WordRep350, ws7WordP350, ws7WordQ350]
  have hall := caps_of_representatives ws7WordRep350 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word350Weak
  intro i
  simpa [ws7WordCap350, ws7WordP350, ws7WordQ350] using hall i

noncomputable def ws7WordCap351 (i : Fin 7) : ℝ :=
  (ws7WordP351 i : ℝ) / (ws7WordQ351 i : ℝ)

def ws7WordRep351 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 6
  | _ => 0

theorem ws7Word351WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep351 i) ≤ ws7WordCap351 (ws7WordRep351 i)) :
    WeakValidRates r
      (periodic ws7Word351.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word351)) := by
  have hrepLe : ∀ i, (ws7WordRep351 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap351 (ws7WordRep351 i) = ws7WordCap351 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap351, ws7WordRep351, ws7WordP351, ws7WordQ351]
  have hall := caps_of_representatives ws7WordRep351 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word351Weak
  intro i
  simpa [ws7WordCap351, ws7WordP351, ws7WordQ351] using hall i

noncomputable def ws7WordCap352 (i : Fin 7) : ℝ :=
  (ws7WordP352 i : ℝ) / (ws7WordQ352 i : ℝ)

def ws7WordRep352 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word352WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep352 i) ≤ ws7WordCap352 (ws7WordRep352 i)) :
    WeakValidRates r
      (periodic ws7Word352.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word352)) := by
  have hrepLe : ∀ i, (ws7WordRep352 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap352 (ws7WordRep352 i) = ws7WordCap352 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap352, ws7WordRep352, ws7WordP352, ws7WordQ352]
  have hall := caps_of_representatives ws7WordRep352 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word352Weak
  intro i
  simpa [ws7WordCap352, ws7WordP352, ws7WordQ352] using hall i

noncomputable def ws7WordCap353 (i : Fin 7) : ℝ :=
  (ws7WordP353 i : ℝ) / (ws7WordQ353 i : ℝ)

def ws7WordRep353 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word353WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep353 i) ≤ ws7WordCap353 (ws7WordRep353 i)) :
    WeakValidRates r
      (periodic ws7Word353.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word353)) := by
  have hrepLe : ∀ i, (ws7WordRep353 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap353 (ws7WordRep353 i) = ws7WordCap353 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap353, ws7WordRep353, ws7WordP353, ws7WordQ353]
  have hall := caps_of_representatives ws7WordRep353 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word353Weak
  intro i
  simpa [ws7WordCap353, ws7WordP353, ws7WordQ353] using hall i

noncomputable def ws7WordCap354 (i : Fin 7) : ℝ :=
  (ws7WordP354 i : ℝ) / (ws7WordQ354 i : ℝ)

def ws7WordRep354 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 6
  | _ => 0

theorem ws7Word354WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep354 i) ≤ ws7WordCap354 (ws7WordRep354 i)) :
    WeakValidRates r
      (periodic ws7Word354.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word354)) := by
  have hrepLe : ∀ i, (ws7WordRep354 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap354 (ws7WordRep354 i) = ws7WordCap354 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap354, ws7WordRep354, ws7WordP354, ws7WordQ354]
  have hall := caps_of_representatives ws7WordRep354 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word354Weak
  intro i
  simpa [ws7WordCap354, ws7WordP354, ws7WordQ354] using hall i

noncomputable def ws7WordCap355 (i : Fin 7) : ℝ :=
  (ws7WordP355 i : ℝ) / (ws7WordQ355 i : ℝ)

def ws7WordRep355 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

theorem ws7Word355WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep355 i) ≤ ws7WordCap355 (ws7WordRep355 i)) :
    WeakValidRates r
      (periodic ws7Word355.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word355)) := by
  have hrepLe : ∀ i, (ws7WordRep355 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap355 (ws7WordRep355 i) = ws7WordCap355 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap355, ws7WordRep355, ws7WordP355, ws7WordQ355]
  have hall := caps_of_representatives ws7WordRep355 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word355Weak
  intro i
  simpa [ws7WordCap355, ws7WordP355, ws7WordQ355] using hall i

noncomputable def ws7WordCap356 (i : Fin 7) : ℝ :=
  (ws7WordP356 i : ℝ) / (ws7WordQ356 i : ℝ)

def ws7WordRep356 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word356WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep356 i) ≤ ws7WordCap356 (ws7WordRep356 i)) :
    WeakValidRates r
      (periodic ws7Word356.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word356)) := by
  have hrepLe : ∀ i, (ws7WordRep356 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap356 (ws7WordRep356 i) = ws7WordCap356 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap356, ws7WordRep356, ws7WordP356, ws7WordQ356]
  have hall := caps_of_representatives ws7WordRep356 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word356Weak
  intro i
  simpa [ws7WordCap356, ws7WordP356, ws7WordQ356] using hall i

noncomputable def ws7WordCap357 (i : Fin 7) : ℝ :=
  (ws7WordP357 i : ℝ) / (ws7WordQ357 i : ℝ)

def ws7WordRep357 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word357WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep357 i) ≤ ws7WordCap357 (ws7WordRep357 i)) :
    WeakValidRates r
      (periodic ws7Word357.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word357)) := by
  have hrepLe : ∀ i, (ws7WordRep357 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap357 (ws7WordRep357 i) = ws7WordCap357 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap357, ws7WordRep357, ws7WordP357, ws7WordQ357]
  have hall := caps_of_representatives ws7WordRep357 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word357Weak
  intro i
  simpa [ws7WordCap357, ws7WordP357, ws7WordQ357] using hall i

noncomputable def ws7WordCap358 (i : Fin 7) : ℝ :=
  (ws7WordP358 i : ℝ) / (ws7WordQ358 i : ℝ)

def ws7WordRep358 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 6
  | _ => 0

theorem ws7Word358WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep358 i) ≤ ws7WordCap358 (ws7WordRep358 i)) :
    WeakValidRates r
      (periodic ws7Word358.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word358)) := by
  have hrepLe : ∀ i, (ws7WordRep358 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap358 (ws7WordRep358 i) = ws7WordCap358 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap358, ws7WordRep358, ws7WordP358, ws7WordQ358]
  have hall := caps_of_representatives ws7WordRep358 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word358Weak
  intro i
  simpa [ws7WordCap358, ws7WordP358, ws7WordQ358] using hall i

noncomputable def ws7WordCap359 (i : Fin 7) : ℝ :=
  (ws7WordP359 i : ℝ) / (ws7WordQ359 i : ℝ)

def ws7WordRep359 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

theorem ws7Word359WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep359 i) ≤ ws7WordCap359 (ws7WordRep359 i)) :
    WeakValidRates r
      (periodic ws7Word359.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word359)) := by
  have hrepLe : ∀ i, (ws7WordRep359 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap359 (ws7WordRep359 i) = ws7WordCap359 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap359, ws7WordRep359, ws7WordP359, ws7WordQ359]
  have hall := caps_of_representatives ws7WordRep359 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word359Weak
  intro i
  simpa [ws7WordCap359, ws7WordP359, ws7WordQ359] using hall i

noncomputable def ws7WordCap360 (i : Fin 7) : ℝ :=
  (ws7WordP360 i : ℝ) / (ws7WordQ360 i : ℝ)

def ws7WordRep360 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 6
  | _ => 0

theorem ws7Word360WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep360 i) ≤ ws7WordCap360 (ws7WordRep360 i)) :
    WeakValidRates r
      (periodic ws7Word360.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word360)) := by
  have hrepLe : ∀ i, (ws7WordRep360 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap360 (ws7WordRep360 i) = ws7WordCap360 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap360, ws7WordRep360, ws7WordP360, ws7WordQ360]
  have hall := caps_of_representatives ws7WordRep360 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word360Weak
  intro i
  simpa [ws7WordCap360, ws7WordP360, ws7WordQ360] using hall i

noncomputable def ws7WordCap361 (i : Fin 7) : ℝ :=
  (ws7WordP361 i : ℝ) / (ws7WordQ361 i : ℝ)

def ws7WordRep361 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word361WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep361 i) ≤ ws7WordCap361 (ws7WordRep361 i)) :
    WeakValidRates r
      (periodic ws7Word361.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word361)) := by
  have hrepLe : ∀ i, (ws7WordRep361 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap361 (ws7WordRep361 i) = ws7WordCap361 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap361, ws7WordRep361, ws7WordP361, ws7WordQ361]
  have hall := caps_of_representatives ws7WordRep361 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word361Weak
  intro i
  simpa [ws7WordCap361, ws7WordP361, ws7WordQ361] using hall i

noncomputable def ws7WordCap362 (i : Fin 7) : ℝ :=
  (ws7WordP362 i : ℝ) / (ws7WordQ362 i : ℝ)

def ws7WordRep362 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word362WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep362 i) ≤ ws7WordCap362 (ws7WordRep362 i)) :
    WeakValidRates r
      (periodic ws7Word362.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word362)) := by
  have hrepLe : ∀ i, (ws7WordRep362 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap362 (ws7WordRep362 i) = ws7WordCap362 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap362, ws7WordRep362, ws7WordP362, ws7WordQ362]
  have hall := caps_of_representatives ws7WordRep362 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word362Weak
  intro i
  simpa [ws7WordCap362, ws7WordP362, ws7WordQ362] using hall i

noncomputable def ws7WordCap363 (i : Fin 7) : ℝ :=
  (ws7WordP363 i : ℝ) / (ws7WordQ363 i : ℝ)

def ws7WordRep363 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 3
  | 6 => 6
  | _ => 0

theorem ws7Word363WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep363 i) ≤ ws7WordCap363 (ws7WordRep363 i)) :
    WeakValidRates r
      (periodic ws7Word363.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word363)) := by
  have hrepLe : ∀ i, (ws7WordRep363 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap363 (ws7WordRep363 i) = ws7WordCap363 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap363, ws7WordRep363, ws7WordP363, ws7WordQ363]
  have hall := caps_of_representatives ws7WordRep363 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word363Weak
  intro i
  simpa [ws7WordCap363, ws7WordP363, ws7WordQ363] using hall i

noncomputable def ws7WordCap364 (i : Fin 7) : ℝ :=
  (ws7WordP364 i : ℝ) / (ws7WordQ364 i : ℝ)

def ws7WordRep364 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

theorem ws7Word364WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep364 i) ≤ ws7WordCap364 (ws7WordRep364 i)) :
    WeakValidRates r
      (periodic ws7Word364.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word364)) := by
  have hrepLe : ∀ i, (ws7WordRep364 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap364 (ws7WordRep364 i) = ws7WordCap364 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap364, ws7WordRep364, ws7WordP364, ws7WordQ364]
  have hall := caps_of_representatives ws7WordRep364 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word364Weak
  intro i
  simpa [ws7WordCap364, ws7WordP364, ws7WordQ364] using hall i

noncomputable def ws7WordCap365 (i : Fin 7) : ℝ :=
  (ws7WordP365 i : ℝ) / (ws7WordQ365 i : ℝ)

def ws7WordRep365 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word365WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep365 i) ≤ ws7WordCap365 (ws7WordRep365 i)) :
    WeakValidRates r
      (periodic ws7Word365.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word365)) := by
  have hrepLe : ∀ i, (ws7WordRep365 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap365 (ws7WordRep365 i) = ws7WordCap365 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap365, ws7WordRep365, ws7WordP365, ws7WordQ365]
  have hall := caps_of_representatives ws7WordRep365 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word365Weak
  intro i
  simpa [ws7WordCap365, ws7WordP365, ws7WordQ365] using hall i

noncomputable def ws7WordCap366 (i : Fin 7) : ℝ :=
  (ws7WordP366 i : ℝ) / (ws7WordQ366 i : ℝ)

def ws7WordRep366 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 4
  | 5 => 4
  | 6 => 6
  | _ => 0

theorem ws7Word366WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep366 i) ≤ ws7WordCap366 (ws7WordRep366 i)) :
    WeakValidRates r
      (periodic ws7Word366.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word366)) := by
  have hrepLe : ∀ i, (ws7WordRep366 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap366 (ws7WordRep366 i) = ws7WordCap366 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap366, ws7WordRep366, ws7WordP366, ws7WordQ366]
  have hall := caps_of_representatives ws7WordRep366 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word366Weak
  intro i
  simpa [ws7WordCap366, ws7WordP366, ws7WordQ366] using hall i

noncomputable def ws7WordCap367 (i : Fin 7) : ℝ :=
  (ws7WordP367 i : ℝ) / (ws7WordQ367 i : ℝ)

def ws7WordRep367 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word367WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep367 i) ≤ ws7WordCap367 (ws7WordRep367 i)) :
    WeakValidRates r
      (periodic ws7Word367.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word367)) := by
  have hrepLe : ∀ i, (ws7WordRep367 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap367 (ws7WordRep367 i) = ws7WordCap367 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap367, ws7WordRep367, ws7WordP367, ws7WordQ367]
  have hall := caps_of_representatives ws7WordRep367 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word367Weak
  intro i
  simpa [ws7WordCap367, ws7WordP367, ws7WordQ367] using hall i

noncomputable def ws7WordCap368 (i : Fin 7) : ℝ :=
  (ws7WordP368 i : ℝ) / (ws7WordQ368 i : ℝ)

def ws7WordRep368 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word368WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep368 i) ≤ ws7WordCap368 (ws7WordRep368 i)) :
    WeakValidRates r
      (periodic ws7Word368.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word368)) := by
  have hrepLe : ∀ i, (ws7WordRep368 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap368 (ws7WordRep368 i) = ws7WordCap368 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap368, ws7WordRep368, ws7WordP368, ws7WordQ368]
  have hall := caps_of_representatives ws7WordRep368 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word368Weak
  intro i
  simpa [ws7WordCap368, ws7WordP368, ws7WordQ368] using hall i

noncomputable def ws7WordCap369 (i : Fin 7) : ℝ :=
  (ws7WordP369 i : ℝ) / (ws7WordQ369 i : ℝ)

def ws7WordRep369 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

theorem ws7Word369WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep369 i) ≤ ws7WordCap369 (ws7WordRep369 i)) :
    WeakValidRates r
      (periodic ws7Word369.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word369)) := by
  have hrepLe : ∀ i, (ws7WordRep369 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap369 (ws7WordRep369 i) = ws7WordCap369 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap369, ws7WordRep369, ws7WordP369, ws7WordQ369]
  have hall := caps_of_representatives ws7WordRep369 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word369Weak
  intro i
  simpa [ws7WordCap369, ws7WordP369, ws7WordQ369] using hall i

noncomputable def ws7WordCap370 (i : Fin 7) : ℝ :=
  (ws7WordP370 i : ℝ) / (ws7WordQ370 i : ℝ)

def ws7WordRep370 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 2
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word370WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep370 i) ≤ ws7WordCap370 (ws7WordRep370 i)) :
    WeakValidRates r
      (periodic ws7Word370.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word370)) := by
  have hrepLe : ∀ i, (ws7WordRep370 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap370 (ws7WordRep370 i) = ws7WordCap370 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap370, ws7WordRep370, ws7WordP370, ws7WordQ370]
  have hall := caps_of_representatives ws7WordRep370 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word370Weak
  intro i
  simpa [ws7WordCap370, ws7WordP370, ws7WordQ370] using hall i

noncomputable def ws7WordCap371 (i : Fin 7) : ℝ :=
  (ws7WordP371 i : ℝ) / (ws7WordQ371 i : ℝ)

def ws7WordRep371 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

theorem ws7Word371WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep371 i) ≤ ws7WordCap371 (ws7WordRep371 i)) :
    WeakValidRates r
      (periodic ws7Word371.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word371)) := by
  have hrepLe : ∀ i, (ws7WordRep371 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap371 (ws7WordRep371 i) = ws7WordCap371 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap371, ws7WordRep371, ws7WordP371, ws7WordQ371]
  have hall := caps_of_representatives ws7WordRep371 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word371Weak
  intro i
  simpa [ws7WordCap371, ws7WordP371, ws7WordQ371] using hall i

noncomputable def ws7WordCap372 (i : Fin 7) : ℝ :=
  (ws7WordP372 i : ℝ) / (ws7WordQ372 i : ℝ)

def ws7WordRep372 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | _ => 0

theorem ws7Word372WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep372 i) ≤ ws7WordCap372 (ws7WordRep372 i)) :
    WeakValidRates r
      (periodic ws7Word372.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word372)) := by
  have hrepLe : ∀ i, (ws7WordRep372 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap372 (ws7WordRep372 i) = ws7WordCap372 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap372, ws7WordRep372, ws7WordP372, ws7WordQ372]
  have hall := caps_of_representatives ws7WordRep372 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word372Weak
  intro i
  simpa [ws7WordCap372, ws7WordP372, ws7WordQ372] using hall i

noncomputable def ws7WordCap373 (i : Fin 7) : ℝ :=
  (ws7WordP373 i : ℝ) / (ws7WordQ373 i : ℝ)

def ws7WordRep373 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 0
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | _ => 0

theorem ws7Word373WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep373 i) ≤ ws7WordCap373 (ws7WordRep373 i)) :
    WeakValidRates r
      (periodic ws7Word373.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word373)) := by
  have hrepLe : ∀ i, (ws7WordRep373 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap373 (ws7WordRep373 i) = ws7WordCap373 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap373, ws7WordRep373, ws7WordP373, ws7WordQ373]
  have hall := caps_of_representatives ws7WordRep373 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word373Weak
  intro i
  simpa [ws7WordCap373, ws7WordP373, ws7WordQ373] using hall i

noncomputable def ws7WordCap374 (i : Fin 7) : ℝ :=
  (ws7WordP374 i : ℝ) / (ws7WordQ374 i : ℝ)

def ws7WordRep374 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 0
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 6
  | _ => 0

theorem ws7Word374WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep374 i) ≤ ws7WordCap374 (ws7WordRep374 i)) :
    WeakValidRates r
      (periodic ws7Word374.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word374)) := by
  have hrepLe : ∀ i, (ws7WordRep374 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap374 (ws7WordRep374 i) = ws7WordCap374 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap374, ws7WordRep374, ws7WordP374, ws7WordQ374]
  have hall := caps_of_representatives ws7WordRep374 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word374Weak
  intro i
  simpa [ws7WordCap374, ws7WordP374, ws7WordQ374] using hall i

noncomputable def ws7WordCap375 (i : Fin 7) : ℝ :=
  (ws7WordP375 i : ℝ) / (ws7WordQ375 i : ℝ)

def ws7WordRep375 : Fin 7 → Fin 7 :=
  fun i => match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 5
  | 6 => 6
  | _ => 0

theorem ws7Word375WeakOfRepresentatives (r : Fin 7 → ℝ)
    (horder : ∀ i k : Fin 7, i.val ≤ k.val → r k ≤ r i)
    (hfit : ∀ i, r (ws7WordRep375 i) ≤ ws7WordCap375 (ws7WordRep375 i)) :
    WeakValidRates r
      (periodic ws7Word375.length (List.length_pos_of_ne_nil (by decide))
        (listWord ws7Word375)) := by
  have hrepLe : ∀ i, (ws7WordRep375 i).val ≤ i.val := by
    intro i; fin_cases i <;> decide
  have hcapEq : ∀ i, ws7WordCap375 (ws7WordRep375 i) = ws7WordCap375 i := by
    intro i; fin_cases i <;> norm_num [ws7WordCap375, ws7WordRep375, ws7WordP375, ws7WordQ375]
  have hall := caps_of_representatives ws7WordRep375 hrepLe hcapEq horder hfit
  apply WeakValidRates.mono ws7Word375Weak
  intro i
  simpa [ws7WordCap375, ws7WordP375, ws7WordQ375] using hall i

end RealPinwheel.WeakSevenBandData
