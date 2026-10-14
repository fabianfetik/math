import Pinwheel.WeakSevenBandData.SourceFits
import Pinwheel.WeakSevenBandData.RateOrder
import Pinwheel.WeakSevenCyclicSources
import Pinwheel.WeakSeven
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Exact reduced-cap bridges for inherited marked-second profiles. -/

namespace RealPinwheel.WeakSevenBandData

def SecondSourceRepresentative (sid : Fin 15) : Fin 7 → Fin 7 :=
  match sid.val with
  | 4 => fun j => match j.val with
    | 0 => 0
    | 1 => 1
    | 2 => 2
    | 3 => 2
    | 4 => 2
    | 5 => 2
    | 6 => 2
    | _ => 2
  | 5 => fun j => match j.val with
    | 0 => 0
    | 1 => 1
    | 2 => 2
    | 3 => 3
    | 4 => 3
    | 5 => 3
    | 6 => 3
    | _ => 3
  | 6 => fun j => match j.val with
    | 0 => 0
    | 1 => 1
    | 2 => 2
    | 3 => 3
    | 4 => 3
    | 5 => 3
    | 6 => 3
    | _ => 3
  | 7 => fun j => match j.val with
    | 0 => 0
    | 1 => 1
    | 2 => 2
    | 3 => 3
    | 4 => 4
    | 5 => 4
    | 6 => 4
    | _ => 4
  | 8 => fun j => match j.val with
    | 0 => 0
    | 1 => 0
    | 2 => 2
    | 3 => 3
    | 4 => 3
    | 5 => 3
    | 6 => 3
    | _ => 3
  | 9 => fun j => match j.val with
    | 0 => 0
    | 1 => 1
    | 2 => 2
    | 3 => 3
    | 4 => 3
    | 5 => 3
    | 6 => 3
    | _ => 3
  | 10 => fun j => match j.val with
    | 0 => 0
    | 1 => 0
    | 2 => 2
    | 3 => 3
    | 4 => 3
    | 5 => 3
    | 6 => 3
    | _ => 3
  | 11 => fun j => match j.val with
    | 0 => 0
    | 1 => 0
    | 2 => 2
    | 3 => 3
    | 4 => 4
    | 5 => 4
    | 6 => 4
    | _ => 4
  | 12 => fun j => match j.val with
    | 0 => 0
    | 1 => 0
    | 2 => 2
    | 3 => 3
    | 4 => 4
    | 5 => 4
    | 6 => 4
    | _ => 4
  | 13 => fun j => match j.val with
    | 0 => 0
    | 1 => 0
    | 2 => 2
    | 3 => 3
    | 4 => 4
    | 5 => 4
    | 6 => 4
    | _ => 4
  | 14 => fun j => match j.val with
    | 0 => 0
    | 1 => 0
    | 2 => 2
    | 3 => 3
    | 4 => 4
    | 5 => 5
    | 6 => 5
    | _ => 5
  | _ => fun i => i

theorem secondSourceCapFitsAtRepresentatives (sid : Fin 15)
    (hsid : 4 ≤ sid.val) {h : Fin 6 → ℝ} {delta : ℝ}
    (hfit : SecondSourceFits sid h delta) :
    ∀ i, secondRankRates h delta (SecondSourceRepresentative sid i) ≤
      ws7SecondCycleCaps sid (SecondSourceRepresentative sid i) := by
  fin_cases sid
  · norm_num at hsid
  · norm_num at hsid
  · norm_num at hsid
  · norm_num at hsid
  · change (h 0 ≤ (162/689 : ℝ)) ∧ (((2 : ℝ) * (delta)) ≤ (146/689 : ℝ)) ∧ (h 1 ≤ (73/689 : ℝ)) at hfit
    rcases hfit with ⟨hc0, hc1, hc2⟩
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc1 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc2 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc2 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc2 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc2 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc2 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
  · change (h 0 ≤ (124660/542367 : ℝ)) ∧ (((2 : ℝ) * (delta)) ≤ (112258/542367 : ℝ)) ∧ (h 1 ≤ (59770/542367 : ℝ)) ∧ (h 2 ≤ (56129/542367 : ℝ)) at hfit
    rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc1 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc2 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc3 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc3 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc3 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc3 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
  · change (h 0 ≤ (10857200/47230299 : ℝ)) ∧ (((2 : ℝ) * (delta)) ≤ (9772466/47230299 : ℝ)) ∧ (h 1 ≤ (5389160/47230299 : ℝ)) ∧ (h 2 ≤ (4886233/47230299 : ℝ)) at hfit
    rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc1 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc2 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc3 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc3 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc3 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc3 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
  · change (h 0 ≤ (8316733826/36179666007 : ℝ)) ∧ (((2 : ℝ) * (delta)) ≤ (2495436562/12059888669 : ℝ)) ∧ (h 1 ≤ (1323923842/12059888669 : ℝ)) ∧ (h 2 ≤ (3879780526/36179666007 : ℝ)) ∧ (h 3 ≤ (1247718281/12059888669 : ℝ)) at hfit
    rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc1 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc2 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc3 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc4 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc4 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc4 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
  · change (h 0 ≤ (83/379 : ℝ)) ∧ (h 1 ≤ (47/379 : ℝ)) ∧ (h 2 ≤ (83/758 : ℝ)) at hfit
    rcases hfit with ⟨hc0, hc1, hc2⟩
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc0 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc1 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc2 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc2 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc2 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc2 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
  · change (h 0 ≤ (352893426530/1586876332767 : ℝ)) ∧ (((2 : ℝ) * (delta)) ≤ (1635980674/8055209811 : ℝ)) ∧ (h 1 ≤ (933539800/8055209811 : ℝ)) ∧ (h 2 ≤ (817990337/8055209811 : ℝ)) at hfit
    rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc1 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc2 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc3 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc3 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc3 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc3 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
  · change (h 0 ≤ (10339/47807 : ℝ)) ∧ (h 1 ≤ (6451/47807 : ℝ)) ∧ (h 2 ≤ (10339/95614 : ℝ)) at hfit
    rcases hfit with ⟨hc0, hc1, hc2⟩
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc0 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc1 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc2 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc2 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc2 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc2 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
  · change (h 0 ≤ (136053119/661424034 : ℝ)) ∧ (h 1 ≤ (84421559/661424034 : ℝ)) ∧ (h 2 ≤ (294532961/2645696136 : ℝ)) ∧ (h 3 ≤ (136053119/1322848068 : ℝ)) at hfit
    rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc0 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc1 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc2 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc3 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc3 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc3 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
  · change (h 0 ≤ (4318/20223 : ℝ)) ∧ (h 1 ≤ (2423/20223 : ℝ)) ∧ (h 2 ≤ (19109/161784 : ℝ)) ∧ (h 3 ≤ (2159/20223 : ℝ)) at hfit
    rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc0 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc1 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc2 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc3 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc3 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc3 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
  · change (h 0 ≤ (89368829179067/428956453720962 : ℝ)) ∧ (h 1 ≤ (53616655394587/428956453720962 : ℝ)) ∧ (h 2 ≤ (24915904083856/214478226860481 : ℝ)) ∧ (h 3 ≤ (89368829179067/857912907441924 : ℝ)) at hfit
    rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc0 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc1 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc2 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc3 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc3 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc3 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
  · change (h 0 ≤ (1926518/9004269 : ℝ)) ∧ (h 1 ≤ (1074905/9004269 : ℝ)) ∧ (h 2 ≤ (8475655/72034152 : ℝ)) ∧ (h 3 ≤ (344405/3001423 : ℝ)) ∧ (h 4 ≤ (963259/9004269 : ℝ)) at hfit
    rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc0 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc1 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc2 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc3 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc4 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
    · convert hc4 using 1
      · rfl
      · norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]

theorem secondSourceCapsOfFit (sid : Fin 15) (hsid : 4 ≤ sid.val)
    {h : Fin 6 → ℝ} {delta : ℝ}
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i)
    (hmarkL : 2 * delta ≤ h 0) (hmarkR : h 1 ≤ 2 * delta)
    (hfit : SecondSourceFits sid h delta) :
    ∀ i, secondRankRates h delta i ≤ ws7SecondCycleCaps sid i := by
  apply caps_of_representatives (SecondSourceRepresentative sid)
  · intro i; fin_cases sid <;> fin_cases i <;> decide
  · intro i; fin_cases sid <;> fin_cases i <;>
      norm_num [SecondSourceRepresentative, ws7SecondCycleCaps]
  · exact secondRankRates_order horder hmarkL hmarkR
  · exact secondSourceCapFitsAtRepresentatives sid hsid hfit

end WeakSevenBandData
