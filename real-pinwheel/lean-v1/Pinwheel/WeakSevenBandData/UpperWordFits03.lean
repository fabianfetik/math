import Pinwheel.WeakSevenBandData.UpperWordFits02
import Pinwheel.WeakSevenBandData.SourceFits
import Pinwheel.WeakSevenBandData.RateOrder
import Pinwheel.WeakSeven
import Mathlib.Tactic.FinCases

/-! Source-box adapters for literal weak words. -/

namespace RealPinwheel.WeakSevenBandData

theorem upperWordFitSchedule125 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨125, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 4 ≤ (5/44 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep207 i) ≤ ws7WordCap207 (ws7WordRep207 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep207, ws7WordCap207, ws7WordP207, ws7WordQ207]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep207, ws7WordCap207, ws7WordP207, ws7WordQ207]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep207, ws7WordCap207, ws7WordP207, ws7WordQ207]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep207, ws7WordCap207, ws7WordP207, ws7WordQ207]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep207, ws7WordCap207, ws7WordP207, ws7WordQ207]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep207, ws7WordCap207, ws7WordP207, ws7WordQ207]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep207, ws7WordCap207, ws7WordP207, ws7WordQ207]
  have hword := ws7Word207WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule126 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨126, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (5/33 : ℝ)) ∧ (h 1 ≤ (21/166 : ℝ)) ∧ (h 2 ≤ (5/41 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep351 i) ≤ ws7WordCap351 (ws7WordRep351 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep351, ws7WordCap351, ws7WordP351, ws7WordQ351]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep351, ws7WordCap351, ws7WordP351, ws7WordQ351]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep351, ws7WordCap351, ws7WordP351, ws7WordQ351]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep351, ws7WordCap351, ws7WordP351, ws7WordQ351]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep351, ws7WordCap351, ws7WordP351, ws7WordQ351]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep351, ws7WordCap351, ws7WordP351, ws7WordQ351]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep351, ws7WordCap351, ws7WordP351, ws7WordQ351]
  have hword := ws7Word351WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule127 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨127, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (12/95 : ℝ)) ∧ (h 2 ≤ (5/41 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (5/44 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep349 i) ≤ ws7WordCap349 (ws7WordRep349 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep349, ws7WordCap349, ws7WordP349, ws7WordQ349]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep349, ws7WordCap349, ws7WordP349, ws7WordQ349]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep349, ws7WordCap349, ws7WordP349, ws7WordQ349]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep349, ws7WordCap349, ws7WordP349, ws7WordQ349]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep349, ws7WordCap349, ws7WordP349, ws7WordQ349]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep349, ws7WordCap349, ws7WordP349, ws7WordQ349]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep349, ws7WordCap349, ws7WordP349, ws7WordQ349]
  have hword := ws7Word349WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule128 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨128, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (10/79 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep313 i) ≤ ws7WordCap313 (ws7WordRep313 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep313, ws7WordCap313, ws7WordP313, ws7WordQ313]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep313, ws7WordCap313, ws7WordP313, ws7WordQ313]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep313, ws7WordCap313, ws7WordP313, ws7WordQ313]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep313, ws7WordCap313, ws7WordP313, ws7WordQ313]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep313, ws7WordCap313, ws7WordP313, ws7WordQ313]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep313, ws7WordCap313, ws7WordP313, ws7WordQ313]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep313, ws7WordCap313, ws7WordP313, ws7WordQ313]
  have hword := ws7Word313WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule129 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨129, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (5/33 : ℝ)) ∧ (h 1 ≤ (5/38 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep212 i) ≤ ws7WordCap212 (ws7WordRep212 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep212, ws7WordCap212, ws7WordP212, ws7WordQ212]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep212, ws7WordCap212, ws7WordP212, ws7WordQ212]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep212, ws7WordCap212, ws7WordP212, ws7WordQ212]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep212, ws7WordCap212, ws7WordP212, ws7WordQ212]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep212, ws7WordCap212, ws7WordP212, ws7WordQ212]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep212, ws7WordCap212, ws7WordP212, ws7WordQ212]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep212, ws7WordCap212, ws7WordP212, ws7WordQ212]
  have hword := ws7Word212WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule130 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨130, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (10/67 : ℝ)) ∧ (h 1 ≤ (6/47 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (5/43 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep337 i) ≤ ws7WordCap337 (ws7WordRep337 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep337, ws7WordCap337, ws7WordP337, ws7WordQ337]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep337, ws7WordCap337, ws7WordP337, ws7WordQ337]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep337, ws7WordCap337, ws7WordP337, ws7WordQ337]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep337, ws7WordCap337, ws7WordP337, ws7WordQ337]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep337, ws7WordCap337, ws7WordP337, ws7WordQ337]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep337, ws7WordCap337, ws7WordP337, ws7WordQ337]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep337, ws7WordCap337, ws7WordP337, ws7WordQ337]
  have hword := ws7Word337WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule131 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨131, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (5/42 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep243 i) ≤ ws7WordCap243 (ws7WordRep243 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep243, ws7WordCap243, ws7WordP243, ws7WordQ243]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep243, ws7WordCap243, ws7WordP243, ws7WordQ243]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep243, ws7WordCap243, ws7WordP243, ws7WordQ243]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep243, ws7WordCap243, ws7WordP243, ws7WordQ243]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep243, ws7WordCap243, ws7WordP243, ws7WordQ243]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep243, ws7WordCap243, ws7WordP243, ws7WordQ243]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep243, ws7WordCap243, ws7WordP243, ws7WordQ243]
  have hword := ws7Word243WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule132 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨132, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 2 ≤ (9/74 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep288 i) ≤ ws7WordCap288 (ws7WordRep288 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep288, ws7WordCap288, ws7WordP288, ws7WordQ288]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep288, ws7WordCap288, ws7WordP288, ws7WordQ288]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep288, ws7WordCap288, ws7WordP288, ws7WordQ288]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep288, ws7WordCap288, ws7WordP288, ws7WordQ288]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep288, ws7WordCap288, ws7WordP288, ws7WordQ288]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep288, ws7WordCap288, ws7WordP288, ws7WordQ288]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep288, ws7WordCap288, ws7WordP288, ws7WordQ288]
  have hword := ws7Word288WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule133 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨133, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 1 ≤ (7/53 : ℝ)) ∧ (h 2 ≤ (5/42 : ℝ)) ∧ (h 4 ≤ (8/71 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep367 i) ≤ ws7WordCap367 (ws7WordRep367 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep367, ws7WordCap367, ws7WordP367, ws7WordQ367]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep367, ws7WordCap367, ws7WordP367, ws7WordQ367]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep367, ws7WordCap367, ws7WordP367, ws7WordQ367]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep367, ws7WordCap367, ws7WordP367, ws7WordQ367]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep367, ws7WordCap367, ws7WordP367, ws7WordQ367]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep367, ws7WordCap367, ws7WordP367, ws7WordQ367]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep367, ws7WordCap367, ws7WordP367, ws7WordQ367]
  have hword := ws7Word367WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule134 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨134, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 1 ≤ (5/38 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep261 i) ≤ ws7WordCap261 (ws7WordRep261 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep261, ws7WordCap261, ws7WordP261, ws7WordQ261]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep261, ws7WordCap261, ws7WordP261, ws7WordQ261]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep261, ws7WordCap261, ws7WordP261, ws7WordQ261]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep261, ws7WordCap261, ws7WordP261, ws7WordQ261]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep261, ws7WordCap261, ws7WordP261, ws7WordQ261]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep261, ws7WordCap261, ws7WordP261, ws7WordQ261]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep261, ws7WordCap261, ws7WordP261, ws7WordQ261]
  have hword := ws7Word261WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule135 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨135, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 1 ≤ (5/39 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep236 i) ≤ ws7WordCap236 (ws7WordRep236 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep236, ws7WordCap236, ws7WordP236, ws7WordQ236]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep236, ws7WordCap236, ws7WordP236, ws7WordQ236]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep236, ws7WordCap236, ws7WordP236, ws7WordQ236]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep236, ws7WordCap236, ws7WordP236, ws7WordQ236]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep236, ws7WordCap236, ws7WordP236, ws7WordQ236]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep236, ws7WordCap236, ws7WordP236, ws7WordQ236]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep236, ws7WordCap236, ws7WordP236, ws7WordQ236]
  have hword := ws7Word236WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule136 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨136, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (5/42 : ℝ)) ∧ (h 4 ≤ (5/44 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep334 i) ≤ ws7WordCap334 (ws7WordRep334 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep334, ws7WordCap334, ws7WordP334, ws7WordQ334]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep334, ws7WordCap334, ws7WordP334, ws7WordQ334]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep334, ws7WordCap334, ws7WordP334, ws7WordQ334]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep334, ws7WordCap334, ws7WordP334, ws7WordQ334]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep334, ws7WordCap334, ws7WordP334, ws7WordQ334]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep334, ws7WordCap334, ws7WordP334, ws7WordQ334]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep334, ws7WordCap334, ws7WordP334, ws7WordQ334]
  have hword := ws7Word334WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule137 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨137, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (6/41 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (4/33 : ℝ)) ∧ (h 3 ≤ (3/25 : ℝ)) ∧ (h 5 ≤ (2/17 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep52 i) ≤ ws7WordCap52 (ws7WordRep52 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep52, ws7WordCap52, ws7WordP52, ws7WordQ52]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep52, ws7WordCap52, ws7WordP52, ws7WordQ52]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep52, ws7WordCap52, ws7WordP52, ws7WordQ52]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep52, ws7WordCap52, ws7WordP52, ws7WordQ52]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep52, ws7WordCap52, ws7WordP52, ws7WordQ52]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep52, ws7WordCap52, ws7WordP52, ws7WordQ52]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep52, ws7WordCap52, ws7WordP52, ws7WordQ52]
  have hword := ws7Word52WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule138 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨138, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (22/151 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep299 i) ≤ ws7WordCap299 (ws7WordRep299 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep299, ws7WordCap299, ws7WordP299, ws7WordQ299]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep299, ws7WordCap299, ws7WordP299, ws7WordQ299]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep299, ws7WordCap299, ws7WordP299, ws7WordQ299]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep299, ws7WordCap299, ws7WordP299, ws7WordQ299]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep299, ws7WordCap299, ws7WordP299, ws7WordQ299]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep299, ws7WordCap299, ws7WordP299, ws7WordQ299]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep299, ws7WordCap299, ws7WordP299, ws7WordQ299]
  have hword := ws7Word299WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule139 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨139, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (4/27 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (7/60 : ℝ)) ∧ (h 4 ≤ (5/43 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep132 i) ≤ ws7WordCap132 (ws7WordRep132 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep132, ws7WordCap132, ws7WordP132, ws7WordQ132]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep132, ws7WordCap132, ws7WordP132, ws7WordQ132]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep132, ws7WordCap132, ws7WordP132, ws7WordQ132]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep132, ws7WordCap132, ws7WordP132, ws7WordQ132]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep132, ws7WordCap132, ws7WordP132, ws7WordQ132]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep132, ws7WordCap132, ws7WordP132, ws7WordQ132]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep132, ws7WordCap132, ws7WordP132, ws7WordQ132]
  have hword := ws7Word132WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule140 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨140, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (9/62 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (6/53 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep294 i) ≤ ws7WordCap294 (ws7WordRep294 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep294, ws7WordCap294, ws7WordP294, ws7WordQ294]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep294, ws7WordCap294, ws7WordP294, ws7WordQ294]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep294, ws7WordCap294, ws7WordP294, ws7WordQ294]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep294, ws7WordCap294, ws7WordP294, ws7WordQ294]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep294, ws7WordCap294, ws7WordP294, ws7WordQ294]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep294, ws7WordCap294, ws7WordP294, ws7WordQ294]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep294, ws7WordCap294, ws7WordP294, ws7WordQ294]
  have hword := ws7Word294WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule141 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨141, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep123 i) ≤ ws7WordCap123 (ws7WordRep123 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep123, ws7WordCap123, ws7WordP123, ws7WordQ123]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep123, ws7WordCap123, ws7WordP123, ws7WordQ123]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep123, ws7WordCap123, ws7WordP123, ws7WordQ123]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep123, ws7WordCap123, ws7WordP123, ws7WordQ123]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep123, ws7WordCap123, ws7WordP123, ws7WordQ123]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep123, ws7WordCap123, ws7WordP123, ws7WordQ123]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep123, ws7WordCap123, ws7WordP123, ws7WordQ123]
  have hword := ws7Word123WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule142 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨142, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (4/27 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 2 ≤ (5/41 : ℝ)) ∧ (h 3 ≤ (3/25 : ℝ)) ∧ (h 4 ≤ (6/53 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep333 i) ≤ ws7WordCap333 (ws7WordRep333 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep333, ws7WordCap333, ws7WordP333, ws7WordQ333]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep333, ws7WordCap333, ws7WordP333, ws7WordQ333]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep333, ws7WordCap333, ws7WordP333, ws7WordQ333]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep333, ws7WordCap333, ws7WordP333, ws7WordQ333]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep333, ws7WordCap333, ws7WordP333, ws7WordQ333]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep333, ws7WordCap333, ws7WordP333, ws7WordQ333]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep333, ws7WordCap333, ws7WordP333, ws7WordQ333]
  have hword := ws7Word333WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule143 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨143, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (9/62 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep210 i) ≤ ws7WordCap210 (ws7WordRep210 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep210, ws7WordCap210, ws7WordP210, ws7WordQ210]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep210, ws7WordCap210, ws7WordP210, ws7WordQ210]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep210, ws7WordCap210, ws7WordP210, ws7WordQ210]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep210, ws7WordCap210, ws7WordP210, ws7WordQ210]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep210, ws7WordCap210, ws7WordP210, ws7WordQ210]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep210, ws7WordCap210, ws7WordP210, ws7WordQ210]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep210, ws7WordCap210, ws7WordP210, ws7WordQ210]
  have hword := ws7Word210WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule144 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨144, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep318 i) ≤ ws7WordCap318 (ws7WordRep318 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep318, ws7WordCap318, ws7WordP318, ws7WordQ318]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep318, ws7WordCap318, ws7WordP318, ws7WordQ318]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep318, ws7WordCap318, ws7WordP318, ws7WordQ318]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep318, ws7WordCap318, ws7WordP318, ws7WordQ318]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep318, ws7WordCap318, ws7WordP318, ws7WordQ318]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep318, ws7WordCap318, ws7WordP318, ws7WordQ318]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep318, ws7WordCap318, ws7WordP318, ws7WordQ318]
  have hword := ws7Word318WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule145 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨145, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (6/41 : ℝ)) ∧ (h 1 ≤ (6/47 : ℝ)) ∧ (h 3 ≤ (4/33 : ℝ)) ∧ (h 4 ≤ (3/25 : ℝ)) ∧ (h 5 ≤ (2/17 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep197 i) ≤ ws7WordCap197 (ws7WordRep197 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep197, ws7WordCap197, ws7WordP197, ws7WordQ197]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep197, ws7WordCap197, ws7WordP197, ws7WordQ197]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep197, ws7WordCap197, ws7WordP197, ws7WordQ197]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep197, ws7WordCap197, ws7WordP197, ws7WordQ197]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep197, ws7WordCap197, ws7WordP197, ws7WordQ197]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep197, ws7WordCap197, ws7WordP197, ws7WordQ197]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep197, ws7WordCap197, ws7WordP197, ws7WordQ197]
  have hword := ws7Word197WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule146 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨146, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (7/48 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 2 ≤ (5/39 : ℝ)) ∧ (h 3 ≤ (8/67 : ℝ)) ∧ (h 4 ≤ (3/26 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep153 i) ≤ ws7WordCap153 (ws7WordRep153 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep153, ws7WordCap153, ws7WordP153, ws7WordQ153]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep153, ws7WordCap153, ws7WordP153, ws7WordQ153]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep153, ws7WordCap153, ws7WordP153, ws7WordQ153]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep153, ws7WordCap153, ws7WordP153, ws7WordQ153]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep153, ws7WordCap153, ws7WordP153, ws7WordQ153]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep153, ws7WordCap153, ws7WordP153, ws7WordQ153]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep153, ws7WordCap153, ws7WordP153, ws7WordQ153]
  have hword := ws7Word153WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule147 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨147, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (4/27 : ℝ)) ∧ (h 1 ≤ (5/39 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (5/42 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep326 i) ≤ ws7WordCap326 (ws7WordRep326 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep326, ws7WordCap326, ws7WordP326, ws7WordQ326]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep326, ws7WordCap326, ws7WordP326, ws7WordQ326]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep326, ws7WordCap326, ws7WordP326, ws7WordQ326]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep326, ws7WordCap326, ws7WordP326, ws7WordQ326]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep326, ws7WordCap326, ws7WordP326, ws7WordQ326]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep326, ws7WordCap326, ws7WordP326, ws7WordQ326]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep326, ws7WordCap326, ws7WordP326, ws7WordQ326]
  have hword := ws7Word326WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule148 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨148, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 1 ≤ (15/118 : ℝ)) ∧ (h 2 ≤ (4/33 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep363 i) ≤ ws7WordCap363 (ws7WordRep363 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep363, ws7WordCap363, ws7WordP363, ws7WordQ363]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep363, ws7WordCap363, ws7WordP363, ws7WordQ363]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep363, ws7WordCap363, ws7WordP363, ws7WordQ363]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep363, ws7WordCap363, ws7WordP363, ws7WordQ363]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep363, ws7WordCap363, ws7WordP363, ws7WordQ363]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep363, ws7WordCap363, ws7WordP363, ws7WordQ363]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep363, ws7WordCap363, ws7WordP363, ws7WordQ363]
  have hword := ws7Word363WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule149 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨149, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (1/7 : ℝ)) ∧ (h 1 ≤ (4/31 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 5 ≤ (3/28 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep102 i) ≤ ws7WordCap102 (ws7WordRep102 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep102, ws7WordCap102, ws7WordP102, ws7WordQ102]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep102, ws7WordCap102, ws7WordP102, ws7WordQ102]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep102, ws7WordCap102, ws7WordP102, ws7WordQ102]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep102, ws7WordCap102, ws7WordP102, ws7WordQ102]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep102, ws7WordCap102, ws7WordP102, ws7WordQ102]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep102, ws7WordCap102, ws7WordP102, ws7WordQ102]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep102, ws7WordCap102, ws7WordP102, ws7WordQ102]
  have hword := ws7Word102WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule150 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨150, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (7/52 : ℝ)) ∧ (h 1 ≤ (4/31 : ℝ)) ∧ (h 2 ≤ (7/55 : ℝ)) ∧ (h 3 ≤ (4/33 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep354 i) ≤ ws7WordCap354 (ws7WordRep354 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep354, ws7WordCap354, ws7WordP354, ws7WordQ354]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep354, ws7WordCap354, ws7WordP354, ws7WordQ354]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep354, ws7WordCap354, ws7WordP354, ws7WordQ354]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep354, ws7WordCap354, ws7WordP354, ws7WordQ354]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep354, ws7WordCap354, ws7WordP354, ws7WordQ354]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep354, ws7WordCap354, ws7WordP354, ws7WordQ354]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep354, ws7WordCap354, ws7WordP354, ws7WordQ354]
  have hword := ws7Word354WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule153 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨153, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)) ∧ (h 0 ≤ (2/11 : ℝ)) ∧ (h 1 ≤ (7/60 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep135 i) ≤ ws7WordCap135 (ws7WordRep135 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep135, ws7WordCap135, ws7WordP135, ws7WordQ135]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep135, ws7WordCap135, ws7WordP135, ws7WordQ135]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep135, ws7WordCap135, ws7WordP135, ws7WordQ135]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep135, ws7WordCap135, ws7WordP135, ws7WordQ135]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep135, ws7WordCap135, ws7WordP135, ws7WordQ135]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep135, ws7WordCap135, ws7WordP135, ws7WordQ135]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep135, ws7WordCap135, ws7WordP135, ws7WordQ135]
  have hword := ws7Word135WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule154 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨154, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (3/16 : ℝ)) ∧ (h 1 ≤ (4/33 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ)) ∧ (h 5 ≤ (3/28 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep213 i) ≤ ws7WordCap213 (ws7WordRep213 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep213, ws7WordCap213, ws7WordP213, ws7WordQ213]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep213, ws7WordCap213, ws7WordP213, ws7WordQ213]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep213, ws7WordCap213, ws7WordP213, ws7WordQ213]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep213, ws7WordCap213, ws7WordP213, ws7WordQ213]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep213, ws7WordCap213, ws7WordP213, ws7WordQ213]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep213, ws7WordCap213, ws7WordP213, ws7WordQ213]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep213, ws7WordCap213, ws7WordP213, ws7WordQ213]
  have hword := ws7Word213WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule155 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨155, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (4/21 : ℝ)) ∧ (h 1 ≤ (2/17 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep58 i) ≤ ws7WordCap58 (ws7WordRep58 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep58, ws7WordCap58, ws7WordP58, ws7WordQ58]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep58, ws7WordCap58, ws7WordP58, ws7WordQ58]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep58, ws7WordCap58, ws7WordP58, ws7WordQ58]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep58, ws7WordCap58, ws7WordP58, ws7WordQ58]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep58, ws7WordCap58, ws7WordP58, ws7WordQ58]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep58, ws7WordCap58, ws7WordP58, ws7WordQ58]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep58, ws7WordCap58, ws7WordP58, ws7WordQ58]
  have hword := ws7Word58WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule156 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨156, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (5/29 : ℝ)) ∧ (h 1 ≤ (5/42 : ℝ)) ∧ (h 2 ≤ (3/26 : ℝ)) ∧ (h 5 ≤ (4/35 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep323 i) ≤ ws7WordCap323 (ws7WordRep323 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep323, ws7WordCap323, ws7WordP323, ws7WordQ323]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep323, ws7WordCap323, ws7WordP323, ws7WordQ323]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep323, ws7WordCap323, ws7WordP323, ws7WordQ323]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep323, ws7WordCap323, ws7WordP323, ws7WordQ323]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep323, ws7WordCap323, ws7WordP323, ws7WordQ323]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep323, ws7WordCap323, ws7WordP323, ws7WordQ323]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep323, ws7WordCap323, ws7WordP323, ws7WordQ323]
  have hword := ws7Word323WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

end WeakSevenBandData
