import Pinwheel.WeakSevenBandData.NewWordFits02
import Pinwheel.WeakSevenBandData.SourceFits
import Pinwheel.WeakSevenBandData.RateOrder
import Pinwheel.WeakSeven
import Mathlib.Tactic.FinCases

/-! Source-box adapters for literal weak words. -/

namespace RealPinwheel.WeakSevenBandData

theorem newWordFitSchedule120 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨120, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep173 i) ≤ ws7WordCap173 (ws7WordRep173 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep173, ws7WordCap173, ws7WordP173, ws7WordQ173]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep173, ws7WordCap173, ws7WordP173, ws7WordQ173]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep173, ws7WordCap173, ws7WordP173, ws7WordQ173]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep173, ws7WordCap173, ws7WordP173, ws7WordQ173]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep173, ws7WordCap173, ws7WordP173, ws7WordQ173]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep173, ws7WordCap173, ws7WordP173, ws7WordQ173]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep173, ws7WordCap173, ws7WordP173, ws7WordQ173]
  have hword := ws7Word173WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule121 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨121, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (7/57 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep174 i) ≤ ws7WordCap174 (ws7WordRep174 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep174, ws7WordCap174, ws7WordP174, ws7WordQ174]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep174, ws7WordCap174, ws7WordP174, ws7WordQ174]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep174, ws7WordCap174, ws7WordP174, ws7WordQ174]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep174, ws7WordCap174, ws7WordP174, ws7WordQ174]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep174, ws7WordCap174, ws7WordP174, ws7WordQ174]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep174, ws7WordCap174, ws7WordP174, ws7WordQ174]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep174, ws7WordCap174, ws7WordP174, ws7WordQ174]
  have hword := ws7Word174WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule122 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨122, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (13/64 : ℝ)) ∧ (h 0 ≤ (10/67 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (4/31 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (4/37 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep175 i) ≤ ws7WordCap175 (ws7WordRep175 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep175, ws7WordCap175, ws7WordP175, ws7WordQ175]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep175, ws7WordCap175, ws7WordP175, ws7WordQ175]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep175, ws7WordCap175, ws7WordP175, ws7WordQ175]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep175, ws7WordCap175, ws7WordP175, ws7WordQ175]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep175, ws7WordCap175, ws7WordP175, ws7WordQ175]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep175, ws7WordCap175, ws7WordP175, ws7WordQ175]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep175, ws7WordCap175, ws7WordP175, ws7WordQ175]
  have hword := ws7Word175WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule123 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨123, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (16/73 : ℝ)) ∧ (h 0 ≤ (7/43 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 3 ≤ (8/73 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep176 i) ≤ ws7WordCap176 (ws7WordRep176 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep176, ws7WordCap176, ws7WordP176, ws7WordQ176]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep176, ws7WordCap176, ws7WordP176, ws7WordQ176]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep176, ws7WordCap176, ws7WordP176, ws7WordQ176]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep176, ws7WordCap176, ws7WordP176, ws7WordQ176]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep176, ws7WordCap176, ws7WordP176, ws7WordQ176]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep176, ws7WordCap176, ws7WordP176, ws7WordQ176]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep176, ws7WordCap176, ws7WordP176, ws7WordQ176]
  have hword := ws7Word176WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule124 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨124, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 0 ≤ (5/31 : ℝ)) ∧ (h 1 ≤ (11/73 : ℝ)) ∧ (h 3 ≤ (3/28 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep177 i) ≤ ws7WordCap177 (ws7WordRep177 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep177, ws7WordCap177, ws7WordP177, ws7WordQ177]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep177, ws7WordCap177, ws7WordP177, ws7WordQ177]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep177, ws7WordCap177, ws7WordP177, ws7WordQ177]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep177, ws7WordCap177, ws7WordP177, ws7WordQ177]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep177, ws7WordCap177, ws7WordP177, ws7WordQ177]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep177, ws7WordCap177, ws7WordP177, ws7WordQ177]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep177, ws7WordCap177, ws7WordP177, ws7WordQ177]
  have hword := ws7Word177WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule125 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨125, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (8/39 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 4 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (5/47 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep179 i) ≤ ws7WordCap179 (ws7WordRep179 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep179, ws7WordCap179, ws7WordP179, ws7WordQ179]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep179, ws7WordCap179, ws7WordP179, ws7WordQ179]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep179, ws7WordCap179, ws7WordP179, ws7WordQ179]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep179, ws7WordCap179, ws7WordP179, ws7WordQ179]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep179, ws7WordCap179, ws7WordP179, ws7WordQ179]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep179, ws7WordCap179, ws7WordP179, ws7WordQ179]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep179, ws7WordCap179, ws7WordP179, ws7WordQ179]
  have hword := ws7Word179WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule126 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨126, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (6/47 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (2/19 : ℝ)) ∧ (h 5 ≤ (3/29 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep180 i) ≤ ws7WordCap180 (ws7WordRep180 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep180, ws7WordCap180, ws7WordP180, ws7WordQ180]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep180, ws7WordCap180, ws7WordP180, ws7WordQ180]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep180, ws7WordCap180, ws7WordP180, ws7WordQ180]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep180, ws7WordCap180, ws7WordP180, ws7WordQ180]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep180, ws7WordCap180, ws7WordP180, ws7WordQ180]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep180, ws7WordCap180, ws7WordP180, ws7WordQ180]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep180, ws7WordCap180, ws7WordP180, ws7WordQ180]
  have hword := ws7Word180WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule127 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨127, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep181 i) ≤ ws7WordCap181 (ws7WordRep181 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep181, ws7WordCap181, ws7WordP181, ws7WordQ181]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep181, ws7WordCap181, ws7WordP181, ws7WordQ181]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep181, ws7WordCap181, ws7WordP181, ws7WordQ181]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep181, ws7WordCap181, ws7WordP181, ws7WordQ181]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep181, ws7WordCap181, ws7WordP181, ws7WordQ181]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep181, ws7WordCap181, ws7WordP181, ws7WordQ181]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep181, ws7WordCap181, ws7WordP181, ws7WordQ181]
  have hword := ws7Word181WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule128 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨128, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 2 ≤ (9/76 : ℝ)) ∧ (h 3 ≤ (5/43 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep182 i) ≤ ws7WordCap182 (ws7WordRep182 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep182, ws7WordCap182, ws7WordP182, ws7WordQ182]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep182, ws7WordCap182, ws7WordP182, ws7WordQ182]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep182, ws7WordCap182, ws7WordP182, ws7WordQ182]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep182, ws7WordCap182, ws7WordP182, ws7WordQ182]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep182, ws7WordCap182, ws7WordP182, ws7WordQ182]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep182, ws7WordCap182, ws7WordP182, ws7WordQ182]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep182, ws7WordCap182, ws7WordP182, ws7WordQ182]
  have hword := ws7Word182WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule129 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨129, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (5/38 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (4/31 : ℝ)) ∧ (h 4 ≤ (1/8 : ℝ)) ∧ (h 5 ≤ (3/29 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep184 i) ≤ ws7WordCap184 (ws7WordRep184 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep184, ws7WordCap184, ws7WordP184, ws7WordQ184]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep184, ws7WordCap184, ws7WordP184, ws7WordQ184]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep184, ws7WordCap184, ws7WordP184, ws7WordQ184]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep184, ws7WordCap184, ws7WordP184, ws7WordQ184]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep184, ws7WordCap184, ws7WordP184, ws7WordQ184]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep184, ws7WordCap184, ws7WordP184, ws7WordQ184]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep184, ws7WordCap184, ws7WordP184, ws7WordQ184]
  have hword := ws7Word184WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule130 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨130, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (7/45 : ℝ)) ∧ (h 1 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (3/29 : ℝ)) ∧ (h 5 ≤ (4/39 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep185 i) ≤ ws7WordCap185 (ws7WordRep185 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep185, ws7WordCap185, ws7WordP185, ws7WordQ185]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep185, ws7WordCap185, ws7WordP185, ws7WordQ185]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep185, ws7WordCap185, ws7WordP185, ws7WordQ185]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep185, ws7WordCap185, ws7WordP185, ws7WordQ185]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep185, ws7WordCap185, ws7WordP185, ws7WordQ185]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep185, ws7WordCap185, ws7WordP185, ws7WordQ185]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep185, ws7WordCap185, ws7WordP185, ws7WordQ185]
  have hword := ws7Word185WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule131 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨131, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (5/38 : ℝ)) ∧ (h 4 ≤ (1/8 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep186 i) ≤ ws7WordCap186 (ws7WordRep186 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep186, ws7WordCap186, ws7WordP186, ws7WordQ186]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep186, ws7WordCap186, ws7WordP186, ws7WordQ186]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep186, ws7WordCap186, ws7WordP186, ws7WordQ186]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep186, ws7WordCap186, ws7WordP186, ws7WordQ186]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep186, ws7WordCap186, ws7WordP186, ws7WordQ186]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep186, ws7WordCap186, ws7WordP186, ws7WordQ186]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep186, ws7WordCap186, ws7WordP186, ws7WordQ186]
  have hword := ws7Word186WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule132 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨132, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (12/59 : ℝ)) ∧ (h 0 ≤ (2/11 : ℝ)) ∧ (h 1 ≤ (4/31 : ℝ)) ∧ (h 2 ≤ (3/26 : ℝ)) ∧ (h 3 ≤ (5/44 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep187 i) ≤ ws7WordCap187 (ws7WordRep187 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep187, ws7WordCap187, ws7WordP187, ws7WordQ187]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep187, ws7WordCap187, ws7WordP187, ws7WordQ187]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep187, ws7WordCap187, ws7WordP187, ws7WordQ187]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep187, ws7WordCap187, ws7WordP187, ws7WordQ187]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep187, ws7WordCap187, ws7WordP187, ws7WordQ187]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep187, ws7WordCap187, ws7WordP187, ws7WordQ187]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep187, ws7WordCap187, ws7WordP187, ws7WordQ187]
  have hword := ws7Word187WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule133 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨133, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (2/13 : ℝ)) ∧ (h 3 ≤ (8/77 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep188 i) ≤ ws7WordCap188 (ws7WordRep188 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep188, ws7WordCap188, ws7WordP188, ws7WordQ188]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep188, ws7WordCap188, ws7WordP188, ws7WordQ188]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep188, ws7WordCap188, ws7WordP188, ws7WordQ188]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep188, ws7WordCap188, ws7WordP188, ws7WordQ188]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep188, ws7WordCap188, ws7WordP188, ws7WordQ188]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep188, ws7WordCap188, ws7WordP188, ws7WordQ188]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep188, ws7WordCap188, ws7WordP188, ws7WordQ188]
  have hword := ws7Word188WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule134 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨134, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (5/39 : ℝ)) ∧ (h 4 ≤ (3/26 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep190 i) ≤ ws7WordCap190 (ws7WordRep190 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep190, ws7WordCap190, ws7WordP190, ws7WordQ190]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep190, ws7WordCap190, ws7WordP190, ws7WordQ190]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep190, ws7WordCap190, ws7WordP190, ws7WordQ190]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep190, ws7WordCap190, ws7WordP190, ws7WordQ190]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep190, ws7WordCap190, ws7WordP190, ws7WordQ190]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep190, ws7WordCap190, ws7WordP190, ws7WordQ190]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep190, ws7WordCap190, ws7WordP190, ws7WordQ190]
  have hword := ws7Word190WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule135 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨135, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (1/5 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 2 ≤ (9/80 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep191 i) ≤ ws7WordCap191 (ws7WordRep191 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep191, ws7WordCap191, ws7WordP191, ws7WordQ191]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep191, ws7WordCap191, ws7WordP191, ws7WordQ191]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep191, ws7WordCap191, ws7WordP191, ws7WordQ191]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep191, ws7WordCap191, ws7WordP191, ws7WordQ191]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep191, ws7WordCap191, ws7WordP191, ws7WordQ191]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep191, ws7WordCap191, ws7WordP191, ws7WordQ191]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep191, ws7WordCap191, ws7WordP191, ws7WordQ191]
  have hword := ws7Word191WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule136 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨136, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep192 i) ≤ ws7WordCap192 (ws7WordRep192 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep192, ws7WordCap192, ws7WordP192, ws7WordQ192]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep192, ws7WordCap192, ws7WordP192, ws7WordQ192]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep192, ws7WordCap192, ws7WordP192, ws7WordQ192]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep192, ws7WordCap192, ws7WordP192, ws7WordQ192]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep192, ws7WordCap192, ws7WordP192, ws7WordQ192]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep192, ws7WordCap192, ws7WordP192, ws7WordQ192]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep192, ws7WordCap192, ws7WordP192, ws7WordQ192]
  have hword := ws7Word192WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule137 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨137, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (4/23 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (9/80 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep194 i) ≤ ws7WordCap194 (ws7WordRep194 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep194, ws7WordCap194, ws7WordP194, ws7WordQ194]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep194, ws7WordCap194, ws7WordP194, ws7WordQ194]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep194, ws7WordCap194, ws7WordP194, ws7WordQ194]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep194, ws7WordCap194, ws7WordP194, ws7WordQ194]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep194, ws7WordCap194, ws7WordP194, ws7WordQ194]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep194, ws7WordCap194, ws7WordP194, ws7WordQ194]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep194, ws7WordCap194, ws7WordP194, ws7WordQ194]
  have hword := ws7Word194WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule138 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨138, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (2/11 : ℝ)) ∧ (h 1 ≤ (7/57 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep195 i) ≤ ws7WordCap195 (ws7WordRep195 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep195, ws7WordCap195, ws7WordP195, ws7WordQ195]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep195, ws7WordCap195, ws7WordP195, ws7WordQ195]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep195, ws7WordCap195, ws7WordP195, ws7WordQ195]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep195, ws7WordCap195, ws7WordP195, ws7WordQ195]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep195, ws7WordCap195, ws7WordP195, ws7WordQ195]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep195, ws7WordCap195, ws7WordP195, ws7WordQ195]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep195, ws7WordCap195, ws7WordP195, ws7WordQ195]
  have hword := ws7Word195WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule139 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨139, by decide⟩ : Fin 263) h delta) :
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

theorem newWordFitSchedule140 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨140, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)) ∧ (h 0 ≤ (3/17 : ℝ)) ∧ (h 1 ≤ (6/47 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (4/37 : ℝ)) ∧ (h 5 ≤ (3/28 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep198 i) ≤ ws7WordCap198 (ws7WordRep198 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep198, ws7WordCap198, ws7WordP198, ws7WordQ198]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep198, ws7WordCap198, ws7WordP198, ws7WordQ198]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep198, ws7WordCap198, ws7WordP198, ws7WordQ198]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep198, ws7WordCap198, ws7WordP198, ws7WordQ198]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep198, ws7WordCap198, ws7WordP198, ws7WordQ198]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep198, ws7WordCap198, ws7WordP198, ws7WordQ198]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep198, ws7WordCap198, ws7WordP198, ws7WordQ198]
  have hword := ws7Word198WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule141 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨141, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (11/54 : ℝ)) ∧ (h 0 ≤ (1/5 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep199 i) ≤ ws7WordCap199 (ws7WordRep199 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep199, ws7WordCap199, ws7WordP199, ws7WordQ199]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep199, ws7WordCap199, ws7WordP199, ws7WordQ199]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep199, ws7WordCap199, ws7WordP199, ws7WordQ199]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep199, ws7WordCap199, ws7WordP199, ws7WordQ199]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep199, ws7WordCap199, ws7WordP199, ws7WordQ199]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep199, ws7WordCap199, ws7WordP199, ws7WordQ199]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep199, ws7WordCap199, ws7WordP199, ws7WordQ199]
  have hword := ws7Word199WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule142 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨142, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (18/83 : ℝ)) ∧ (h 0 ≤ (12/83 : ℝ)) ∧ (h 2 ≤ (1/7 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (9/83 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep200 i) ≤ ws7WordCap200 (ws7WordRep200 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep200, ws7WordCap200, ws7WordP200, ws7WordQ200]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep200, ws7WordCap200, ws7WordP200, ws7WordQ200]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep200, ws7WordCap200, ws7WordP200, ws7WordQ200]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep200, ws7WordCap200, ws7WordP200, ws7WordQ200]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep200, ws7WordCap200, ws7WordP200, ws7WordQ200]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep200, ws7WordCap200, ws7WordP200, ws7WordQ200]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep200, ws7WordCap200, ws7WordP200, ws7WordQ200]
  have hword := ws7Word200WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule143 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨143, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 4 ≤ (5/47 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep201 i) ≤ ws7WordCap201 (ws7WordRep201 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep201, ws7WordCap201, ws7WordP201, ws7WordQ201]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep201, ws7WordCap201, ws7WordP201, ws7WordQ201]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep201, ws7WordCap201, ws7WordP201, ws7WordQ201]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep201, ws7WordCap201, ws7WordP201, ws7WordQ201]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep201, ws7WordCap201, ws7WordP201, ws7WordQ201]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep201, ws7WordCap201, ws7WordP201, ws7WordQ201]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep201, ws7WordCap201, ws7WordP201, ws7WordQ201]
  have hword := ws7Word201WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule144 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨144, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (5/31 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (3/28 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep202 i) ≤ ws7WordCap202 (ws7WordRep202 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep202, ws7WordCap202, ws7WordP202, ws7WordQ202]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep202, ws7WordCap202, ws7WordP202, ws7WordQ202]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep202, ws7WordCap202, ws7WordP202, ws7WordQ202]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep202, ws7WordCap202, ws7WordP202, ws7WordQ202]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep202, ws7WordCap202, ws7WordP202, ws7WordQ202]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep202, ws7WordCap202, ws7WordP202, ws7WordQ202]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep202, ws7WordCap202, ws7WordP202, ws7WordQ202]
  have hword := ws7Word202WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule145 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨145, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)) ∧ (h 0 ≤ (7/41 : ℝ)) ∧ (h 1 ≤ (4/31 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (5/44 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep205 i) ≤ ws7WordCap205 (ws7WordRep205 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep205, ws7WordCap205, ws7WordP205, ws7WordQ205]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep205, ws7WordCap205, ws7WordP205, ws7WordQ205]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep205, ws7WordCap205, ws7WordP205, ws7WordQ205]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep205, ws7WordCap205, ws7WordP205, ws7WordQ205]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep205, ws7WordCap205, ws7WordP205, ws7WordQ205]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep205, ws7WordCap205, ws7WordP205, ws7WordQ205]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep205, ws7WordCap205, ws7WordP205, ws7WordQ205]
  have hword := ws7Word205WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule146 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨146, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (5/36 : ℝ)) ∧ (h 4 ≤ (3/26 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep206 i) ≤ ws7WordCap206 (ws7WordRep206 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep206, ws7WordCap206, ws7WordP206, ws7WordQ206]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep206, ws7WordCap206, ws7WordP206, ws7WordQ206]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep206, ws7WordCap206, ws7WordP206, ws7WordQ206]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep206, ws7WordCap206, ws7WordP206, ws7WordQ206]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep206, ws7WordCap206, ws7WordP206, ws7WordQ206]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep206, ws7WordCap206, ws7WordP206, ws7WordQ206]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep206, ws7WordCap206, ws7WordP206, ws7WordQ206]
  have hword := ws7Word206WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule147 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨147, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (9/44 : ℝ)) ∧ (h 0 ≤ (4/23 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep208 i) ≤ ws7WordCap208 (ws7WordRep208 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep208, ws7WordCap208, ws7WordP208, ws7WordQ208]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep208, ws7WordCap208, ws7WordP208, ws7WordQ208]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep208, ws7WordCap208, ws7WordP208, ws7WordQ208]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep208, ws7WordCap208, ws7WordP208, ws7WordQ208]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep208, ws7WordCap208, ws7WordP208, ws7WordQ208]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep208, ws7WordCap208, ws7WordP208, ws7WordQ208]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep208, ws7WordCap208, ws7WordP208, ws7WordQ208]
  have hword := ws7Word208WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule148 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨148, by decide⟩ : Fin 263) h delta) :
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

theorem newWordFitSchedule149 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨149, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)) ∧ (h 0 ≤ (12/71 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (9/80 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep211 i) ≤ ws7WordCap211 (ws7WordRep211 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep211, ws7WordCap211, ws7WordP211, ws7WordQ211]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep211, ws7WordCap211, ws7WordP211, ws7WordQ211]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep211, ws7WordCap211, ws7WordP211, ws7WordQ211]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep211, ws7WordCap211, ws7WordP211, ws7WordQ211]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep211, ws7WordCap211, ws7WordP211, ws7WordQ211]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep211, ws7WordCap211, ws7WordP211, ws7WordQ211]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep211, ws7WordCap211, ws7WordP211, ws7WordQ211]
  have hword := ws7Word211WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule150 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨150, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 0 ≤ (5/33 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep214 i) ≤ ws7WordCap214 (ws7WordRep214 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep214, ws7WordCap214, ws7WordP214, ws7WordQ214]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep214, ws7WordCap214, ws7WordP214, ws7WordQ214]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep214, ws7WordCap214, ws7WordP214, ws7WordQ214]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep214, ws7WordCap214, ws7WordP214, ws7WordQ214]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep214, ws7WordCap214, ws7WordP214, ws7WordQ214]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep214, ws7WordCap214, ws7WordP214, ws7WordQ214]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep214, ws7WordCap214, ws7WordP214, ws7WordQ214]
  have hword := ws7Word214WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule151 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨151, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (3/26 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep215 i) ≤ ws7WordCap215 (ws7WordRep215 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep215, ws7WordCap215, ws7WordP215, ws7WordQ215]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep215, ws7WordCap215, ws7WordP215, ws7WordQ215]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep215, ws7WordCap215, ws7WordP215, ws7WordQ215]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep215, ws7WordCap215, ws7WordP215, ws7WordQ215]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep215, ws7WordCap215, ws7WordP215, ws7WordQ215]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep215, ws7WordCap215, ws7WordP215, ws7WordQ215]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep215, ws7WordCap215, ws7WordP215, ws7WordQ215]
  have hword := ws7Word215WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule152 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨152, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (5/46 : ℝ)) ∧ (h 5 ≤ (4/37 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep217 i) ≤ ws7WordCap217 (ws7WordRep217 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep217, ws7WordCap217, ws7WordP217, ws7WordQ217]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep217, ws7WordCap217, ws7WordP217, ws7WordQ217]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep217, ws7WordCap217, ws7WordP217, ws7WordQ217]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep217, ws7WordCap217, ws7WordP217, ws7WordQ217]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep217, ws7WordCap217, ws7WordP217, ws7WordQ217]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep217, ws7WordCap217, ws7WordP217, ws7WordQ217]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep217, ws7WordCap217, ws7WordP217, ws7WordQ217]
  have hword := ws7Word217WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule153 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨153, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (2/11 : ℝ)) ∧ (h 1 ≤ (7/55 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 4 ≤ (3/28 : ℝ)) ∧ (h 5 ≤ (4/39 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep218 i) ≤ ws7WordCap218 (ws7WordRep218 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep218, ws7WordCap218, ws7WordP218, ws7WordQ218]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep218, ws7WordCap218, ws7WordP218, ws7WordQ218]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep218, ws7WordCap218, ws7WordP218, ws7WordQ218]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep218, ws7WordCap218, ws7WordP218, ws7WordQ218]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep218, ws7WordCap218, ws7WordP218, ws7WordQ218]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep218, ws7WordCap218, ws7WordP218, ws7WordQ218]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep218, ws7WordCap218, ws7WordP218, ws7WordQ218]
  have hword := ws7Word218WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule154 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨154, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (4/31 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep219 i) ≤ ws7WordCap219 (ws7WordRep219 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep219, ws7WordCap219, ws7WordP219, ws7WordQ219]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep219, ws7WordCap219, ws7WordP219, ws7WordQ219]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep219, ws7WordCap219, ws7WordP219, ws7WordQ219]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep219, ws7WordCap219, ws7WordP219, ws7WordQ219]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep219, ws7WordCap219, ws7WordP219, ws7WordQ219]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep219, ws7WordCap219, ws7WordP219, ws7WordQ219]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep219, ws7WordCap219, ws7WordP219, ws7WordQ219]
  have hword := ws7Word219WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule155 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨155, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (9/44 : ℝ)) ∧ (h 0 ≤ (5/31 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (5/48 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep222 i) ≤ ws7WordCap222 (ws7WordRep222 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep222, ws7WordCap222, ws7WordP222, ws7WordQ222]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep222, ws7WordCap222, ws7WordP222, ws7WordQ222]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep222, ws7WordCap222, ws7WordP222, ws7WordQ222]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep222, ws7WordCap222, ws7WordP222, ws7WordQ222]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep222, ws7WordCap222, ws7WordP222, ws7WordQ222]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep222, ws7WordCap222, ws7WordP222, ws7WordQ222]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep222, ws7WordCap222, ws7WordP222, ws7WordQ222]
  have hword := ws7Word222WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule156 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨156, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (10/49 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (6/47 : ℝ)) ∧ (h 3 ≤ (4/33 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep223 i) ≤ ws7WordCap223 (ws7WordRep223 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep223, ws7WordCap223, ws7WordP223, ws7WordQ223]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep223, ws7WordCap223, ws7WordP223, ws7WordQ223]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep223, ws7WordCap223, ws7WordP223, ws7WordQ223]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep223, ws7WordCap223, ws7WordP223, ws7WordQ223]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep223, ws7WordCap223, ws7WordP223, ws7WordQ223]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep223, ws7WordCap223, ws7WordP223, ws7WordQ223]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep223, ws7WordCap223, ws7WordP223, ws7WordQ223]
  have hword := ws7Word223WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule157 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨157, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (6/47 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ)) ∧ (h 4 ≤ (5/46 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep224 i) ≤ ws7WordCap224 (ws7WordRep224 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep224, ws7WordCap224, ws7WordP224, ws7WordQ224]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep224, ws7WordCap224, ws7WordP224, ws7WordQ224]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep224, ws7WordCap224, ws7WordP224, ws7WordQ224]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep224, ws7WordCap224, ws7WordP224, ws7WordQ224]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep224, ws7WordCap224, ws7WordP224, ws7WordQ224]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep224, ws7WordCap224, ws7WordP224, ws7WordQ224]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep224, ws7WordCap224, ws7WordP224, ws7WordQ224]
  have hword := ws7Word224WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule158 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨158, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (4/23 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (4/33 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ)) ∧ (h 4 ≤ (3/28 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep226 i) ≤ ws7WordCap226 (ws7WordRep226 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep226, ws7WordCap226, ws7WordP226, ws7WordQ226]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep226, ws7WordCap226, ws7WordP226, ws7WordQ226]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep226, ws7WordCap226, ws7WordP226, ws7WordQ226]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep226, ws7WordCap226, ws7WordP226, ws7WordQ226]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep226, ws7WordCap226, ws7WordP226, ws7WordQ226]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep226, ws7WordCap226, ws7WordP226, ws7WordQ226]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep226, ws7WordCap226, ws7WordP226, ws7WordQ226]
  have hword := ws7Word226WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule159 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨159, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (8/39 : ℝ)) ∧ (h 0 ≤ (11/76 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (3/25 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep228 i) ≤ ws7WordCap228 (ws7WordRep228 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep228, ws7WordCap228, ws7WordP228, ws7WordQ228]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep228, ws7WordCap228, ws7WordP228, ws7WordQ228]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep228, ws7WordCap228, ws7WordP228, ws7WordQ228]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep228, ws7WordCap228, ws7WordP228, ws7WordQ228]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep228, ws7WordCap228, ws7WordP228, ws7WordQ228]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep228, ws7WordCap228, ws7WordP228, ws7WordQ228]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep228, ws7WordCap228, ws7WordP228, ws7WordQ228]
  have hword := ws7Word228WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

end WeakSevenBandData
