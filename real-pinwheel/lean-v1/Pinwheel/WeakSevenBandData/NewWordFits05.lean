import Pinwheel.WeakSevenBandData.NewWordFits04
import Pinwheel.WeakSevenBandData.SourceFits
import Pinwheel.WeakSevenBandData.RateOrder
import Pinwheel.WeakSeven
import Mathlib.Tactic.FinCases

/-! Source-box adapters for literal weak words. -/

namespace RealPinwheel.WeakSevenBandData

theorem newWordFitSchedule200 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨200, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 4 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep308 i) ≤ ws7WordCap308 (ws7WordRep308 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep308, ws7WordCap308, ws7WordP308, ws7WordQ308]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep308, ws7WordCap308, ws7WordP308, ws7WordQ308]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep308, ws7WordCap308, ws7WordP308, ws7WordQ308]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep308, ws7WordCap308, ws7WordP308, ws7WordQ308]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep308, ws7WordCap308, ws7WordP308, ws7WordQ308]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep308, ws7WordCap308, ws7WordP308, ws7WordQ308]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep308, ws7WordCap308, ws7WordP308, ws7WordQ308]
  have hword := ws7Word308WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule201 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨201, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (2/11 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (3/26 : ℝ)) ∧ (h 3 ≤ (5/46 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep312 i) ≤ ws7WordCap312 (ws7WordRep312 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep312, ws7WordCap312, ws7WordP312, ws7WordQ312]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep312, ws7WordCap312, ws7WordP312, ws7WordQ312]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep312, ws7WordCap312, ws7WordP312, ws7WordQ312]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep312, ws7WordCap312, ws7WordP312, ws7WordQ312]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep312, ws7WordCap312, ws7WordP312, ws7WordQ312]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep312, ws7WordCap312, ws7WordP312, ws7WordQ312]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep312, ws7WordCap312, ws7WordP312, ws7WordQ312]
  have hword := ws7Word312WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule202 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨202, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 4 ≤ (9/80 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep325 i) ≤ ws7WordCap325 (ws7WordRep325 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep325, ws7WordCap325, ws7WordP325, ws7WordQ325]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep325, ws7WordCap325, ws7WordP325, ws7WordQ325]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep325, ws7WordCap325, ws7WordP325, ws7WordQ325]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep325, ws7WordCap325, ws7WordP325, ws7WordQ325]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep325, ws7WordCap325, ws7WordP325, ws7WordQ325]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep325, ws7WordCap325, ws7WordP325, ws7WordQ325]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep325, ws7WordCap325, ws7WordP325, ws7WordQ325]
  have hword := ws7Word325WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule203 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨203, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (15/74 : ℝ)) ∧ (h 0 ≤ (2/11 : ℝ)) ∧ (h 1 ≤ (13/99 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (3/28 : ℝ)) ∧ (h 4 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep328 i) ≤ ws7WordCap328 (ws7WordRep328 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep328, ws7WordCap328, ws7WordP328, ws7WordQ328]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep328, ws7WordCap328, ws7WordP328, ws7WordQ328]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep328, ws7WordCap328, ws7WordP328, ws7WordQ328]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep328, ws7WordCap328, ws7WordP328, ws7WordQ328]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep328, ws7WordCap328, ws7WordP328, ws7WordQ328]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep328, ws7WordCap328, ws7WordP328, ws7WordQ328]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep328, ws7WordCap328, ws7WordP328, ws7WordQ328]
  have hword := ws7Word328WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule204 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨204, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (3/22 : ℝ)) ∧ (h 3 ≤ (5/46 : ℝ)) ∧ (h 4 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep332 i) ≤ ws7WordCap332 (ws7WordRep332 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep332, ws7WordCap332, ws7WordP332, ws7WordQ332]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep332, ws7WordCap332, ws7WordP332, ws7WordQ332]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep332, ws7WordCap332, ws7WordP332, ws7WordQ332]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep332, ws7WordCap332, ws7WordP332, ws7WordQ332]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep332, ws7WordCap332, ws7WordP332, ws7WordQ332]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep332, ws7WordCap332, ws7WordP332, ws7WordQ332]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep332, ws7WordCap332, ws7WordP332, ws7WordQ332]
  have hword := ws7Word332WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule205 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨205, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (6/41 : ℝ)) ∧ (h 2 ≤ (4/31 : ℝ)) ∧ (h 3 ≤ (9/83 : ℝ)) ∧ (h 4 ≤ (3/28 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep336 i) ≤ ws7WordCap336 (ws7WordRep336 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep336, ws7WordCap336, ws7WordP336, ws7WordQ336]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep336, ws7WordCap336, ws7WordP336, ws7WordQ336]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep336, ws7WordCap336, ws7WordP336, ws7WordQ336]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep336, ws7WordCap336, ws7WordP336, ws7WordQ336]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep336, ws7WordCap336, ws7WordP336, ws7WordQ336]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep336, ws7WordCap336, ws7WordP336, ws7WordQ336]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep336, ws7WordCap336, ws7WordP336, ws7WordQ336]
  have hword := ws7Word336WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule206 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨206, by decide⟩ : Fin 263) h delta) :
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

theorem newWordFitSchedule207 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨207, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (13/63 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (22/185 : ℝ)) ∧ (h 3 ≤ (7/61 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep338 i) ≤ ws7WordCap338 (ws7WordRep338 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep338, ws7WordCap338, ws7WordP338, ws7WordQ338]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep338, ws7WordCap338, ws7WordP338, ws7WordQ338]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep338, ws7WordCap338, ws7WordP338, ws7WordQ338]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep338, ws7WordCap338, ws7WordP338, ws7WordQ338]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep338, ws7WordCap338, ws7WordP338, ws7WordQ338]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep338, ws7WordCap338, ws7WordP338, ws7WordQ338]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep338, ws7WordCap338, ws7WordP338, ws7WordQ338]
  have hword := ws7Word338WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule208 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨208, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (14/69 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (5/39 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 4 ≤ (9/79 : ℝ)) ∧ (h 5 ≤ (3/29 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep339 i) ≤ ws7WordCap339 (ws7WordRep339 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep339, ws7WordCap339, ws7WordP339, ws7WordQ339]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep339, ws7WordCap339, ws7WordP339, ws7WordQ339]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep339, ws7WordCap339, ws7WordP339, ws7WordQ339]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep339, ws7WordCap339, ws7WordP339, ws7WordQ339]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep339, ws7WordCap339, ws7WordP339, ws7WordQ339]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep339, ws7WordCap339, ws7WordP339, ws7WordQ339]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep339, ws7WordCap339, ws7WordP339, ws7WordQ339]
  have hword := ws7Word339WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule209 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨209, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (5/34 : ℝ)) ∧ (h 2 ≤ (27/236 : ℝ)) ∧ (h 3 ≤ (6/53 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep342 i) ≤ ws7WordCap342 (ws7WordRep342 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep342, ws7WordCap342, ws7WordP342, ws7WordQ342]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep342, ws7WordCap342, ws7WordP342, ws7WordQ342]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep342, ws7WordCap342, ws7WordP342, ws7WordQ342]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep342, ws7WordCap342, ws7WordP342, ws7WordQ342]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep342, ws7WordCap342, ws7WordP342, ws7WordQ342]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep342, ws7WordCap342, ws7WordP342, ws7WordQ342]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep342, ws7WordCap342, ws7WordP342, ws7WordQ342]
  have hword := ws7Word342WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule210 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨210, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)) ∧ (h 0 ≤ (3/17 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (7/61 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep343 i) ≤ ws7WordCap343 (ws7WordRep343 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep343, ws7WordCap343, ws7WordP343, ws7WordQ343]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep343, ws7WordCap343, ws7WordP343, ws7WordQ343]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep343, ws7WordCap343, ws7WordP343, ws7WordQ343]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep343, ws7WordCap343, ws7WordP343, ws7WordQ343]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep343, ws7WordCap343, ws7WordP343, ws7WordQ343]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep343, ws7WordCap343, ws7WordP343, ws7WordQ343]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep343, ws7WordCap343, ws7WordP343, ws7WordQ343]
  have hword := ws7Word343WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule211 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨211, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)) ∧ (h 0 ≤ (13/90 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (3/26 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep345 i) ≤ ws7WordCap345 (ws7WordRep345 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep345, ws7WordCap345, ws7WordP345, ws7WordQ345]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep345, ws7WordCap345, ws7WordP345, ws7WordQ345]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep345, ws7WordCap345, ws7WordP345, ws7WordQ345]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep345, ws7WordCap345, ws7WordP345, ws7WordQ345]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep345, ws7WordCap345, ws7WordP345, ws7WordQ345]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep345, ws7WordCap345, ws7WordP345, ws7WordQ345]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep345, ws7WordCap345, ws7WordP345, ws7WordQ345]
  have hword := ws7Word345WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule212 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨212, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (12/59 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep348 i) ≤ ws7WordCap348 (ws7WordRep348 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep348, ws7WordCap348, ws7WordP348, ws7WordQ348]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep348, ws7WordCap348, ws7WordP348, ws7WordQ348]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep348, ws7WordCap348, ws7WordP348, ws7WordQ348]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep348, ws7WordCap348, ws7WordP348, ws7WordQ348]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep348, ws7WordCap348, ws7WordP348, ws7WordQ348]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep348, ws7WordCap348, ws7WordP348, ws7WordQ348]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep348, ws7WordCap348, ws7WordP348, ws7WordQ348]
  have hword := ws7Word348WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule213 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨213, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (8/39 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep353 i) ≤ ws7WordCap353 (ws7WordRep353 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep353, ws7WordCap353, ws7WordP353, ws7WordQ353]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep353, ws7WordCap353, ws7WordP353, ws7WordQ353]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep353, ws7WordCap353, ws7WordP353, ws7WordQ353]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep353, ws7WordCap353, ws7WordP353, ws7WordQ353]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep353, ws7WordCap353, ws7WordP353, ws7WordQ353]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep353, ws7WordCap353, ws7WordP353, ws7WordQ353]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep353, ws7WordCap353, ws7WordP353, ws7WordQ353]
  have hword := ws7Word353WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule214 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨214, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (4/31 : ℝ)) ∧ (h 3 ≤ (9/83 : ℝ)) ∧ (h 4 ≤ (3/29 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep362 i) ≤ ws7WordCap362 (ws7WordRep362 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep362, ws7WordCap362, ws7WordP362, ws7WordQ362]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep362, ws7WordCap362, ws7WordP362, ws7WordQ362]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep362, ws7WordCap362, ws7WordP362, ws7WordQ362]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep362, ws7WordCap362, ws7WordP362, ws7WordQ362]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep362, ws7WordCap362, ws7WordP362, ws7WordQ362]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep362, ws7WordCap362, ws7WordP362, ws7WordQ362]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep362, ws7WordCap362, ws7WordP362, ws7WordQ362]
  have hword := ws7Word362WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule215 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨215, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (19/94 : ℝ)) ∧ (h 0 ≤ (5/33 : ℝ)) ∧ (h 1 ≤ (13/99 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 5 ≤ (8/79 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep366 i) ≤ ws7WordCap366 (ws7WordRep366 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep366, ws7WordCap366, ws7WordP366, ws7WordQ366]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep366, ws7WordCap366, ws7WordP366, ws7WordQ366]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep366, ws7WordCap366, ws7WordP366, ws7WordQ366]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep366, ws7WordCap366, ws7WordP366, ws7WordQ366]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep366, ws7WordCap366, ws7WordP366, ws7WordQ366]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep366, ws7WordCap366, ws7WordP366, ws7WordQ366]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep366, ws7WordCap366, ws7WordP366, ws7WordQ366]
  have hword := ws7Word366WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule216 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨216, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 4 ≤ (7/62 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep370 i) ≤ ws7WordCap370 (ws7WordRep370 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep370, ws7WordCap370, ws7WordP370, ws7WordQ370]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep370, ws7WordCap370, ws7WordP370, ws7WordQ370]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep370, ws7WordCap370, ws7WordP370, ws7WordQ370]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep370, ws7WordCap370, ws7WordP370, ws7WordQ370]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep370, ws7WordCap370, ws7WordP370, ws7WordQ370]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep370, ws7WordCap370, ws7WordP370, ws7WordQ370]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep370, ws7WordCap370, ws7WordP370, ws7WordQ370]
  have hword := ws7Word370WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule217 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨217, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (15/73 : ℝ)) ∧ (h 0 ≤ (6/35 : ℝ)) ∧ (h 1 ≤ (508/3957 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (3/28 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep375 i) ≤ ws7WordCap375 (ws7WordRep375 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep375, ws7WordCap375, ws7WordP375, ws7WordQ375]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep375, ws7WordCap375, ws7WordP375, ws7WordQ375]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep375, ws7WordCap375, ws7WordP375, ws7WordQ375]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep375, ws7WordCap375, ws7WordP375, ws7WordQ375]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep375, ws7WordCap375, ws7WordP375, ws7WordQ375]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep375, ws7WordCap375, ws7WordP375, ws7WordQ375]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep375, ws7WordCap375, ws7WordP375, ws7WordQ375]
  have hword := ws7Word375WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule218 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨218, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (3/28 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep5 i) ≤ ws7WordCap5 (ws7WordRep5 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep5, ws7WordCap5, ws7WordP5, ws7WordQ5]
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep5, ws7WordCap5, ws7WordP5, ws7WordQ5]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep5, ws7WordCap5, ws7WordP5, ws7WordQ5]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep5, ws7WordCap5, ws7WordP5, ws7WordQ5]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep5, ws7WordCap5, ws7WordP5, ws7WordQ5]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep5, ws7WordCap5, ws7WordP5, ws7WordQ5]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep5, ws7WordCap5, ws7WordP5, ws7WordQ5]
  have hword := ws7Word5WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule219 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨219, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (7/32 : ℝ)) ∧ (h 1 ≤ (2/17 : ℝ)) ∧ (h 2 ≤ (7/64 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep146 i) ≤ ws7WordCap146 (ws7WordRep146 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep146, ws7WordCap146, ws7WordP146, ws7WordQ146]
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep146, ws7WordCap146, ws7WordP146, ws7WordQ146]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep146, ws7WordCap146, ws7WordP146, ws7WordQ146]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep146, ws7WordCap146, ws7WordP146, ws7WordQ146]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep146, ws7WordCap146, ws7WordP146, ws7WordQ146]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep146, ws7WordCap146, ws7WordP146, ws7WordQ146]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep146, ws7WordCap146, ws7WordP146, ws7WordQ146]
  have hword := ws7Word146WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule220 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨220, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 1 ≤ (6/53 : ℝ)) ∧ (h 2 ≤ (7/62 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep166 i) ≤ ws7WordCap166 (ws7WordRep166 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep166, ws7WordCap166, ws7WordP166, ws7WordQ166]
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep166, ws7WordCap166, ws7WordP166, ws7WordQ166]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep166, ws7WordCap166, ws7WordP166, ws7WordQ166]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep166, ws7WordCap166, ws7WordP166, ws7WordQ166]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep166, ws7WordCap166, ws7WordP166, ws7WordQ166]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep166, ws7WordCap166, ws7WordP166, ws7WordQ166]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep166, ws7WordCap166, ws7WordP166, ws7WordQ166]
  have hword := ws7Word166WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule221 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨221, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (3/28 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep117 i) ≤ ws7WordCap117 (ws7WordRep117 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep117, ws7WordCap117, ws7WordP117, ws7WordQ117]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep117, ws7WordCap117, ws7WordP117, ws7WordQ117]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep117, ws7WordCap117, ws7WordP117, ws7WordQ117]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep117, ws7WordCap117, ws7WordP117, ws7WordQ117]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep117, ws7WordCap117, ws7WordP117, ws7WordQ117]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep117, ws7WordCap117, ws7WordP117, ws7WordQ117]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep117, ws7WordCap117, ws7WordP117, ws7WordQ117]
  have hword := ws7Word117WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule222 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨222, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (5/32 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (4/33 : ℝ)) ∧ (h 3 ≤ (6/53 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep156 i) ≤ ws7WordCap156 (ws7WordRep156 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep156, ws7WordCap156, ws7WordP156, ws7WordQ156]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep156, ws7WordCap156, ws7WordP156, ws7WordQ156]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep156, ws7WordCap156, ws7WordP156, ws7WordQ156]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep156, ws7WordCap156, ws7WordP156, ws7WordQ156]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep156, ws7WordCap156, ws7WordP156, ws7WordQ156]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep156, ws7WordCap156, ws7WordP156, ws7WordQ156]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep156, ws7WordCap156, ws7WordP156, ws7WordQ156]
  have hword := ws7Word156WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule223 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨223, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (7/50 : ℝ)) ∧ (h 2 ≤ (3/22 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep227 i) ≤ ws7WordCap227 (ws7WordRep227 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep227, ws7WordCap227, ws7WordP227, ws7WordQ227]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep227, ws7WordCap227, ws7WordP227, ws7WordQ227]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep227, ws7WordCap227, ws7WordP227, ws7WordQ227]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep227, ws7WordCap227, ws7WordP227, ws7WordQ227]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep227, ws7WordCap227, ws7WordP227, ws7WordQ227]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep227, ws7WordCap227, ws7WordP227, ws7WordQ227]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep227, ws7WordCap227, ws7WordP227, ws7WordQ227]
  have hword := ws7Word227WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule224 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨224, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (5/32 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep330 i) ≤ ws7WordCap330 (ws7WordRep330 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep330, ws7WordCap330, ws7WordP330, ws7WordQ330]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep330, ws7WordCap330, ws7WordP330, ws7WordQ330]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep330, ws7WordCap330, ws7WordP330, ws7WordQ330]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep330, ws7WordCap330, ws7WordP330, ws7WordQ330]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep330, ws7WordCap330, ws7WordP330, ws7WordQ330]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep330, ws7WordCap330, ws7WordP330, ws7WordQ330]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep330, ws7WordCap330, ws7WordP330, ws7WordQ330]
  have hword := ws7Word330WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule225 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨225, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (5/42 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep55 i) ≤ ws7WordCap55 (ws7WordRep55 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep55, ws7WordCap55, ws7WordP55, ws7WordQ55]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep55, ws7WordCap55, ws7WordP55, ws7WordQ55]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep55, ws7WordCap55, ws7WordP55, ws7WordQ55]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep55, ws7WordCap55, ws7WordP55, ws7WordQ55]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep55, ws7WordCap55, ws7WordP55, ws7WordQ55]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep55, ws7WordCap55, ws7WordP55, ws7WordQ55]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep55, ws7WordCap55, ws7WordP55, ws7WordQ55]
  have hword := ws7Word55WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule226 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨226, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (8/51 : ℝ)) ∧ (h 1 ≤ (5/32 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 3 ≤ (5/43 : ℝ)) ∧ (h 5 ≤ (3/26 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep90 i) ≤ ws7WordCap90 (ws7WordRep90 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep90, ws7WordCap90, ws7WordP90, ws7WordQ90]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep90, ws7WordCap90, ws7WordP90, ws7WordQ90]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep90, ws7WordCap90, ws7WordP90, ws7WordQ90]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep90, ws7WordCap90, ws7WordP90, ws7WordQ90]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep90, ws7WordCap90, ws7WordP90, ws7WordQ90]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep90, ws7WordCap90, ws7WordP90, ws7WordQ90]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep90, ws7WordCap90, ws7WordP90, ws7WordQ90]
  have hword := ws7Word90WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule227 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨227, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (7/33 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (5/37 : ℝ)) ∧ (h 2 ≤ (2/15 : ℝ)) ∧ (h 4 ≤ (4/37 : ℝ)) ∧ (h 5 ≤ (3/28 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep31 i) ≤ ws7WordCap31 (ws7WordRep31 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep31, ws7WordCap31, ws7WordP31, ws7WordQ31]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep31, ws7WordCap31, ws7WordP31, ws7WordQ31]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep31, ws7WordCap31, ws7WordP31, ws7WordQ31]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep31, ws7WordCap31, ws7WordP31, ws7WordQ31]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep31, ws7WordCap31, ws7WordP31, ws7WordQ31]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep31, ws7WordCap31, ws7WordP31, ws7WordQ31]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep31, ws7WordCap31, ws7WordP31, ws7WordQ31]
  have hword := ws7Word31WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule228 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨228, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (5/31 : ℝ)) ∧ (h 1 ≤ (6/43 : ℝ)) ∧ (h 2 ≤ (3/22 : ℝ)) ∧ (h 3 ≤ (5/43 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep61 i) ≤ ws7WordCap61 (ws7WordRep61 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep61, ws7WordCap61, ws7WordP61, ws7WordQ61]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep61, ws7WordCap61, ws7WordP61, ws7WordQ61]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep61, ws7WordCap61, ws7WordP61, ws7WordQ61]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep61, ws7WordCap61, ws7WordP61, ws7WordQ61]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep61, ws7WordCap61, ws7WordP61, ws7WordQ61]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep61, ws7WordCap61, ws7WordP61, ws7WordQ61]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep61, ws7WordCap61, ws7WordP61, ws7WordQ61]
  have hword := ws7Word61WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule229 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨229, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (5/33 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (5/41 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep116 i) ≤ ws7WordCap116 (ws7WordRep116 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep116, ws7WordCap116, ws7WordP116, ws7WordQ116]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep116, ws7WordCap116, ws7WordP116, ws7WordQ116]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep116, ws7WordCap116, ws7WordP116, ws7WordQ116]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep116, ws7WordCap116, ws7WordP116, ws7WordQ116]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep116, ws7WordCap116, ws7WordP116, ws7WordQ116]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep116, ws7WordCap116, ws7WordP116, ws7WordQ116]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep116, ws7WordCap116, ws7WordP116, ws7WordQ116]
  have hword := ws7Word116WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule230 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨230, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (7/48 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep80 i) ≤ ws7WordCap80 (ws7WordRep80 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep80, ws7WordCap80, ws7WordP80, ws7WordQ80]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep80, ws7WordCap80, ws7WordP80, ws7WordQ80]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep80, ws7WordCap80, ws7WordP80, ws7WordQ80]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep80, ws7WordCap80, ws7WordP80, ws7WordQ80]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep80, ws7WordCap80, ws7WordP80, ws7WordQ80]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep80, ws7WordCap80, ws7WordP80, ws7WordQ80]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep80, ws7WordCap80, ws7WordP80, ws7WordQ80]
  have hword := ws7Word80WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule231 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨231, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (7/33 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 2 ≤ (5/46 : ℝ)) ∧ (h 3 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep373 i) ≤ ws7WordCap373 (ws7WordRep373 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep373, ws7WordCap373, ws7WordP373, ws7WordQ373]
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep373, ws7WordCap373, ws7WordP373, ws7WordQ373]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep373, ws7WordCap373, ws7WordP373, ws7WordQ373]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep373, ws7WordCap373, ws7WordP373, ws7WordQ373]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep373, ws7WordCap373, ws7WordP373, ws7WordQ373]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep373, ws7WordCap373, ws7WordP373, ws7WordQ373]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep373, ws7WordCap373, ws7WordP373, ws7WordQ373]
  have hword := ws7Word373WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule232 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨232, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)) ∧ (h 0 ≤ (1/5 : ℝ)) ∧ (h 1 ≤ (4/29 : ℝ)) ∧ (h 2 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (3/29 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep8 i) ≤ ws7WordCap8 (ws7WordRep8 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep8, ws7WordCap8, ws7WordP8, ws7WordQ8]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep8, ws7WordCap8, ws7WordP8, ws7WordQ8]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep8, ws7WordCap8, ws7WordP8, ws7WordQ8]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep8, ws7WordCap8, ws7WordP8, ws7WordQ8]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep8, ws7WordCap8, ws7WordP8, ws7WordQ8]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep8, ws7WordCap8, ws7WordP8, ws7WordQ8]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep8, ws7WordCap8, ws7WordP8, ws7WordQ8]
  have hword := ws7Word8WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule233 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨233, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (7/33 : ℝ)) ∧ (h 0 ≤ (1/5 : ℝ)) ∧ (h 1 ≤ (6/47 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (5/47 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep78 i) ≤ ws7WordCap78 (ws7WordRep78 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep78, ws7WordCap78, ws7WordP78, ws7WordQ78]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep78, ws7WordCap78, ws7WordP78, ws7WordQ78]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep78, ws7WordCap78, ws7WordP78, ws7WordQ78]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep78, ws7WordCap78, ws7WordP78, ws7WordQ78]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep78, ws7WordCap78, ws7WordP78, ws7WordQ78]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep78, ws7WordCap78, ws7WordP78, ws7WordQ78]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep78, ws7WordCap78, ws7WordP78, ws7WordQ78]
  have hword := ws7Word78WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule234 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨234, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 1 ≤ (3/26 : ℝ)) ∧ (h 4 ≤ (3/28 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep203 i) ≤ ws7WordCap203 (ws7WordRep203 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep203, ws7WordCap203, ws7WordP203, ws7WordQ203]
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep203, ws7WordCap203, ws7WordP203, ws7WordQ203]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep203, ws7WordCap203, ws7WordP203, ws7WordQ203]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep203, ws7WordCap203, ws7WordP203, ws7WordQ203]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep203, ws7WordCap203, ws7WordP203, ws7WordQ203]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep203, ws7WordCap203, ws7WordP203, ws7WordQ203]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep203, ws7WordCap203, ws7WordP203, ws7WordQ203]
  have hword := ws7Word203WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule235 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨235, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 1 ≤ (2/17 : ℝ)) ∧ (h 2 ≤ (1/9 : ℝ)) ∧ (h 3 ≤ (3/28 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep374 i) ≤ ws7WordCap374 (ws7WordRep374 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep374, ws7WordCap374, ws7WordP374, ws7WordQ374]
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep374, ws7WordCap374, ws7WordP374, ws7WordQ374]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep374, ws7WordCap374, ws7WordP374, ws7WordQ374]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep374, ws7WordCap374, ws7WordP374, ws7WordQ374]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep374, ws7WordCap374, ws7WordP374, ws7WordQ374]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep374, ws7WordCap374, ws7WordP374, ws7WordQ374]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep374, ws7WordCap374, ws7WordP374, ws7WordQ374]
  have hword := ws7Word374WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule236 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨236, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (1/7 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ)) ∧ (h 4 ≤ (3/28 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep225 i) ≤ ws7WordCap225 (ws7WordRep225 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep225, ws7WordCap225, ws7WordP225, ws7WordQ225]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep225, ws7WordCap225, ws7WordP225, ws7WordQ225]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep225, ws7WordCap225, ws7WordP225, ws7WordQ225]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep225, ws7WordCap225, ws7WordP225, ws7WordQ225]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep225, ws7WordCap225, ws7WordP225, ws7WordQ225]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep225, ws7WordCap225, ws7WordP225, ws7WordQ225]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep225, ws7WordCap225, ws7WordP225, ws7WordQ225]
  have hword := ws7Word225WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule237 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨237, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (13/64 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (5/42 : ℝ)) ∧ (h 3 ≤ (9/79 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ)) ∧ (h 5 ≤ (3/28 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep254 i) ≤ ws7WordCap254 (ws7WordRep254 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep254, ws7WordCap254, ws7WordP254, ws7WordQ254]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep254, ws7WordCap254, ws7WordP254, ws7WordQ254]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep254, ws7WordCap254, ws7WordP254, ws7WordQ254]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep254, ws7WordCap254, ws7WordP254, ws7WordQ254]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep254, ws7WordCap254, ws7WordP254, ws7WordQ254]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep254, ws7WordCap254, ws7WordP254, ws7WordQ254]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep254, ws7WordCap254, ws7WordP254, ws7WordQ254]
  have hword := ws7Word254WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule238 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨238, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (5/41 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep196 i) ≤ ws7WordCap196 (ws7WordRep196 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep196, ws7WordCap196, ws7WordP196, ws7WordQ196]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep196, ws7WordCap196, ws7WordP196, ws7WordQ196]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep196, ws7WordCap196, ws7WordP196, ws7WordQ196]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep196, ws7WordCap196, ws7WordP196, ws7WordQ196]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep196, ws7WordCap196, ws7WordP196, ws7WordQ196]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep196, ws7WordCap196, ws7WordP196, ws7WordQ196]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep196, ws7WordCap196, ws7WordP196, ws7WordQ196]
  have hword := ws7Word196WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule239 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨239, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (9/44 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (9/70 : ℝ)) ∧ (h 3 ≤ (8/73 : ℝ)) ∧ (h 4 ≤ (3/29 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep357 i) ≤ ws7WordCap357 (ws7WordRep357 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep357, ws7WordCap357, ws7WordP357, ws7WordQ357]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep357, ws7WordCap357, ws7WordP357, ws7WordQ357]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep357, ws7WordCap357, ws7WordP357, ws7WordQ357]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep357, ws7WordCap357, ws7WordP357, ws7WordQ357]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep357, ws7WordCap357, ws7WordP357, ws7WordQ357]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep357, ws7WordCap357, ws7WordP357, ws7WordQ357]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep357, ws7WordCap357, ws7WordP357, ws7WordQ357]
  have hword := ws7Word357WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

end WeakSevenBandData
