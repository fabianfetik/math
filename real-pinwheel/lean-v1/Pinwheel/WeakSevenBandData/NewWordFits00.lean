import Pinwheel.WeakSevenBandData.WordSources
import Pinwheel.WeakSevenBandData.SourceFits
import Pinwheel.WeakSevenBandData.RateOrder
import Pinwheel.WeakSeven
import Mathlib.Tactic.FinCases

/-! Source-box adapters for literal weak words. -/

namespace RealPinwheel.WeakSevenBandData

theorem newWordFitSchedule0 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨0, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 1 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep0 i) ≤ ws7WordCap0 (ws7WordRep0 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep0, ws7WordCap0, ws7WordP0, ws7WordQ0]
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep0, ws7WordCap0, ws7WordP0, ws7WordQ0]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep0, ws7WordCap0, ws7WordP0, ws7WordQ0]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep0, ws7WordCap0, ws7WordP0, ws7WordQ0]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep0, ws7WordCap0, ws7WordP0, ws7WordQ0]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep0, ws7WordCap0, ws7WordP0, ws7WordQ0]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep0, ws7WordCap0, ws7WordP0, ws7WordQ0]
  have hword := ws7Word0WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule1 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨1, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep1 i) ≤ ws7WordCap1 (ws7WordRep1 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep1, ws7WordCap1, ws7WordP1, ws7WordQ1]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep1, ws7WordCap1, ws7WordP1, ws7WordQ1]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep1, ws7WordCap1, ws7WordP1, ws7WordQ1]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep1, ws7WordCap1, ws7WordP1, ws7WordQ1]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep1, ws7WordCap1, ws7WordP1, ws7WordQ1]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep1, ws7WordCap1, ws7WordP1, ws7WordQ1]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep1, ws7WordCap1, ws7WordP1, ws7WordQ1]
  have hword := ws7Word1WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule2 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨2, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 1 ≤ (3/25 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep2 i) ≤ ws7WordCap2 (ws7WordRep2 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep2, ws7WordCap2, ws7WordP2, ws7WordQ2]
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep2, ws7WordCap2, ws7WordP2, ws7WordQ2]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep2, ws7WordCap2, ws7WordP2, ws7WordQ2]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep2, ws7WordCap2, ws7WordP2, ws7WordQ2]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep2, ws7WordCap2, ws7WordP2, ws7WordQ2]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep2, ws7WordCap2, ws7WordP2, ws7WordQ2]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep2, ws7WordCap2, ws7WordP2, ws7WordQ2]
  have hword := ws7Word2WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule3 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨3, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)) ∧ (h 0 ≤ (5/26 : ℝ)) ∧ (h 1 ≤ (3/26 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep3 i) ≤ ws7WordCap3 (ws7WordRep3 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep3, ws7WordCap3, ws7WordP3, ws7WordQ3]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep3, ws7WordCap3, ws7WordP3, ws7WordQ3]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep3, ws7WordCap3, ws7WordP3, ws7WordQ3]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep3, ws7WordCap3, ws7WordP3, ws7WordQ3]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep3, ws7WordCap3, ws7WordP3, ws7WordQ3]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep3, ws7WordCap3, ws7WordP3, ws7WordQ3]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep3, ws7WordCap3, ws7WordP3, ws7WordQ3]
  have hword := ws7Word3WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule4 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨4, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 0 ≤ (5/28 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 3 ≤ (3/28 : ℝ)) ∧ (h 4 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep4 i) ≤ ws7WordCap4 (ws7WordRep4 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep4, ws7WordCap4, ws7WordP4, ws7WordQ4]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep4, ws7WordCap4, ws7WordP4, ws7WordQ4]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep4, ws7WordCap4, ws7WordP4, ws7WordQ4]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep4, ws7WordCap4, ws7WordP4, ws7WordQ4]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep4, ws7WordCap4, ws7WordP4, ws7WordQ4]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep4, ws7WordCap4, ws7WordP4, ws7WordQ4]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep4, ws7WordCap4, ws7WordP4, ws7WordQ4]
  have hword := ws7Word4WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule5 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨5, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (3/17 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (3/28 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep6 i) ≤ ws7WordCap6 (ws7WordRep6 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep6, ws7WordCap6, ws7WordP6, ws7WordQ6]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep6, ws7WordCap6, ws7WordP6, ws7WordQ6]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep6, ws7WordCap6, ws7WordP6, ws7WordQ6]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep6, ws7WordCap6, ws7WordP6, ws7WordQ6]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep6, ws7WordCap6, ws7WordP6, ws7WordQ6]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep6, ws7WordCap6, ws7WordP6, ws7WordQ6]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep6, ws7WordCap6, ws7WordP6, ws7WordQ6]
  have hword := ws7Word6WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule6 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨6, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 0 ≤ (5/29 : ℝ)) ∧ (h 1 ≤ (1/6 : ℝ)) ∧ (h 2 ≤ (3/22 : ℝ)) ∧ (h 3 ≤ (3/29 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep9 i) ≤ ws7WordCap9 (ws7WordRep9 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep9, ws7WordCap9, ws7WordP9, ws7WordQ9]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep9, ws7WordCap9, ws7WordP9, ws7WordQ9]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep9, ws7WordCap9, ws7WordP9, ws7WordQ9]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep9, ws7WordCap9, ws7WordP9, ws7WordQ9]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep9, ws7WordCap9, ws7WordP9, ws7WordQ9]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep9, ws7WordCap9, ws7WordP9, ws7WordQ9]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep9, ws7WordCap9, ws7WordP9, ws7WordQ9]
  have hword := ws7Word9WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule7 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨7, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)) ∧ (h 0 ≤ (5/29 : ℝ)) ∧ (h 1 ≤ (4/29 : ℝ)) ∧ (h 4 ≤ (3/29 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep10 i) ≤ ws7WordCap10 (ws7WordRep10 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep10, ws7WordCap10, ws7WordP10, ws7WordQ10]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep10, ws7WordCap10, ws7WordP10, ws7WordQ10]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep10, ws7WordCap10, ws7WordP10, ws7WordQ10]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep10, ws7WordCap10, ws7WordP10, ws7WordQ10]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep10, ws7WordCap10, ws7WordP10, ws7WordQ10]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep10, ws7WordCap10, ws7WordP10, ws7WordQ10]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep10, ws7WordCap10, ws7WordP10, ws7WordQ10]
  have hword := ws7Word10WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule8 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨8, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (3/29 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep11 i) ≤ ws7WordCap11 (ws7WordRep11 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep11, ws7WordCap11, ws7WordP11, ws7WordQ11]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep11, ws7WordCap11, ws7WordP11, ws7WordQ11]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep11, ws7WordCap11, ws7WordP11, ws7WordQ11]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep11, ws7WordCap11, ws7WordP11, ws7WordQ11]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep11, ws7WordCap11, ws7WordP11, ws7WordQ11]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep11, ws7WordCap11, ws7WordP11, ws7WordQ11]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep11, ws7WordCap11, ws7WordP11, ws7WordQ11]
  have hword := ws7Word11WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule9 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨9, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 3 ≤ (1/10 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep12 i) ≤ ws7WordCap12 (ws7WordRep12 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep12, ws7WordCap12, ws7WordP12, ws7WordQ12]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep12, ws7WordCap12, ws7WordP12, ws7WordQ12]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep12, ws7WordCap12, ws7WordP12, ws7WordQ12]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep12, ws7WordCap12, ws7WordP12, ws7WordQ12]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep12, ws7WordCap12, ws7WordP12, ws7WordQ12]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep12, ws7WordCap12, ws7WordP12, ws7WordQ12]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep12, ws7WordCap12, ws7WordP12, ws7WordQ12]
  have hword := ws7Word12WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule10 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨10, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 4 ≤ (1/8 : ℝ)) ∧ (h 5 ≤ (1/10 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep13 i) ≤ ws7WordCap13 (ws7WordRep13 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep13, ws7WordCap13, ws7WordP13, ws7WordQ13]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep13, ws7WordCap13, ws7WordP13, ws7WordQ13]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep13, ws7WordCap13, ws7WordP13, ws7WordQ13]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep13, ws7WordCap13, ws7WordP13, ws7WordQ13]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep13, ws7WordCap13, ws7WordP13, ws7WordQ13]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep13, ws7WordCap13, ws7WordP13, ws7WordQ13]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep13, ws7WordCap13, ws7WordP13, ws7WordQ13]
  have hword := ws7Word13WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule11 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨11, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (7/33 : ℝ)) ∧ (h 0 ≤ (5/33 : ℝ)) ∧ (h 1 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (4/33 : ℝ)) ∧ (h 3 ≤ (3/25 : ℝ)) ∧ (h 5 ≤ (2/17 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep15 i) ≤ ws7WordCap15 (ws7WordRep15 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep15, ws7WordCap15, ws7WordP15, ws7WordQ15]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep15, ws7WordCap15, ws7WordP15, ws7WordQ15]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep15, ws7WordCap15, ws7WordP15, ws7WordQ15]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep15, ws7WordCap15, ws7WordP15, ws7WordQ15]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep15, ws7WordCap15, ws7WordP15, ws7WordQ15]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep15, ws7WordCap15, ws7WordP15, ws7WordQ15]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep15, ws7WordCap15, ws7WordP15, ws7WordQ15]
  have hword := ws7Word15WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule12 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨12, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (7/33 : ℝ)) ∧ (h 0 ≤ (2/11 : ℝ)) ∧ (h 1 ≤ (4/33 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep16 i) ≤ ws7WordCap16 (ws7WordRep16 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep16, ws7WordCap16, ws7WordP16, ws7WordQ16]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep16, ws7WordCap16, ws7WordP16, ws7WordQ16]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep16, ws7WordCap16, ws7WordP16, ws7WordQ16]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep16, ws7WordCap16, ws7WordP16, ws7WordQ16]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep16, ws7WordCap16, ws7WordP16, ws7WordQ16]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep16, ws7WordCap16, ws7WordP16, ws7WordQ16]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep16, ws7WordCap16, ws7WordP16, ws7WordQ16]
  have hword := ws7Word16WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule13 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨13, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)) ∧ (h 0 ≤ (4/23 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep17 i) ≤ ws7WordCap17 (ws7WordRep17 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep17, ws7WordCap17, ws7WordP17, ws7WordQ17]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep17, ws7WordCap17, ws7WordP17, ws7WordQ17]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep17, ws7WordCap17, ws7WordP17, ws7WordQ17]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep17, ws7WordCap17, ws7WordP17, ws7WordQ17]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep17, ws7WordCap17, ws7WordP17, ws7WordQ17]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep17, ws7WordCap17, ws7WordP17, ws7WordQ17]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep17, ws7WordCap17, ws7WordP17, ws7WordQ17]
  have hword := ws7Word17WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule14 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨14, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)) ∧ (h 0 ≤ (5/34 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (3/26 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep18 i) ≤ ws7WordCap18 (ws7WordRep18 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep18, ws7WordCap18, ws7WordP18, ws7WordQ18]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep18, ws7WordCap18, ws7WordP18, ws7WordQ18]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep18, ws7WordCap18, ws7WordP18, ws7WordQ18]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep18, ws7WordCap18, ws7WordP18, ws7WordQ18]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep18, ws7WordCap18, ws7WordP18, ws7WordQ18]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep18, ws7WordCap18, ws7WordP18, ws7WordQ18]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep18, ws7WordCap18, ws7WordP18, ws7WordQ18]
  have hword := ws7Word18WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule15 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨15, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (3/26 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep19 i) ≤ ws7WordCap19 (ws7WordRep19 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep19, ws7WordCap19, ws7WordP19, ws7WordQ19]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep19, ws7WordCap19, ws7WordP19, ws7WordQ19]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep19, ws7WordCap19, ws7WordP19, ws7WordQ19]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep19, ws7WordCap19, ws7WordP19, ws7WordQ19]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep19, ws7WordCap19, ws7WordP19, ws7WordQ19]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep19, ws7WordCap19, ws7WordP19, ws7WordQ19]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep19, ws7WordCap19, ws7WordP19, ws7WordQ19]
  have hword := ws7Word19WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule16 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨16, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (8/35 : ℝ)) ∧ (h 0 ≤ (6/35 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (4/35 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep21 i) ≤ ws7WordCap21 (ws7WordRep21 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep21, ws7WordCap21, ws7WordP21, ws7WordQ21]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep21, ws7WordCap21, ws7WordP21, ws7WordQ21]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep21, ws7WordCap21, ws7WordP21, ws7WordQ21]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep21, ws7WordCap21, ws7WordP21, ws7WordQ21]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep21, ws7WordCap21, ws7WordP21, ws7WordQ21]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep21, ws7WordCap21, ws7WordP21, ws7WordQ21]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep21, ws7WordCap21, ws7WordP21, ws7WordQ21]
  have hword := ws7Word21WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule17 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨17, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 0 ≤ (6/35 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (3/22 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep22 i) ≤ ws7WordCap22 (ws7WordRep22 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep22, ws7WordCap22, ws7WordP22, ws7WordQ22]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep22, ws7WordCap22, ws7WordP22, ws7WordQ22]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep22, ws7WordCap22, ws7WordP22, ws7WordQ22]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep22, ws7WordCap22, ws7WordP22, ws7WordQ22]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep22, ws7WordCap22, ws7WordP22, ws7WordQ22]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep22, ws7WordCap22, ws7WordP22, ws7WordQ22]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep22, ws7WordCap22, ws7WordP22, ws7WordQ22]
  have hword := ws7Word22WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule18 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨18, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 0 ≤ (6/35 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep23 i) ≤ ws7WordCap23 (ws7WordRep23 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep23, ws7WordCap23, ws7WordP23, ws7WordQ23]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep23, ws7WordCap23, ws7WordP23, ws7WordQ23]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep23, ws7WordCap23, ws7WordP23, ws7WordQ23]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep23, ws7WordCap23, ws7WordP23, ws7WordQ23]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep23, ws7WordCap23, ws7WordP23, ws7WordQ23]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep23, ws7WordCap23, ws7WordP23, ws7WordQ23]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep23, ws7WordCap23, ws7WordP23, ws7WordQ23]
  have hword := ws7Word23WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule19 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨19, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (6/35 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep24 i) ≤ ws7WordCap24 (ws7WordRep24 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep24, ws7WordCap24, ws7WordP24, ws7WordQ24]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep24, ws7WordCap24, ws7WordP24, ws7WordQ24]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep24, ws7WordCap24, ws7WordP24, ws7WordQ24]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep24, ws7WordCap24, ws7WordP24, ws7WordQ24]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep24, ws7WordCap24, ws7WordP24, ws7WordQ24]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep24, ws7WordCap24, ws7WordP24, ws7WordQ24]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep24, ws7WordCap24, ws7WordP24, ws7WordQ24]
  have hword := ws7Word24WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule20 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨20, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (6/31 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep25 i) ≤ ws7WordCap25 (ws7WordRep25 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep25, ws7WordCap25, ws7WordP25, ws7WordQ25]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep25, ws7WordCap25, ws7WordP25, ws7WordQ25]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep25, ws7WordCap25, ws7WordP25, ws7WordQ25]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep25, ws7WordCap25, ws7WordP25, ws7WordQ25]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep25, ws7WordCap25, ws7WordP25, ws7WordQ25]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep25, ws7WordCap25, ws7WordP25, ws7WordQ25]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep25, ws7WordCap25, ws7WordP25, ws7WordQ25]
  have hword := ws7Word25WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule21 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨21, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (5/26 : ℝ)) ∧ (h 1 ≤ (5/36 : ℝ)) ∧ (h 2 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep26 i) ≤ ws7WordCap26 (ws7WordRep26 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep26, ws7WordCap26, ws7WordP26, ws7WordQ26]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep26, ws7WordCap26, ws7WordP26, ws7WordQ26]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep26, ws7WordCap26, ws7WordP26, ws7WordQ26]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep26, ws7WordCap26, ws7WordP26, ws7WordQ26]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep26, ws7WordCap26, ws7WordP26, ws7WordQ26]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep26, ws7WordCap26, ws7WordP26, ws7WordQ26]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep26, ws7WordCap26, ws7WordP26, ws7WordQ26]
  have hword := ws7Word26WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule22 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨22, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (5/36 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep28 i) ≤ ws7WordCap28 (ws7WordRep28 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep28, ws7WordCap28, ws7WordP28, ws7WordQ28]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep28, ws7WordCap28, ws7WordP28, ws7WordQ28]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep28, ws7WordCap28, ws7WordP28, ws7WordQ28]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep28, ws7WordCap28, ws7WordP28, ws7WordQ28]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep28, ws7WordCap28, ws7WordP28, ws7WordQ28]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep28, ws7WordCap28, ws7WordP28, ws7WordQ28]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep28, ws7WordCap28, ws7WordP28, ws7WordQ28]
  have hword := ws7Word28WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule23 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨23, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (7/33 : ℝ)) ∧ (h 0 ≤ (5/37 : ℝ)) ∧ (h 2 ≤ (2/15 : ℝ)) ∧ (h 5 ≤ (4/37 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep29 i) ≤ ws7WordCap29 (ws7WordRep29 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep29, ws7WordCap29, ws7WordP29, ws7WordQ29]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep29, ws7WordCap29, ws7WordP29, ws7WordQ29]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep29, ws7WordCap29, ws7WordP29, ws7WordQ29]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep29, ws7WordCap29, ws7WordP29, ws7WordQ29]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep29, ws7WordCap29, ws7WordP29, ws7WordQ29]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep29, ws7WordCap29, ws7WordP29, ws7WordQ29]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep29, ws7WordCap29, ws7WordP29, ws7WordQ29]
  have hword := ws7Word29WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule24 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨24, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (3/23 : ℝ)) ∧ (h 4 ≤ (4/37 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep30 i) ≤ ws7WordCap30 (ws7WordRep30 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep30, ws7WordCap30, ws7WordP30, ws7WordQ30]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep30, ws7WordCap30, ws7WordP30, ws7WordQ30]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep30, ws7WordCap30, ws7WordP30, ws7WordQ30]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep30, ws7WordCap30, ws7WordP30, ws7WordQ30]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep30, ws7WordCap30, ws7WordP30, ws7WordQ30]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep30, ws7WordCap30, ws7WordP30, ws7WordQ30]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep30, ws7WordCap30, ws7WordP30, ws7WordQ30]
  have hword := ws7Word30WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule25 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨25, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (8/37 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (4/37 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep32 i) ≤ ws7WordCap32 (ws7WordRep32 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep32, ws7WordCap32, ws7WordP32, ws7WordQ32]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep32, ws7WordCap32, ws7WordP32, ws7WordQ32]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep32, ws7WordCap32, ws7WordP32, ws7WordQ32]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep32, ws7WordCap32, ws7WordP32, ws7WordQ32]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep32, ws7WordCap32, ws7WordP32, ws7WordQ32]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep32, ws7WordCap32, ws7WordP32, ws7WordQ32]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep32, ws7WordCap32, ws7WordP32, ws7WordQ32]
  have hword := ws7Word32WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule26 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨26, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (8/37 : ℝ)) ∧ (h 0 ≤ (6/37 : ℝ)) ∧ (h 1 ≤ (4/25 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (4/37 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep34 i) ≤ ws7WordCap34 (ws7WordRep34 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep34, ws7WordCap34, ws7WordP34, ws7WordQ34]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep34, ws7WordCap34, ws7WordP34, ws7WordQ34]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep34, ws7WordCap34, ws7WordP34, ws7WordQ34]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep34, ws7WordCap34, ws7WordP34, ws7WordQ34]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep34, ws7WordCap34, ws7WordP34, ws7WordQ34]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep34, ws7WordCap34, ws7WordP34, ws7WordQ34]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep34, ws7WordCap34, ws7WordP34, ws7WordQ34]
  have hword := ws7Word34WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule27 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨27, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 0 ≤ (2/11 : ℝ)) ∧ (h 1 ≤ (5/38 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (2/19 : ℝ)) ∧ (h 5 ≤ (3/29 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep35 i) ≤ ws7WordCap35 (ws7WordRep35 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep35, ws7WordCap35, ws7WordP35, ws7WordQ35]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep35, ws7WordCap35, ws7WordP35, ws7WordQ35]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep35, ws7WordCap35, ws7WordP35, ws7WordQ35]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep35, ws7WordCap35, ws7WordP35, ws7WordQ35]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep35, ws7WordCap35, ws7WordP35, ws7WordQ35]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep35, ws7WordCap35, ws7WordP35, ws7WordQ35]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep35, ws7WordCap35, ws7WordP35, ws7WordQ35]
  have hword := ws7Word35WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule28 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨28, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (5/38 : ℝ)) ∧ (h 4 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep36 i) ≤ ws7WordCap36 (ws7WordRep36 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep36, ws7WordCap36, ws7WordP36, ws7WordQ36]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep36, ws7WordCap36, ws7WordP36, ws7WordQ36]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep36, ws7WordCap36, ws7WordP36, ws7WordQ36]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep36, ws7WordCap36, ws7WordP36, ws7WordQ36]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep36, ws7WordCap36, ws7WordP36, ws7WordQ36]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep36, ws7WordCap36, ws7WordP36, ws7WordQ36]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep36, ws7WordCap36, ws7WordP36, ws7WordQ36]
  have hword := ws7Word36WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule29 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨29, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)) ∧ (h 0 ≤ (2/11 : ℝ)) ∧ (h 1 ≤ (4/27 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep37 i) ≤ ws7WordCap37 (ws7WordRep37 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep37, ws7WordCap37, ws7WordP37, ws7WordQ37]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep37, ws7WordCap37, ws7WordP37, ws7WordQ37]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep37, ws7WordCap37, ws7WordP37, ws7WordQ37]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep37, ws7WordCap37, ws7WordP37, ws7WordQ37]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep37, ws7WordCap37, ws7WordP37, ws7WordQ37]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep37, ws7WordCap37, ws7WordP37, ws7WordQ37]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep37, ws7WordCap37, ws7WordP37, ws7WordQ37]
  have hword := ws7Word37WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule30 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨30, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (5/38 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep38 i) ≤ ws7WordCap38 (ws7WordRep38 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep38, ws7WordCap38, ws7WordP38, ws7WordQ38]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep38, ws7WordCap38, ws7WordP38, ws7WordQ38]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep38, ws7WordCap38, ws7WordP38, ws7WordQ38]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep38, ws7WordCap38, ws7WordP38, ws7WordQ38]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep38, ws7WordCap38, ws7WordP38, ws7WordQ38]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep38, ws7WordCap38, ws7WordP38, ws7WordQ38]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep38, ws7WordCap38, ws7WordP38, ws7WordQ38]
  have hword := ws7Word38WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule31 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨31, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 3 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep39 i) ≤ ws7WordCap39 (ws7WordRep39 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep39, ws7WordCap39, ws7WordP39, ws7WordQ39]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep39, ws7WordCap39, ws7WordP39, ws7WordQ39]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep39, ws7WordCap39, ws7WordP39, ws7WordQ39]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep39, ws7WordCap39, ws7WordP39, ws7WordQ39]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep39, ws7WordCap39, ws7WordP39, ws7WordQ39]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep39, ws7WordCap39, ws7WordP39, ws7WordQ39]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep39, ws7WordCap39, ws7WordP39, ws7WordQ39]
  have hword := ws7Word39WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule32 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨32, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (8/39 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (5/39 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep40 i) ≤ ws7WordCap40 (ws7WordRep40 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep40, ws7WordCap40, ws7WordP40, ws7WordQ40]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep40, ws7WordCap40, ws7WordP40, ws7WordQ40]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep40, ws7WordCap40, ws7WordP40, ws7WordQ40]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep40, ws7WordCap40, ws7WordP40, ws7WordQ40]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep40, ws7WordCap40, ws7WordP40, ws7WordQ40]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep40, ws7WordCap40, ws7WordP40, ws7WordQ40]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep40, ws7WordCap40, ws7WordP40, ws7WordQ40]
  have hword := ws7Word40WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule33 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨33, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (4/39 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep41 i) ≤ ws7WordCap41 (ws7WordRep41 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep41, ws7WordCap41, ws7WordP41, ws7WordQ41]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep41, ws7WordCap41, ws7WordP41, ws7WordQ41]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep41, ws7WordCap41, ws7WordP41, ws7WordQ41]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep41, ws7WordCap41, ws7WordP41, ws7WordQ41]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep41, ws7WordCap41, ws7WordP41, ws7WordQ41]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep41, ws7WordCap41, ws7WordP41, ws7WordQ41]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep41, ws7WordCap41, ws7WordP41, ws7WordQ41]
  have hword := ws7Word41WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule34 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨34, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 0 ≤ (3/17 : ℝ)) ∧ (h 1 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (1/7 : ℝ)) ∧ (h 3 ≤ (4/39 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep42 i) ≤ ws7WordCap42 (ws7WordRep42 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep42, ws7WordCap42, ws7WordP42, ws7WordQ42]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep42, ws7WordCap42, ws7WordP42, ws7WordQ42]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep42, ws7WordCap42, ws7WordP42, ws7WordQ42]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep42, ws7WordCap42, ws7WordP42, ws7WordQ42]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep42, ws7WordCap42, ws7WordP42, ws7WordQ42]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep42, ws7WordCap42, ws7WordP42, ws7WordQ42]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep42, ws7WordCap42, ws7WordP42, ws7WordQ42]
  have hword := ws7Word42WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule35 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨35, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (8/39 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (3/20 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (4/39 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep43 i) ≤ ws7WordCap43 (ws7WordRep43 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep43, ws7WordCap43, ws7WordP43, ws7WordQ43]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep43, ws7WordCap43, ws7WordP43, ws7WordQ43]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep43, ws7WordCap43, ws7WordP43, ws7WordQ43]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep43, ws7WordCap43, ws7WordP43, ws7WordQ43]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep43, ws7WordCap43, ws7WordP43, ws7WordQ43]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep43, ws7WordCap43, ws7WordP43, ws7WordQ43]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep43, ws7WordCap43, ws7WordP43, ws7WordQ43]
  have hword := ws7Word43WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule36 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨36, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 0 ≤ (4/23 : ℝ)) ∧ (h 1 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (5/39 : ℝ)) ∧ (h 4 ≤ (4/39 : ℝ)) ∧ (h 5 ≤ (1/10 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep44 i) ≤ ws7WordCap44 (ws7WordRep44 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep44, ws7WordCap44, ws7WordP44, ws7WordQ44]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep44, ws7WordCap44, ws7WordP44, ws7WordQ44]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep44, ws7WordCap44, ws7WordP44, ws7WordQ44]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep44, ws7WordCap44, ws7WordP44, ws7WordQ44]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep44, ws7WordCap44, ws7WordP44, ws7WordQ44]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep44, ws7WordCap44, ws7WordP44, ws7WordQ44]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep44, ws7WordCap44, ws7WordP44, ws7WordQ44]
  have hword := ws7Word44WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule37 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨37, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep46 i) ≤ ws7WordCap46 (ws7WordRep46 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep46, ws7WordCap46, ws7WordP46, ws7WordQ46]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep46, ws7WordCap46, ws7WordP46, ws7WordQ46]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep46, ws7WordCap46, ws7WordP46, ws7WordQ46]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep46, ws7WordCap46, ws7WordP46, ws7WordQ46]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep46, ws7WordCap46, ws7WordP46, ws7WordQ46]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep46, ws7WordCap46, ws7WordP46, ws7WordQ46]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep46, ws7WordCap46, ws7WordP46, ws7WordQ46]
  have hword := ws7Word46WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule38 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨38, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (1/7 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 5 ≤ (1/10 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep47 i) ≤ ws7WordCap47 (ws7WordRep47 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep47, ws7WordCap47, ws7WordP47, ws7WordQ47]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep47, ws7WordCap47, ws7WordP47, ws7WordQ47]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep47, ws7WordCap47, ws7WordP47, ws7WordQ47]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep47, ws7WordCap47, ws7WordP47, ws7WordQ47]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep47, ws7WordCap47, ws7WordP47, ws7WordQ47]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep47, ws7WordCap47, ws7WordP47, ws7WordQ47]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep47, ws7WordCap47, ws7WordP47, ws7WordQ47]
  have hword := ws7Word47WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule39 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨39, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 1 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (1/10 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep49 i) ≤ ws7WordCap49 (ws7WordRep49 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep49, ws7WordCap49, ws7WordP49, ws7WordQ49]
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep49, ws7WordCap49, ws7WordP49, ws7WordQ49]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep49, ws7WordCap49, ws7WordP49, ws7WordQ49]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep49, ws7WordCap49, ws7WordP49, ws7WordQ49]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep49, ws7WordCap49, ws7WordP49, ws7WordQ49]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep49, ws7WordCap49, ws7WordP49, ws7WordQ49]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep49, ws7WordCap49, ws7WordP49, ws7WordQ49]
  have hword := ws7Word49WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

end WeakSevenBandData
