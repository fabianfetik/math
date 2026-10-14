import Pinwheel.WeakSevenBandData.NewWordFits03
import Pinwheel.WeakSevenBandData.SourceFits
import Pinwheel.WeakSevenBandData.RateOrder
import Pinwheel.WeakSeven
import Mathlib.Tactic.FinCases

/-! Source-box adapters for literal weak words. -/

namespace RealPinwheel.WeakSevenBandData

theorem newWordFitSchedule160 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨160, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 4 ≤ (3/28 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep229 i) ≤ ws7WordCap229 (ws7WordRep229 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep229, ws7WordCap229, ws7WordP229, ws7WordQ229]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep229, ws7WordCap229, ws7WordP229, ws7WordQ229]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep229, ws7WordCap229, ws7WordP229, ws7WordQ229]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep229, ws7WordCap229, ws7WordP229, ws7WordQ229]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep229, ws7WordCap229, ws7WordP229, ws7WordQ229]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep229, ws7WordCap229, ws7WordP229, ws7WordQ229]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep229, ws7WordCap229, ws7WordP229, ws7WordQ229]
  have hword := ws7Word229WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule161 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨161, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 1 ≤ (6/43 : ℝ)) ∧ (h 2 ≤ (4/29 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (1/10 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep230 i) ≤ ws7WordCap230 (ws7WordRep230 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep230, ws7WordCap230, ws7WordP230, ws7WordQ230]
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep230, ws7WordCap230, ws7WordP230, ws7WordQ230]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep230, ws7WordCap230, ws7WordP230, ws7WordQ230]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep230, ws7WordCap230, ws7WordP230, ws7WordQ230]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep230, ws7WordCap230, ws7WordP230, ws7WordQ230]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep230, ws7WordCap230, ws7WordP230, ws7WordQ230]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep230, ws7WordCap230, ws7WordP230, ws7WordQ230]
  have hword := ws7Word230WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule162 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨162, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (7/33 : ℝ)) ∧ (h 0 ≤ (5/32 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (5/39 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 4 ≤ (3/28 : ℝ)) ∧ (h 5 ≤ (3/29 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep231 i) ≤ ws7WordCap231 (ws7WordRep231 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep231, ws7WordCap231, ws7WordP231, ws7WordQ231]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep231, ws7WordCap231, ws7WordP231, ws7WordQ231]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep231, ws7WordCap231, ws7WordP231, ws7WordQ231]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep231, ws7WordCap231, ws7WordP231, ws7WordQ231]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep231, ws7WordCap231, ws7WordP231, ws7WordQ231]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep231, ws7WordCap231, ws7WordP231, ws7WordQ231]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep231, ws7WordCap231, ws7WordP231, ws7WordQ231]
  have hword := ws7Word231WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule163 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨163, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)) ∧ (h 0 ≤ (3/17 : ℝ)) ∧ (h 1 ≤ (1/6 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 3 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep232 i) ≤ ws7WordCap232 (ws7WordRep232 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep232, ws7WordCap232, ws7WordP232, ws7WordQ232]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep232, ws7WordCap232, ws7WordP232, ws7WordQ232]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep232, ws7WordCap232, ws7WordP232, ws7WordQ232]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep232, ws7WordCap232, ws7WordP232, ws7WordQ232]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep232, ws7WordCap232, ws7WordP232, ws7WordQ232]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep232, ws7WordCap232, ws7WordP232, ws7WordQ232]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep232, ws7WordCap232, ws7WordP232, ws7WordQ232]
  have hword := ws7Word232WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule164 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨164, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep233 i) ≤ ws7WordCap233 (ws7WordRep233 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep233, ws7WordCap233, ws7WordP233, ws7WordQ233]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep233, ws7WordCap233, ws7WordP233, ws7WordQ233]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep233, ws7WordCap233, ws7WordP233, ws7WordQ233]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep233, ws7WordCap233, ws7WordP233, ws7WordQ233]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep233, ws7WordCap233, ws7WordP233, ws7WordQ233]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep233, ws7WordCap233, ws7WordP233, ws7WordQ233]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep233, ws7WordCap233, ws7WordP233, ws7WordQ233]
  have hword := ws7Word233WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule165 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨165, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (3/17 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (2/19 : ℝ)) ∧ (h 5 ≤ (4/39 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep234 i) ≤ ws7WordCap234 (ws7WordRep234 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep234, ws7WordCap234, ws7WordP234, ws7WordQ234]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep234, ws7WordCap234, ws7WordP234, ws7WordQ234]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep234, ws7WordCap234, ws7WordP234, ws7WordQ234]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep234, ws7WordCap234, ws7WordP234, ws7WordQ234]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep234, ws7WordCap234, ws7WordP234, ws7WordQ234]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep234, ws7WordCap234, ws7WordP234, ws7WordQ234]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep234, ws7WordCap234, ws7WordP234, ws7WordQ234]
  have hword := ws7Word234WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule166 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨166, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)) ∧ (h 0 ≤ (5/26 : ℝ)) ∧ (h 1 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (3/26 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ)) ∧ (h 4 ≤ (3/29 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep235 i) ≤ ws7WordCap235 (ws7WordRep235 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep235, ws7WordCap235, ws7WordP235, ws7WordQ235]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep235, ws7WordCap235, ws7WordP235, ws7WordQ235]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep235, ws7WordCap235, ws7WordP235, ws7WordQ235]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep235, ws7WordCap235, ws7WordP235, ws7WordQ235]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep235, ws7WordCap235, ws7WordP235, ws7WordQ235]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep235, ws7WordCap235, ws7WordP235, ws7WordQ235]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep235, ws7WordCap235, ws7WordP235, ws7WordQ235]
  have hword := ws7Word235WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule167 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨167, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (4/27 : ℝ)) ∧ (h 1 ≤ (4/31 : ℝ)) ∧ (h 3 ≤ (8/63 : ℝ)) ∧ (h 4 ≤ (5/43 : ℝ)) ∧ (h 5 ≤ (9/89 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep238 i) ≤ ws7WordCap238 (ws7WordRep238 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep238, ws7WordCap238, ws7WordP238, ws7WordQ238]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep238, ws7WordCap238, ws7WordP238, ws7WordQ238]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep238, ws7WordCap238, ws7WordP238, ws7WordQ238]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep238, ws7WordCap238, ws7WordP238, ws7WordQ238]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep238, ws7WordCap238, ws7WordP238, ws7WordQ238]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep238, ws7WordCap238, ws7WordP238, ws7WordQ238]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep238, ws7WordCap238, ws7WordP238, ws7WordQ238]
  have hword := ws7Word238WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule168 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨168, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (8/39 : ℝ)) ∧ (h 0 ≤ (8/47 : ℝ)) ∧ (h 1 ≤ (4/27 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 3 ≤ (6/55 : ℝ)) ∧ (h 4 ≤ (3/28 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep241 i) ≤ ws7WordCap241 (ws7WordRep241 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep241, ws7WordCap241, ws7WordP241, ws7WordQ241]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep241, ws7WordCap241, ws7WordP241, ws7WordQ241]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep241, ws7WordCap241, ws7WordP241, ws7WordQ241]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep241, ws7WordCap241, ws7WordP241, ws7WordQ241]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep241, ws7WordCap241, ws7WordP241, ws7WordQ241]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep241, ws7WordCap241, ws7WordP241, ws7WordQ241]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep241, ws7WordCap241, ws7WordP241, ws7WordQ241]
  have hword := ws7Word241WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule169 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨169, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)) ∧ (h 0 ≤ (4/23 : ℝ)) ∧ (h 1 ≤ (14/109 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep244 i) ≤ ws7WordCap244 (ws7WordRep244 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep244, ws7WordCap244, ws7WordP244, ws7WordQ244]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep244, ws7WordCap244, ws7WordP244, ws7WordQ244]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep244, ws7WordCap244, ws7WordP244, ws7WordQ244]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep244, ws7WordCap244, ws7WordP244, ws7WordQ244]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep244, ws7WordCap244, ws7WordP244, ws7WordQ244]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep244, ws7WordCap244, ws7WordP244, ws7WordQ244]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep244, ws7WordCap244, ws7WordP244, ws7WordQ244]
  have hword := ws7Word244WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule170 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨170, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (8/39 : ℝ)) ∧ (h 0 ≤ (15/89 : ℝ)) ∧ (h 1 ≤ (11/87 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep246 i) ≤ ws7WordCap246 (ws7WordRep246 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep246, ws7WordCap246, ws7WordP246, ws7WordQ246]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep246, ws7WordCap246, ws7WordP246, ws7WordQ246]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep246, ws7WordCap246, ws7WordP246, ws7WordQ246]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep246, ws7WordCap246, ws7WordP246, ws7WordQ246]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep246, ws7WordCap246, ws7WordP246, ws7WordQ246]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep246, ws7WordCap246, ws7WordP246, ws7WordQ246]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep246, ws7WordCap246, ws7WordP246, ws7WordQ246]
  have hword := ws7Word246WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule171 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨171, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 5 ≤ (3/28 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep249 i) ≤ ws7WordCap249 (ws7WordRep249 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep249, ws7WordCap249, ws7WordP249, ws7WordQ249]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep249, ws7WordCap249, ws7WordP249, ws7WordQ249]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep249, ws7WordCap249, ws7WordP249, ws7WordQ249]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep249, ws7WordCap249, ws7WordP249, ws7WordQ249]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep249, ws7WordCap249, ws7WordP249, ws7WordQ249]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep249, ws7WordCap249, ws7WordP249, ws7WordQ249]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep249, ws7WordCap249, ws7WordP249, ws7WordQ249]
  have hword := ws7Word249WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule172 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨172, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (5/38 : ℝ)) ∧ (h 2 ≤ (4/31 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (3/28 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep250 i) ≤ ws7WordCap250 (ws7WordRep250 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep250, ws7WordCap250, ws7WordP250, ws7WordQ250]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep250, ws7WordCap250, ws7WordP250, ws7WordQ250]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep250, ws7WordCap250, ws7WordP250, ws7WordQ250]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep250, ws7WordCap250, ws7WordP250, ws7WordQ250]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep250, ws7WordCap250, ws7WordP250, ws7WordQ250]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep250, ws7WordCap250, ws7WordP250, ws7WordQ250]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep250, ws7WordCap250, ws7WordP250, ws7WordQ250]
  have hword := ws7Word250WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule173 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨173, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (7/62 : ℝ)) ∧ (h 5 ≤ (5/47 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep252 i) ≤ ws7WordCap252 (ws7WordRep252 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep252, ws7WordCap252, ws7WordP252, ws7WordQ252]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep252, ws7WordCap252, ws7WordP252, ws7WordQ252]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep252, ws7WordCap252, ws7WordP252, ws7WordQ252]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep252, ws7WordCap252, ws7WordP252, ws7WordQ252]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep252, ws7WordCap252, ws7WordP252, ws7WordQ252]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep252, ws7WordCap252, ws7WordP252, ws7WordQ252]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep252, ws7WordCap252, ws7WordP252, ws7WordQ252]
  have hword := ws7Word252WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule174 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨174, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (11/52 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (4/29 : ℝ)) ∧ (h 3 ≤ (7/62 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep253 i) ≤ ws7WordCap253 (ws7WordRep253 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep253, ws7WordCap253, ws7WordP253, ws7WordQ253]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep253, ws7WordCap253, ws7WordP253, ws7WordQ253]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep253, ws7WordCap253, ws7WordP253, ws7WordQ253]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep253, ws7WordCap253, ws7WordP253, ws7WordQ253]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep253, ws7WordCap253, ws7WordP253, ws7WordQ253]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep253, ws7WordCap253, ws7WordP253, ws7WordQ253]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep253, ws7WordCap253, ws7WordP253, ws7WordQ253]
  have hword := ws7Word253WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule175 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨175, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (1/7 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 5 ≤ (3/28 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep255 i) ≤ ws7WordCap255 (ws7WordRep255 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep255, ws7WordCap255, ws7WordP255, ws7WordQ255]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep255, ws7WordCap255, ws7WordP255, ws7WordQ255]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep255, ws7WordCap255, ws7WordP255, ws7WordQ255]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep255, ws7WordCap255, ws7WordP255, ws7WordQ255]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep255, ws7WordCap255, ws7WordP255, ws7WordQ255]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep255, ws7WordCap255, ws7WordP255, ws7WordQ255]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep255, ws7WordCap255, ws7WordP255, ws7WordQ255]
  have hword := ws7Word255WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule176 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨176, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (12/83 : ℝ)) ∧ (h 1 ≤ (5/37 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (3/25 : ℝ)) ∧ (h 4 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (3/29 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep257 i) ≤ ws7WordCap257 (ws7WordRep257 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep257, ws7WordCap257, ws7WordP257, ws7WordQ257]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep257, ws7WordCap257, ws7WordP257, ws7WordQ257]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep257, ws7WordCap257, ws7WordP257, ws7WordQ257]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep257, ws7WordCap257, ws7WordP257, ws7WordQ257]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep257, ws7WordCap257, ws7WordP257, ws7WordQ257]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep257, ws7WordCap257, ws7WordP257, ws7WordQ257]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep257, ws7WordCap257, ws7WordP257, ws7WordQ257]
  have hword := ws7Word257WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule177 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨177, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 1 ≤ (5/36 : ℝ)) ∧ (h 2 ≤ (3/22 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (6/55 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep258 i) ≤ ws7WordCap258 (ws7WordRep258 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep258, ws7WordCap258, ws7WordP258, ws7WordQ258]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep258, ws7WordCap258, ws7WordP258, ws7WordQ258]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep258, ws7WordCap258, ws7WordP258, ws7WordQ258]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep258, ws7WordCap258, ws7WordP258, ws7WordQ258]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep258, ws7WordCap258, ws7WordP258, ws7WordQ258]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep258, ws7WordCap258, ws7WordP258, ws7WordQ258]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep258, ws7WordCap258, ws7WordP258, ws7WordQ258]
  have hword := ws7Word258WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule178 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨178, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (8/39 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ)) ∧ (h 4 ≤ (5/46 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep259 i) ≤ ws7WordCap259 (ws7WordRep259 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep259, ws7WordCap259, ws7WordP259, ws7WordQ259]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep259, ws7WordCap259, ws7WordP259, ws7WordQ259]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep259, ws7WordCap259, ws7WordP259, ws7WordQ259]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep259, ws7WordCap259, ws7WordP259, ws7WordQ259]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep259, ws7WordCap259, ws7WordP259, ws7WordQ259]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep259, ws7WordCap259, ws7WordP259, ws7WordQ259]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep259, ws7WordCap259, ws7WordP259, ws7WordQ259]
  have hword := ws7Word259WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule179 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨179, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (12/85 : ℝ)) ∧ (h 1 ≤ (6/43 : ℝ)) ∧ (h 2 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 5 ≤ (7/65 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep262 i) ≤ ws7WordCap262 (ws7WordRep262 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep262, ws7WordCap262, ws7WordP262, ws7WordQ262]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep262, ws7WordCap262, ws7WordP262, ws7WordQ262]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep262, ws7WordCap262, ws7WordP262, ws7WordQ262]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep262, ws7WordCap262, ws7WordP262, ws7WordQ262]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep262, ws7WordCap262, ws7WordP262, ws7WordQ262]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep262, ws7WordCap262, ws7WordP262, ws7WordQ262]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep262, ws7WordCap262, ws7WordP262, ws7WordQ262]
  have hword := ws7Word262WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule180 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨180, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)) ∧ (h 0 ≤ (7/41 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 4 ≤ (3/28 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep263 i) ≤ ws7WordCap263 (ws7WordRep263 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep263, ws7WordCap263, ws7WordP263, ws7WordQ263]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep263, ws7WordCap263, ws7WordP263, ws7WordQ263]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep263, ws7WordCap263, ws7WordP263, ws7WordQ263]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep263, ws7WordCap263, ws7WordP263, ws7WordQ263]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep263, ws7WordCap263, ws7WordP263, ws7WordQ263]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep263, ws7WordCap263, ws7WordP263, ws7WordQ263]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep263, ws7WordCap263, ws7WordP263, ws7WordQ263]
  have hword := ws7Word263WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule181 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨181, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (9/44 : ℝ)) ∧ (h 0 ≤ (1/5 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 3 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep265 i) ≤ ws7WordCap265 (ws7WordRep265 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep265, ws7WordCap265, ws7WordP265, ws7WordQ265]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep265, ws7WordCap265, ws7WordP265, ws7WordQ265]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep265, ws7WordCap265, ws7WordP265, ws7WordQ265]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep265, ws7WordCap265, ws7WordP265, ws7WordQ265]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep265, ws7WordCap265, ws7WordP265, ws7WordQ265]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep265, ws7WordCap265, ws7WordP265, ws7WordQ265]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep265, ws7WordCap265, ws7WordP265, ws7WordQ265]
  have hword := ws7Word265WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule182 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨182, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (6/41 : ℝ)) ∧ (h 2 ≤ (1/7 : ℝ)) ∧ (h 3 ≤ (8/71 : ℝ)) ∧ (h 4 ≤ (10/89 : ℝ)) ∧ (h 5 ≤ (7/67 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep266 i) ≤ ws7WordCap266 (ws7WordRep266 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep266, ws7WordCap266, ws7WordP266, ws7WordQ266]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep266, ws7WordCap266, ws7WordP266, ws7WordQ266]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep266, ws7WordCap266, ws7WordP266, ws7WordQ266]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep266, ws7WordCap266, ws7WordP266, ws7WordQ266]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep266, ws7WordCap266, ws7WordP266, ws7WordQ266]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep266, ws7WordCap266, ws7WordP266, ws7WordQ266]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep266, ws7WordCap266, ws7WordP266, ws7WordQ266]
  have hword := ws7Word266WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule183 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨183, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (6/47 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (5/44 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep270 i) ≤ ws7WordCap270 (ws7WordRep270 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep270, ws7WordCap270, ws7WordP270, ws7WordQ270]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep270, ws7WordCap270, ws7WordP270, ws7WordQ270]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep270, ws7WordCap270, ws7WordP270, ws7WordQ270]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep270, ws7WordCap270, ws7WordP270, ws7WordQ270]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep270, ws7WordCap270, ws7WordP270, ws7WordQ270]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep270, ws7WordCap270, ws7WordP270, ws7WordQ270]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep270, ws7WordCap270, ws7WordP270, ws7WordQ270]
  have hword := ws7Word270WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule184 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨184, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (8/39 : ℝ)) ∧ (h 0 ≤ (8/53 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 2 ≤ (4/31 : ℝ)) ∧ (h 3 ≤ (3/25 : ℝ)) ∧ (h 4 ≤ (5/42 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep273 i) ≤ ws7WordCap273 (ws7WordRep273 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep273, ws7WordCap273, ws7WordP273, ws7WordQ273]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep273, ws7WordCap273, ws7WordP273, ws7WordQ273]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep273, ws7WordCap273, ws7WordP273, ws7WordQ273]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep273, ws7WordCap273, ws7WordP273, ws7WordQ273]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep273, ws7WordCap273, ws7WordP273, ws7WordQ273]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep273, ws7WordCap273, ws7WordP273, ws7WordQ273]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep273, ws7WordCap273, ws7WordP273, ws7WordQ273]
  have hword := ws7Word273WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule185 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨185, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (7/62 : ℝ)) ∧ (h 5 ≤ (4/37 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep274 i) ≤ ws7WordCap274 (ws7WordRep274 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep274, ws7WordCap274, ws7WordP274, ws7WordQ274]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep274, ws7WordCap274, ws7WordP274, ws7WordQ274]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep274, ws7WordCap274, ws7WordP274, ws7WordQ274]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep274, ws7WordCap274, ws7WordP274, ws7WordQ274]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep274, ws7WordCap274, ws7WordP274, ws7WordQ274]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep274, ws7WordCap274, ws7WordP274, ws7WordQ274]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep274, ws7WordCap274, ws7WordP274, ws7WordQ274]
  have hword := ws7Word274WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule186 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨186, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (1/5 : ℝ)) ∧ (h 1 ≤ (6/43 : ℝ)) ∧ (h 2 ≤ (4/35 : ℝ)) ∧ (h 3 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep276 i) ≤ ws7WordCap276 (ws7WordRep276 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep276, ws7WordCap276, ws7WordP276, ws7WordQ276]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep276, ws7WordCap276, ws7WordP276, ws7WordQ276]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep276, ws7WordCap276, ws7WordP276, ws7WordQ276]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep276, ws7WordCap276, ws7WordP276, ws7WordQ276]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep276, ws7WordCap276, ws7WordP276, ws7WordQ276]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep276, ws7WordCap276, ws7WordP276, ws7WordQ276]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep276, ws7WordCap276, ws7WordP276, ws7WordQ276]
  have hword := ws7Word276WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule187 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨187, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (11/73 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 2 ≤ (5/41 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 4 ≤ (5/44 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep281 i) ≤ ws7WordCap281 (ws7WordRep281 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep281, ws7WordCap281, ws7WordP281, ws7WordQ281]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep281, ws7WordCap281, ws7WordP281, ws7WordQ281]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep281, ws7WordCap281, ws7WordP281, ws7WordQ281]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep281, ws7WordCap281, ws7WordP281, ws7WordQ281]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep281, ws7WordCap281, ws7WordP281, ws7WordQ281]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep281, ws7WordCap281, ws7WordP281, ws7WordQ281]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep281, ws7WordCap281, ws7WordP281, ws7WordQ281]
  have hword := ws7Word281WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule188 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨188, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 2 ≤ (4/35 : ℝ)) ∧ (h 3 ≤ (5/44 : ℝ)) ∧ (h 5 ≤ (1/10 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep282 i) ≤ ws7WordCap282 (ws7WordRep282 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep282, ws7WordCap282, ws7WordP282, ws7WordQ282]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep282, ws7WordCap282, ws7WordP282, ws7WordQ282]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep282, ws7WordCap282, ws7WordP282, ws7WordQ282]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep282, ws7WordCap282, ws7WordP282, ws7WordQ282]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep282, ws7WordCap282, ws7WordP282, ws7WordQ282]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep282, ws7WordCap282, ws7WordP282, ws7WordQ282]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep282, ws7WordCap282, ws7WordP282, ws7WordQ282]
  have hword := ws7Word282WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule189 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨189, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (6/35 : ℝ)) ∧ (h 1 ≤ (1/6 : ℝ)) ∧ (h 2 ≤ (4/35 : ℝ)) ∧ (h 3 ≤ (6/53 : ℝ)) ∧ (h 4 ≤ (5/48 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep284 i) ≤ ws7WordCap284 (ws7WordRep284 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep284, ws7WordCap284, ws7WordP284, ws7WordQ284]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep284, ws7WordCap284, ws7WordP284, ws7WordQ284]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep284, ws7WordCap284, ws7WordP284, ws7WordQ284]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep284, ws7WordCap284, ws7WordP284, ws7WordQ284]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep284, ws7WordCap284, ws7WordP284, ws7WordQ284]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep284, ws7WordCap284, ws7WordP284, ws7WordQ284]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep284, ws7WordCap284, ws7WordP284, ws7WordQ284]
  have hword := ws7Word284WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule190 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨190, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (1/7 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep285 i) ≤ ws7WordCap285 (ws7WordRep285 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep285, ws7WordCap285, ws7WordP285, ws7WordQ285]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep285, ws7WordCap285, ws7WordP285, ws7WordQ285]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep285, ws7WordCap285, ws7WordP285, ws7WordQ285]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep285, ws7WordCap285, ws7WordP285, ws7WordQ285]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep285, ws7WordCap285, ws7WordP285, ws7WordQ285]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep285, ws7WordCap285, ws7WordP285, ws7WordQ285]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep285, ws7WordCap285, ws7WordP285, ws7WordQ285]
  have hword := ws7Word285WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule191 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨191, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)) ∧ (h 0 ≤ (11/76 : ℝ)) ∧ (h 1 ≤ (5/37 : ℝ)) ∧ (h 2 ≤ (5/39 : ℝ)) ∧ (h 3 ≤ (3/25 : ℝ)) ∧ (h 5 ≤ (3/29 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep286 i) ≤ ws7WordCap286 (ws7WordRep286 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep286, ws7WordCap286, ws7WordP286, ws7WordQ286]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep286, ws7WordCap286, ws7WordP286, ws7WordQ286]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep286, ws7WordCap286, ws7WordP286, ws7WordQ286]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep286, ws7WordCap286, ws7WordP286, ws7WordQ286]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep286, ws7WordCap286, ws7WordP286, ws7WordQ286]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep286, ws7WordCap286, ws7WordP286, ws7WordQ286]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep286, ws7WordCap286, ws7WordP286, ws7WordQ286]
  have hword := ws7Word286WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule192 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨192, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)) ∧ (h 0 ≤ (4/21 : ℝ)) ∧ (h 1 ≤ (6/47 : ℝ)) ∧ (h 2 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep287 i) ≤ ws7WordCap287 (ws7WordRep287 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep287, ws7WordCap287, ws7WordP287, ws7WordQ287]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep287, ws7WordCap287, ws7WordP287, ws7WordQ287]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep287, ws7WordCap287, ws7WordP287, ws7WordQ287]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep287, ws7WordCap287, ws7WordP287, ws7WordQ287]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep287, ws7WordCap287, ws7WordP287, ws7WordQ287]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep287, ws7WordCap287, ws7WordP287, ws7WordQ287]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep287, ws7WordCap287, ws7WordP287, ws7WordQ287]
  have hword := ws7Word287WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule193 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨193, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (4/23 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (9/74 : ℝ)) ∧ (h 3 ≤ (6/55 : ℝ)) ∧ (h 4 ≤ (3/28 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep290 i) ≤ ws7WordCap290 (ws7WordRep290 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep290, ws7WordCap290, ws7WordP290, ws7WordQ290]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep290, ws7WordCap290, ws7WordP290, ws7WordQ290]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep290, ws7WordCap290, ws7WordP290, ws7WordQ290]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep290, ws7WordCap290, ws7WordP290, ws7WordQ290]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep290, ws7WordCap290, ws7WordP290, ws7WordQ290]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep290, ws7WordCap290, ws7WordP290, ws7WordQ290]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep290, ws7WordCap290, ws7WordP290, ws7WordQ290]
  have hword := ws7Word290WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule194 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨194, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (10/49 : ℝ)) ∧ (h 0 ≤ (2/11 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (4/29 : ℝ)) ∧ (h 3 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep292 i) ≤ ws7WordCap292 (ws7WordRep292 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep292, ws7WordCap292, ws7WordP292, ws7WordQ292]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep292, ws7WordCap292, ws7WordP292, ws7WordQ292]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep292, ws7WordCap292, ws7WordP292, ws7WordQ292]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep292, ws7WordCap292, ws7WordP292, ws7WordQ292]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep292, ws7WordCap292, ws7WordP292, ws7WordQ292]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep292, ws7WordCap292, ws7WordP292, ws7WordQ292]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep292, ws7WordCap292, ws7WordP292, ws7WordQ292]
  have hword := ws7Word292WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule195 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨195, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (9/41 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep295 i) ≤ ws7WordCap295 (ws7WordRep295 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep295, ws7WordCap295, ws7WordP295, ws7WordQ295]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep295, ws7WordCap295, ws7WordP295, ws7WordQ295]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep295, ws7WordCap295, ws7WordP295, ws7WordQ295]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep295, ws7WordCap295, ws7WordP295, ws7WordQ295]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep295, ws7WordCap295, ws7WordP295, ws7WordQ295]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep295, ws7WordCap295, ws7WordP295, ws7WordQ295]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep295, ws7WordCap295, ws7WordP295, ws7WordQ295]
  have hword := ws7Word295WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule196 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨196, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 0 ≤ (2/11 : ℝ)) ∧ (h 1 ≤ (9/68 : ℝ)) ∧ (h 2 ≤ (5/42 : ℝ)) ∧ (h 3 ≤ (7/59 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (3/29 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep296 i) ≤ ws7WordCap296 (ws7WordRep296 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep296, ws7WordCap296, ws7WordP296, ws7WordQ296]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep296, ws7WordCap296, ws7WordP296, ws7WordQ296]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep296, ws7WordCap296, ws7WordP296, ws7WordQ296]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep296, ws7WordCap296, ws7WordP296, ws7WordQ296]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep296, ws7WordCap296, ws7WordP296, ws7WordQ296]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep296, ws7WordCap296, ws7WordP296, ws7WordQ296]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep296, ws7WordCap296, ws7WordP296, ws7WordQ296]
  have hword := ws7Word296WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule197 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨197, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (4/23 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep298 i) ≤ ws7WordCap298 (ws7WordRep298 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep298, ws7WordCap298, ws7WordP298, ws7WordQ298]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep298, ws7WordCap298, ws7WordP298, ws7WordQ298]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep298, ws7WordCap298, ws7WordP298, ws7WordQ298]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep298, ws7WordCap298, ws7WordP298, ws7WordQ298]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep298, ws7WordCap298, ws7WordP298, ws7WordQ298]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep298, ws7WordCap298, ws7WordP298, ws7WordQ298]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep298, ws7WordCap298, ws7WordP298, ws7WordQ298]
  have hword := ws7Word298WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule198 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨198, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (8/39 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep301 i) ≤ ws7WordCap301 (ws7WordRep301 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep301, ws7WordCap301, ws7WordP301, ws7WordQ301]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep301, ws7WordCap301, ws7WordP301, ws7WordQ301]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep301, ws7WordCap301, ws7WordP301, ws7WordQ301]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep301, ws7WordCap301, ws7WordP301, ws7WordQ301]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep301, ws7WordCap301, ws7WordP301, ws7WordQ301]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep301, ws7WordCap301, ws7WordP301, ws7WordQ301]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep301, ws7WordCap301, ws7WordP301, ws7WordQ301]
  have hword := ws7Word301WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule199 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨199, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (3/29 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep304 i) ≤ ws7WordCap304 (ws7WordRep304 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep304, ws7WordCap304, ws7WordP304, ws7WordQ304]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep304, ws7WordCap304, ws7WordP304, ws7WordQ304]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep304, ws7WordCap304, ws7WordP304, ws7WordQ304]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep304, ws7WordCap304, ws7WordP304, ws7WordQ304]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep304, ws7WordCap304, ws7WordP304, ws7WordQ304]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep304, ws7WordCap304, ws7WordP304, ws7WordQ304]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep304, ws7WordCap304, ws7WordP304, ws7WordQ304]
  have hword := ws7Word304WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

end WeakSevenBandData
