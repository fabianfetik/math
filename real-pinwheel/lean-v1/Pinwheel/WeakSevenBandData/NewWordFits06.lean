import Pinwheel.WeakSevenBandData.NewWordFits05
import Pinwheel.WeakSevenBandData.SourceFits
import Pinwheel.WeakSevenBandData.RateOrder
import Pinwheel.WeakSeven
import Mathlib.Tactic.FinCases

/-! Source-box adapters for literal weak words. -/

namespace RealPinwheel.WeakSevenBandData

theorem newWordFitSchedule240 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨240, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (8/39 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (3/23 : ℝ)) ∧ (h 4 ≤ (4/39 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep289 i) ≤ ws7WordCap289 (ws7WordRep289 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep289, ws7WordCap289, ws7WordP289, ws7WordQ289]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep289, ws7WordCap289, ws7WordP289, ws7WordQ289]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep289, ws7WordCap289, ws7WordP289, ws7WordQ289]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep289, ws7WordCap289, ws7WordP289, ws7WordQ289]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep289, ws7WordCap289, ws7WordP289, ws7WordQ289]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep289, ws7WordCap289, ws7WordP289, ws7WordQ289]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep289, ws7WordCap289, ws7WordP289, ws7WordQ289]
  have hword := ws7Word289WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule241 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨241, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (8/57 : ℝ)) ∧ (h 2 ≤ (3/22 : ℝ)) ∧ (h 3 ≤ (2/15 : ℝ)) ∧ (h 4 ≤ (2/19 : ℝ)) ∧ (h 5 ≤ (5/48 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep121 i) ≤ ws7WordCap121 (ws7WordRep121 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep121, ws7WordCap121, ws7WordP121, ws7WordQ121]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep121, ws7WordCap121, ws7WordP121, ws7WordQ121]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep121, ws7WordCap121, ws7WordP121, ws7WordQ121]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep121, ws7WordCap121, ws7WordP121, ws7WordQ121]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep121, ws7WordCap121, ws7WordP121, ws7WordQ121]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep121, ws7WordCap121, ws7WordP121, ws7WordQ121]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep121, ws7WordCap121, ws7WordP121, ws7WordQ121]
  have hword := ws7Word121WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule242 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨242, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (3/28 : ℝ)) ∧ (h 5 ≤ (5/47 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep114 i) ≤ ws7WordCap114 (ws7WordRep114 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep114, ws7WordCap114, ws7WordP114, ws7WordQ114]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep114, ws7WordCap114, ws7WordP114, ws7WordQ114]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep114, ws7WordCap114, ws7WordP114, ws7WordQ114]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep114, ws7WordCap114, ws7WordP114, ws7WordQ114]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep114, ws7WordCap114, ws7WordP114, ws7WordQ114]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep114, ws7WordCap114, ws7WordP114, ws7WordQ114]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep114, ws7WordCap114, ws7WordP114, ws7WordQ114]
  have hword := ws7Word114WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule243 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨243, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (9/44 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (5/44 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep65 i) ≤ ws7WordCap65 (ws7WordRep65 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep65, ws7WordCap65, ws7WordP65, ws7WordQ65]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep65, ws7WordCap65, ws7WordP65, ws7WordQ65]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep65, ws7WordCap65, ws7WordP65, ws7WordQ65]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep65, ws7WordCap65, ws7WordP65, ws7WordQ65]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep65, ws7WordCap65, ws7WordP65, ws7WordQ65]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep65, ws7WordCap65, ws7WordP65, ws7WordQ65]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep65, ws7WordCap65, ws7WordP65, ws7WordQ65]
  have hword := ws7Word65WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule244 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨244, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)) ∧ (h 0 ≤ (7/45 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (4/33 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 4 ≤ (5/44 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep189 i) ≤ ws7WordCap189 (ws7WordRep189 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep189, ws7WordCap189, ws7WordP189, ws7WordQ189]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep189, ws7WordCap189, ws7WordP189, ws7WordQ189]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep189, ws7WordCap189, ws7WordP189, ws7WordQ189]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep189, ws7WordCap189, ws7WordP189, ws7WordQ189]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep189, ws7WordCap189, ws7WordP189, ws7WordQ189]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep189, ws7WordCap189, ws7WordP189, ws7WordQ189]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep189, ws7WordCap189, ws7WordP189, ws7WordQ189]
  have hword := ws7Word189WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule245 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨245, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (16/79 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (5/36 : ℝ)) ∧ (h 2 ≤ (7/58 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ)) ∧ (h 5 ≤ (7/66 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep344 i) ≤ ws7WordCap344 (ws7WordRep344 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep344, ws7WordCap344, ws7WordP344, ws7WordQ344]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep344, ws7WordCap344, ws7WordP344, ws7WordQ344]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep344, ws7WordCap344, ws7WordP344, ws7WordQ344]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep344, ws7WordCap344, ws7WordP344, ws7WordQ344]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep344, ws7WordCap344, ws7WordP344, ws7WordQ344]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep344, ws7WordCap344, ws7WordP344, ws7WordQ344]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep344, ws7WordCap344, ws7WordP344, ws7WordQ344]
  have hword := ws7Word344WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule246 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨246, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (14/69 : ℝ)) ∧ (h 0 ≤ (11/69 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep283 i) ≤ ws7WordCap283 (ws7WordRep283 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep283, ws7WordCap283, ws7WordP283, ws7WordQ283]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep283, ws7WordCap283, ws7WordP283, ws7WordQ283]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep283, ws7WordCap283, ws7WordP283, ws7WordQ283]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep283, ws7WordCap283, ws7WordP283, ws7WordQ283]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep283, ws7WordCap283, ws7WordP283, ws7WordQ283]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep283, ws7WordCap283, ws7WordP283, ws7WordQ283]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep283, ws7WordCap283, ws7WordP283, ws7WordQ283]
  have hword := ws7Word283WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule247 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨247, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)) ∧ (h 0 ≤ (7/46 : ℝ)) ∧ (h 1 ≤ (4/29 : ℝ)) ∧ (h 2 ≤ (8/65 : ℝ)) ∧ (h 3 ≤ (8/69 : ℝ)) ∧ (h 4 ≤ (5/44 : ℝ)) ∧ (h 5 ≤ (3/29 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep335 i) ≤ ws7WordCap335 (ws7WordRep335 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep335, ws7WordCap335, ws7WordP335, ws7WordQ335]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep335, ws7WordCap335, ws7WordP335, ws7WordQ335]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep335, ws7WordCap335, ws7WordP335, ws7WordQ335]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep335, ws7WordCap335, ws7WordP335, ws7WordQ335]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep335, ws7WordCap335, ws7WordP335, ws7WordQ335]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep335, ws7WordCap335, ws7WordP335, ws7WordQ335]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep335, ws7WordCap335, ws7WordP335, ws7WordQ335]
  have hword := ws7Word335WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule248 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨248, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (9/44 : ℝ)) ∧ (h 0 ≤ (5/28 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (4/37 : ℝ)) ∧ (h 4 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep245 i) ≤ ws7WordCap245 (ws7WordRep245 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep245, ws7WordCap245, ws7WordP245, ws7WordQ245]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep245, ws7WordCap245, ws7WordP245, ws7WordQ245]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep245, ws7WordCap245, ws7WordP245, ws7WordQ245]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep245, ws7WordCap245, ws7WordP245, ws7WordQ245]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep245, ws7WordCap245, ws7WordP245, ws7WordQ245]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep245, ws7WordCap245, ws7WordP245, ws7WordQ245]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep245, ws7WordCap245, ws7WordP245, ws7WordQ245]
  have hword := ws7Word245WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule249 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨249, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (7/33 : ℝ)) ∧ (h 0 ≤ (6/37 : ℝ)) ∧ (h 1 ≤ (5/37 : ℝ)) ∧ (h 2 ≤ (2/15 : ℝ)) ∧ (h 4 ≤ (4/37 : ℝ)) ∧ (h 5 ≤ (3/28 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep33 i) ≤ ws7WordCap33 (ws7WordRep33 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep33, ws7WordCap33, ws7WordP33, ws7WordQ33]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep33, ws7WordCap33, ws7WordP33, ws7WordQ33]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep33, ws7WordCap33, ws7WordP33, ws7WordQ33]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep33, ws7WordCap33, ws7WordP33, ws7WordQ33]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep33, ws7WordCap33, ws7WordP33, ws7WordQ33]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep33, ws7WordCap33, ws7WordP33, ws7WordQ33]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep33, ws7WordCap33, ws7WordP33, ws7WordQ33]
  have hword := ws7Word33WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule250 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨250, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (9/43 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (4/29 : ℝ)) ∧ (h 2 ≤ (4/31 : ℝ)) ∧ (h 3 ≤ (5/39 : ℝ)) ∧ (h 4 ≤ (5/47 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep178 i) ≤ ws7WordCap178 (ws7WordRep178 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep178, ws7WordCap178, ws7WordP178, ws7WordQ178]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep178, ws7WordCap178, ws7WordP178, ws7WordQ178]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep178, ws7WordCap178, ws7WordP178, ws7WordQ178]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep178, ws7WordCap178, ws7WordP178, ws7WordQ178]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep178, ws7WordCap178, ws7WordP178, ws7WordQ178]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep178, ws7WordCap178, ws7WordP178, ws7WordQ178]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep178, ws7WordCap178, ws7WordP178, ws7WordQ178]
  have hword := ws7Word178WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule251 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨251, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (8/59 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep279 i) ≤ ws7WordCap279 (ws7WordRep279 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep279, ws7WordCap279, ws7WordP279, ws7WordQ279]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep279, ws7WordCap279, ws7WordP279, ws7WordQ279]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep279, ws7WordCap279, ws7WordP279, ws7WordQ279]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep279, ws7WordCap279, ws7WordP279, ws7WordQ279]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep279, ws7WordCap279, ws7WordP279, ws7WordQ279]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep279, ws7WordCap279, ws7WordP279, ws7WordQ279]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep279, ws7WordCap279, ws7WordP279, ws7WordQ279]
  have hword := ws7Word279WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule252 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨252, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 2 ≤ (4/31 : ℝ)) ∧ (h 3 ≤ (3/25 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ)) ∧ (h 5 ≤ (4/39 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep183 i) ≤ ws7WordCap183 (ws7WordRep183 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep183, ws7WordCap183, ws7WordP183, ws7WordQ183]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep183, ws7WordCap183, ws7WordP183, ws7WordQ183]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep183, ws7WordCap183, ws7WordP183, ws7WordQ183]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep183, ws7WordCap183, ws7WordP183, ws7WordQ183]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep183, ws7WordCap183, ws7WordP183, ws7WordQ183]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep183, ws7WordCap183, ws7WordP183, ws7WordQ183]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep183, ws7WordCap183, ws7WordP183, ws7WordQ183]
  have hword := ws7Word183WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule253 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨253, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)) ∧ (h 0 ≤ (13/90 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 2 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (5/42 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep324 i) ≤ ws7WordCap324 (ws7WordRep324 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep324, ws7WordCap324, ws7WordP324, ws7WordQ324]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep324, ws7WordCap324, ws7WordP324, ws7WordQ324]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep324, ws7WordCap324, ws7WordP324, ws7WordQ324]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep324, ws7WordCap324, ws7WordP324, ws7WordQ324]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep324, ws7WordCap324, ws7WordP324, ws7WordQ324]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep324, ws7WordCap324, ws7WordP324, ws7WordQ324]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep324, ws7WordCap324, ws7WordP324, ws7WordQ324]
  have hword := ws7Word324WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule254 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨254, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (13/64 : ℝ)) ∧ (h 0 ≤ (5/33 : ℝ)) ∧ (h 1 ≤ (5/37 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep145 i) ≤ ws7WordCap145 (ws7WordRep145 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep145, ws7WordCap145, ws7WordP145, ws7WordQ145]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep145, ws7WordCap145, ws7WordP145, ws7WordQ145]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep145, ws7WordCap145, ws7WordP145, ws7WordQ145]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep145, ws7WordCap145, ws7WordP145, ws7WordQ145]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep145, ws7WordCap145, ws7WordP145, ws7WordQ145]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep145, ws7WordCap145, ws7WordP145, ws7WordQ145]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep145, ws7WordCap145, ws7WordP145, ws7WordQ145]
  have hword := ws7Word145WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule255 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨255, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (9/56 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 2 ≤ (4/33 : ℝ)) ∧ (h 3 ≤ (3/25 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep110 i) ≤ ws7WordCap110 (ws7WordRep110 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep110, ws7WordCap110, ws7WordP110, ws7WordQ110]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep110, ws7WordCap110, ws7WordP110, ws7WordQ110]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep110, ws7WordCap110, ws7WordP110, ws7WordQ110]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep110, ws7WordCap110, ws7WordP110, ws7WordQ110]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep110, ws7WordCap110, ws7WordP110, ws7WordQ110]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep110, ws7WordCap110, ws7WordP110, ws7WordQ110]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep110, ws7WordCap110, ws7WordP110, ws7WordQ110]
  have hword := ws7Word110WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule256 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨256, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)) ∧ (h 0 ≤ (8/51 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (3/25 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep115 i) ≤ ws7WordCap115 (ws7WordRep115 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep115, ws7WordCap115, ws7WordP115, ws7WordQ115]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep115, ws7WordCap115, ws7WordP115, ws7WordQ115]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep115, ws7WordCap115, ws7WordP115, ws7WordQ115]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep115, ws7WordCap115, ws7WordP115, ws7WordQ115]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep115, ws7WordCap115, ws7WordP115, ws7WordQ115]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep115, ws7WordCap115, ws7WordP115, ws7WordQ115]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep115, ws7WordCap115, ws7WordP115, ws7WordQ115]
  have hword := ws7Word115WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule257 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨257, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (5/34 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (5/42 : ℝ)) ∧ (h 4 ≤ (8/71 : ℝ)) ∧ (h 5 ≤ (3/29 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep314 i) ≤ ws7WordCap314 (ws7WordRep314 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep314, ws7WordCap314, ws7WordP314, ws7WordQ314]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep314, ws7WordCap314, ws7WordP314, ws7WordQ314]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep314, ws7WordCap314, ws7WordP314, ws7WordQ314]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep314, ws7WordCap314, ws7WordP314, ws7WordQ314]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep314, ws7WordCap314, ws7WordP314, ws7WordQ314]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep314, ws7WordCap314, ws7WordP314, ws7WordQ314]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep314, ws7WordCap314, ws7WordP314, ws7WordQ314]
  have hword := ws7Word314WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule258 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨258, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)) ∧ (h 0 ≤ (5/34 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (4/31 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (8/71 : ℝ)) ∧ (h 5 ≤ (3/29 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep291 i) ≤ ws7WordCap291 (ws7WordRep291 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep291, ws7WordCap291, ws7WordP291, ws7WordQ291]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep291, ws7WordCap291, ws7WordP291, ws7WordQ291]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep291, ws7WordCap291, ws7WordP291, ws7WordQ291]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep291, ws7WordCap291, ws7WordP291, ws7WordQ291]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep291, ws7WordCap291, ws7WordP291, ws7WordQ291]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep291, ws7WordCap291, ws7WordP291, ws7WordQ291]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep291, ws7WordCap291, ws7WordP291, ws7WordQ291]
  have hword := ws7Word291WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule259 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨259, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (16/79 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (7/54 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (5/43 : ℝ)) ∧ (h 4 ≤ (3/26 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep307 i) ≤ ws7WordCap307 (ws7WordRep307 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep307, ws7WordCap307, ws7WordP307, ws7WordQ307]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep307, ws7WordCap307, ws7WordP307, ws7WordQ307]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep307, ws7WordCap307, ws7WordP307, ws7WordQ307]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep307, ws7WordCap307, ws7WordP307, ws7WordQ307]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep307, ws7WordCap307, ws7WordP307, ws7WordQ307]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep307, ws7WordCap307, ws7WordP307, ws7WordQ307]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep307, ws7WordCap307, ws7WordP307, ws7WordQ307]
  have hword := ws7Word307WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule260 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨260, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (11/87 : ℝ)) ∧ (h 2 ≤ (5/42 : ℝ)) ∧ (h 3 ≤ (5/43 : ℝ)) ∧ (h 4 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep268 i) ≤ ws7WordCap268 (ws7WordRep268 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep268, ws7WordCap268, ws7WordP268, ws7WordQ268]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep268, ws7WordCap268, ws7WordP268, ws7WordQ268]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep268, ws7WordCap268, ws7WordP268, ws7WordQ268]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep268, ws7WordCap268, ws7WordP268, ws7WordQ268]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep268, ws7WordCap268, ws7WordP268, ws7WordQ268]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep268, ws7WordCap268, ws7WordP268, ws7WordQ268]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep268, ws7WordCap268, ws7WordP268, ws7WordQ268]
  have hword := ws7Word268WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule261 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨261, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (12/59 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep209 i) ≤ ws7WordCap209 (ws7WordRep209 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep209, ws7WordCap209, ws7WordP209, ws7WordQ209]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep209, ws7WordCap209, ws7WordP209, ws7WordQ209]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep209, ws7WordCap209, ws7WordP209, ws7WordQ209]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep209, ws7WordCap209, ws7WordP209, ws7WordQ209]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep209, ws7WordCap209, ws7WordP209, ws7WordQ209]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep209, ws7WordCap209, ws7WordP209, ws7WordQ209]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep209, ws7WordCap209, ws7WordP209, ws7WordQ209]
  have hword := ws7Word209WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule262 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨262, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (8/39 : ℝ)) ∧ (h 0 ≤ (4/27 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep170 i) ≤ ws7WordCap170 (ws7WordRep170 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep170, ws7WordCap170, ws7WordP170, ws7WordQ170]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep170, ws7WordCap170, ws7WordP170, ws7WordQ170]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep170, ws7WordCap170, ws7WordP170, ws7WordQ170]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep170, ws7WordCap170, ws7WordP170, ws7WordQ170]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep170, ws7WordCap170, ws7WordP170, ws7WordQ170]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep170, ws7WordCap170, ws7WordP170, ws7WordQ170]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep170, ws7WordCap170, ws7WordP170, ws7WordQ170]
  have hword := ws7Word170WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

end WeakSevenBandData
