import Pinwheel.WeakSevenBandData.NewWordFits00
import Pinwheel.WeakSevenBandData.SourceFits
import Pinwheel.WeakSevenBandData.RateOrder
import Pinwheel.WeakSeven
import Mathlib.Tactic.FinCases

/-! Source-box adapters for literal weak words. -/

namespace RealPinwheel.WeakSevenBandData

theorem newWordFitSchedule40 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨40, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 0 ≤ (5/29 : ℝ)) ∧ (h 2 ≤ (3/20 : ℝ)) ∧ (h 3 ≤ (1/10 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep51 i) ≤ ws7WordCap51 (ws7WordRep51 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep51, ws7WordCap51, ws7WordP51, ws7WordQ51]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep51, ws7WordCap51, ws7WordP51, ws7WordQ51]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep51, ws7WordCap51, ws7WordP51, ws7WordQ51]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep51, ws7WordCap51, ws7WordP51, ws7WordQ51]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep51, ws7WordCap51, ws7WordP51, ws7WordQ51]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep51, ws7WordCap51, ws7WordP51, ws7WordQ51]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep51, ws7WordCap51, ws7WordP51, ws7WordQ51]
  have hword := ws7Word51WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule41 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨41, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (9/41 : ℝ)) ∧ (h 0 ≤ (6/41 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (5/41 : ℝ)) ∧ (h 3 ≤ (3/25 : ℝ)) ∧ (h 5 ≤ (2/17 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep53 i) ≤ ws7WordCap53 (ws7WordRep53 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep53, ws7WordCap53, ws7WordP53, ws7WordQ53]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep53, ws7WordCap53, ws7WordP53, ws7WordQ53]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep53, ws7WordCap53, ws7WordP53, ws7WordQ53]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep53, ws7WordCap53, ws7WordP53, ws7WordQ53]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep53, ws7WordCap53, ws7WordP53, ws7WordQ53]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep53, ws7WordCap53, ws7WordP53, ws7WordQ53]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep53, ws7WordCap53, ws7WordP53, ws7WordQ53]
  have hword := ws7Word53WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule42 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨42, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (1/7 : ℝ)) ∧ (h 3 ≤ (5/42 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep57 i) ≤ ws7WordCap57 (ws7WordRep57 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep57, ws7WordCap57, ws7WordP57, ws7WordQ57]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep57, ws7WordCap57, ws7WordP57, ws7WordQ57]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep57, ws7WordCap57, ws7WordP57, ws7WordQ57]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep57, ws7WordCap57, ws7WordP57, ws7WordQ57]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep57, ws7WordCap57, ws7WordP57, ws7WordQ57]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep57, ws7WordCap57, ws7WordP57, ws7WordQ57]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep57, ws7WordCap57, ws7WordP57, ws7WordQ57]
  have hword := ws7Word57WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule43 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨43, by decide⟩ : Fin 263) h delta) :
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

theorem newWordFitSchedule44 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨44, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (10/43 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (6/43 : ℝ)) ∧ (h 2 ≤ (5/43 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep59 i) ≤ ws7WordCap59 (ws7WordRep59 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep59, ws7WordCap59, ws7WordP59, ws7WordQ59]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep59, ws7WordCap59, ws7WordP59, ws7WordQ59]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep59, ws7WordCap59, ws7WordP59, ws7WordQ59]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep59, ws7WordCap59, ws7WordP59, ws7WordQ59]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep59, ws7WordCap59, ws7WordP59, ws7WordQ59]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep59, ws7WordCap59, ws7WordP59, ws7WordQ59]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep59, ws7WordCap59, ws7WordP59, ws7WordQ59]
  have hword := ws7Word59WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule45 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨45, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (5/43 : ℝ)) ∧ (h 4 ≤ (4/35 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep60 i) ≤ ws7WordCap60 (ws7WordRep60 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep60, ws7WordCap60, ws7WordP60, ws7WordQ60]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep60, ws7WordCap60, ws7WordP60, ws7WordQ60]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep60, ws7WordCap60, ws7WordP60, ws7WordQ60]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep60, ws7WordCap60, ws7WordP60, ws7WordQ60]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep60, ws7WordCap60, ws7WordP60, ws7WordQ60]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep60, ws7WordCap60, ws7WordP60, ws7WordQ60]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep60, ws7WordCap60, ws7WordP60, ws7WordQ60]
  have hword := ws7Word60WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule46 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨46, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (2/11 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 2 ≤ (5/44 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep62 i) ≤ ws7WordCap62 (ws7WordRep62 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep62, ws7WordCap62, ws7WordP62, ws7WordQ62]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep62, ws7WordCap62, ws7WordP62, ws7WordQ62]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep62, ws7WordCap62, ws7WordP62, ws7WordQ62]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep62, ws7WordCap62, ws7WordP62, ws7WordQ62]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep62, ws7WordCap62, ws7WordP62, ws7WordQ62]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep62, ws7WordCap62, ws7WordP62, ws7WordQ62]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep62, ws7WordCap62, ws7WordP62, ws7WordQ62]
  have hword := ws7Word62WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule47 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨47, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/17 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (5/44 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep63 i) ≤ ws7WordCap63 (ws7WordRep63 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep63, ws7WordCap63, ws7WordP63, ws7WordQ63]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep63, ws7WordCap63, ws7WordP63, ws7WordQ63]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep63, ws7WordCap63, ws7WordP63, ws7WordQ63]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep63, ws7WordCap63, ws7WordP63, ws7WordQ63]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep63, ws7WordCap63, ws7WordP63, ws7WordQ63]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep63, ws7WordCap63, ws7WordP63, ws7WordQ63]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep63, ws7WordCap63, ws7WordP63, ws7WordQ63]
  have hword := ws7Word63WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule48 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨48, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (9/44 : ℝ)) ∧ (h 0 ≤ (3/17 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep64 i) ≤ ws7WordCap64 (ws7WordRep64 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep64, ws7WordCap64, ws7WordP64, ws7WordQ64]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep64, ws7WordCap64, ws7WordP64, ws7WordQ64]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep64, ws7WordCap64, ws7WordP64, ws7WordQ64]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep64, ws7WordCap64, ws7WordP64, ws7WordQ64]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep64, ws7WordCap64, ws7WordP64, ws7WordQ64]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep64, ws7WordCap64, ws7WordP64, ws7WordQ64]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep64, ws7WordCap64, ws7WordP64, ws7WordQ64]
  have hword := ws7Word64WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule49 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨49, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (5/44 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep66 i) ≤ ws7WordCap66 (ws7WordRep66 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep66, ws7WordCap66, ws7WordP66, ws7WordQ66]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep66, ws7WordCap66, ws7WordP66, ws7WordQ66]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep66, ws7WordCap66, ws7WordP66, ws7WordQ66]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep66, ws7WordCap66, ws7WordP66, ws7WordQ66]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep66, ws7WordCap66, ws7WordP66, ws7WordQ66]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep66, ws7WordCap66, ws7WordP66, ws7WordQ66]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep66, ws7WordCap66, ws7WordP66, ws7WordQ66]
  have hword := ws7Word66WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule50 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨50, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 0 ≤ (7/45 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 5 ≤ (3/28 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep67 i) ≤ ws7WordCap67 (ws7WordRep67 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep67, ws7WordCap67, ws7WordP67, ws7WordQ67]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep67, ws7WordCap67, ws7WordP67, ws7WordQ67]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep67, ws7WordCap67, ws7WordP67, ws7WordQ67]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep67, ws7WordCap67, ws7WordP67, ws7WordQ67]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep67, ws7WordCap67, ws7WordP67, ws7WordQ67]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep67, ws7WordCap67, ws7WordP67, ws7WordQ67]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep67, ws7WordCap67, ws7WordP67, ws7WordQ67]
  have hword := ws7Word67WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule51 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨51, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (8/45 : ℝ)) ∧ (h 1 ≤ (5/38 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep68 i) ≤ ws7WordCap68 (ws7WordRep68 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep68, ws7WordCap68, ws7WordP68, ws7WordQ68]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep68, ws7WordCap68, ws7WordP68, ws7WordQ68]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep68, ws7WordCap68, ws7WordP68, ws7WordQ68]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep68, ws7WordCap68, ws7WordP68, ws7WordQ68]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep68, ws7WordCap68, ws7WordP68, ws7WordQ68]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep68, ws7WordCap68, ws7WordP68, ws7WordQ68]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep68, ws7WordCap68, ws7WordP68, ws7WordQ68]
  have hword := ws7Word68WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule52 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨52, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (6/31 : ℝ)) ∧ (h 1 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (5/46 : ℝ)) ∧ (h 4 ≤ (3/28 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep69 i) ≤ ws7WordCap69 (ws7WordRep69 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep69, ws7WordCap69, ws7WordP69, ws7WordQ69]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep69, ws7WordCap69, ws7WordP69, ws7WordQ69]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep69, ws7WordCap69, ws7WordP69, ws7WordQ69]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep69, ws7WordCap69, ws7WordP69, ws7WordQ69]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep69, ws7WordCap69, ws7WordP69, ws7WordQ69]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep69, ws7WordCap69, ws7WordP69, ws7WordQ69]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep69, ws7WordCap69, ws7WordP69, ws7WordQ69]
  have hword := ws7Word69WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule53 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨53, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (8/41 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 3 ≤ (5/46 : ℝ)) ∧ (h 4 ≤ (3/28 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep70 i) ≤ ws7WordCap70 (ws7WordRep70 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep70, ws7WordCap70, ws7WordP70, ws7WordQ70]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep70, ws7WordCap70, ws7WordP70, ws7WordQ70]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep70, ws7WordCap70, ws7WordP70, ws7WordQ70]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep70, ws7WordCap70, ws7WordP70, ws7WordQ70]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep70, ws7WordCap70, ws7WordP70, ws7WordQ70]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep70, ws7WordCap70, ws7WordP70, ws7WordQ70]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep70, ws7WordCap70, ws7WordP70, ws7WordQ70]
  have hword := ws7Word70WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule54 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨54, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (4/23 : ℝ)) ∧ (h 1 ≤ (4/27 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (3/28 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep71 i) ≤ ws7WordCap71 (ws7WordRep71 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep71, ws7WordCap71, ws7WordP71, ws7WordQ71]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep71, ws7WordCap71, ws7WordP71, ws7WordQ71]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep71, ws7WordCap71, ws7WordP71, ws7WordQ71]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep71, ws7WordCap71, ws7WordP71, ws7WordQ71]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep71, ws7WordCap71, ws7WordP71, ws7WordQ71]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep71, ws7WordCap71, ws7WordP71, ws7WordQ71]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep71, ws7WordCap71, ws7WordP71, ws7WordQ71]
  have hword := ws7Word71WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule55 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨55, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (4/27 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (5/46 : ℝ)) ∧ (h 5 ≤ (4/37 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep72 i) ≤ ws7WordCap72 (ws7WordRep72 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep72, ws7WordCap72, ws7WordP72, ws7WordQ72]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep72, ws7WordCap72, ws7WordP72, ws7WordQ72]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep72, ws7WordCap72, ws7WordP72, ws7WordQ72]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep72, ws7WordCap72, ws7WordP72, ws7WordQ72]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep72, ws7WordCap72, ws7WordP72, ws7WordQ72]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep72, ws7WordCap72, ws7WordP72, ws7WordQ72]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep72, ws7WordCap72, ws7WordP72, ws7WordQ72]
  have hword := ws7Word72WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule56 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨56, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (8/47 : ℝ)) ∧ (h 1 ≤ (6/47 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (3/25 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep73 i) ≤ ws7WordCap73 (ws7WordRep73 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep73, ws7WordCap73, ws7WordP73, ws7WordQ73]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep73, ws7WordCap73, ws7WordP73, ws7WordQ73]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep73, ws7WordCap73, ws7WordP73, ws7WordQ73]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep73, ws7WordCap73, ws7WordP73, ws7WordQ73]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep73, ws7WordCap73, ws7WordP73, ws7WordQ73]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep73, ws7WordCap73, ws7WordP73, ws7WordQ73]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep73, ws7WordCap73, ws7WordP73, ws7WordQ73]
  have hword := ws7Word73WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule57 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨57, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (10/47 : ℝ)) ∧ (h 0 ≤ (4/27 : ℝ)) ∧ (h 1 ≤ (5/34 : ℝ)) ∧ (h 2 ≤ (1/7 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (5/47 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep74 i) ≤ ws7WordCap74 (ws7WordRep74 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep74, ws7WordCap74, ws7WordP74, ws7WordQ74]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep74, ws7WordCap74, ws7WordP74, ws7WordQ74]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep74, ws7WordCap74, ws7WordP74, ws7WordQ74]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep74, ws7WordCap74, ws7WordP74, ws7WordQ74]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep74, ws7WordCap74, ws7WordP74, ws7WordQ74]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep74, ws7WordCap74, ws7WordP74, ws7WordQ74]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep74, ws7WordCap74, ws7WordP74, ws7WordQ74]
  have hword := ws7Word74WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule58 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨58, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 0 ≤ (8/47 : ℝ)) ∧ (h 1 ≤ (4/27 : ℝ)) ∧ (h 2 ≤ (1/7 : ℝ)) ∧ (h 3 ≤ (5/47 : ℝ)) ∧ (h 4 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep75 i) ≤ ws7WordCap75 (ws7WordRep75 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep75, ws7WordCap75, ws7WordP75, ws7WordQ75]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep75, ws7WordCap75, ws7WordP75, ws7WordQ75]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep75, ws7WordCap75, ws7WordP75, ws7WordQ75]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep75, ws7WordCap75, ws7WordP75, ws7WordQ75]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep75, ws7WordCap75, ws7WordP75, ws7WordQ75]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep75, ws7WordCap75, ws7WordP75, ws7WordQ75]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep75, ws7WordCap75, ws7WordP75, ws7WordQ75]
  have hword := ws7Word75WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule59 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨59, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (4/27 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (6/47 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (3/29 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep76 i) ≤ ws7WordCap76 (ws7WordRep76 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep76, ws7WordCap76, ws7WordP76, ws7WordQ76]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep76, ws7WordCap76, ws7WordP76, ws7WordQ76]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep76, ws7WordCap76, ws7WordP76, ws7WordQ76]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep76, ws7WordCap76, ws7WordP76, ws7WordQ76]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep76, ws7WordCap76, ws7WordP76, ws7WordQ76]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep76, ws7WordCap76, ws7WordP76, ws7WordQ76]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep76, ws7WordCap76, ws7WordP76, ws7WordQ76]
  have hword := ws7Word76WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule60 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨60, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (5/34 : ℝ)) ∧ (h 2 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (5/47 : ℝ)) ∧ (h 4 ≤ (2/19 : ℝ)) ∧ (h 5 ≤ (3/29 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep77 i) ≤ ws7WordCap77 (ws7WordRep77 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep77, ws7WordCap77, ws7WordP77, ws7WordQ77]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep77, ws7WordCap77, ws7WordP77, ws7WordQ77]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep77, ws7WordCap77, ws7WordP77, ws7WordQ77]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep77, ws7WordCap77, ws7WordP77, ws7WordQ77]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep77, ws7WordCap77, ws7WordP77, ws7WordQ77]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep77, ws7WordCap77, ws7WordP77, ws7WordQ77]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep77, ws7WordCap77, ws7WordP77, ws7WordQ77]
  have hword := ws7Word77WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule61 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨61, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (4/27 : ℝ)) ∧ (h 1 ≤ (6/41 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep79 i) ≤ ws7WordCap79 (ws7WordRep79 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep79, ws7WordCap79, ws7WordP79, ws7WordQ79]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep79, ws7WordCap79, ws7WordP79, ws7WordQ79]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep79, ws7WordCap79, ws7WordP79, ws7WordQ79]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep79, ws7WordCap79, ws7WordP79, ws7WordQ79]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep79, ws7WordCap79, ws7WordP79, ws7WordQ79]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep79, ws7WordCap79, ws7WordP79, ws7WordQ79]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep79, ws7WordCap79, ws7WordP79, ws7WordQ79]
  have hword := ws7Word79WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule62 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨62, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 0 ≤ (8/43 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 4 ≤ (5/48 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep81 i) ≤ ws7WordCap81 (ws7WordRep81 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep81, ws7WordCap81, ws7WordP81, ws7WordQ81]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep81, ws7WordCap81, ws7WordP81, ws7WordQ81]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep81, ws7WordCap81, ws7WordP81, ws7WordQ81]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep81, ws7WordCap81, ws7WordP81, ws7WordQ81]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep81, ws7WordCap81, ws7WordP81, ws7WordQ81]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep81, ws7WordCap81, ws7WordP81, ws7WordQ81]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep81, ws7WordCap81, ws7WordP81, ws7WordQ81]
  have hword := ws7Word81WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule63 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨63, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (5/48 : ℝ)) ∧ (h 5 ≤ (3/29 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep82 i) ≤ ws7WordCap82 (ws7WordRep82 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep82, ws7WordCap82, ws7WordP82, ws7WordQ82]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep82, ws7WordCap82, ws7WordP82, ws7WordQ82]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep82, ws7WordCap82, ws7WordP82, ws7WordQ82]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep82, ws7WordCap82, ws7WordP82, ws7WordQ82]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep82, ws7WordCap82, ws7WordP82, ws7WordQ82]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep82, ws7WordCap82, ws7WordP82, ws7WordQ82]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep82, ws7WordCap82, ws7WordP82, ws7WordQ82]
  have hword := ws7Word82WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule64 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨64, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (5/48 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep84 i) ≤ ws7WordCap84 (ws7WordRep84 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep84, ws7WordCap84, ws7WordP84, ws7WordQ84]
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep84, ws7WordCap84, ws7WordP84, ws7WordQ84]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep84, ws7WordCap84, ws7WordP84, ws7WordQ84]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep84, ws7WordCap84, ws7WordP84, ws7WordQ84]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep84, ws7WordCap84, ws7WordP84, ws7WordQ84]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep84, ws7WordCap84, ws7WordP84, ws7WordQ84]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep84, ws7WordCap84, ws7WordP84, ws7WordQ84]
  have hword := ws7Word84WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule65 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨65, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (10/49 : ℝ)) ∧ (h 0 ≤ (2/11 : ℝ)) ∧ (h 1 ≤ (5/41 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep86 i) ≤ ws7WordCap86 (ws7WordRep86 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep86, ws7WordCap86, ws7WordP86, ws7WordQ86]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep86, ws7WordCap86, ws7WordP86, ws7WordQ86]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep86, ws7WordCap86, ws7WordP86, ws7WordQ86]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep86, ws7WordCap86, ws7WordP86, ws7WordQ86]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep86, ws7WordCap86, ws7WordP86, ws7WordQ86]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep86, ws7WordCap86, ws7WordP86, ws7WordQ86]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep86, ws7WordCap86, ws7WordP86, ws7WordQ86]
  have hword := ws7Word86WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule66 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨66, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 2 ≤ (3/19 : ℝ)) ∧ (h 3 ≤ (3/25 : ℝ)) ∧ (h 4 ≤ (1/10 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep88 i) ≤ ws7WordCap88 (ws7WordRep88 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep88, ws7WordCap88, ws7WordP88, ws7WordQ88]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep88, ws7WordCap88, ws7WordP88, ws7WordQ88]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep88, ws7WordCap88, ws7WordP88, ws7WordQ88]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep88, ws7WordCap88, ws7WordP88, ws7WordQ88]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep88, ws7WordCap88, ws7WordP88, ws7WordQ88]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep88, ws7WordCap88, ws7WordP88, ws7WordQ88]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep88, ws7WordCap88, ws7WordP88, ws7WordQ88]
  have hword := ws7Word88WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule67 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨67, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (4/23 : ℝ)) ∧ (h 1 ≤ (5/37 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 4 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep89 i) ≤ ws7WordCap89 (ws7WordRep89 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep89, ws7WordCap89, ws7WordP89, ws7WordQ89]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep89, ws7WordCap89, ws7WordP89, ws7WordQ89]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep89, ws7WordCap89, ws7WordP89, ws7WordQ89]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep89, ws7WordCap89, ws7WordP89, ws7WordQ89]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep89, ws7WordCap89, ws7WordP89, ws7WordQ89]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep89, ws7WordCap89, ws7WordP89, ws7WordQ89]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep89, ws7WordCap89, ws7WordP89, ws7WordQ89]
  have hword := ws7Word89WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule68 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨68, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep92 i) ≤ ws7WordCap92 (ws7WordRep92 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep92, ws7WordCap92, ws7WordP92, ws7WordQ92]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep92, ws7WordCap92, ws7WordP92, ws7WordQ92]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep92, ws7WordCap92, ws7WordP92, ws7WordQ92]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep92, ws7WordCap92, ws7WordP92, ws7WordQ92]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep92, ws7WordCap92, ws7WordP92, ws7WordQ92]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep92, ws7WordCap92, ws7WordP92, ws7WordQ92]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep92, ws7WordCap92, ws7WordP92, ws7WordQ92]
  have hword := ws7Word92WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule69 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨69, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)) ∧ (h 0 ≤ (5/33 : ℝ)) ∧ (h 1 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (5/44 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep93 i) ≤ ws7WordCap93 (ws7WordRep93 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep93, ws7WordCap93, ws7WordP93, ws7WordQ93]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep93, ws7WordCap93, ws7WordP93, ws7WordQ93]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep93, ws7WordCap93, ws7WordP93, ws7WordQ93]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep93, ws7WordCap93, ws7WordP93, ws7WordQ93]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep93, ws7WordCap93, ws7WordP93, ws7WordQ93]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep93, ws7WordCap93, ws7WordP93, ws7WordQ93]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep93, ws7WordCap93, ws7WordP93, ws7WordQ93]
  have hword := ws7Word93WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule70 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨70, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep94 i) ≤ ws7WordCap94 (ws7WordRep94 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep94, ws7WordCap94, ws7WordP94, ws7WordQ94]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep94, ws7WordCap94, ws7WordP94, ws7WordQ94]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep94, ws7WordCap94, ws7WordP94, ws7WordQ94]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep94, ws7WordCap94, ws7WordP94, ws7WordQ94]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep94, ws7WordCap94, ws7WordP94, ws7WordQ94]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep94, ws7WordCap94, ws7WordP94, ws7WordQ94]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep94, ws7WordCap94, ws7WordP94, ws7WordQ94]
  have hword := ws7Word94WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule71 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨71, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)) ∧ (h 0 ≤ (8/47 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep95 i) ≤ ws7WordCap95 (ws7WordRep95 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep95, ws7WordCap95, ws7WordP95, ws7WordQ95]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep95, ws7WordCap95, ws7WordP95, ws7WordQ95]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep95, ws7WordCap95, ws7WordP95, ws7WordQ95]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep95, ws7WordCap95, ws7WordP95, ws7WordQ95]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep95, ws7WordCap95, ws7WordP95, ws7WordQ95]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep95, ws7WordCap95, ws7WordP95, ws7WordQ95]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep95, ws7WordCap95, ws7WordP95, ws7WordQ95]
  have hword := ws7Word95WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule72 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨72, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (7/31 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (6/53 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep96 i) ≤ ws7WordCap96 (ws7WordRep96 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep96, ws7WordCap96, ws7WordP96, ws7WordQ96]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep96, ws7WordCap96, ws7WordP96, ws7WordQ96]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep96, ws7WordCap96, ws7WordP96, ws7WordQ96]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep96, ws7WordCap96, ws7WordP96, ws7WordQ96]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep96, ws7WordCap96, ws7WordP96, ws7WordQ96]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep96, ws7WordCap96, ws7WordP96, ws7WordQ96]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep96, ws7WordCap96, ws7WordP96, ws7WordQ96]
  have hword := ws7Word96WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule73 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨73, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)) ∧ (h 0 ≤ (3/17 : ℝ)) ∧ (h 1 ≤ (7/53 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep97 i) ≤ ws7WordCap97 (ws7WordRep97 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep97, ws7WordCap97, ws7WordP97, ws7WordQ97]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep97, ws7WordCap97, ws7WordP97, ws7WordQ97]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep97, ws7WordCap97, ws7WordP97, ws7WordQ97]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep97, ws7WordCap97, ws7WordP97, ws7WordQ97]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep97, ws7WordCap97, ws7WordP97, ws7WordQ97]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep97, ws7WordCap97, ws7WordP97, ws7WordQ97]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep97, ws7WordCap97, ws7WordP97, ws7WordQ97]
  have hword := ws7Word97WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule74 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨74, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (8/39 : ℝ)) ∧ (h 0 ≤ (1/5 : ℝ)) ∧ (h 1 ≤ (7/53 : ℝ)) ∧ (h 2 ≤ (6/53 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep98 i) ≤ ws7WordCap98 (ws7WordRep98 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep98, ws7WordCap98, ws7WordP98, ws7WordQ98]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep98, ws7WordCap98, ws7WordP98, ws7WordQ98]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep98, ws7WordCap98, ws7WordP98, ws7WordQ98]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep98, ws7WordCap98, ws7WordP98, ws7WordQ98]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep98, ws7WordCap98, ws7WordP98, ws7WordQ98]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep98, ws7WordCap98, ws7WordP98, ws7WordQ98]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep98, ws7WordCap98, ws7WordP98, ws7WordQ98]
  have hword := ws7Word98WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule75 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨75, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 0 ≤ (8/53 : ℝ)) ∧ (h 3 ≤ (6/53 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep99 i) ≤ ws7WordCap99 (ws7WordRep99 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep99, ws7WordCap99, ws7WordP99, ws7WordQ99]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep99, ws7WordCap99, ws7WordP99, ws7WordQ99]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep99, ws7WordCap99, ws7WordP99, ws7WordQ99]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep99, ws7WordCap99, ws7WordP99, ws7WordQ99]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep99, ws7WordCap99, ws7WordP99, ws7WordQ99]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep99, ws7WordCap99, ws7WordP99, ws7WordQ99]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep99, ws7WordCap99, ws7WordP99, ws7WordQ99]
  have hword := ws7Word99WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule76 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨76, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (4/27 : ℝ)) ∧ (h 2 ≤ (7/54 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep100 i) ≤ ws7WordCap100 (ws7WordRep100 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep100, ws7WordCap100, ws7WordP100, ws7WordQ100]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep100, ws7WordCap100, ws7WordP100, ws7WordQ100]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep100, ws7WordCap100, ws7WordP100, ws7WordQ100]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep100, ws7WordCap100, ws7WordP100, ws7WordQ100]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep100, ws7WordCap100, ws7WordP100, ws7WordQ100]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep100, ws7WordCap100, ws7WordP100, ws7WordQ100]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep100, ws7WordCap100, ws7WordP100, ws7WordQ100]
  have hword := ws7Word100WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule77 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨77, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (11/50 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep101 i) ≤ ws7WordCap101 (ws7WordRep101 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep101, ws7WordCap101, ws7WordP101, ws7WordQ101]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep101, ws7WordCap101, ws7WordP101, ws7WordQ101]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep101, ws7WordCap101, ws7WordP101, ws7WordQ101]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep101, ws7WordCap101, ws7WordP101, ws7WordQ101]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep101, ws7WordCap101, ws7WordP101, ws7WordQ101]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep101, ws7WordCap101, ws7WordP101, ws7WordQ101]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep101, ws7WordCap101, ws7WordP101, ws7WordQ101]
  have hword := ws7Word101WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule78 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨78, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (5/27 : ℝ)) ∧ (h 1 ≤ (7/54 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep103 i) ≤ ws7WordCap103 (ws7WordRep103 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep103, ws7WordCap103, ws7WordP103, ws7WordQ103]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep103, ws7WordCap103, ws7WordP103, ws7WordQ103]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep103, ws7WordCap103, ws7WordP103, ws7WordQ103]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep103, ws7WordCap103, ws7WordP103, ws7WordQ103]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep103, ws7WordCap103, ws7WordP103, ws7WordQ103]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep103, ws7WordCap103, ws7WordP103, ws7WordQ103]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep103, ws7WordCap103, ws7WordP103, ws7WordQ103]
  have hword := ws7Word103WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule79 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨79, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (5/27 : ℝ)) ∧ (h 1 ≤ (4/27 : ℝ)) ∧ (h 2 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep104 i) ≤ ws7WordCap104 (ws7WordRep104 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep104, ws7WordCap104, ws7WordP104, ws7WordQ104]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep104, ws7WordCap104, ws7WordP104, ws7WordQ104]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep104, ws7WordCap104, ws7WordP104, ws7WordQ104]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep104, ws7WordCap104, ws7WordP104, ws7WordQ104]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep104, ws7WordCap104, ws7WordP104, ws7WordQ104]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep104, ws7WordCap104, ws7WordP104, ws7WordQ104]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep104, ws7WordCap104, ws7WordP104, ws7WordQ104]
  have hword := ws7Word104WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

end WeakSevenBandData
