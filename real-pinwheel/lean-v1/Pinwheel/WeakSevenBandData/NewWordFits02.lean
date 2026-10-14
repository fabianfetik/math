import Pinwheel.WeakSevenBandData.NewWordFits01
import Pinwheel.WeakSevenBandData.SourceFits
import Pinwheel.WeakSevenBandData.RateOrder
import Pinwheel.WeakSeven
import Mathlib.Tactic.FinCases

/-! Source-box adapters for literal weak words. -/

namespace RealPinwheel.WeakSevenBandData

theorem newWordFitSchedule80 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨80, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (7/54 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep105 i) ≤ ws7WordCap105 (ws7WordRep105 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep105, ws7WordCap105, ws7WordP105, ws7WordQ105]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep105, ws7WordCap105, ws7WordP105, ws7WordQ105]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep105, ws7WordCap105, ws7WordP105, ws7WordQ105]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep105, ws7WordCap105, ws7WordP105, ws7WordQ105]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep105, ws7WordCap105, ws7WordP105, ws7WordQ105]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep105, ws7WordCap105, ws7WordP105, ws7WordQ105]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep105, ws7WordCap105, ws7WordP105, ws7WordQ105]
  have hword := ws7Word105WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule81 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨81, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (4/27 : ℝ)) ∧ (h 2 ≤ (1/7 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep106 i) ≤ ws7WordCap106 (ws7WordRep106 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep106, ws7WordCap106, ws7WordP106, ws7WordQ106]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep106, ws7WordCap106, ws7WordP106, ws7WordQ106]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep106, ws7WordCap106, ws7WordP106, ws7WordQ106]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep106, ws7WordCap106, ws7WordP106, ws7WordQ106]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep106, ws7WordCap106, ws7WordP106, ws7WordQ106]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep106, ws7WordCap106, ws7WordP106, ws7WordQ106]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep106, ws7WordCap106, ws7WordP106, ws7WordQ106]
  have hword := ws7Word106WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule82 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨82, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (8/55 : ℝ)) ∧ (h 2 ≤ (1/7 : ℝ)) ∧ (h 3 ≤ (6/55 : ℝ)) ∧ (h 4 ≤ (5/46 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep107 i) ≤ ws7WordCap107 (ws7WordRep107 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep107, ws7WordCap107, ws7WordP107, ws7WordQ107]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep107, ws7WordCap107, ws7WordP107, ws7WordQ107]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep107, ws7WordCap107, ws7WordP107, ws7WordQ107]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep107, ws7WordCap107, ws7WordP107, ws7WordQ107]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep107, ws7WordCap107, ws7WordP107, ws7WordQ107]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep107, ws7WordCap107, ws7WordP107, ws7WordQ107]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep107, ws7WordCap107, ws7WordP107, ws7WordQ107]
  have hword := ws7Word107WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule83 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨83, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (5/28 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (3/28 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep108 i) ≤ ws7WordCap108 (ws7WordRep108 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep108, ws7WordCap108, ws7WordP108, ws7WordQ108]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep108, ws7WordCap108, ws7WordP108, ws7WordQ108]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep108, ws7WordCap108, ws7WordP108, ws7WordQ108]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep108, ws7WordCap108, ws7WordP108, ws7WordQ108]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep108, ws7WordCap108, ws7WordP108, ws7WordQ108]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep108, ws7WordCap108, ws7WordP108, ws7WordQ108]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep108, ws7WordCap108, ws7WordP108, ws7WordQ108]
  have hword := ws7Word108WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule84 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨84, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep109 i) ≤ ws7WordCap109 (ws7WordRep109 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep109, ws7WordCap109, ws7WordP109, ws7WordQ109]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep109, ws7WordCap109, ws7WordP109, ws7WordQ109]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep109, ws7WordCap109, ws7WordP109, ws7WordQ109]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep109, ws7WordCap109, ws7WordP109, ws7WordQ109]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep109, ws7WordCap109, ws7WordP109, ws7WordQ109]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep109, ws7WordCap109, ws7WordP109, ws7WordQ109]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep109, ws7WordCap109, ws7WordP109, ws7WordQ109]
  have hword := ws7Word109WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule85 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨85, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (5/28 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (5/41 : ℝ)) ∧ (h 5 ≤ (3/28 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep111 i) ≤ ws7WordCap111 (ws7WordRep111 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep111, ws7WordCap111, ws7WordP111, ws7WordQ111]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep111, ws7WordCap111, ws7WordP111, ws7WordQ111]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep111, ws7WordCap111, ws7WordP111, ws7WordQ111]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep111, ws7WordCap111, ws7WordP111, ws7WordQ111]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep111, ws7WordCap111, ws7WordP111, ws7WordQ111]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep111, ws7WordCap111, ws7WordP111, ws7WordQ111]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep111, ws7WordCap111, ws7WordP111, ws7WordQ111]
  have hword := ws7Word111WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule86 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨86, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (3/17 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep112 i) ≤ ws7WordCap112 (ws7WordRep112 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep112, ws7WordCap112, ws7WordP112, ws7WordQ112]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep112, ws7WordCap112, ws7WordP112, ws7WordQ112]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep112, ws7WordCap112, ws7WordP112, ws7WordQ112]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep112, ws7WordCap112, ws7WordP112, ws7WordQ112]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep112, ws7WordCap112, ws7WordP112, ws7WordQ112]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep112, ws7WordCap112, ws7WordP112, ws7WordQ112]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep112, ws7WordCap112, ws7WordP112, ws7WordQ112]
  have hword := ws7Word112WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule87 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨87, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (7/33 : ℝ)) ∧ (h 0 ≤ (8/41 : ℝ)) ∧ (h 1 ≤ (9/56 : ℝ)) ∧ (h 2 ≤ (3/28 : ℝ)) ∧ (h 4 ≤ (5/47 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep118 i) ≤ ws7WordCap118 (ws7WordRep118 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep118, ws7WordCap118, ws7WordP118, ws7WordQ118]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep118, ws7WordCap118, ws7WordP118, ws7WordQ118]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep118, ws7WordCap118, ws7WordP118, ws7WordQ118]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep118, ws7WordCap118, ws7WordP118, ws7WordQ118]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep118, ws7WordCap118, ws7WordP118, ws7WordQ118]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep118, ws7WordCap118, ws7WordP118, ws7WordQ118]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep118, ws7WordCap118, ws7WordP118, ws7WordQ118]
  have hword := ws7Word118WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule88 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨88, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (7/44 : ℝ)) ∧ (h 2 ≤ (1/7 : ℝ)) ∧ (h 3 ≤ (3/28 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep119 i) ≤ ws7WordCap119 (ws7WordRep119 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep119, ws7WordCap119, ws7WordP119, ws7WordQ119]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep119, ws7WordCap119, ws7WordP119, ws7WordQ119]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep119, ws7WordCap119, ws7WordP119, ws7WordQ119]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep119, ws7WordCap119, ws7WordP119, ws7WordQ119]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep119, ws7WordCap119, ws7WordP119, ws7WordQ119]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep119, ws7WordCap119, ws7WordP119, ws7WordQ119]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep119, ws7WordCap119, ws7WordP119, ws7WordQ119]
  have hword := ws7Word119WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule89 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨89, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)) ∧ (h 0 ≤ (5/29 : ℝ)) ∧ (h 1 ≤ (4/29 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (3/29 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep122 i) ≤ ws7WordCap122 (ws7WordRep122 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep122, ws7WordCap122, ws7WordP122, ws7WordQ122]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep122, ws7WordCap122, ws7WordP122, ws7WordQ122]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep122, ws7WordCap122, ws7WordP122, ws7WordQ122]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep122, ws7WordCap122, ws7WordP122, ws7WordQ122]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep122, ws7WordCap122, ws7WordP122, ws7WordQ122]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep122, ws7WordCap122, ws7WordP122, ws7WordQ122]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep122, ws7WordCap122, ws7WordP122, ws7WordQ122]
  have hword := ws7Word122WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule90 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨90, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)) ∧ (h 0 ≤ (3/22 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep124 i) ≤ ws7WordCap124 (ws7WordRep124 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep124, ws7WordCap124, ws7WordP124, ws7WordQ124]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep124, ws7WordCap124, ws7WordP124, ws7WordQ124]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep124, ws7WordCap124, ws7WordP124, ws7WordQ124]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep124, ws7WordCap124, ws7WordP124, ws7WordQ124]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep124, ws7WordCap124, ws7WordP124, ws7WordQ124]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep124, ws7WordCap124, ws7WordP124, ws7WordQ124]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep124, ws7WordCap124, ws7WordP124, ws7WordQ124]
  have hword := ws7Word124WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule91 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨91, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (7/59 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ)) ∧ (h 5 ≤ (1/10 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep126 i) ≤ ws7WordCap126 (ws7WordRep126 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep126, ws7WordCap126, ws7WordP126, ws7WordQ126]
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep126, ws7WordCap126, ws7WordP126, ws7WordQ126]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep126, ws7WordCap126, ws7WordP126, ws7WordQ126]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep126, ws7WordCap126, ws7WordP126, ws7WordQ126]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep126, ws7WordCap126, ws7WordP126, ws7WordQ126]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep126, ws7WordCap126, ws7WordP126, ws7WordQ126]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep126, ws7WordCap126, ws7WordP126, ws7WordQ126]
  have hword := ws7Word126WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule92 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨92, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (12/59 : ℝ)) ∧ (h 0 ≤ (7/38 : ℝ)) ∧ (h 1 ≤ (8/59 : ℝ)) ∧ (h 4 ≤ (6/59 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep127 i) ≤ ws7WordCap127 (ws7WordRep127 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep127, ws7WordCap127, ws7WordP127, ws7WordQ127]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep127, ws7WordCap127, ws7WordP127, ws7WordQ127]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep127, ws7WordCap127, ws7WordP127, ws7WordQ127]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep127, ws7WordCap127, ws7WordP127, ws7WordQ127]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep127, ws7WordCap127, ws7WordP127, ws7WordQ127]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep127, ws7WordCap127, ws7WordP127, ws7WordQ127]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep127, ws7WordCap127, ws7WordP127, ws7WordQ127]
  have hword := ws7Word127WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule93 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨93, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (6/59 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep128 i) ≤ ws7WordCap128 (ws7WordRep128 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep128, ws7WordCap128, ws7WordP128, ws7WordQ128]
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep128, ws7WordCap128, ws7WordP128, ws7WordQ128]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep128, ws7WordCap128, ws7WordP128, ws7WordQ128]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep128, ws7WordCap128, ws7WordP128, ws7WordQ128]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep128, ws7WordCap128, ws7WordP128, ws7WordQ128]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep128, ws7WordCap128, ws7WordP128, ws7WordQ128]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep128, ws7WordCap128, ws7WordP128, ws7WordQ128]
  have hword := ws7Word128WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule94 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨94, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (1/7 : ℝ)) ∧ (h 3 ≤ (7/60 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep129 i) ≤ ws7WordCap129 (ws7WordRep129 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep129, ws7WordCap129, ws7WordP129, ws7WordQ129]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep129, ws7WordCap129, ws7WordP129, ws7WordQ129]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep129, ws7WordCap129, ws7WordP129, ws7WordQ129]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep129, ws7WordCap129, ws7WordP129, ws7WordQ129]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep129, ws7WordCap129, ws7WordP129, ws7WordQ129]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep129, ws7WordCap129, ws7WordP129, ws7WordQ129]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep129, ws7WordCap129, ws7WordP129, ws7WordQ129]
  have hword := ws7Word129WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule95 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨95, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 1 ≤ (1/6 : ℝ)) ∧ (h 2 ≤ (3/26 : ℝ)) ∧ (h 4 ≤ (1/10 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep130 i) ≤ ws7WordCap130 (ws7WordRep130 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep130, ws7WordCap130, ws7WordP130, ws7WordQ130]
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep130, ws7WordCap130, ws7WordP130, ws7WordQ130]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep130, ws7WordCap130, ws7WordP130, ws7WordQ130]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep130, ws7WordCap130, ws7WordP130, ws7WordQ130]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep130, ws7WordCap130, ws7WordP130, ws7WordQ130]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep130, ws7WordCap130, ws7WordP130, ws7WordQ130]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep130, ws7WordCap130, ws7WordP130, ws7WordQ130]
  have hword := ws7Word130WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule96 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨96, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (4/27 : ℝ)) ∧ (h 2 ≤ (1/7 : ℝ)) ∧ (h 3 ≤ (3/23 : ℝ)) ∧ (h 4 ≤ (1/10 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep131 i) ≤ ws7WordCap131 (ws7WordRep131 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep131, ws7WordCap131, ws7WordP131, ws7WordQ131]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep131, ws7WordCap131, ws7WordP131, ws7WordQ131]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep131, ws7WordCap131, ws7WordP131, ws7WordQ131]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep131, ws7WordCap131, ws7WordP131, ws7WordQ131]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep131, ws7WordCap131, ws7WordP131, ws7WordQ131]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep131, ws7WordCap131, ws7WordP131, ws7WordQ131]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep131, ws7WordCap131, ws7WordP131, ws7WordQ131]
  have hword := ws7Word131WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule97 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨97, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)) ∧ (h 0 ≤ (3/17 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 2 ≤ (3/26 : ℝ)) ∧ (h 4 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep133 i) ≤ ws7WordCap133 (ws7WordRep133 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep133, ws7WordCap133, ws7WordP133, ws7WordQ133]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep133, ws7WordCap133, ws7WordP133, ws7WordQ133]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep133, ws7WordCap133, ws7WordP133, ws7WordQ133]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep133, ws7WordCap133, ws7WordP133, ws7WordQ133]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep133, ws7WordCap133, ws7WordP133, ws7WordQ133]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep133, ws7WordCap133, ws7WordP133, ws7WordQ133]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep133, ws7WordCap133, ws7WordP133, ws7WordQ133]
  have hword := ws7Word133WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule98 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨98, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (7/31 : ℝ)) ∧ (h 0 ≤ (5/34 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (7/61 : ℝ)) ∧ (h 5 ≤ (5/44 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep138 i) ≤ ws7WordCap138 (ws7WordRep138 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep138, ws7WordCap138, ws7WordP138, ws7WordQ138]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep138, ws7WordCap138, ws7WordP138, ws7WordQ138]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep138, ws7WordCap138, ws7WordP138, ws7WordQ138]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep138, ws7WordCap138, ws7WordP138, ws7WordQ138]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep138, ws7WordCap138, ws7WordP138, ws7WordQ138]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep138, ws7WordCap138, ws7WordP138, ws7WordQ138]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep138, ws7WordCap138, ws7WordP138, ws7WordQ138]
  have hword := ws7Word138WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule99 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨99, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (11/54 : ℝ)) ∧ (h 0 ≤ (2/11 : ℝ)) ∧ (h 1 ≤ (5/37 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ)) ∧ (h 4 ≤ (3/28 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep139 i) ≤ ws7WordCap139 (ws7WordRep139 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep139, ws7WordCap139, ws7WordP139, ws7WordQ139]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep139, ws7WordCap139, ws7WordP139, ws7WordQ139]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep139, ws7WordCap139, ws7WordP139, ws7WordQ139]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep139, ws7WordCap139, ws7WordP139, ws7WordQ139]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep139, ws7WordCap139, ws7WordP139, ws7WordQ139]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep139, ws7WordCap139, ws7WordP139, ws7WordQ139]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep139, ws7WordCap139, ws7WordP139, ws7WordQ139]
  have hword := ws7Word139WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule100 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨100, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/16 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep140 i) ≤ ws7WordCap140 (ws7WordRep140 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep140, ws7WordCap140, ws7WordP140, ws7WordQ140]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep140, ws7WordCap140, ws7WordP140, ws7WordQ140]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep140, ws7WordCap140, ws7WordP140, ws7WordQ140]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep140, ws7WordCap140, ws7WordP140, ws7WordQ140]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep140, ws7WordCap140, ws7WordP140, ws7WordQ140]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep140, ws7WordCap140, ws7WordP140, ws7WordQ140]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep140, ws7WordCap140, ws7WordP140, ws7WordQ140]
  have hword := ws7Word140WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule101 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨101, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (7/32 : ℝ)) ∧ (h 0 ≤ (3/16 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (7/64 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep141 i) ≤ ws7WordCap141 (ws7WordRep141 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep141, ws7WordCap141, ws7WordP141, ws7WordQ141]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep141, ws7WordCap141, ws7WordP141, ws7WordQ141]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep141, ws7WordCap141, ws7WordP141, ws7WordQ141]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep141, ws7WordCap141, ws7WordP141, ws7WordQ141]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep141, ws7WordCap141, ws7WordP141, ws7WordQ141]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep141, ws7WordCap141, ws7WordP141, ws7WordQ141]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep141, ws7WordCap141, ws7WordP141, ws7WordQ141]
  have hword := ws7Word141WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule102 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨102, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (11/51 : ℝ)) ∧ (h 0 ≤ (1/5 : ℝ)) ∧ (h 1 ≤ (8/57 : ℝ)) ∧ (h 2 ≤ (5/46 : ℝ)) ∧ (h 4 ≤ (4/37 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep142 i) ≤ ws7WordCap142 (ws7WordRep142 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep142, ws7WordCap142, ws7WordP142, ws7WordQ142]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep142, ws7WordCap142, ws7WordP142, ws7WordQ142]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep142, ws7WordCap142, ws7WordP142, ws7WordQ142]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep142, ws7WordCap142, ws7WordP142, ws7WordQ142]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep142, ws7WordCap142, ws7WordP142, ws7WordQ142]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep142, ws7WordCap142, ws7WordP142, ws7WordQ142]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep142, ws7WordCap142, ws7WordP142, ws7WordQ142]
  have hword := ws7Word142WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule103 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨103, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (6/43 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 5 ≤ (5/46 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep143 i) ≤ ws7WordCap143 (ws7WordRep143 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep143, ws7WordCap143, ws7WordP143, ws7WordQ143]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep143, ws7WordCap143, ws7WordP143, ws7WordQ143]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep143, ws7WordCap143, ws7WordP143, ws7WordQ143]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep143, ws7WordCap143, ws7WordP143, ws7WordQ143]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep143, ws7WordCap143, ws7WordP143, ws7WordQ143]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep143, ws7WordCap143, ws7WordP143, ws7WordQ143]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep143, ws7WordCap143, ws7WordP143, ws7WordQ143]
  have hword := ws7Word143WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule104 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨104, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (6/55 : ℝ)) ∧ (h 5 ≤ (3/28 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep144 i) ≤ ws7WordCap144 (ws7WordRep144 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep144, ws7WordCap144, ws7WordP144, ws7WordQ144]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep144, ws7WordCap144, ws7WordP144, ws7WordQ144]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep144, ws7WordCap144, ws7WordP144, ws7WordQ144]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep144, ws7WordCap144, ws7WordP144, ws7WordQ144]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep144, ws7WordCap144, ws7WordP144, ws7WordQ144]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep144, ws7WordCap144, ws7WordP144, ws7WordQ144]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep144, ws7WordCap144, ws7WordP144, ws7WordQ144]
  have hword := ws7Word144WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule105 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨105, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 0 ≤ (5/32 : ℝ)) ∧ (h 1 ≤ (4/29 : ℝ)) ∧ (h 2 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (5/46 : ℝ)) ∧ (h 5 ≤ (3/28 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep148 i) ≤ ws7WordCap148 (ws7WordRep148 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep148, ws7WordCap148, ws7WordP148, ws7WordQ148]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep148, ws7WordCap148, ws7WordP148, ws7WordQ148]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep148, ws7WordCap148, ws7WordP148, ws7WordQ148]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep148, ws7WordCap148, ws7WordP148, ws7WordQ148]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep148, ws7WordCap148, ws7WordP148, ws7WordQ148]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep148, ws7WordCap148, ws7WordP148, ws7WordQ148]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep148, ws7WordCap148, ws7WordP148, ws7WordQ148]
  have hword := ws7Word148WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule106 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨106, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (10/47 : ℝ)) ∧ (h 0 ≤ (1/5 : ℝ)) ∧ (h 1 ≤ (7/57 : ℝ)) ∧ (h 2 ≤ (5/41 : ℝ)) ∧ (h 3 ≤ (4/33 : ℝ)) ∧ (h 4 ≤ (3/28 : ℝ)) ∧ (h 5 ≤ (5/47 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep149 i) ≤ ws7WordCap149 (ws7WordRep149 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep149, ws7WordCap149, ws7WordP149, ws7WordQ149]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep149, ws7WordCap149, ws7WordP149, ws7WordQ149]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep149, ws7WordCap149, ws7WordP149, ws7WordQ149]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep149, ws7WordCap149, ws7WordP149, ws7WordQ149]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep149, ws7WordCap149, ws7WordP149, ws7WordQ149]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep149, ws7WordCap149, ws7WordP149, ws7WordQ149]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep149, ws7WordCap149, ws7WordP149, ws7WordQ149]
  have hword := ws7Word149WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule107 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨107, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (4/23 : ℝ)) ∧ (h 1 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 4 ≤ (3/29 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep150 i) ≤ ws7WordCap150 (ws7WordRep150 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep150, ws7WordCap150, ws7WordP150, ws7WordQ150]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep150, ws7WordCap150, ws7WordP150, ws7WordQ150]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep150, ws7WordCap150, ws7WordP150, ws7WordQ150]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep150, ws7WordCap150, ws7WordP150, ws7WordQ150]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep150, ws7WordCap150, ws7WordP150, ws7WordQ150]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep150, ws7WordCap150, ws7WordP150, ws7WordQ150]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep150, ws7WordCap150, ws7WordP150, ws7WordQ150]
  have hword := ws7Word150WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule108 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨108, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (4/27 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep152 i) ≤ ws7WordCap152 (ws7WordRep152 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep152, ws7WordCap152, ws7WordP152, ws7WordQ152]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep152, ws7WordCap152, ws7WordP152, ws7WordQ152]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep152, ws7WordCap152, ws7WordP152, ws7WordQ152]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep152, ws7WordCap152, ws7WordP152, ws7WordQ152]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep152, ws7WordCap152, ws7WordP152, ws7WordQ152]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep152, ws7WordCap152, ws7WordP152, ws7WordQ152]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep152, ws7WordCap152, ws7WordP152, ws7WordQ152]
  have hword := ws7Word152WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule109 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨109, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (5/34 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep154 i) ≤ ws7WordCap154 (ws7WordRep154 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep154, ws7WordCap154, ws7WordP154, ws7WordQ154]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep154, ws7WordCap154, ws7WordP154, ws7WordQ154]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep154, ws7WordCap154, ws7WordP154, ws7WordQ154]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep154, ws7WordCap154, ws7WordP154, ws7WordQ154]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep154, ws7WordCap154, ws7WordP154, ws7WordQ154]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep154, ws7WordCap154, ws7WordP154, ws7WordQ154]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep154, ws7WordCap154, ws7WordP154, ws7WordQ154]
  have hword := ws7Word154WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule110 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨110, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 0 ≤ (4/23 : ℝ)) ∧ (h 1 ≤ (4/31 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep157 i) ≤ ws7WordCap157 (ws7WordRep157 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep157, ws7WordCap157, ws7WordP157, ws7WordQ157]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep157, ws7WordCap157, ws7WordP157, ws7WordQ157]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep157, ws7WordCap157, ws7WordP157, ws7WordQ157]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep157, ws7WordCap157, ws7WordP157, ws7WordQ157]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep157, ws7WordCap157, ws7WordP157, ws7WordQ157]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep157, ws7WordCap157, ws7WordP157, ws7WordQ157]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep157, ws7WordCap157, ws7WordP157, ws7WordQ157]
  have hword := ws7Word157WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule111 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨111, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (7/45 : ℝ)) ∧ (h 1 ≤ (9/70 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (4/35 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep159 i) ≤ ws7WordCap159 (ws7WordRep159 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep159, ws7WordCap159, ws7WordP159, ws7WordQ159]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep159, ws7WordCap159, ws7WordP159, ws7WordQ159]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep159, ws7WordCap159, ws7WordP159, ws7WordQ159]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep159, ws7WordCap159, ws7WordP159, ws7WordQ159]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep159, ws7WordCap159, ws7WordP159, ws7WordQ159]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep159, ws7WordCap159, ws7WordP159, ws7WordQ159]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep159, ws7WordCap159, ws7WordP159, ws7WordQ159]
  have hword := ws7Word159WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule112 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨112, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (1/5 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 2 ≤ (4/35 : ℝ)) ∧ (h 3 ≤ (6/53 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep162 i) ≤ ws7WordCap162 (ws7WordRep162 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep162, ws7WordCap162, ws7WordP162, ws7WordQ162]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep162, ws7WordCap162, ws7WordP162, ws7WordQ162]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep162, ws7WordCap162, ws7WordP162, ws7WordQ162]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep162, ws7WordCap162, ws7WordP162, ws7WordQ162]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep162, ws7WordCap162, ws7WordP162, ws7WordQ162]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep162, ws7WordCap162, ws7WordP162, ws7WordQ162]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep162, ws7WordCap162, ws7WordP162, ws7WordQ162]
  have hword := ws7Word162WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule113 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨113, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (6/35 : ℝ)) ∧ (h 1 ≤ (5/36 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep163 i) ≤ ws7WordCap163 (ws7WordRep163 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep163, ws7WordCap163, ws7WordP163, ws7WordQ163]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep163, ws7WordCap163, ws7WordP163, ws7WordQ163]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep163, ws7WordCap163, ws7WordP163, ws7WordQ163]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep163, ws7WordCap163, ws7WordP163, ws7WordQ163]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep163, ws7WordCap163, ws7WordP163, ws7WordQ163]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep163, ws7WordCap163, ws7WordP163, ws7WordQ163]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep163, ws7WordCap163, ws7WordP163, ws7WordQ163]
  have hword := ws7Word163WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule114 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨114, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (4/23 : ℝ)) ∧ (h 1 ≤ (9/70 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (6/53 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep165 i) ≤ ws7WordCap165 (ws7WordRep165 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep165, ws7WordCap165, ws7WordP165, ws7WordQ165]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep165, ws7WordCap165, ws7WordP165, ws7WordQ165]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep165, ws7WordCap165, ws7WordP165, ws7WordQ165]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep165, ws7WordCap165, ws7WordP165, ws7WordQ165]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep165, ws7WordCap165, ws7WordP165, ws7WordQ165]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep165, ws7WordCap165, ws7WordP165, ws7WordQ165]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep165, ws7WordCap165, ws7WordP165, ws7WordQ165]
  have hword := ws7Word165WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule115 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨115, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (3/17 : ℝ)) ∧ (h 1 ≤ (8/53 : ℝ)) ∧ (h 2 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep167 i) ≤ ws7WordCap167 (ws7WordRep167 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep167, ws7WordCap167, ws7WordP167, ws7WordQ167]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep167, ws7WordCap167, ws7WordP167, ws7WordQ167]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep167, ws7WordCap167, ws7WordP167, ws7WordQ167]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep167, ws7WordCap167, ws7WordP167, ws7WordQ167]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep167, ws7WordCap167, ws7WordP167, ws7WordQ167]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep167, ws7WordCap167, ws7WordP167, ws7WordQ167]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep167, ws7WordCap167, ws7WordP167, ws7WordQ167]
  have hword := ws7Word167WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule116 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨116, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ)) ∧ (h 4 ≤ (3/28 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep168 i) ≤ ws7WordCap168 (ws7WordRep168 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep168, ws7WordCap168, ws7WordP168, ws7WordQ168]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep168, ws7WordCap168, ws7WordP168, ws7WordQ168]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep168, ws7WordCap168, ws7WordP168, ws7WordQ168]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep168, ws7WordCap168, ws7WordP168, ws7WordQ168]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep168, ws7WordCap168, ws7WordP168, ws7WordQ168]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep168, ws7WordCap168, ws7WordP168, ws7WordQ168]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep168, ws7WordCap168, ws7WordP168, ws7WordQ168]
  have hword := ws7Word168WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule117 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨117, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (5/36 : ℝ)) ∧ (h 1 ≤ (9/65 : ℝ)) ∧ (h 2 ≤ (3/22 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (5/41 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep169 i) ≤ ws7WordCap169 (ws7WordRep169 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep169, ws7WordCap169, ws7WordP169, ws7WordQ169]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep169, ws7WordCap169, ws7WordP169, ws7WordQ169]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep169, ws7WordCap169, ws7WordP169, ws7WordQ169]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep169, ws7WordCap169, ws7WordP169, ws7WordQ169]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep169, ws7WordCap169, ws7WordP169, ws7WordQ169]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep169, ws7WordCap169, ws7WordP169, ws7WordQ169]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep169, ws7WordCap169, ws7WordP169, ws7WordQ169]
  have hword := ws7Word169WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule118 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨118, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (11/54 : ℝ)) ∧ (h 0 ≤ (3/16 : ℝ)) ∧ (h 1 ≤ (9/59 : ℝ)) ∧ (h 2 ≤ (1/9 : ℝ)) ∧ (h 5 ≤ (3/28 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep171 i) ≤ ws7WordCap171 (ws7WordRep171 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep171, ws7WordCap171, ws7WordP171, ws7WordQ171]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep171, ws7WordCap171, ws7WordP171, ws7WordQ171]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep171, ws7WordCap171, ws7WordP171, ws7WordQ171]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep171, ws7WordCap171, ws7WordP171, ws7WordQ171]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep171, ws7WordCap171, ws7WordP171, ws7WordQ171]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep171, ws7WordCap171, ws7WordP171, ws7WordQ171]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep171, ws7WordCap171, ws7WordP171, ws7WordQ171]
  have hword := ws7Word171WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem newWordFitSchedule119 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : NewSourceFits (⟨119, by decide⟩ : Fin 263) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (5/33 : ℝ)) ∧ (h 1 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (7/57 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep172 i) ≤ ws7WordCap172 (ws7WordRep172 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep172, ws7WordCap172, ws7WordP172, ws7WordQ172]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep172, ws7WordCap172, ws7WordP172, ws7WordQ172]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep172, ws7WordCap172, ws7WordP172, ws7WordQ172]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep172, ws7WordCap172, ws7WordP172, ws7WordQ172]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep172, ws7WordCap172, ws7WordP172, ws7WordQ172]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep172, ws7WordCap172, ws7WordP172, ws7WordQ172]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep172, ws7WordCap172, ws7WordP172, ws7WordQ172]
  have hword := ws7Word172WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

end WeakSevenBandData
