import Pinwheel.WeakSevenBandData.UpperWordFits01
import Pinwheel.WeakSevenBandData.SourceFits
import Pinwheel.WeakSevenBandData.RateOrder
import Pinwheel.WeakSeven
import Mathlib.Tactic.FinCases

/-! Source-box adapters for literal weak words. -/

namespace RealPinwheel.WeakSevenBandData

theorem upperWordFitSchedule84 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨84, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep161 i) ≤ ws7WordCap161 (ws7WordRep161 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep161, ws7WordCap161, ws7WordP161, ws7WordQ161]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep161, ws7WordCap161, ws7WordP161, ws7WordQ161]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep161, ws7WordCap161, ws7WordP161, ws7WordQ161]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep161, ws7WordCap161, ws7WordP161, ws7WordQ161]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep161, ws7WordCap161, ws7WordP161, ws7WordQ161]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep161, ws7WordCap161, ws7WordP161, ws7WordQ161]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep161, ws7WordCap161, ws7WordP161, ws7WordQ161]
  have hword := ws7Word161WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule85 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨85, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (4/31 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep220 i) ≤ ws7WordCap220 (ws7WordRep220 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep220, ws7WordCap220, ws7WordP220, ws7WordQ220]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep220, ws7WordCap220, ws7WordP220, ws7WordQ220]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep220, ws7WordCap220, ws7WordP220, ws7WordQ220]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep220, ws7WordCap220, ws7WordP220, ws7WordQ220]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep220, ws7WordCap220, ws7WordP220, ws7WordQ220]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep220, ws7WordCap220, ws7WordP220, ws7WordQ220]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep220, ws7WordCap220, ws7WordP220, ws7WordQ220]
  have hword := ws7Word220WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule86 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨86, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (5/32 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep329 i) ≤ ws7WordCap329 (ws7WordRep329 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep329, ws7WordCap329, ws7WordP329, ws7WordQ329]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep329, ws7WordCap329, ws7WordP329, ws7WordQ329]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep329, ws7WordCap329, ws7WordP329, ws7WordQ329]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep329, ws7WordCap329, ws7WordP329, ws7WordQ329]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep329, ws7WordCap329, ws7WordP329, ws7WordQ329]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep329, ws7WordCap329, ws7WordP329, ws7WordQ329]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep329, ws7WordCap329, ws7WordP329, ws7WordQ329]
  have hword := ws7Word329WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule87 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨87, by decide⟩ : Fin 157) h delta) :
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

theorem upperWordFitSchedule88 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨88, by decide⟩ : Fin 157) h delta) :
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

theorem upperWordFitSchedule89 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨89, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (15/107 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 3 ≤ (6/53 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep340 i) ≤ ws7WordCap340 (ws7WordRep340 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep340, ws7WordCap340, ws7WordP340, ws7WordQ340]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep340, ws7WordCap340, ws7WordP340, ws7WordQ340]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep340, ws7WordCap340, ws7WordP340, ws7WordQ340]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep340, ws7WordCap340, ws7WordP340, ws7WordQ340]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep340, ws7WordCap340, ws7WordP340, ws7WordQ340]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep340, ws7WordCap340, ws7WordP340, ws7WordQ340]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep340, ws7WordCap340, ws7WordP340, ws7WordQ340]
  have hword := ws7Word340WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule91 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨91, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 2 ≤ (33/278 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep358 i) ≤ ws7WordCap358 (ws7WordRep358 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep358, ws7WordCap358, ws7WordP358, ws7WordQ358]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep358, ws7WordCap358, ws7WordP358, ws7WordQ358]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep358, ws7WordCap358, ws7WordP358, ws7WordQ358]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep358, ws7WordCap358, ws7WordP358, ws7WordQ358]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep358, ws7WordCap358, ws7WordP358, ws7WordQ358]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep358, ws7WordCap358, ws7WordP358, ws7WordQ358]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep358, ws7WordCap358, ws7WordP358, ws7WordQ358]
  have hword := ws7Word358WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule92 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨92, by decide⟩ : Fin 157) h delta) :
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

theorem upperWordFitSchedule93 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨93, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (7/32 : ℝ)) ∧ (h 0 ≤ (6/41 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (4/33 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep151 i) ≤ ws7WordCap151 (ws7WordRep151 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep151, ws7WordCap151, ws7WordP151, ws7WordQ151]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep151, ws7WordCap151, ws7WordP151, ws7WordQ151]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep151, ws7WordCap151, ws7WordP151, ws7WordQ151]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep151, ws7WordCap151, ws7WordP151, ws7WordQ151]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep151, ws7WordCap151, ws7WordP151, ws7WordQ151]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep151, ws7WordCap151, ws7WordP151, ws7WordQ151]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep151, ws7WordCap151, ws7WordP151, ws7WordQ151]
  have hword := ws7Word151WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule94 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨94, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (8/55 : ℝ)) ∧ (h 1 ≤ (11/87 : ℝ)) ∧ (h 2 ≤ (4/33 : ℝ)) ∧ (h 3 ≤ (5/42 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep305 i) ≤ ws7WordCap305 (ws7WordRep305 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep305, ws7WordCap305, ws7WordP305, ws7WordQ305]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep305, ws7WordCap305, ws7WordP305, ws7WordQ305]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep305, ws7WordCap305, ws7WordP305, ws7WordQ305]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep305, ws7WordCap305, ws7WordP305, ws7WordQ305]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep305, ws7WordCap305, ws7WordP305, ws7WordQ305]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep305, ws7WordCap305, ws7WordP305, ws7WordQ305]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep305, ws7WordCap305, ws7WordP305, ws7WordQ305]
  have hword := ws7Word305WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule95 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨95, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (7/47 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 2 ≤ (6/49 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep317 i) ≤ ws7WordCap317 (ws7WordRep317 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep317, ws7WordCap317, ws7WordP317, ws7WordQ317]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep317, ws7WordCap317, ws7WordP317, ws7WordQ317]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep317, ws7WordCap317, ws7WordP317, ws7WordQ317]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep317, ws7WordCap317, ws7WordP317, ws7WordQ317]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep317, ws7WordCap317, ws7WordP317, ws7WordQ317]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep317, ws7WordCap317, ws7WordP317, ws7WordQ317]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep317, ws7WordCap317, ws7WordP317, ws7WordQ317]
  have hword := ws7Word317WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule96 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨96, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (1/7 : ℝ)) ∧ (h 1 ≤ (9/71 : ℝ)) ∧ (h 3 ≤ (3/25 : ℝ)) ∧ (h 4 ≤ (5/44 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep346 i) ≤ ws7WordCap346 (ws7WordRep346 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep346, ws7WordCap346, ws7WordP346, ws7WordQ346]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep346, ws7WordCap346, ws7WordP346, ws7WordQ346]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep346, ws7WordCap346, ws7WordP346, ws7WordQ346]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep346, ws7WordCap346, ws7WordP346, ws7WordQ346]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep346, ws7WordCap346, ws7WordP346, ws7WordQ346]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep346, ws7WordCap346, ws7WordP346, ws7WordQ346]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep346, ws7WordCap346, ws7WordP346, ws7WordQ346]
  have hword := ws7Word346WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule97 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨97, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (4/35 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep158 i) ≤ ws7WordCap158 (ws7WordRep158 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep158, ws7WordCap158, ws7WordP158, ws7WordQ158]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep158, ws7WordCap158, ws7WordP158, ws7WordQ158]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep158, ws7WordCap158, ws7WordP158, ws7WordQ158]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep158, ws7WordCap158, ws7WordP158, ws7WordQ158]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep158, ws7WordCap158, ws7WordP158, ws7WordQ158]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep158, ws7WordCap158, ws7WordP158, ws7WordQ158]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep158, ws7WordCap158, ws7WordP158, ws7WordQ158]
  have hword := ws7Word158WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule98 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨98, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (4/29 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (5/41 : ℝ)) ∧ (h 4 ≤ (4/33 : ℝ)) ∧ (h 5 ≤ (7/64 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep147 i) ≤ ws7WordCap147 (ws7WordRep147 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep147, ws7WordCap147, ws7WordP147, ws7WordQ147]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep147, ws7WordCap147, ws7WordP147, ws7WordQ147]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep147, ws7WordCap147, ws7WordP147, ws7WordQ147]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep147, ws7WordCap147, ws7WordP147, ws7WordQ147]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep147, ws7WordCap147, ws7WordP147, ws7WordQ147]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep147, ws7WordCap147, ws7WordP147, ws7WordQ147]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep147, ws7WordCap147, ws7WordP147, ws7WordQ147]
  have hword := ws7Word147WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule99 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨99, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (1/7 : ℝ)) ∧ (h 1 ≤ (11/87 : ℝ)) ∧ (h 2 ≤ (6/49 : ℝ)) ∧ (h 3 ≤ (3/25 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep341 i) ≤ ws7WordCap341 (ws7WordRep341 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep341, ws7WordCap341, ws7WordP341, ws7WordQ341]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep341, ws7WordCap341, ws7WordP341, ws7WordQ341]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep341, ws7WordCap341, ws7WordP341, ws7WordQ341]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep341, ws7WordCap341, ws7WordP341, ws7WordQ341]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep341, ws7WordCap341, ws7WordP341, ws7WordQ341]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep341, ws7WordCap341, ws7WordP341, ws7WordQ341]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep341, ws7WordCap341, ws7WordP341, ws7WordQ341]
  have hword := ws7Word341WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule100 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨100, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (12/55 : ℝ)) ∧ (h 0 ≤ (1/7 : ℝ)) ∧ (h 1 ≤ (5/39 : ℝ)) ∧ (h 2 ≤ (7/57 : ℝ)) ∧ (h 3 ≤ (3/25 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep315 i) ≤ ws7WordCap315 (ws7WordRep315 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep315, ws7WordCap315, ws7WordP315, ws7WordQ315]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep315, ws7WordCap315, ws7WordP315, ws7WordQ315]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep315, ws7WordCap315, ws7WordP315, ws7WordQ315]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep315, ws7WordCap315, ws7WordP315, ws7WordQ315]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep315, ws7WordCap315, ws7WordP315, ws7WordQ315]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep315, ws7WordCap315, ws7WordP315, ws7WordQ315]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep315, ws7WordCap315, ws7WordP315, ws7WordQ315]
  have hword := ws7Word315WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule101 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨101, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (1/7 : ℝ)) ∧ (h 1 ≤ (7/55 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (3/25 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep269 i) ≤ ws7WordCap269 (ws7WordRep269 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep269, ws7WordCap269, ws7WordP269, ws7WordQ269]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep269, ws7WordCap269, ws7WordP269, ws7WordQ269]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep269, ws7WordCap269, ws7WordP269, ws7WordQ269]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep269, ws7WordCap269, ws7WordP269, ws7WordQ269]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep269, ws7WordCap269, ws7WordP269, ws7WordQ269]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep269, ws7WordCap269, ws7WordP269, ws7WordQ269]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep269, ws7WordCap269, ws7WordP269, ws7WordQ269]
  have hword := ws7Word269WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule102 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨102, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (6/37 : ℝ)) ∧ (h 1 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (13/113 : ℝ)) ∧ (h 3 ≤ (3/28 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep364 i) ≤ ws7WordCap364 (ws7WordRep364 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep364, ws7WordCap364, ws7WordP364, ws7WordQ364]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep364, ws7WordCap364, ws7WordP364, ws7WordQ364]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep364, ws7WordCap364, ws7WordP364, ws7WordQ364]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep364, ws7WordCap364, ws7WordP364, ws7WordQ364]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep364, ws7WordCap364, ws7WordP364, ws7WordQ364]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep364, ws7WordCap364, ws7WordP364, ws7WordQ364]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep364, ws7WordCap364, ws7WordP364, ws7WordQ364]
  have hword := ws7Word364WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule103 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨103, by decide⟩ : Fin 157) h delta) :
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

theorem upperWordFitSchedule104 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨104, by decide⟩ : Fin 157) h delta) :
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

theorem upperWordFitSchedule105 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨105, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (5/32 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 3 ≤ (9/80 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep321 i) ≤ ws7WordCap321 (ws7WordRep321 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep321, ws7WordCap321, ws7WordP321, ws7WordQ321]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep321, ws7WordCap321, ws7WordP321, ws7WordQ321]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep321, ws7WordCap321, ws7WordP321, ws7WordQ321]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep321, ws7WordCap321, ws7WordP321, ws7WordQ321]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep321, ws7WordCap321, ws7WordP321, ws7WordQ321]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep321, ws7WordCap321, ws7WordP321, ws7WordQ321]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep321, ws7WordCap321, ws7WordP321, ws7WordQ321]
  have hword := ws7Word321WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule106 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨106, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (8/37 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (5/37 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (6/53 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep275 i) ≤ ws7WordCap275 (ws7WordRep275 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep275, ws7WordCap275, ws7WordP275, ws7WordQ275]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep275, ws7WordCap275, ws7WordP275, ws7WordQ275]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep275, ws7WordCap275, ws7WordP275, ws7WordQ275]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep275, ws7WordCap275, ws7WordP275, ws7WordQ275]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep275, ws7WordCap275, ws7WordP275, ws7WordQ275]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep275, ws7WordCap275, ws7WordP275, ws7WordQ275]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep275, ws7WordCap275, ws7WordP275, ws7WordQ275]
  have hword := ws7Word275WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule107 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨107, by decide⟩ : Fin 157) h delta) :
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

theorem upperWordFitSchedule108 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨108, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (7/45 : ℝ)) ∧ (h 1 ≤ (5/36 : ℝ)) ∧ (h 2 ≤ (5/42 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep251 i) ≤ ws7WordCap251 (ws7WordRep251 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep251, ws7WordCap251, ws7WordP251, ws7WordQ251]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep251, ws7WordCap251, ws7WordP251, ws7WordQ251]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep251, ws7WordCap251, ws7WordP251, ws7WordQ251]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep251, ws7WordCap251, ws7WordP251, ws7WordQ251]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep251, ws7WordCap251, ws7WordP251, ws7WordQ251]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep251, ws7WordCap251, ws7WordP251, ws7WordQ251]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep251, ws7WordCap251, ws7WordP251, ws7WordQ251]
  have hword := ws7Word251WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule109 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨109, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 2 ≤ (5/42 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep272 i) ≤ ws7WordCap272 (ws7WordRep272 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep272, ws7WordCap272, ws7WordP272, ws7WordQ272]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep272, ws7WordCap272, ws7WordP272, ws7WordQ272]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep272, ws7WordCap272, ws7WordP272, ws7WordQ272]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep272, ws7WordCap272, ws7WordP272, ws7WordQ272]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep272, ws7WordCap272, ws7WordP272, ws7WordQ272]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep272, ws7WordCap272, ws7WordP272, ws7WordQ272]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep272, ws7WordCap272, ws7WordP272, ws7WordQ272]
  have hword := ws7Word272WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule110 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨110, by decide⟩ : Fin 157) h delta) :
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

theorem upperWordFitSchedule111 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨111, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (7/45 : ℝ)) ∧ (h 1 ≤ (4/29 : ℝ)) ∧ (h 2 ≤ (7/60 : ℝ)) ∧ (h 3 ≤ (6/53 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep360 i) ≤ ws7WordCap360 (ws7WordRep360 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep360, ws7WordCap360, ws7WordP360, ws7WordQ360]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep360, ws7WordCap360, ws7WordP360, ws7WordQ360]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep360, ws7WordCap360, ws7WordP360, ws7WordQ360]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep360, ws7WordCap360, ws7WordP360, ws7WordQ360]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep360, ws7WordCap360, ws7WordP360, ws7WordQ360]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep360, ws7WordCap360, ws7WordP360, ws7WordQ360]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep360, ws7WordCap360, ws7WordP360, ws7WordQ360]
  have hword := ws7Word360WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule112 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨112, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (5/37 : ℝ)) ∧ (h 2 ≤ (31/263 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 4 ≤ (5/44 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep361 i) ≤ ws7WordCap361 (ws7WordRep361 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep361, ws7WordCap361, ws7WordP361, ws7WordQ361]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep361, ws7WordCap361, ws7WordP361, ws7WordQ361]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep361, ws7WordCap361, ws7WordP361, ws7WordQ361]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep361, ws7WordCap361, ws7WordP361, ws7WordQ361]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep361, ws7WordCap361, ws7WordP361, ws7WordQ361]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep361, ws7WordCap361, ws7WordP361, ws7WordQ361]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep361, ws7WordCap361, ws7WordP361, ws7WordQ361]
  have hword := ws7Word361WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule113 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨113, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (4/31 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (3/26 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep87 i) ≤ ws7WordCap87 (ws7WordRep87 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep87, ws7WordCap87, ws7WordP87, ws7WordQ87]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep87, ws7WordCap87, ws7WordP87, ws7WordQ87]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep87, ws7WordCap87, ws7WordP87, ws7WordQ87]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep87, ws7WordCap87, ws7WordP87, ws7WordQ87]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep87, ws7WordCap87, ws7WordP87, ws7WordQ87]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep87, ws7WordCap87, ws7WordP87, ws7WordQ87]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep87, ws7WordCap87, ws7WordP87, ws7WordQ87]
  have hword := ws7Word87WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule114 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨114, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (7/33 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (8/61 : ℝ)) ∧ (h 2 ≤ (9/76 : ℝ)) ∧ (h 3 ≤ (5/44 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep327 i) ≤ ws7WordCap327 (ws7WordRep327 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep327, ws7WordCap327, ws7WordP327, ws7WordQ327]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep327, ws7WordCap327, ws7WordP327, ws7WordQ327]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep327, ws7WordCap327, ws7WordP327, ws7WordQ327]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep327, ws7WordCap327, ws7WordP327, ws7WordQ327]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep327, ws7WordCap327, ws7WordP327, ws7WordQ327]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep327, ws7WordCap327, ws7WordP327, ws7WordQ327]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep327, ws7WordCap327, ws7WordP327, ws7WordQ327]
  have hword := ws7Word327WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule115 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨115, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (6/47 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (3/26 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep216 i) ≤ ws7WordCap216 (ws7WordRep216 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep216, ws7WordCap216, ws7WordP216, ws7WordQ216]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep216, ws7WordCap216, ws7WordP216, ws7WordQ216]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep216, ws7WordCap216, ws7WordP216, ws7WordQ216]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep216, ws7WordCap216, ws7WordP216, ws7WordQ216]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep216, ws7WordCap216, ws7WordP216, ws7WordQ216]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep216, ws7WordCap216, ws7WordP216, ws7WordQ216]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep216, ws7WordCap216, ws7WordP216, ws7WordQ216]
  have hword := ws7Word216WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule116 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨116, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (7/33 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (7/59 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 4 ≤ (5/44 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep319 i) ≤ ws7WordCap319 (ws7WordRep319 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep319, ws7WordCap319, ws7WordP319, ws7WordQ319]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep319, ws7WordCap319, ws7WordP319, ws7WordQ319]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep319, ws7WordCap319, ws7WordP319, ws7WordQ319]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep319, ws7WordCap319, ws7WordP319, ws7WordQ319]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep319, ws7WordCap319, ws7WordP319, ws7WordQ319]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep319, ws7WordCap319, ws7WordP319, ws7WordQ319]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep319, ws7WordCap319, ws7WordP319, ws7WordQ319]
  have hword := ws7Word319WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule117 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨117, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 2 ≤ (12/101 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (3/26 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep271 i) ≤ ws7WordCap271 (ws7WordRep271 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep271, ws7WordCap271, ws7WordP271, ws7WordQ271]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep271, ws7WordCap271, ws7WordP271, ws7WordQ271]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep271, ws7WordCap271, ws7WordP271, ws7WordQ271]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep271, ws7WordCap271, ws7WordP271, ws7WordQ271]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep271, ws7WordCap271, ws7WordP271, ws7WordQ271]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep271, ws7WordCap271, ws7WordP271, ws7WordQ271]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep271, ws7WordCap271, ws7WordP271, ws7WordQ271]
  have hword := ws7Word271WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule118 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨118, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep91 i) ≤ ws7WordCap91 (ws7WordRep91 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep91, ws7WordCap91, ws7WordP91, ws7WordQ91]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep91, ws7WordCap91, ws7WordP91, ws7WordQ91]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep91, ws7WordCap91, ws7WordP91, ws7WordQ91]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep91, ws7WordCap91, ws7WordP91, ws7WordQ91]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep91, ws7WordCap91, ws7WordP91, ws7WordQ91]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep91, ws7WordCap91, ws7WordP91, ws7WordQ91]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep91, ws7WordCap91, ws7WordP91, ws7WordQ91]
  have hword := ws7Word91WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule119 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨119, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (10/79 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep277 i) ≤ ws7WordCap277 (ws7WordRep277 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep277, ws7WordCap277, ws7WordP277, ws7WordQ277]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep277, ws7WordCap277, ws7WordP277, ws7WordQ277]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep277, ws7WordCap277, ws7WordP277, ws7WordQ277]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep277, ws7WordCap277, ws7WordP277, ws7WordQ277]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep277, ws7WordCap277, ws7WordP277, ws7WordQ277]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep277, ws7WordCap277, ws7WordP277, ws7WordQ277]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep277, ws7WordCap277, ws7WordP277, ws7WordQ277]
  have hword := ws7Word277WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule120 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨120, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (12/79 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 2 ≤ (5/42 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 4 ≤ (5/44 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep306 i) ≤ ws7WordCap306 (ws7WordRep306 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep306, ws7WordCap306, ws7WordP306, ws7WordQ306]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep306, ws7WordCap306, ws7WordP306, ws7WordQ306]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep306, ws7WordCap306, ws7WordP306, ws7WordQ306]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep306, ws7WordCap306, ws7WordP306, ws7WordQ306]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep306, ws7WordCap306, ws7WordP306, ws7WordQ306]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep306, ws7WordCap306, ws7WordP306, ws7WordQ306]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep306, ws7WordCap306, ws7WordP306, ws7WordQ306]
  have hword := ws7Word306WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule121 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨121, by decide⟩ : Fin 157) h delta) :
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

theorem upperWordFitSchedule122 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨122, by decide⟩ : Fin 157) h delta) :
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

theorem upperWordFitSchedule123 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨123, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (5/33 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (3/26 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep239 i) ≤ ws7WordCap239 (ws7WordRep239 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep239, ws7WordCap239, ws7WordP239, ws7WordQ239]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep239, ws7WordCap239, ws7WordP239, ws7WordQ239]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep239, ws7WordCap239, ws7WordP239, ws7WordQ239]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep239, ws7WordCap239, ws7WordP239, ws7WordQ239]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep239, ws7WordCap239, ws7WordP239, ws7WordQ239]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep239, ws7WordCap239, ws7WordP239, ws7WordQ239]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep239, ws7WordCap239, ws7WordP239, ws7WordQ239]
  have hword := ws7Word239WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule124 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨124, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (5/33 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 2 ≤ (9/74 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep320 i) ≤ ws7WordCap320 (ws7WordRep320 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep320, ws7WordCap320, ws7WordP320, ws7WordQ320]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep320, ws7WordCap320, ws7WordP320, ws7WordQ320]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep320, ws7WordCap320, ws7WordP320, ws7WordQ320]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep320, ws7WordCap320, ws7WordP320, ws7WordQ320]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep320, ws7WordCap320, ws7WordP320, ws7WordQ320]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep320, ws7WordCap320, ws7WordP320, ws7WordQ320]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep320, ws7WordCap320, ws7WordP320, ws7WordQ320]
  have hword := ws7Word320WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

end WeakSevenBandData
