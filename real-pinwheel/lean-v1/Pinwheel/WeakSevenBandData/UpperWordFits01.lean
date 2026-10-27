import Pinwheel.WeakSevenBandData.UpperWordFits00
import Pinwheel.WeakSevenBandData.SourceFits
import Pinwheel.WeakSevenBandData.RateOrder
import Pinwheel.WeakSeven
import Mathlib.Tactic.FinCases

/-! Source-box adapters for literal weak words. -/

namespace RealPinwheel.WeakSevenBandData

theorem upperWordFitSchedule43 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨43, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)) ∧ (h 0 ≤ (1/7 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep113 i) ≤ ws7WordCap113 (ws7WordRep113 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep113, ws7WordCap113, ws7WordP113, ws7WordQ113]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep113, ws7WordCap113, ws7WordP113, ws7WordQ113]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep113, ws7WordCap113, ws7WordP113, ws7WordQ113]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep113, ws7WordCap113, ws7WordP113, ws7WordQ113]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep113, ws7WordCap113, ws7WordP113, ws7WordQ113]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep113, ws7WordCap113, ws7WordP113, ws7WordQ113]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep113, ws7WordCap113, ws7WordP113, ws7WordQ113]
  have hword := ws7Word113WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule44 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨44, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)) ∧ (h 0 ≤ (9/64 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 2 ≤ (5/41 : ℝ)) ∧ (h 3 ≤ (7/60 : ℝ)) ∧ (h 4 ≤ (3/26 : ℝ)) ∧ (h 5 ≤ (4/35 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep280 i) ≤ ws7WordCap280 (ws7WordRep280 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep280, ws7WordCap280, ws7WordP280, ws7WordQ280]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep280, ws7WordCap280, ws7WordP280, ws7WordQ280]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep280, ws7WordCap280, ws7WordP280, ws7WordQ280]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep280, ws7WordCap280, ws7WordP280, ws7WordQ280]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep280, ws7WordCap280, ws7WordP280, ws7WordQ280]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep280, ws7WordCap280, ws7WordP280, ws7WordQ280]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep280, ws7WordCap280, ws7WordP280, ws7WordQ280]
  have hword := ws7Word280WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule45 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨45, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (11/49 : ℝ)) ∧ (h 0 ≤ (1/7 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (5/41 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep85 i) ≤ ws7WordCap85 (ws7WordRep85 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep85, ws7WordCap85, ws7WordP85, ws7WordQ85]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep85, ws7WordCap85, ws7WordP85, ws7WordQ85]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep85, ws7WordCap85, ws7WordP85, ws7WordQ85]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep85, ws7WordCap85, ws7WordP85, ws7WordQ85]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep85, ws7WordCap85, ws7WordP85, ws7WordQ85]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep85, ws7WordCap85, ws7WordP85, ws7WordQ85]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep85, ws7WordCap85, ws7WordP85, ws7WordQ85]
  have hword := ws7Word85WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule46 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨46, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/17 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 2 ≤ (4/35 : ℝ)) ∧ (h 3 ≤ (5/44 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep160 i) ≤ ws7WordCap160 (ws7WordRep160 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep160, ws7WordCap160, ws7WordP160, ws7WordQ160]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep160, ws7WordCap160, ws7WordP160, ws7WordQ160]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep160, ws7WordCap160, ws7WordP160, ws7WordQ160]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep160, ws7WordCap160, ws7WordP160, ws7WordQ160]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep160, ws7WordCap160, ws7WordP160, ws7WordQ160]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep160, ws7WordCap160, ws7WordP160, ws7WordQ160]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep160, ws7WordCap160, ws7WordP160, ws7WordQ160]
  have hword := ws7Word160WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule47 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨47, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 2 ≤ (7/60 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep136 i) ≤ ws7WordCap136 (ws7WordRep136 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep136, ws7WordCap136, ws7WordP136, ws7WordQ136]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep136, ws7WordCap136, ws7WordP136, ws7WordQ136]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep136, ws7WordCap136, ws7WordP136, ws7WordQ136]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep136, ws7WordCap136, ws7WordP136, ws7WordQ136]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep136, ws7WordCap136, ws7WordP136, ws7WordQ136]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep136, ws7WordCap136, ws7WordP136, ws7WordQ136]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep136, ws7WordCap136, ws7WordP136, ws7WordQ136]
  have hword := ws7Word136WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule48 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨48, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (4/33 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep237 i) ≤ ws7WordCap237 (ws7WordRep237 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep237, ws7WordCap237, ws7WordP237, ws7WordQ237]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep237, ws7WordCap237, ws7WordP237, ws7WordQ237]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep237, ws7WordCap237, ws7WordP237, ws7WordQ237]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep237, ws7WordCap237, ws7WordP237, ws7WordQ237]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep237, ws7WordCap237, ws7WordP237, ws7WordQ237]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep237, ws7WordCap237, ws7WordP237, ws7WordQ237]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep237, ws7WordCap237, ws7WordP237, ws7WordQ237]
  have hword := ws7Word237WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule49 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨49, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 1 ≤ (5/39 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep260 i) ≤ ws7WordCap260 (ws7WordRep260 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep260, ws7WordCap260, ws7WordP260, ws7WordQ260]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep260, ws7WordCap260, ws7WordP260, ws7WordQ260]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep260, ws7WordCap260, ws7WordP260, ws7WordQ260]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep260, ws7WordCap260, ws7WordP260, ws7WordQ260]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep260, ws7WordCap260, ws7WordP260, ws7WordQ260]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep260, ws7WordCap260, ws7WordP260, ws7WordQ260]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep260, ws7WordCap260, ws7WordP260, ws7WordQ260]
  have hword := ws7Word260WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule51 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨51, by decide⟩ : Fin 157) h delta) :
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

theorem upperWordFitSchedule52 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨52, by decide⟩ : Fin 157) h delta) :
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

theorem upperWordFitSchedule53 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨53, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (7/60 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep134 i) ≤ ws7WordCap134 (ws7WordRep134 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep134, ws7WordCap134, ws7WordP134, ws7WordQ134]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep134, ws7WordCap134, ws7WordP134, ws7WordQ134]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep134, ws7WordCap134, ws7WordP134, ws7WordQ134]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep134, ws7WordCap134, ws7WordP134, ws7WordQ134]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep134, ws7WordCap134, ws7WordP134, ws7WordQ134]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep134, ws7WordCap134, ws7WordP134, ws7WordQ134]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep134, ws7WordCap134, ws7WordP134, ws7WordQ134]
  have hword := ws7Word134WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule54 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨54, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (7/60 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep137 i) ≤ ws7WordCap137 (ws7WordRep137 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep137, ws7WordCap137, ws7WordP137, ws7WordQ137]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep137, ws7WordCap137, ws7WordP137, ws7WordQ137]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep137, ws7WordCap137, ws7WordP137, ws7WordQ137]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep137, ws7WordCap137, ws7WordP137, ws7WordQ137]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep137, ws7WordCap137, ws7WordP137, ws7WordQ137]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep137, ws7WordCap137, ws7WordP137, ws7WordQ137]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep137, ws7WordCap137, ws7WordP137, ws7WordQ137]
  have hword := ws7Word137WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule55 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨55, by decide⟩ : Fin 157) h delta) :
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

theorem upperWordFitSchedule56 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨56, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (8/63 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep365 i) ≤ ws7WordCap365 (ws7WordRep365 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep365, ws7WordCap365, ws7WordP365, ws7WordQ365]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep365, ws7WordCap365, ws7WordP365, ws7WordQ365]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep365, ws7WordCap365, ws7WordP365, ws7WordQ365]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep365, ws7WordCap365, ws7WordP365, ws7WordQ365]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep365, ws7WordCap365, ws7WordP365, ws7WordQ365]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep365, ws7WordCap365, ws7WordP365, ws7WordQ365]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep365, ws7WordCap365, ws7WordP365, ws7WordQ365]
  have hword := ws7Word365WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule57 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨57, by decide⟩ : Fin 157) h delta) :
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

theorem upperWordFitSchedule58 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨58, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (5/22 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (5/44 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep221 i) ≤ ws7WordCap221 (ws7WordRep221 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep221, ws7WordCap221, ws7WordP221, ws7WordQ221]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep221, ws7WordCap221, ws7WordP221, ws7WordQ221]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep221, ws7WordCap221, ws7WordP221, ws7WordQ221]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep221, ws7WordCap221, ws7WordP221, ws7WordQ221]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep221, ws7WordCap221, ws7WordP221, ws7WordQ221]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep221, ws7WordCap221, ws7WordP221, ws7WordQ221]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep221, ws7WordCap221, ws7WordP221, ws7WordQ221]
  have hword := ws7Word221WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule59 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨59, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (4/33 : ℝ)) ∧ (h 2 ≤ (3/26 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep316 i) ≤ ws7WordCap316 (ws7WordRep316 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep316, ws7WordCap316, ws7WordP316, ws7WordQ316]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep316, ws7WordCap316, ws7WordP316, ws7WordQ316]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep316, ws7WordCap316, ws7WordP316, ws7WordQ316]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep316, ws7WordCap316, ws7WordP316, ws7WordQ316]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep316, ws7WordCap316, ws7WordP316, ws7WordQ316]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep316, ws7WordCap316, ws7WordP316, ws7WordQ316]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep316, ws7WordCap316, ws7WordP316, ws7WordQ316]
  have hword := ws7Word316WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule60 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨60, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (11/92 : ℝ)) ∧ (h 4 ≤ (8/67 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep240 i) ≤ ws7WordCap240 (ws7WordRep240 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep240, ws7WordCap240, ws7WordP240, ws7WordQ240]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep240, ws7WordCap240, ws7WordP240, ws7WordQ240]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep240, ws7WordCap240, ws7WordP240, ws7WordQ240]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep240, ws7WordCap240, ws7WordP240, ws7WordQ240]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep240, ws7WordCap240, ws7WordP240, ws7WordQ240]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep240, ws7WordCap240, ws7WordP240, ws7WordQ240]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep240, ws7WordCap240, ws7WordP240, ws7WordQ240]
  have hword := ws7Word240WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule61 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨61, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (3/16 : ℝ)) ∧ (h 1 ≤ (5/36 : ℝ)) ∧ (h 2 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep27 i) ≤ ws7WordCap27 (ws7WordRep27 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep27, ws7WordCap27, ws7WordP27, ws7WordQ27]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep27, ws7WordCap27, ws7WordP27, ws7WordQ27]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep27, ws7WordCap27, ws7WordP27, ws7WordQ27]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep27, ws7WordCap27, ws7WordP27, ws7WordQ27]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep27, ws7WordCap27, ws7WordP27, ws7WordQ27]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep27, ws7WordCap27, ws7WordP27, ws7WordQ27]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep27, ws7WordCap27, ws7WordP27, ws7WordQ27]
  have hword := ws7Word27WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule62 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨62, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (2/11 : ℝ)) ∧ (h 1 ≤ (6/47 : ℝ)) ∧ (h 2 ≤ (5/44 : ℝ)) ∧ (h 3 ≤ (3/28 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep371 i) ≤ ws7WordCap371 (ws7WordRep371 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep371, ws7WordCap371, ws7WordP371, ws7WordQ371]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep371, ws7WordCap371, ws7WordP371, ws7WordQ371]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep371, ws7WordCap371, ws7WordP371, ws7WordQ371]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep371, ws7WordCap371, ws7WordP371, ws7WordQ371]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep371, ws7WordCap371, ws7WordP371, ws7WordQ371]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep371, ws7WordCap371, ws7WordP371, ws7WordQ371]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep371, ws7WordCap371, ws7WordP371, ws7WordQ371]
  have hword := ws7Word371WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule63 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨63, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (2/11 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 2 ≤ (4/35 : ℝ)) ∧ (h 4 ≤ (5/44 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep164 i) ≤ ws7WordCap164 (ws7WordRep164 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep164, ws7WordCap164, ws7WordP164, ws7WordQ164]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep164, ws7WordCap164, ws7WordP164, ws7WordQ164]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep164, ws7WordCap164, ws7WordP164, ws7WordQ164]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep164, ws7WordCap164, ws7WordP164, ws7WordQ164]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep164, ws7WordCap164, ws7WordP164, ws7WordQ164]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep164, ws7WordCap164, ws7WordP164, ws7WordQ164]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep164, ws7WordCap164, ws7WordP164, ws7WordQ164]
  have hword := ws7Word164WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule64 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨64, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (7/36 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 2 ≤ (6/53 : ℝ)) ∧ (h 3 ≤ (6/55 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep359 i) ≤ ws7WordCap359 (ws7WordRep359 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep359, ws7WordCap359, ws7WordP359, ws7WordQ359]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep359, ws7WordCap359, ws7WordP359, ws7WordQ359]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep359, ws7WordCap359, ws7WordP359, ws7WordQ359]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep359, ws7WordCap359, ws7WordP359, ws7WordQ359]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep359, ws7WordCap359, ws7WordP359, ws7WordQ359]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep359, ws7WordCap359, ws7WordP359, ws7WordQ359]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep359, ws7WordCap359, ws7WordP359, ws7WordQ359]
  have hword := ws7Word359WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule65 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨65, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (2/11 : ℝ)) ∧ (h 1 ≤ (11/87 : ℝ)) ∧ (h 2 ≤ (3/26 : ℝ)) ∧ (h 3 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep355 i) ≤ ws7WordCap355 (ws7WordRep355 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep355, ws7WordCap355, ws7WordP355, ws7WordQ355]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep355, ws7WordCap355, ws7WordP355, ws7WordQ355]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep355, ws7WordCap355, ws7WordP355, ws7WordQ355]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep355, ws7WordCap355, ws7WordP355, ws7WordQ355]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep355, ws7WordCap355, ws7WordP355, ws7WordQ355]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep355, ws7WordCap355, ws7WordP355, ws7WordQ355]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep355, ws7WordCap355, ws7WordP355, ws7WordQ355]
  have hword := ws7Word355WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule66 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨66, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (11/51 : ℝ)) ∧ (h 0 ≤ (3/17 : ℝ)) ∧ (h 1 ≤ (7/50 : ℝ)) ∧ (h 2 ≤ (4/35 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep331 i) ≤ ws7WordCap331 (ws7WordRep331 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep331, ws7WordCap331, ws7WordP331, ws7WordQ331]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep331, ws7WordCap331, ws7WordP331, ws7WordQ331]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep331, ws7WordCap331, ws7WordP331, ws7WordQ331]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep331, ws7WordCap331, ws7WordP331, ws7WordQ331]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep331, ws7WordCap331, ws7WordP331, ws7WordQ331]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep331, ws7WordCap331, ws7WordP331, ws7WordQ331]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep331, ws7WordCap331, ws7WordP331, ws7WordQ331]
  have hword := ws7Word331WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule67 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨67, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (7/41 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 3 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep267 i) ≤ ws7WordCap267 (ws7WordRep267 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep267, ws7WordCap267, ws7WordP267, ws7WordQ267]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep267, ws7WordCap267, ws7WordP267, ws7WordQ267]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep267, ws7WordCap267, ws7WordP267, ws7WordQ267]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep267, ws7WordCap267, ws7WordP267, ws7WordQ267]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep267, ws7WordCap267, ws7WordP267, ws7WordQ267]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep267, ws7WordCap267, ws7WordP267, ws7WordQ267]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep267, ws7WordCap267, ws7WordP267, ws7WordQ267]
  have hword := ws7Word267WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule68 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨68, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (2/11 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 3 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep311 i) ≤ ws7WordCap311 (ws7WordRep311 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep311, ws7WordCap311, ws7WordP311, ws7WordQ311]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep311, ws7WordCap311, ws7WordP311, ws7WordQ311]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep311, ws7WordCap311, ws7WordP311, ws7WordQ311]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep311, ws7WordCap311, ws7WordP311, ws7WordQ311]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep311, ws7WordCap311, ws7WordP311, ws7WordQ311]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep311, ws7WordCap311, ws7WordP311, ws7WordQ311]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep311, ws7WordCap311, ws7WordP311, ws7WordQ311]
  have hword := ws7Word311WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule69 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨69, by decide⟩ : Fin 157) h delta) :
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

theorem upperWordFitSchedule70 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨70, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (17/99 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep297 i) ≤ ws7WordCap297 (ws7WordRep297 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep297, ws7WordCap297, ws7WordP297, ws7WordQ297]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep297, ws7WordCap297, ws7WordP297, ws7WordQ297]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep297, ws7WordCap297, ws7WordP297, ws7WordQ297]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep297, ws7WordCap297, ws7WordP297, ws7WordQ297]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep297, ws7WordCap297, ws7WordP297, ws7WordQ297]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep297, ws7WordCap297, ws7WordP297, ws7WordQ297]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep297, ws7WordCap297, ws7WordP297, ws7WordQ297]
  have hword := ws7Word297WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule71 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨71, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (3/28 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep7 i) ≤ ws7WordCap7 (ws7WordRep7 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep7, ws7WordCap7, ws7WordP7, ws7WordQ7]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep7, ws7WordCap7, ws7WordP7, ws7WordQ7]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep7, ws7WordCap7, ws7WordP7, ws7WordQ7]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep7, ws7WordCap7, ws7WordP7, ws7WordQ7]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep7, ws7WordCap7, ws7WordP7, ws7WordQ7]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep7, ws7WordCap7, ws7WordP7, ws7WordQ7]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep7, ws7WordCap7, ws7WordP7, ws7WordQ7]
  have hword := ws7Word7WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule72 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨72, by decide⟩ : Fin 157) h delta) :
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

theorem upperWordFitSchedule73 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨73, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (5/32 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 2 ≤ (22/189 : ℝ)) ∧ (h 3 ≤ (5/44 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep372 i) ≤ ws7WordCap372 (ws7WordRep372 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep372, ws7WordCap372, ws7WordP372, ws7WordQ372]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep372, ws7WordCap372, ws7WordP372, ws7WordQ372]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep372, ws7WordCap372, ws7WordP372, ws7WordQ372]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep372, ws7WordCap372, ws7WordP372, ws7WordQ372]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep372, ws7WordCap372, ws7WordP372, ws7WordQ372]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep372, ws7WordCap372, ws7WordP372, ws7WordQ372]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep372, ws7WordCap372, ws7WordP372, ws7WordQ372]
  have hword := ws7Word372WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule74 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨74, by decide⟩ : Fin 157) h delta) :
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

theorem upperWordFitSchedule75 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨75, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (5/37 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 4 ≤ (3/28 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep352 i) ≤ ws7WordCap352 (ws7WordRep352 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep352, ws7WordCap352, ws7WordP352, ws7WordQ352]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep352, ws7WordCap352, ws7WordP352, ws7WordQ352]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep352, ws7WordCap352, ws7WordP352, ws7WordQ352]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep352, ws7WordCap352, ws7WordP352, ws7WordQ352]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep352, ws7WordCap352, ws7WordP352, ws7WordQ352]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep352, ws7WordCap352, ws7WordP352, ws7WordQ352]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep352, ws7WordCap352, ws7WordP352, ws7WordQ352]
  have hword := ws7Word352WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule76 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨76, by decide⟩ : Fin 157) h delta) :
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

theorem upperWordFitSchedule77 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨77, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (7/41 : ℝ)) ∧ (h 1 ≤ (9/71 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 4 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep368 i) ≤ ws7WordCap368 (ws7WordRep368 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep368, ws7WordCap368, ws7WordP368, ws7WordQ368]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep368, ws7WordCap368, ws7WordP368, ws7WordQ368]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep368, ws7WordCap368, ws7WordP368, ws7WordQ368]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep368, ws7WordCap368, ws7WordP368, ws7WordQ368]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep368, ws7WordCap368, ws7WordP368, ws7WordQ368]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep368, ws7WordCap368, ws7WordP368, ws7WordQ368]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep368, ws7WordCap368, ws7WordP368, ws7WordQ368]
  have hword := ws7Word368WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule78 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨78, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (12/71 : ℝ)) ∧ (h 1 ≤ (10/79 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep347 i) ≤ ws7WordCap347 (ws7WordRep347 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep347, ws7WordCap347, ws7WordP347, ws7WordQ347]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep347, ws7WordCap347, ws7WordP347, ws7WordQ347]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep347, ws7WordCap347, ws7WordP347, ws7WordQ347]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep347, ws7WordCap347, ws7WordP347, ws7WordQ347]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep347, ws7WordCap347, ws7WordP347, ws7WordQ347]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep347, ws7WordCap347, ws7WordP347, ws7WordQ347]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep347, ws7WordCap347, ws7WordP347, ws7WordQ347]
  have hword := ws7Word347WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule79 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨79, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (2/11 : ℝ)) ∧ (h 1 ≤ (4/31 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 4 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep300 i) ≤ ws7WordCap300 (ws7WordRep300 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep300, ws7WordCap300, ws7WordP300, ws7WordQ300]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep300, ws7WordCap300, ws7WordP300, ws7WordQ300]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep300, ws7WordCap300, ws7WordP300, ws7WordQ300]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep300, ws7WordCap300, ws7WordP300, ws7WordQ300]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep300, ws7WordCap300, ws7WordP300, ws7WordQ300]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep300, ws7WordCap300, ws7WordP300, ws7WordQ300]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep300, ws7WordCap300, ws7WordP300, ws7WordQ300]
  have hword := ws7Word300WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule80 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨80, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (4/23 : ℝ)) ∧ (h 1 ≤ (4/31 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 4 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep155 i) ≤ ws7WordCap155 (ws7WordRep155 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep155, ws7WordCap155, ws7WordP155, ws7WordQ155]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep155, ws7WordCap155, ws7WordP155, ws7WordQ155]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep155, ws7WordCap155, ws7WordP155, ws7WordQ155]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep155, ws7WordCap155, ws7WordP155, ws7WordQ155]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep155, ws7WordCap155, ws7WordP155, ws7WordQ155]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep155, ws7WordCap155, ws7WordP155, ws7WordQ155]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep155, ws7WordCap155, ws7WordP155, ws7WordQ155]
  have hword := ws7Word155WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule81 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨81, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (11/65 : ℝ)) ∧ (h 1 ≤ (7/55 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (5/44 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep247 i) ≤ ws7WordCap247 (ws7WordRep247 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep247, ws7WordCap247, ws7WordP247, ws7WordQ247]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep247, ws7WordCap247, ws7WordP247, ws7WordQ247]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep247, ws7WordCap247, ws7WordP247, ws7WordQ247]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep247, ws7WordCap247, ws7WordP247, ws7WordQ247]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep247, ws7WordCap247, ws7WordP247, ws7WordQ247]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep247, ws7WordCap247, ws7WordP247, ws7WordQ247]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep247, ws7WordCap247, ws7WordP247, ws7WordQ247]
  have hword := ws7Word247WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule82 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨82, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (9/71 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 4 ≤ (6/53 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep310 i) ≤ ws7WordCap310 (ws7WordRep310 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep310, ws7WordCap310, ws7WordP310, ws7WordQ310]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep310, ws7WordCap310, ws7WordP310, ws7WordQ310]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep310, ws7WordCap310, ws7WordP310, ws7WordQ310]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep310, ws7WordCap310, ws7WordP310, ws7WordQ310]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep310, ws7WordCap310, ws7WordP310, ws7WordQ310]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep310, ws7WordCap310, ws7WordP310, ws7WordQ310]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep310, ws7WordCap310, ws7WordP310, ws7WordQ310]
  have hword := ws7Word310WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule83 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨83, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (10/47 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep120 i) ≤ ws7WordCap120 (ws7WordRep120 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep120, ws7WordCap120, ws7WordP120, ws7WordQ120]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep120, ws7WordCap120, ws7WordP120, ws7WordQ120]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep120, ws7WordCap120, ws7WordP120, ws7WordQ120]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep120, ws7WordCap120, ws7WordP120, ws7WordQ120]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep120, ws7WordCap120, ws7WordP120, ws7WordQ120]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep120, ws7WordCap120, ws7WordP120, ws7WordQ120]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep120, ws7WordCap120, ws7WordP120, ws7WordQ120]
  have hword := ws7Word120WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

end WeakSevenBandData
