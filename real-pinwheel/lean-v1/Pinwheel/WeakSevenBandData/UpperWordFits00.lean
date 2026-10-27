import Pinwheel.WeakSevenBandData.WordSources
import Pinwheel.WeakSevenBandData.SourceFits
import Pinwheel.WeakSevenBandData.RateOrder
import Pinwheel.WeakSeven
import Mathlib.Tactic.FinCases

/-! Source-box adapters for literal weak words. -/

namespace RealPinwheel.WeakSevenBandData

theorem upperWordFitSchedule0 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨0, by decide⟩ : Fin 157) h delta) :
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

theorem upperWordFitSchedule1 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨1, by decide⟩ : Fin 157) h delta) :
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

theorem upperWordFitSchedule2 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨2, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (7/32 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep14 i) ≤ ws7WordCap14 (ws7WordRep14 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep14, ws7WordCap14, ws7WordP14, ws7WordQ14]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep14, ws7WordCap14, ws7WordP14, ws7WordQ14]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep14, ws7WordCap14, ws7WordP14, ws7WordQ14]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep14, ws7WordCap14, ws7WordP14, ws7WordQ14]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep14, ws7WordCap14, ws7WordP14, ws7WordQ14]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep14, ws7WordCap14, ws7WordP14, ws7WordQ14]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep14, ws7WordCap14, ws7WordP14, ws7WordQ14]
  have hword := ws7Word14WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule3 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨3, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep50 i) ≤ ws7WordCap50 (ws7WordRep50 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep50, ws7WordCap50, ws7WordP50, ws7WordQ50]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep50, ws7WordCap50, ws7WordP50, ws7WordQ50]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep50, ws7WordCap50, ws7WordP50, ws7WordQ50]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep50, ws7WordCap50, ws7WordP50, ws7WordQ50]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep50, ws7WordCap50, ws7WordP50, ws7WordQ50]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep50, ws7WordCap50, ws7WordP50, ws7WordQ50]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep50, ws7WordCap50, ws7WordP50, ws7WordQ50]
  have hword := ws7Word50WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule4 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨4, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (13/112 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep256 i) ≤ ws7WordCap256 (ws7WordRep256 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep256, ws7WordCap256, ws7WordP256, ws7WordQ256]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep256, ws7WordCap256, ws7WordP256, ws7WordQ256]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep256, ws7WordCap256, ws7WordP256, ws7WordQ256]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep256, ws7WordCap256, ws7WordP256, ws7WordQ256]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep256, ws7WordCap256, ws7WordP256, ws7WordQ256]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep256, ws7WordCap256, ws7WordP256, ws7WordQ256]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep256, ws7WordCap256, ws7WordP256, ws7WordQ256]
  have hword := ws7Word256WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule5 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨5, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (5/21 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (13/108 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep242 i) ≤ ws7WordCap242 (ws7WordRep242 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep242, ws7WordCap242, ws7WordP242, ws7WordQ242]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep242, ws7WordCap242, ws7WordP242, ws7WordQ242]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep242, ws7WordCap242, ws7WordP242, ws7WordQ242]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep242, ws7WordCap242, ws7WordP242, ws7WordQ242]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep242, ws7WordCap242, ws7WordP242, ws7WordQ242]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep242, ws7WordCap242, ws7WordP242, ws7WordQ242]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep242, ws7WordCap242, ws7WordP242, ws7WordQ242]
  have hword := ws7Word242WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule6 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨6, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (11/80 : ℝ)) ∧ (h 1 ≤ (7/51 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep193 i) ≤ ws7WordCap193 (ws7WordRep193 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep193, ws7WordCap193, ws7WordP193, ws7WordQ193]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep193, ws7WordCap193, ws7WordP193, ws7WordQ193]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep193, ws7WordCap193, ws7WordP193, ws7WordQ193]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep193, ws7WordCap193, ws7WordP193, ws7WordQ193]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep193, ws7WordCap193, ws7WordP193, ws7WordQ193]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep193, ws7WordCap193, ws7WordP193, ws7WordQ193]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep193, ws7WordCap193, ws7WordP193, ws7WordQ193]
  have hword := ws7Word193WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule7 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨7, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (6/41 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (5/44 : ℝ)) ∧ (h 4 ≤ (6/53 : ℝ)) ∧ (h 5 ≤ (3/28 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep350 i) ≤ ws7WordCap350 (ws7WordRep350 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep350, ws7WordCap350, ws7WordP350, ws7WordQ350]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep350, ws7WordCap350, ws7WordP350, ws7WordQ350]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep350, ws7WordCap350, ws7WordP350, ws7WordQ350]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep350, ws7WordCap350, ws7WordP350, ws7WordQ350]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep350, ws7WordCap350, ws7WordP350, ws7WordQ350]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep350, ws7WordCap350, ws7WordP350, ws7WordQ350]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep350, ws7WordCap350, ws7WordP350, ws7WordQ350]
  have hword := ws7Word350WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule8 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨8, by decide⟩ : Fin 157) h delta) :
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

theorem upperWordFitSchedule9 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨9, by decide⟩ : Fin 157) h delta) :
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

theorem upperWordFitSchedule10 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨10, by decide⟩ : Fin 157) h delta) :
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

theorem upperWordFitSchedule11 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨11, by decide⟩ : Fin 157) h delta) :
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

theorem upperWordFitSchedule12 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨12, by decide⟩ : Fin 157) h delta) :
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

theorem upperWordFitSchedule13 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨13, by decide⟩ : Fin 157) h delta) :
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

theorem upperWordFitSchedule14 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨14, by decide⟩ : Fin 157) h delta) :
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

theorem upperWordFitSchedule15 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨15, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (7/33 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (5/37 : ℝ)) ∧ (h 2 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 4 ≤ (3/28 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep293 i) ≤ ws7WordCap293 (ws7WordRep293 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep293, ws7WordCap293, ws7WordP293, ws7WordQ293]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep293, ws7WordCap293, ws7WordP293, ws7WordQ293]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep293, ws7WordCap293, ws7WordP293, ws7WordQ293]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep293, ws7WordCap293, ws7WordP293, ws7WordQ293]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep293, ws7WordCap293, ws7WordP293, ws7WordQ293]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep293, ws7WordCap293, ws7WordP293, ws7WordQ293]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep293, ws7WordCap293, ws7WordP293, ws7WordQ293]
  have hword := ws7Word293WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule16 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨16, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (5/32 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 2 ≤ (5/38 : ℝ)) ∧ (h 3 ≤ (9/79 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep278 i) ≤ ws7WordCap278 (ws7WordRep278 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep278, ws7WordCap278, ws7WordP278, ws7WordQ278]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep278, ws7WordCap278, ws7WordP278, ws7WordQ278]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep278, ws7WordCap278, ws7WordP278, ws7WordQ278]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep278, ws7WordCap278, ws7WordP278, ws7WordQ278]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep278, ws7WordCap278, ws7WordP278, ws7WordQ278]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep278, ws7WordCap278, ws7WordP278, ws7WordQ278]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep278, ws7WordCap278, ws7WordP278, ws7WordQ278]
  have hword := ws7Word278WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule17 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨17, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (5/38 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (3/28 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep248 i) ≤ ws7WordCap248 (ws7WordRep248 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep248, ws7WordCap248, ws7WordP248, ws7WordQ248]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep248, ws7WordCap248, ws7WordP248, ws7WordQ248]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep248, ws7WordCap248, ws7WordP248, ws7WordQ248]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep248, ws7WordCap248, ws7WordP248, ws7WordQ248]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep248, ws7WordCap248, ws7WordP248, ws7WordQ248]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep248, ws7WordCap248, ws7WordP248, ws7WordQ248]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep248, ws7WordCap248, ws7WordP248, ws7WordQ248]
  have hword := ws7Word248WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule18 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨18, by decide⟩ : Fin 157) h delta) :
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

theorem upperWordFitSchedule19 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨19, by decide⟩ : Fin 157) h delta) :
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

theorem upperWordFitSchedule20 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨20, by decide⟩ : Fin 157) h delta) :
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

theorem upperWordFitSchedule21 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨21, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (1/7 : ℝ)) ∧ (h 3 ≤ (5/42 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep54 i) ≤ ws7WordCap54 (ws7WordRep54 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep54, ws7WordCap54, ws7WordP54, ws7WordQ54]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep54, ws7WordCap54, ws7WordP54, ws7WordQ54]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep54, ws7WordCap54, ws7WordP54, ws7WordQ54]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep54, ws7WordCap54, ws7WordP54, ws7WordQ54]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep54, ws7WordCap54, ws7WordP54, ws7WordQ54]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep54, ws7WordCap54, ws7WordP54, ws7WordQ54]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep54, ws7WordCap54, ws7WordP54, ws7WordQ54]
  have hword := ws7Word54WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule22 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨22, by decide⟩ : Fin 157) h delta) :
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

theorem upperWordFitSchedule23 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨23, by decide⟩ : Fin 157) h delta) :
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

theorem upperWordFitSchedule24 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨24, by decide⟩ : Fin 157) h delta) :
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

theorem upperWordFitSchedule25 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨25, by decide⟩ : Fin 157) h delta) :
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

theorem upperWordFitSchedule26 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨26, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (6/41 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep125 i) ≤ ws7WordCap125 (ws7WordRep125 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep125, ws7WordCap125, ws7WordP125, ws7WordQ125]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep125, ws7WordCap125, ws7WordP125, ws7WordQ125]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep125, ws7WordCap125, ws7WordP125, ws7WordQ125]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep125, ws7WordCap125, ws7WordP125, ws7WordQ125]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep125, ws7WordCap125, ws7WordP125, ws7WordQ125]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep125, ws7WordCap125, ws7WordP125, ws7WordQ125]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep125, ws7WordCap125, ws7WordP125, ws7WordQ125]
  have hword := ws7Word125WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule27 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨27, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (25/173 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (3/22 : ℝ)) ∧ (h 3 ≤ (7/61 : ℝ)) ∧ (h 4 ≤ (5/44 : ℝ)) ∧ (h 5 ≤ (6/53 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep309 i) ≤ ws7WordCap309 (ws7WordRep309 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep309, ws7WordCap309, ws7WordP309, ws7WordQ309]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep309, ws7WordCap309, ws7WordP309, ws7WordQ309]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep309, ws7WordCap309, ws7WordP309, ws7WordQ309]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep309, ws7WordCap309, ws7WordP309, ws7WordQ309]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep309, ws7WordCap309, ws7WordP309, ws7WordQ309]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep309, ws7WordCap309, ws7WordP309, ws7WordQ309]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep309, ws7WordCap309, ws7WordP309, ws7WordQ309]
  have hword := ws7Word309WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule28 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨28, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (13/90 : ℝ)) ∧ (h 1 ≤ (5/37 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (15/131 : ℝ)) ∧ (h 4 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep303 i) ≤ ws7WordCap303 (ws7WordRep303 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep303, ws7WordCap303, ws7WordP303, ws7WordQ303]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep303, ws7WordCap303, ws7WordP303, ws7WordQ303]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep303, ws7WordCap303, ws7WordP303, ws7WordQ303]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep303, ws7WordCap303, ws7WordP303, ws7WordQ303]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep303, ws7WordCap303, ws7WordP303, ws7WordQ303]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep303, ws7WordCap303, ws7WordP303, ws7WordQ303]
    · convert hc6 using 1
      · rfl
      · norm_num [ws7WordRep303, ws7WordCap303, ws7WordP303, ws7WordQ303]
  have hword := ws7Word303WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule29 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨29, by decide⟩ : Fin 157) h delta) :
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

theorem upperWordFitSchedule33 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨33, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (8/35 : ℝ)) ∧ (h 0 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep20 i) ≤ ws7WordCap20 (ws7WordRep20 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep20, ws7WordCap20, ws7WordP20, ws7WordQ20]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep20, ws7WordCap20, ws7WordP20, ws7WordQ20]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep20, ws7WordCap20, ws7WordP20, ws7WordQ20]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep20, ws7WordCap20, ws7WordP20, ws7WordQ20]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep20, ws7WordCap20, ws7WordP20, ws7WordQ20]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep20, ws7WordCap20, ws7WordP20, ws7WordQ20]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep20, ws7WordCap20, ws7WordP20, ws7WordQ20]
  have hword := ws7Word20WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule34 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨34, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (5/42 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep56 i) ≤ ws7WordCap56 (ws7WordRep56 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep56, ws7WordCap56, ws7WordP56, ws7WordQ56]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep56, ws7WordCap56, ws7WordP56, ws7WordQ56]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep56, ws7WordCap56, ws7WordP56, ws7WordQ56]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep56, ws7WordCap56, ws7WordP56, ws7WordQ56]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep56, ws7WordCap56, ws7WordP56, ws7WordQ56]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep56, ws7WordCap56, ws7WordP56, ws7WordQ56]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep56, ws7WordCap56, ws7WordP56, ws7WordQ56]
  have hword := ws7Word56WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule35 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨35, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (5/22 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (17/141 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (3/26 : ℝ)) ∧ (h 5 ≤ (5/44 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep356 i) ≤ ws7WordCap356 (ws7WordRep356 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep356, ws7WordCap356, ws7WordP356, ws7WordQ356]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep356, ws7WordCap356, ws7WordP356, ws7WordQ356]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep356, ws7WordCap356, ws7WordP356, ws7WordQ356]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep356, ws7WordCap356, ws7WordP356, ws7WordQ356]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep356, ws7WordCap356, ws7WordP356, ws7WordQ356]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep356, ws7WordCap356, ws7WordP356, ws7WordQ356]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep356, ws7WordCap356, ws7WordP356, ws7WordQ356]
  have hword := ws7Word356WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule36 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨36, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (1/4 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep264 i) ≤ ws7WordCap264 (ws7WordRep264 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep264, ws7WordCap264, ws7WordP264, ws7WordQ264]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep264, ws7WordCap264, ws7WordP264, ws7WordQ264]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep264, ws7WordCap264, ws7WordP264, ws7WordQ264]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep264, ws7WordCap264, ws7WordP264, ws7WordQ264]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep264, ws7WordCap264, ws7WordP264, ws7WordQ264]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep264, ws7WordCap264, ws7WordP264, ws7WordQ264]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep264, ws7WordCap264, ws7WordP264, ws7WordQ264]
  have hword := ws7Word264WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule37 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨37, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (4/17 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep204 i) ≤ ws7WordCap204 (ws7WordRep204 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep204, ws7WordCap204, ws7WordP204, ws7WordQ204]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep204, ws7WordCap204, ws7WordP204, ws7WordQ204]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep204, ws7WordCap204, ws7WordP204, ws7WordQ204]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep204, ws7WordCap204, ws7WordP204, ws7WordQ204]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep204, ws7WordCap204, ws7WordP204, ws7WordQ204]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep204, ws7WordCap204, ws7WordP204, ws7WordQ204]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep204, ws7WordCap204, ws7WordP204, ws7WordQ204]
  have hword := ws7Word204WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule38 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨38, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (5/22 : ℝ)) ∧ (h 0 ≤ (7/46 : ℝ)) ∧ (h 1 ≤ (5/41 : ℝ)) ∧ (h 2 ≤ (7/58 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep369 i) ≤ ws7WordCap369 (ws7WordRep369 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep369, ws7WordCap369, ws7WordP369, ws7WordQ369]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep369, ws7WordCap369, ws7WordP369, ws7WordQ369]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep369, ws7WordCap369, ws7WordP369, ws7WordQ369]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep369, ws7WordCap369, ws7WordP369, ws7WordQ369]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep369, ws7WordCap369, ws7WordP369, ws7WordQ369]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep369, ws7WordCap369, ws7WordP369, ws7WordQ369]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep369, ws7WordCap369, ws7WordP369, ws7WordQ369]
  have hword := ws7Word369WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule39 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨39, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (7/31 : ℝ)) ∧ (h 0 ≤ (8/55 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (6/53 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep302 i) ≤ ws7WordCap302 (ws7WordRep302 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep302, ws7WordCap302, ws7WordP302, ws7WordQ302]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep302, ws7WordCap302, ws7WordP302, ws7WordQ302]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep302, ws7WordCap302, ws7WordP302, ws7WordQ302]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep302, ws7WordCap302, ws7WordP302, ws7WordQ302]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep302, ws7WordCap302, ws7WordP302, ws7WordQ302]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep302, ws7WordCap302, ws7WordP302, ws7WordQ302]
    · convert hc5 using 1
      · rfl
      · norm_num [ws7WordRep302, ws7WordCap302, ws7WordP302, ws7WordQ302]
  have hword := ws7Word302WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule40 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨40, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (16/71 : ℝ)) ∧ (h 0 ≤ (5/34 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (5/44 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3, hc4⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep322 i) ≤ ws7WordCap322 (ws7WordRep322 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep322, ws7WordCap322, ws7WordP322, ws7WordQ322]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep322, ws7WordCap322, ws7WordP322, ws7WordQ322]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep322, ws7WordCap322, ws7WordP322, ws7WordQ322]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep322, ws7WordCap322, ws7WordP322, ws7WordQ322]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep322, ws7WordCap322, ws7WordP322, ws7WordQ322]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep322, ws7WordCap322, ws7WordP322, ws7WordQ322]
    · convert hc4 using 1
      · rfl
      · norm_num [ws7WordRep322, ws7WordCap322, ws7WordP322, ws7WordQ322]
  have hword := ws7Word322WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule41 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨41, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (7/31 : ℝ)) ∧ (h 0 ≤ (7/48 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep83 i) ≤ ws7WordCap83 (ws7WordRep83 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep83, ws7WordCap83, ws7WordP83, ws7WordQ83]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep83, ws7WordCap83, ws7WordP83, ws7WordQ83]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep83, ws7WordCap83, ws7WordP83, ws7WordQ83]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep83, ws7WordCap83, ws7WordP83, ws7WordQ83]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep83, ws7WordCap83, ws7WordP83, ws7WordQ83]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep83, ws7WordCap83, ws7WordP83, ws7WordQ83]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep83, ws7WordCap83, ws7WordP83, ws7WordQ83]
  have hword := ws7Word83WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem upperWordFitSchedule42 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmark : h 0 ≤ 2 * delta)
    (hfit : UpperSourceFits (⟨42, by decide⟩ : Fin 157) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (weakSevenRates h delta) S := by
  change (((2 : ℝ) * (delta)) ≤ (9/40 : ℝ)) ∧ (h 0 ≤ (4/27 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (weakSevenRates h delta) k ≤ (weakSevenRates h delta) i := by
    exact weakSeven_rates_order_m0 horder hmark
  have hfitRep : ∀ i, (weakSevenRates h delta) (ws7WordRep45 i) ≤ ws7WordCap45 (ws7WordRep45 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep45, ws7WordCap45, ws7WordP45, ws7WordQ45]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep45, ws7WordCap45, ws7WordP45, ws7WordQ45]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep45, ws7WordCap45, ws7WordP45, ws7WordQ45]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep45, ws7WordCap45, ws7WordP45, ws7WordQ45]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep45, ws7WordCap45, ws7WordP45, ws7WordQ45]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep45, ws7WordCap45, ws7WordP45, ws7WordQ45]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep45, ws7WordCap45, ws7WordP45, ws7WordQ45]
  have hword := ws7Word45WeakOfRepresentatives (weakSevenRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

end WeakSevenBandData
