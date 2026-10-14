import Pinwheel.WeakSevenBandData.WordSources
import Pinwheel.WeakSevenBandData.SourceFits
import Pinwheel.WeakSevenBandData.RateOrder
import Pinwheel.WeakSeven
import Mathlib.Tactic.FinCases

/-! Source-box adapters for literal weak words. -/

namespace RealPinwheel.WeakSevenBandData

theorem secondWordFitSchedule0 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmarkL : 2 * delta ≤ h 0) (hmarkR : h 1 ≤ 2 * delta)
    (hfit : SecondSourceFits (⟨0, by decide⟩ : Fin 15) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (secondRankRates h delta) S := by
  change (h 0 ≤ (1/5 : ℝ)) ∧ (h 1 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (1/10 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (secondRankRates h delta) k ≤ (secondRankRates h delta) i := by
    exact secondRankRates_order horder hmarkL hmarkR
  have hfitRep : ∀ i, (secondRankRates h delta) (ws7WordRep49 i) ≤ ws7WordCap49 (ws7WordRep49 i) := by
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
  have hword := ws7Word49WeakOfRepresentatives (secondRankRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem secondWordFitSchedule1 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmarkL : 2 * delta ≤ h 0) (hmarkR : h 1 ≤ 2 * delta)
    (hfit : SecondSourceFits (⟨1, by decide⟩ : Fin 15) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (secondRankRates h delta) S := by
  change (h 0 ≤ (2/9 : ℝ)) ∧ (h 1 ≤ (1/9 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (secondRankRates h delta) k ≤ (secondRankRates h delta) i := by
    exact secondRankRates_order horder hmarkL hmarkR
  have hfitRep : ∀ i, (secondRankRates h delta) (ws7WordRep0 i) ≤ ws7WordCap0 (ws7WordRep0 i) := by
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
  have hword := ws7Word0WeakOfRepresentatives (secondRankRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem secondWordFitSchedule2 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmarkL : 2 * delta ≤ h 0) (hmarkR : h 1 ≤ 2 * delta)
    (hfit : SecondSourceFits (⟨2, by decide⟩ : Fin 15) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (secondRankRates h delta) S := by
  change (h 0 ≤ (1/4 : ℝ)) ∧ (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (1/10 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1, hc2, hc3⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (secondRankRates h delta) k ≤ (secondRankRates h delta) i := by
    exact secondRankRates_order horder hmarkL hmarkR
  have hfitRep : ∀ i, (secondRankRates h delta) (ws7WordRep48 i) ≤ ws7WordCap48 (ws7WordRep48 i) := by
    intro i
    fin_cases i
    · convert hc0 using 1
      · rfl
      · norm_num [ws7WordRep48, ws7WordCap48, ws7WordP48, ws7WordQ48]
    · convert hc1 using 1
      · rfl
      · norm_num [ws7WordRep48, ws7WordCap48, ws7WordP48, ws7WordQ48]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep48, ws7WordCap48, ws7WordP48, ws7WordQ48]
    · convert hc2 using 1
      · rfl
      · norm_num [ws7WordRep48, ws7WordCap48, ws7WordP48, ws7WordQ48]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep48, ws7WordCap48, ws7WordP48, ws7WordQ48]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep48, ws7WordCap48, ws7WordP48, ws7WordQ48]
    · convert hc3 using 1
      · rfl
      · norm_num [ws7WordRep48, ws7WordCap48, ws7WordP48, ws7WordQ48]
  have hword := ws7Word48WeakOfRepresentatives (secondRankRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

theorem secondWordFitSchedule3 (h : Fin 6 → ℝ) (delta : ℝ)
    (horder : ∀ i j : Fin 6, i.val ≤ j.val → h j ≤ h i) (hmarkL : 2 * delta ≤ h 0) (hmarkR : h 1 ≤ 2 * delta)
    (hfit : SecondSourceFits (⟨3, by decide⟩ : Fin 15) h delta) :
    ∃ S : ℤ → Fin 7, WeakValidRates (secondRankRates h delta) S := by
  change (h 0 ≤ (1/5 : ℝ)) ∧ (h 1 ≤ (3/25 : ℝ)) at hfit
  rcases hfit with ⟨hc0, hc1⟩
  have hrateOrder : ∀ i k : Fin 7, i.val ≤ k.val → (secondRankRates h delta) k ≤ (secondRankRates h delta) i := by
    exact secondRankRates_order horder hmarkL hmarkR
  have hfitRep : ∀ i, (secondRankRates h delta) (ws7WordRep2 i) ≤ ws7WordCap2 (ws7WordRep2 i) := by
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
  have hword := ws7Word2WeakOfRepresentatives (secondRankRates h delta) hrateOrder hfitRep
  exact ⟨_, hword⟩

end WeakSevenBandData
