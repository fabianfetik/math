import Pinwheel.WeakSevenBandData.SecondInputs

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem second_node_186 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a14 : -(h 1) < (-3/25 : ℝ))
    (a17 : -(h 2) < (-83/758 : ℝ))
    (a18 : -(h 3) < (-89368829179067/857912907441924 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order4 + (2/3 : ℝ) * _ctx.min + (5/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * _ctx.markL + (1/3 : ℝ) * a14 + (1/3 : ℝ) * a17 + (1/3 : ℝ) * a18 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_185 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a14 : -(h 1) < (-3/25 : ℝ))
    (a18 : -(h 2) < (-24915904083856/214478226860481 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/2 : ℝ) * _ctx.order3 + (1 : ℝ) * _ctx.order4 + (3/2 : ℝ) * _ctx.min + (3 : ℝ) * _ctx.lower + (1/2 : ℝ) * _ctx.markL + (1/2 : ℝ) * a14 + (1/2 : ℝ) * a18 + (1/2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_184 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a17 : -(h 2) < (-83/758 : ℝ))
    (a18 : -(h 1) < (-53616655394587/428956453720962 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/2 : ℝ) * _ctx.order3 + (1 : ℝ) * _ctx.order4 + (3/2 : ℝ) * _ctx.min + (3 : ℝ) * _ctx.lower + (1/2 : ℝ) * _ctx.markL + (1/2 : ℝ) * a17 + (1/2 : ℝ) * a18 + (1/2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_183 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a14 : -(h 1) < (-3/25 : ℝ))
    (a17 : -(h 2) < (-83/758 : ℝ))
    (a18 : -(h 0) < (-89368829179067/428956453720962 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order3 + (2/3 : ℝ) * _ctx.order4 + (1 : ℝ) * _ctx.min + (4/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * a14 + (1/3 : ℝ) * a17 + (1/3 : ℝ) * a18 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_182 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a14 : -(h 1) < (-3/25 : ℝ))
    (a17 : -(h 2) < (-83/758 : ℝ))
    : False := by
  by_cases p0 : h 0 ≤ (89368829179067/428956453720962 : ℝ)
  swap
  · have f0 : -(h 0) < (-89368829179067/428956453720962 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact second_node_183 h delta _ctx _hno a14 a17 f0
  by_cases p1 : h 1 ≤ (53616655394587/428956453720962 : ℝ)
  swap
  · have f1 : -(h 1) < (-53616655394587/428956453720962 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact second_node_184 h delta _ctx _hno a17 f1
  by_cases p2 : h 2 ≤ (24915904083856/214478226860481 : ℝ)
  swap
  · have f2 : -(h 2) < (-24915904083856/214478226860481 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact second_node_185 h delta _ctx _hno a14 f2
  by_cases p3 : h 3 ≤ (89368829179067/857912907441924 : ℝ)
  swap
  · have f3 : -(h 3) < (-89368829179067/857912907441924 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact second_node_186 h delta _ctx _hno a14 a17 f3
  apply _hno 13
  change (h 0 ≤ (89368829179067/428956453720962 : ℝ)) ∧ (h 1 ≤ (53616655394587/428956453720962 : ℝ)) ∧ (h 2 ≤ (24915904083856/214478226860481 : ℝ)) ∧ (h 3 ≤ (89368829179067/857912907441924 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem second_node_181 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 2) < (-10339/95614 : ℝ))
    (a17 : -(h 1) < (-47/379 : ℝ))
    (a18 : -(h 3) < (-89368829179067/857912907441924 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order4 + (2/3 : ℝ) * _ctx.min + (5/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * _ctx.markL + (1/3 : ℝ) * a16 + (1/3 : ℝ) * a17 + (1/3 : ℝ) * a18 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_180 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a17 : -(h 1) < (-47/379 : ℝ))
    (a18 : -(h 2) < (-24915904083856/214478226860481 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/2 : ℝ) * _ctx.order3 + (1 : ℝ) * _ctx.order4 + (3/2 : ℝ) * _ctx.min + (3 : ℝ) * _ctx.lower + (1/2 : ℝ) * _ctx.markL + (1/2 : ℝ) * a17 + (1/2 : ℝ) * a18 + (1/2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_179 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 2) < (-10339/95614 : ℝ))
    (a18 : -(h 1) < (-53616655394587/428956453720962 : ℝ))
    (a19 : -(h 3) < (-136053119/1322848068 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order4 + (2/3 : ℝ) * _ctx.min + (5/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * _ctx.markL + (1/3 : ℝ) * a16 + (1/3 : ℝ) * a18 + (1/3 : ℝ) * a19 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_178 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a18 : -(h 1) < (-53616655394587/428956453720962 : ℝ))
    (a19 : -(h 2) < (-294532961/2645696136 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/2 : ℝ) * _ctx.order3 + (1 : ℝ) * _ctx.order4 + (3/2 : ℝ) * _ctx.min + (3 : ℝ) * _ctx.lower + (1/2 : ℝ) * _ctx.markL + (1/2 : ℝ) * a18 + (1/2 : ℝ) * a19 + (1/2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_177 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 2) < (-10339/95614 : ℝ))
    (a19 : -(h 1) < (-84421559/661424034 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/2 : ℝ) * _ctx.order3 + (1 : ℝ) * _ctx.order4 + (3/2 : ℝ) * _ctx.min + (3 : ℝ) * _ctx.lower + (1/2 : ℝ) * _ctx.markL + (1/2 : ℝ) * a16 + (1/2 : ℝ) * a19 + (1/2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_176 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 2) < (-10339/95614 : ℝ))
    (a18 : -(h 1) < (-53616655394587/428956453720962 : ℝ))
    (a19 : -(h 0) < (-136053119/661424034 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order3 + (2/3 : ℝ) * _ctx.order4 + (1 : ℝ) * _ctx.min + (4/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * a16 + (1/3 : ℝ) * a18 + (1/3 : ℝ) * a19 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_175 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 2) < (-10339/95614 : ℝ))
    (a18 : -(h 1) < (-53616655394587/428956453720962 : ℝ))
    : False := by
  by_cases p0 : h 0 ≤ (136053119/661424034 : ℝ)
  swap
  · have f0 : -(h 0) < (-136053119/661424034 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact second_node_176 h delta _ctx _hno a16 a18 f0
  by_cases p1 : h 1 ≤ (84421559/661424034 : ℝ)
  swap
  · have f1 : -(h 1) < (-84421559/661424034 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact second_node_177 h delta _ctx _hno a16 f1
  by_cases p2 : h 2 ≤ (294532961/2645696136 : ℝ)
  swap
  · have f2 : -(h 2) < (-294532961/2645696136 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact second_node_178 h delta _ctx _hno a18 f2
  by_cases p3 : h 3 ≤ (136053119/1322848068 : ℝ)
  swap
  · have f3 : -(h 3) < (-136053119/1322848068 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact second_node_179 h delta _ctx _hno a16 a18 f3
  apply _hno 11
  change (h 0 ≤ (136053119/661424034 : ℝ)) ∧ (h 1 ≤ (84421559/661424034 : ℝ)) ∧ (h 2 ≤ (294532961/2645696136 : ℝ)) ∧ (h 3 ≤ (136053119/1322848068 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem second_node_174 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 2) < (-10339/95614 : ℝ))
    (a17 : -(h 1) < (-47/379 : ℝ))
    (a18 : -(h 0) < (-89368829179067/428956453720962 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order3 + (2/3 : ℝ) * _ctx.order4 + (1 : ℝ) * _ctx.min + (4/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * a16 + (1/3 : ℝ) * a17 + (1/3 : ℝ) * a18 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_173 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 2) < (-10339/95614 : ℝ))
    (a17 : -(h 1) < (-47/379 : ℝ))
    : False := by
  by_cases p0 : h 0 ≤ (89368829179067/428956453720962 : ℝ)
  swap
  · have f0 : -(h 0) < (-89368829179067/428956453720962 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact second_node_174 h delta _ctx _hno a16 a17 f0
  by_cases p1 : h 1 ≤ (53616655394587/428956453720962 : ℝ)
  swap
  · have f1 : -(h 1) < (-53616655394587/428956453720962 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact second_node_175 h delta _ctx _hno a16 f1
  by_cases p2 : h 2 ≤ (24915904083856/214478226860481 : ℝ)
  swap
  · have f2 : -(h 2) < (-24915904083856/214478226860481 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact second_node_180 h delta _ctx _hno a17 f2
  by_cases p3 : h 3 ≤ (89368829179067/857912907441924 : ℝ)
  swap
  · have f3 : -(h 3) < (-89368829179067/857912907441924 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact second_node_181 h delta _ctx _hno a16 a17 f3
  apply _hno 13
  change (h 0 ≤ (89368829179067/428956453720962 : ℝ)) ∧ (h 1 ≤ (53616655394587/428956453720962 : ℝ)) ∧ (h 2 ≤ (24915904083856/214478226860481 : ℝ)) ∧ (h 3 ≤ (89368829179067/857912907441924 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem second_node_172 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a14 : -(h 1) < (-3/25 : ℝ))
    (a16 : -(h 2) < (-10339/95614 : ℝ))
    (a17 : -(h 0) < (-83/379 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order3 + (2/3 : ℝ) * _ctx.order4 + (1 : ℝ) * _ctx.min + (4/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * a14 + (1/3 : ℝ) * a16 + (1/3 : ℝ) * a17 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_171 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a14 : -(h 1) < (-3/25 : ℝ))
    (a16 : -(h 2) < (-10339/95614 : ℝ))
    : False := by
  by_cases p0 : h 0 ≤ (83/379 : ℝ)
  swap
  · have f0 : -(h 0) < (-83/379 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact second_node_172 h delta _ctx _hno a14 a16 f0
  by_cases p1 : h 1 ≤ (47/379 : ℝ)
  swap
  · have f1 : -(h 1) < (-47/379 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact second_node_173 h delta _ctx _hno a16 f1
  by_cases p2 : h 2 ≤ (83/758 : ℝ)
  swap
  · have f2 : -(h 2) < (-83/758 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact second_node_182 h delta _ctx _hno a14 f2
  apply _hno 8
  change (h 0 ≤ (83/379 : ℝ)) ∧ (h 1 ≤ (47/379 : ℝ)) ∧ (h 2 ≤ (83/758 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem second_node_170 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 1) < (-6451/47807 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * _ctx.order2 + (2 : ℝ) * _ctx.order3 + (3 : ℝ) * _ctx.order4 + (4 : ℝ) * _ctx.min + (7 : ℝ) * _ctx.lower + (1 : ℝ) * _ctx.markL + (1 : ℝ) * a16 + (1 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_169 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a14 : -(h 1) < (-3/25 : ℝ))
    (a16 : -(h 0) < (-10339/47807 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/2 : ℝ) * _ctx.order2 + (1 : ℝ) * _ctx.order3 + (3/2 : ℝ) * _ctx.order4 + (2 : ℝ) * _ctx.min + (5/2 : ℝ) * _ctx.lower + (1/2 : ℝ) * a14 + (1/2 : ℝ) * a16 + (1/2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_168 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a14 : -(h 1) < (-3/25 : ℝ))
    : False := by
  by_cases p0 : h 0 ≤ (10339/47807 : ℝ)
  swap
  · have f0 : -(h 0) < (-10339/47807 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact second_node_169 h delta _ctx _hno a14 f0
  by_cases p1 : h 1 ≤ (6451/47807 : ℝ)
  swap
  · have f1 : -(h 1) < (-6451/47807 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact second_node_170 h delta _ctx _hno f1
  by_cases p2 : h 2 ≤ (10339/95614 : ℝ)
  swap
  · have f2 : -(h 2) < (-10339/95614 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact second_node_171 h delta _ctx _hno a14 f2
  apply _hno 10
  change (h 0 ≤ (10339/47807 : ℝ)) ∧ (h 1 ≤ (6451/47807 : ℝ)) ∧ (h 2 ≤ (10339/95614 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem second_node_167 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a15 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/2 : ℝ) * _ctx.order1 + (1/2 : ℝ) * _ctx.order3 + (1 : ℝ) * _ctx.order4 + (3/2 : ℝ) * _ctx.min + (3 : ℝ) * _ctx.lower + (1/2 : ℝ) * _ctx.markL + (1 : ℝ) * a15 + (1/2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_166 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a15 : -(h 1) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * _ctx.order2 + (2 : ℝ) * _ctx.order3 + (3 : ℝ) * _ctx.order4 + (4 : ℝ) * _ctx.min + (7 : ℝ) * _ctx.lower + (1 : ℝ) * _ctx.markL + (1 : ℝ) * a15 + (1 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_165 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a14 : -(h 1) < (-3/25 : ℝ))
    (a18 : -(h 2) < (-83/758 : ℝ))
    (a19 : -(h 3) < (-89368829179067/857912907441924 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order4 + (2/3 : ℝ) * _ctx.min + (5/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * _ctx.markL + (1/3 : ℝ) * a14 + (1/3 : ℝ) * a18 + (1/3 : ℝ) * a19 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_164 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a14 : -(h 1) < (-3/25 : ℝ))
    (a19 : -(h 2) < (-24915904083856/214478226860481 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/2 : ℝ) * _ctx.order3 + (1 : ℝ) * _ctx.order4 + (3/2 : ℝ) * _ctx.min + (3 : ℝ) * _ctx.lower + (1/2 : ℝ) * _ctx.markL + (1/2 : ℝ) * a14 + (1/2 : ℝ) * a19 + (1/2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_163 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a18 : -(h 2) < (-83/758 : ℝ))
    (a19 : -(h 1) < (-53616655394587/428956453720962 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/2 : ℝ) * _ctx.order3 + (1 : ℝ) * _ctx.order4 + (3/2 : ℝ) * _ctx.min + (3 : ℝ) * _ctx.lower + (1/2 : ℝ) * _ctx.markL + (1/2 : ℝ) * a18 + (1/2 : ℝ) * a19 + (1/2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_162 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a14 : -(h 1) < (-3/25 : ℝ))
    (a18 : -(h 2) < (-83/758 : ℝ))
    (a19 : -(h 0) < (-89368829179067/428956453720962 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order3 + (2/3 : ℝ) * _ctx.order4 + (1 : ℝ) * _ctx.min + (4/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * a14 + (1/3 : ℝ) * a18 + (1/3 : ℝ) * a19 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_161 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a14 : -(h 1) < (-3/25 : ℝ))
    (a18 : -(h 2) < (-83/758 : ℝ))
    : False := by
  by_cases p0 : h 0 ≤ (89368829179067/428956453720962 : ℝ)
  swap
  · have f0 : -(h 0) < (-89368829179067/428956453720962 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact second_node_162 h delta _ctx _hno a14 a18 f0
  by_cases p1 : h 1 ≤ (53616655394587/428956453720962 : ℝ)
  swap
  · have f1 : -(h 1) < (-53616655394587/428956453720962 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact second_node_163 h delta _ctx _hno a18 f1
  by_cases p2 : h 2 ≤ (24915904083856/214478226860481 : ℝ)
  swap
  · have f2 : -(h 2) < (-24915904083856/214478226860481 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact second_node_164 h delta _ctx _hno a14 f2
  by_cases p3 : h 3 ≤ (89368829179067/857912907441924 : ℝ)
  swap
  · have f3 : -(h 3) < (-89368829179067/857912907441924 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact second_node_165 h delta _ctx _hno a14 a18 f3
  apply _hno 13
  change (h 0 ≤ (89368829179067/428956453720962 : ℝ)) ∧ (h 1 ≤ (53616655394587/428956453720962 : ℝ)) ∧ (h 2 ≤ (24915904083856/214478226860481 : ℝ)) ∧ (h 3 ≤ (89368829179067/857912907441924 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem second_node_160 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 2) < (-10339/95614 : ℝ))
    (a18 : -(h 1) < (-47/379 : ℝ))
    (a19 : -(h 3) < (-89368829179067/857912907441924 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order4 + (2/3 : ℝ) * _ctx.min + (5/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * _ctx.markL + (1/3 : ℝ) * a16 + (1/3 : ℝ) * a18 + (1/3 : ℝ) * a19 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_159 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a18 : -(h 1) < (-47/379 : ℝ))
    (a19 : -(h 2) < (-24915904083856/214478226860481 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/2 : ℝ) * _ctx.order3 + (1 : ℝ) * _ctx.order4 + (3/2 : ℝ) * _ctx.min + (3 : ℝ) * _ctx.lower + (1/2 : ℝ) * _ctx.markL + (1/2 : ℝ) * a18 + (1/2 : ℝ) * a19 + (1/2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_158 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 2) < (-10339/95614 : ℝ))
    (a19 : -(h 1) < (-53616655394587/428956453720962 : ℝ))
    (a20 : -(h 3) < (-136053119/1322848068 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order4 + (2/3 : ℝ) * _ctx.min + (5/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * _ctx.markL + (1/3 : ℝ) * a16 + (1/3 : ℝ) * a19 + (1/3 : ℝ) * a20 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_157 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a19 : -(h 1) < (-53616655394587/428956453720962 : ℝ))
    (a20 : -(h 2) < (-294532961/2645696136 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/2 : ℝ) * _ctx.order3 + (1 : ℝ) * _ctx.order4 + (3/2 : ℝ) * _ctx.min + (3 : ℝ) * _ctx.lower + (1/2 : ℝ) * _ctx.markL + (1/2 : ℝ) * a19 + (1/2 : ℝ) * a20 + (1/2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_156 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 2) < (-10339/95614 : ℝ))
    (a20 : -(h 1) < (-84421559/661424034 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/2 : ℝ) * _ctx.order3 + (1 : ℝ) * _ctx.order4 + (3/2 : ℝ) * _ctx.min + (3 : ℝ) * _ctx.lower + (1/2 : ℝ) * _ctx.markL + (1/2 : ℝ) * a16 + (1/2 : ℝ) * a20 + (1/2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_155 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 2) < (-10339/95614 : ℝ))
    (a19 : -(h 1) < (-53616655394587/428956453720962 : ℝ))
    (a20 : -(h 0) < (-136053119/661424034 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order3 + (2/3 : ℝ) * _ctx.order4 + (1 : ℝ) * _ctx.min + (4/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * a16 + (1/3 : ℝ) * a19 + (1/3 : ℝ) * a20 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_154 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 2) < (-10339/95614 : ℝ))
    (a19 : -(h 1) < (-53616655394587/428956453720962 : ℝ))
    : False := by
  by_cases p0 : h 0 ≤ (136053119/661424034 : ℝ)
  swap
  · have f0 : -(h 0) < (-136053119/661424034 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact second_node_155 h delta _ctx _hno a16 a19 f0
  by_cases p1 : h 1 ≤ (84421559/661424034 : ℝ)
  swap
  · have f1 : -(h 1) < (-84421559/661424034 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact second_node_156 h delta _ctx _hno a16 f1
  by_cases p2 : h 2 ≤ (294532961/2645696136 : ℝ)
  swap
  · have f2 : -(h 2) < (-294532961/2645696136 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact second_node_157 h delta _ctx _hno a19 f2
  by_cases p3 : h 3 ≤ (136053119/1322848068 : ℝ)
  swap
  · have f3 : -(h 3) < (-136053119/1322848068 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact second_node_158 h delta _ctx _hno a16 a19 f3
  apply _hno 11
  change (h 0 ≤ (136053119/661424034 : ℝ)) ∧ (h 1 ≤ (84421559/661424034 : ℝ)) ∧ (h 2 ≤ (294532961/2645696136 : ℝ)) ∧ (h 3 ≤ (136053119/1322848068 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem second_node_153 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 2) < (-10339/95614 : ℝ))
    (a18 : -(h 1) < (-47/379 : ℝ))
    (a19 : -(h 0) < (-89368829179067/428956453720962 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order3 + (2/3 : ℝ) * _ctx.order4 + (1 : ℝ) * _ctx.min + (4/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * a16 + (1/3 : ℝ) * a18 + (1/3 : ℝ) * a19 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_152 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 2) < (-10339/95614 : ℝ))
    (a18 : -(h 1) < (-47/379 : ℝ))
    : False := by
  by_cases p0 : h 0 ≤ (89368829179067/428956453720962 : ℝ)
  swap
  · have f0 : -(h 0) < (-89368829179067/428956453720962 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact second_node_153 h delta _ctx _hno a16 a18 f0
  by_cases p1 : h 1 ≤ (53616655394587/428956453720962 : ℝ)
  swap
  · have f1 : -(h 1) < (-53616655394587/428956453720962 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact second_node_154 h delta _ctx _hno a16 f1
  by_cases p2 : h 2 ≤ (24915904083856/214478226860481 : ℝ)
  swap
  · have f2 : -(h 2) < (-24915904083856/214478226860481 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact second_node_159 h delta _ctx _hno a18 f2
  by_cases p3 : h 3 ≤ (89368829179067/857912907441924 : ℝ)
  swap
  · have f3 : -(h 3) < (-89368829179067/857912907441924 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact second_node_160 h delta _ctx _hno a16 a18 f3
  apply _hno 13
  change (h 0 ≤ (89368829179067/428956453720962 : ℝ)) ∧ (h 1 ≤ (53616655394587/428956453720962 : ℝ)) ∧ (h 2 ≤ (24915904083856/214478226860481 : ℝ)) ∧ (h 3 ≤ (89368829179067/857912907441924 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem second_node_151 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a14 : -(h 1) < (-3/25 : ℝ))
    (a16 : -(h 2) < (-10339/95614 : ℝ))
    (a18 : -(h 0) < (-83/379 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order3 + (2/3 : ℝ) * _ctx.order4 + (1 : ℝ) * _ctx.min + (4/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * a14 + (1/3 : ℝ) * a16 + (1/3 : ℝ) * a18 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_150 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a14 : -(h 1) < (-3/25 : ℝ))
    (a16 : -(h 2) < (-10339/95614 : ℝ))
    : False := by
  by_cases p0 : h 0 ≤ (83/379 : ℝ)
  swap
  · have f0 : -(h 0) < (-83/379 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact second_node_151 h delta _ctx _hno a14 a16 f0
  by_cases p1 : h 1 ≤ (47/379 : ℝ)
  swap
  · have f1 : -(h 1) < (-47/379 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact second_node_152 h delta _ctx _hno a16 f1
  by_cases p2 : h 2 ≤ (83/758 : ℝ)
  swap
  · have f2 : -(h 2) < (-83/758 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact second_node_161 h delta _ctx _hno a14 f2
  apply _hno 8
  change (h 0 ≤ (83/379 : ℝ)) ∧ (h 1 ≤ (47/379 : ℝ)) ∧ (h 2 ≤ (83/758 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem second_node_149 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 2) < (-10339/95614 : ℝ))
    (a17 : -(h 1) < (-1/8 : ℝ))
    (a18 : -(h 3) < (-136053119/1322848068 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order4 + (2/3 : ℝ) * _ctx.min + (5/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * _ctx.markL + (1/3 : ℝ) * a16 + (1/3 : ℝ) * a17 + (1/3 : ℝ) * a18 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_148 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a17 : -(h 1) < (-1/8 : ℝ))
    (a18 : -(h 2) < (-294532961/2645696136 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/2 : ℝ) * _ctx.order3 + (1 : ℝ) * _ctx.order4 + (3/2 : ℝ) * _ctx.min + (3 : ℝ) * _ctx.lower + (1/2 : ℝ) * _ctx.markL + (1/2 : ℝ) * a17 + (1/2 : ℝ) * a18 + (1/2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_147 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 2) < (-10339/95614 : ℝ))
    (a18 : -(h 1) < (-84421559/661424034 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/2 : ℝ) * _ctx.order3 + (1 : ℝ) * _ctx.order4 + (3/2 : ℝ) * _ctx.min + (3 : ℝ) * _ctx.lower + (1/2 : ℝ) * _ctx.markL + (1/2 : ℝ) * a16 + (1/2 : ℝ) * a18 + (1/2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_146 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 2) < (-10339/95614 : ℝ))
    (a17 : -(h 1) < (-1/8 : ℝ))
    (a18 : -(h 0) < (-136053119/661424034 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order3 + (2/3 : ℝ) * _ctx.order4 + (1 : ℝ) * _ctx.min + (4/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * a16 + (1/3 : ℝ) * a17 + (1/3 : ℝ) * a18 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_145 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 2) < (-10339/95614 : ℝ))
    (a17 : -(h 1) < (-1/8 : ℝ))
    : False := by
  by_cases p0 : h 0 ≤ (136053119/661424034 : ℝ)
  swap
  · have f0 : -(h 0) < (-136053119/661424034 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact second_node_146 h delta _ctx _hno a16 a17 f0
  by_cases p1 : h 1 ≤ (84421559/661424034 : ℝ)
  swap
  · have f1 : -(h 1) < (-84421559/661424034 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact second_node_147 h delta _ctx _hno a16 f1
  by_cases p2 : h 2 ≤ (294532961/2645696136 : ℝ)
  swap
  · have f2 : -(h 2) < (-294532961/2645696136 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact second_node_148 h delta _ctx _hno a17 f2
  by_cases p3 : h 3 ≤ (136053119/1322848068 : ℝ)
  swap
  · have f3 : -(h 3) < (-136053119/1322848068 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact second_node_149 h delta _ctx _hno a16 a17 f3
  apply _hno 11
  change (h 0 ≤ (136053119/661424034 : ℝ)) ∧ (h 1 ≤ (84421559/661424034 : ℝ)) ∧ (h 2 ≤ (294532961/2645696136 : ℝ)) ∧ (h 3 ≤ (136053119/1322848068 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem second_node_144 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a14 : -(h 1) < (-3/25 : ℝ))
    (a18 : -(h 2) < (-83/758 : ℝ))
    (a19 : -(h 3) < (-89368829179067/857912907441924 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order4 + (2/3 : ℝ) * _ctx.min + (5/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * _ctx.markL + (1/3 : ℝ) * a14 + (1/3 : ℝ) * a18 + (1/3 : ℝ) * a19 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_143 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a14 : -(h 1) < (-3/25 : ℝ))
    (a19 : -(h 2) < (-24915904083856/214478226860481 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/2 : ℝ) * _ctx.order3 + (1 : ℝ) * _ctx.order4 + (3/2 : ℝ) * _ctx.min + (3 : ℝ) * _ctx.lower + (1/2 : ℝ) * _ctx.markL + (1/2 : ℝ) * a14 + (1/2 : ℝ) * a19 + (1/2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_142 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a18 : -(h 2) < (-83/758 : ℝ))
    (a19 : -(h 1) < (-53616655394587/428956453720962 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/2 : ℝ) * _ctx.order3 + (1 : ℝ) * _ctx.order4 + (3/2 : ℝ) * _ctx.min + (3 : ℝ) * _ctx.lower + (1/2 : ℝ) * _ctx.markL + (1/2 : ℝ) * a18 + (1/2 : ℝ) * a19 + (1/2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_141 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a14 : -(h 1) < (-3/25 : ℝ))
    (a18 : -(h 2) < (-83/758 : ℝ))
    (a19 : -(h 0) < (-89368829179067/428956453720962 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order3 + (2/3 : ℝ) * _ctx.order4 + (1 : ℝ) * _ctx.min + (4/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * a14 + (1/3 : ℝ) * a18 + (1/3 : ℝ) * a19 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_140 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a14 : -(h 1) < (-3/25 : ℝ))
    (a18 : -(h 2) < (-83/758 : ℝ))
    : False := by
  by_cases p0 : h 0 ≤ (89368829179067/428956453720962 : ℝ)
  swap
  · have f0 : -(h 0) < (-89368829179067/428956453720962 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact second_node_141 h delta _ctx _hno a14 a18 f0
  by_cases p1 : h 1 ≤ (53616655394587/428956453720962 : ℝ)
  swap
  · have f1 : -(h 1) < (-53616655394587/428956453720962 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact second_node_142 h delta _ctx _hno a18 f1
  by_cases p2 : h 2 ≤ (24915904083856/214478226860481 : ℝ)
  swap
  · have f2 : -(h 2) < (-24915904083856/214478226860481 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact second_node_143 h delta _ctx _hno a14 f2
  by_cases p3 : h 3 ≤ (89368829179067/857912907441924 : ℝ)
  swap
  · have f3 : -(h 3) < (-89368829179067/857912907441924 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact second_node_144 h delta _ctx _hno a14 a18 f3
  apply _hno 13
  change (h 0 ≤ (89368829179067/428956453720962 : ℝ)) ∧ (h 1 ≤ (53616655394587/428956453720962 : ℝ)) ∧ (h 2 ≤ (24915904083856/214478226860481 : ℝ)) ∧ (h 3 ≤ (89368829179067/857912907441924 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem second_node_139 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 2) < (-10339/95614 : ℝ))
    (a18 : -(h 1) < (-47/379 : ℝ))
    (a19 : -(h 3) < (-89368829179067/857912907441924 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order4 + (2/3 : ℝ) * _ctx.min + (5/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * _ctx.markL + (1/3 : ℝ) * a16 + (1/3 : ℝ) * a18 + (1/3 : ℝ) * a19 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_138 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a18 : -(h 1) < (-47/379 : ℝ))
    (a19 : -(h 2) < (-24915904083856/214478226860481 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/2 : ℝ) * _ctx.order3 + (1 : ℝ) * _ctx.order4 + (3/2 : ℝ) * _ctx.min + (3 : ℝ) * _ctx.lower + (1/2 : ℝ) * _ctx.markL + (1/2 : ℝ) * a18 + (1/2 : ℝ) * a19 + (1/2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_137 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 2) < (-10339/95614 : ℝ))
    (a19 : -(h 1) < (-53616655394587/428956453720962 : ℝ))
    (a20 : -(h 3) < (-136053119/1322848068 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order4 + (2/3 : ℝ) * _ctx.min + (5/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * _ctx.markL + (1/3 : ℝ) * a16 + (1/3 : ℝ) * a19 + (1/3 : ℝ) * a20 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_136 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a19 : -(h 1) < (-53616655394587/428956453720962 : ℝ))
    (a20 : -(h 2) < (-294532961/2645696136 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/2 : ℝ) * _ctx.order3 + (1 : ℝ) * _ctx.order4 + (3/2 : ℝ) * _ctx.min + (3 : ℝ) * _ctx.lower + (1/2 : ℝ) * _ctx.markL + (1/2 : ℝ) * a19 + (1/2 : ℝ) * a20 + (1/2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_135 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 2) < (-10339/95614 : ℝ))
    (a20 : -(h 1) < (-84421559/661424034 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/2 : ℝ) * _ctx.order3 + (1 : ℝ) * _ctx.order4 + (3/2 : ℝ) * _ctx.min + (3 : ℝ) * _ctx.lower + (1/2 : ℝ) * _ctx.markL + (1/2 : ℝ) * a16 + (1/2 : ℝ) * a20 + (1/2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_134 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 2) < (-10339/95614 : ℝ))
    (a19 : -(h 1) < (-53616655394587/428956453720962 : ℝ))
    (a20 : -(h 0) < (-136053119/661424034 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order3 + (2/3 : ℝ) * _ctx.order4 + (1 : ℝ) * _ctx.min + (4/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * a16 + (1/3 : ℝ) * a19 + (1/3 : ℝ) * a20 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_133 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 2) < (-10339/95614 : ℝ))
    (a19 : -(h 1) < (-53616655394587/428956453720962 : ℝ))
    : False := by
  by_cases p0 : h 0 ≤ (136053119/661424034 : ℝ)
  swap
  · have f0 : -(h 0) < (-136053119/661424034 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact second_node_134 h delta _ctx _hno a16 a19 f0
  by_cases p1 : h 1 ≤ (84421559/661424034 : ℝ)
  swap
  · have f1 : -(h 1) < (-84421559/661424034 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact second_node_135 h delta _ctx _hno a16 f1
  by_cases p2 : h 2 ≤ (294532961/2645696136 : ℝ)
  swap
  · have f2 : -(h 2) < (-294532961/2645696136 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact second_node_136 h delta _ctx _hno a19 f2
  by_cases p3 : h 3 ≤ (136053119/1322848068 : ℝ)
  swap
  · have f3 : -(h 3) < (-136053119/1322848068 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact second_node_137 h delta _ctx _hno a16 a19 f3
  apply _hno 11
  change (h 0 ≤ (136053119/661424034 : ℝ)) ∧ (h 1 ≤ (84421559/661424034 : ℝ)) ∧ (h 2 ≤ (294532961/2645696136 : ℝ)) ∧ (h 3 ≤ (136053119/1322848068 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem second_node_132 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 2) < (-10339/95614 : ℝ))
    (a18 : -(h 1) < (-47/379 : ℝ))
    (a19 : -(h 0) < (-89368829179067/428956453720962 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order3 + (2/3 : ℝ) * _ctx.order4 + (1 : ℝ) * _ctx.min + (4/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * a16 + (1/3 : ℝ) * a18 + (1/3 : ℝ) * a19 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_131 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 2) < (-10339/95614 : ℝ))
    (a18 : -(h 1) < (-47/379 : ℝ))
    : False := by
  by_cases p0 : h 0 ≤ (89368829179067/428956453720962 : ℝ)
  swap
  · have f0 : -(h 0) < (-89368829179067/428956453720962 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact second_node_132 h delta _ctx _hno a16 a18 f0
  by_cases p1 : h 1 ≤ (53616655394587/428956453720962 : ℝ)
  swap
  · have f1 : -(h 1) < (-53616655394587/428956453720962 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact second_node_133 h delta _ctx _hno a16 f1
  by_cases p2 : h 2 ≤ (24915904083856/214478226860481 : ℝ)
  swap
  · have f2 : -(h 2) < (-24915904083856/214478226860481 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact second_node_138 h delta _ctx _hno a18 f2
  by_cases p3 : h 3 ≤ (89368829179067/857912907441924 : ℝ)
  swap
  · have f3 : -(h 3) < (-89368829179067/857912907441924 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact second_node_139 h delta _ctx _hno a16 a18 f3
  apply _hno 13
  change (h 0 ≤ (89368829179067/428956453720962 : ℝ)) ∧ (h 1 ≤ (53616655394587/428956453720962 : ℝ)) ∧ (h 2 ≤ (24915904083856/214478226860481 : ℝ)) ∧ (h 3 ≤ (89368829179067/857912907441924 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem second_node_130 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a14 : -(h 1) < (-3/25 : ℝ))
    (a16 : -(h 2) < (-10339/95614 : ℝ))
    (a18 : -(h 0) < (-83/379 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order3 + (2/3 : ℝ) * _ctx.order4 + (1 : ℝ) * _ctx.min + (4/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * a14 + (1/3 : ℝ) * a16 + (1/3 : ℝ) * a18 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_129 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a14 : -(h 1) < (-3/25 : ℝ))
    (a16 : -(h 2) < (-10339/95614 : ℝ))
    : False := by
  by_cases p0 : h 0 ≤ (83/379 : ℝ)
  swap
  · have f0 : -(h 0) < (-83/379 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact second_node_130 h delta _ctx _hno a14 a16 f0
  by_cases p1 : h 1 ≤ (47/379 : ℝ)
  swap
  · have f1 : -(h 1) < (-47/379 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact second_node_131 h delta _ctx _hno a16 f1
  by_cases p2 : h 2 ≤ (83/758 : ℝ)
  swap
  · have f2 : -(h 2) < (-83/758 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact second_node_140 h delta _ctx _hno a14 f2
  apply _hno 8
  change (h 0 ≤ (83/379 : ℝ)) ∧ (h 1 ≤ (47/379 : ℝ)) ∧ (h 2 ≤ (83/758 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem second_node_128 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a14 : -(h 1) < (-3/25 : ℝ))
    (a17 : -(h 0) < (-1/4 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/2 : ℝ) * _ctx.order2 + (1 : ℝ) * _ctx.order3 + (3/2 : ℝ) * _ctx.order4 + (2 : ℝ) * _ctx.min + (5/2 : ℝ) * _ctx.lower + (1/2 : ℝ) * a14 + (1/2 : ℝ) * a17 + (1/2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_127 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a14 : -(h 1) < (-3/25 : ℝ))
    (a16 : -(h 2) < (-10339/95614 : ℝ))
    : False := by
  by_cases p0 : h 0 ≤ (1/4 : ℝ)
  swap
  · have f0 : -(h 0) < (-1/4 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact second_node_128 h delta _ctx _hno a14 f0
  by_cases p1 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)
  swap
  · have f1 : ((-2 : ℝ) * (delta)) < (-1/5 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact second_node_129 h delta _ctx _hno a14 a16
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact second_node_145 h delta _ctx _hno a16 f2
  by_cases p3 : h 3 ≤ (1/10 : ℝ)
  swap
  · have f3 : -(h 3) < (-1/10 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact second_node_150 h delta _ctx _hno a14 a16
  apply _hno 2
  change (h 0 ≤ (1/4 : ℝ)) ∧ (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (1/10 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem second_node_126 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 1) < (-6451/47807 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * _ctx.order2 + (2 : ℝ) * _ctx.order3 + (3 : ℝ) * _ctx.order4 + (4 : ℝ) * _ctx.min + (7 : ℝ) * _ctx.lower + (1 : ℝ) * _ctx.markL + (1 : ℝ) * a16 + (1 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_125 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a14 : -(h 1) < (-3/25 : ℝ))
    (a16 : -(h 0) < (-10339/47807 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/2 : ℝ) * _ctx.order2 + (1 : ℝ) * _ctx.order3 + (3/2 : ℝ) * _ctx.order4 + (2 : ℝ) * _ctx.min + (5/2 : ℝ) * _ctx.lower + (1/2 : ℝ) * a14 + (1/2 : ℝ) * a16 + (1/2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_124 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a14 : -(h 1) < (-3/25 : ℝ))
    : False := by
  by_cases p0 : h 0 ≤ (10339/47807 : ℝ)
  swap
  · have f0 : -(h 0) < (-10339/47807 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact second_node_125 h delta _ctx _hno a14 f0
  by_cases p1 : h 1 ≤ (6451/47807 : ℝ)
  swap
  · have f1 : -(h 1) < (-6451/47807 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact second_node_126 h delta _ctx _hno f1
  by_cases p2 : h 2 ≤ (10339/95614 : ℝ)
  swap
  · have f2 : -(h 2) < (-10339/95614 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact second_node_127 h delta _ctx _hno a14 f2
  apply _hno 10
  change (h 0 ≤ (10339/47807 : ℝ)) ∧ (h 1 ≤ (6451/47807 : ℝ)) ∧ (h 2 ≤ (10339/95614 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem second_node_123 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a14 : -(h 1) < (-3/25 : ℝ))
    : False := by
  by_cases p0 : h 0 ≤ (1/5 : ℝ)
  swap
  · have f0 : -(h 0) < (-1/5 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact second_node_124 h delta _ctx _hno a14
  by_cases p1 : h 1 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 1) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact second_node_166 h delta _ctx _hno f1
  by_cases p2 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact second_node_167 h delta _ctx _hno f2
  by_cases p3 : h 4 ≤ (1/10 : ℝ)
  swap
  · have f3 : -(h 4) < (-1/10 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact second_node_168 h delta _ctx _hno a14
  apply _hno 0
  change (h 0 ≤ (1/5 : ℝ)) ∧ (h 1 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (1/10 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem second_node_122 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 2) < (-83/758 : ℝ))
    (a17 : -(h 4) < (-963259/9004269 : ℝ))
    (a18 : -(h 1) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.order3 + (1/4 : ℝ) * _ctx.min + (1 : ℝ) * _ctx.lower + (1/4 : ℝ) * _ctx.markL + (1/4 : ℝ) * a16 + (1/2 : ℝ) * a17 + (1/4 : ℝ) * a18 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_121 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 2) < (-83/758 : ℝ))
    (a17 : -(h 4) < (-963259/9004269 : ℝ))
    (a18 : -(h 0) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order1 + (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (2/5 : ℝ) * a16 + (2/5 : ℝ) * a17 + (1/5 : ℝ) * a18 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_120 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 2) < (-83/758 : ℝ))
    (a17 : -(h 4) < (-963259/9004269 : ℝ))
    : False := by
  by_cases p0 : h 0 ≤ (2/9 : ℝ)
  swap
  · have f0 : -(h 0) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact second_node_121 h delta _ctx _hno a16 a17 f0
  by_cases p1 : h 1 ≤ (1/9 : ℝ)
  swap
  · have f1 : -(h 1) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact second_node_122 h delta _ctx _hno a16 a17 f1
  apply _hno 1
  change (h 0 ≤ (2/9 : ℝ)) ∧ (h 1 ≤ (1/9 : ℝ))
  exact ⟨p0, p1⟩

theorem second_node_119 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a17 : -(h 3) < (-344405/3001423 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order1 + (2/3 : ℝ) * _ctx.order2 + (1/3 : ℝ) * _ctx.order4 + (2/3 : ℝ) * _ctx.min + (5/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * _ctx.markL + (1 : ℝ) * a17 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_118 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a17 : -(h 2) < (-8475655/72034152 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/2 : ℝ) * _ctx.order1 + (1/2 : ℝ) * _ctx.order3 + (1 : ℝ) * _ctx.order4 + (3/2 : ℝ) * _ctx.min + (3 : ℝ) * _ctx.lower + (1/2 : ℝ) * _ctx.markL + (1 : ℝ) * a17 + (1/2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_117 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 2) < (-83/758 : ℝ))
    (a17 : -(h 1) < (-1074905/9004269 : ℝ))
    (a19 : -(h 3) < (-2159/20223 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order4 + (2/3 : ℝ) * _ctx.min + (5/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * _ctx.markL + (1/3 : ℝ) * a16 + (1/3 : ℝ) * a17 + (1/3 : ℝ) * a19 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_116 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a17 : -(h 1) < (-1074905/9004269 : ℝ))
    (a18 : -(h 3) < (-89368829179067/857912907441924 : ℝ))
    (a19 : -(h 2) < (-19109/161784 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order4 + (2/3 : ℝ) * _ctx.min + (5/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * _ctx.markL + (1/3 : ℝ) * a17 + (1/3 : ℝ) * a18 + (1/3 : ℝ) * a19 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_115 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 2) < (-83/758 : ℝ))
    (a18 : -(h 3) < (-89368829179067/857912907441924 : ℝ))
    (a19 : -(h 1) < (-2423/20223 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order4 + (2/3 : ℝ) * _ctx.min + (5/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * _ctx.markL + (1/3 : ℝ) * a16 + (1/3 : ℝ) * a18 + (1/3 : ℝ) * a19 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_114 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 2) < (-83/758 : ℝ))
    (a17 : -(h 1) < (-1074905/9004269 : ℝ))
    (a18 : -(h 3) < (-89368829179067/857912907441924 : ℝ))
    (a19 : -(h 0) < (-4318/20223 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.order4 + (1/2 : ℝ) * _ctx.min + (3/4 : ℝ) * _ctx.lower + (1/4 : ℝ) * a16 + (1/4 : ℝ) * a17 + (1/4 : ℝ) * a18 + (1/4 : ℝ) * a19 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_113 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 2) < (-83/758 : ℝ))
    (a17 : -(h 1) < (-1074905/9004269 : ℝ))
    (a18 : -(h 3) < (-89368829179067/857912907441924 : ℝ))
    : False := by
  by_cases p0 : h 0 ≤ (4318/20223 : ℝ)
  swap
  · have f0 : -(h 0) < (-4318/20223 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact second_node_114 h delta _ctx _hno a16 a17 a18 f0
  by_cases p1 : h 1 ≤ (2423/20223 : ℝ)
  swap
  · have f1 : -(h 1) < (-2423/20223 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact second_node_115 h delta _ctx _hno a16 a18 f1
  by_cases p2 : h 2 ≤ (19109/161784 : ℝ)
  swap
  · have f2 : -(h 2) < (-19109/161784 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact second_node_116 h delta _ctx _hno a17 a18 f2
  by_cases p3 : h 3 ≤ (2159/20223 : ℝ)
  swap
  · have f3 : -(h 3) < (-2159/20223 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact second_node_117 h delta _ctx _hno a16 a17 f3
  apply _hno 12
  change (h 0 ≤ (4318/20223 : ℝ)) ∧ (h 1 ≤ (2423/20223 : ℝ)) ∧ (h 2 ≤ (19109/161784 : ℝ)) ∧ (h 3 ≤ (2159/20223 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem second_node_112 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a17 : -(h 1) < (-1074905/9004269 : ℝ))
    (a18 : -(h 2) < (-24915904083856/214478226860481 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/2 : ℝ) * _ctx.order3 + (1 : ℝ) * _ctx.order4 + (3/2 : ℝ) * _ctx.min + (3 : ℝ) * _ctx.lower + (1/2 : ℝ) * _ctx.markL + (1/2 : ℝ) * a17 + (1/2 : ℝ) * a18 + (1/2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_111 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 2) < (-83/758 : ℝ))
    (a18 : -(h 1) < (-53616655394587/428956453720962 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/2 : ℝ) * _ctx.order3 + (1 : ℝ) * _ctx.order4 + (3/2 : ℝ) * _ctx.min + (3 : ℝ) * _ctx.lower + (1/2 : ℝ) * _ctx.markL + (1/2 : ℝ) * a16 + (1/2 : ℝ) * a18 + (1/2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_110 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 2) < (-83/758 : ℝ))
    (a17 : -(h 1) < (-1074905/9004269 : ℝ))
    (a18 : -(h 0) < (-89368829179067/428956453720962 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order3 + (2/3 : ℝ) * _ctx.order4 + (1 : ℝ) * _ctx.min + (4/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * a16 + (1/3 : ℝ) * a17 + (1/3 : ℝ) * a18 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_109 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 2) < (-83/758 : ℝ))
    (a17 : -(h 1) < (-1074905/9004269 : ℝ))
    : False := by
  by_cases p0 : h 0 ≤ (89368829179067/428956453720962 : ℝ)
  swap
  · have f0 : -(h 0) < (-89368829179067/428956453720962 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact second_node_110 h delta _ctx _hno a16 a17 f0
  by_cases p1 : h 1 ≤ (53616655394587/428956453720962 : ℝ)
  swap
  · have f1 : -(h 1) < (-53616655394587/428956453720962 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact second_node_111 h delta _ctx _hno a16 f1
  by_cases p2 : h 2 ≤ (24915904083856/214478226860481 : ℝ)
  swap
  · have f2 : -(h 2) < (-24915904083856/214478226860481 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact second_node_112 h delta _ctx _hno a17 f2
  by_cases p3 : h 3 ≤ (89368829179067/857912907441924 : ℝ)
  swap
  · have f3 : -(h 3) < (-89368829179067/857912907441924 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact second_node_113 h delta _ctx _hno a16 a17 f3
  apply _hno 13
  change (h 0 ≤ (89368829179067/428956453720962 : ℝ)) ∧ (h 1 ≤ (53616655394587/428956453720962 : ℝ)) ∧ (h 2 ≤ (24915904083856/214478226860481 : ℝ)) ∧ (h 3 ≤ (89368829179067/857912907441924 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem second_node_108 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 2) < (-83/758 : ℝ))
    (a17 : -(h 0) < (-1926518/9004269 : ℝ))
    (a18 : -(h 1) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order3 + (2/3 : ℝ) * _ctx.order4 + (1 : ℝ) * _ctx.min + (4/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * a16 + (1/3 : ℝ) * a17 + (1/3 : ℝ) * a18 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_107 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 2) < (-83/758 : ℝ))
    (a18 : -(h 0) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order1 + (1/3 : ℝ) * _ctx.order3 + (2/3 : ℝ) * _ctx.order4 + (1 : ℝ) * _ctx.min + (4/3 : ℝ) * _ctx.lower + (2/3 : ℝ) * a16 + (1/3 : ℝ) * a18 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

end RealPinwheel.WeakSevenBandData
