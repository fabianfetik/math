import Pinwheel.WeakSevenBandData.CoverChunks.Second000

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem second_node_106 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 2) < (-83/758 : ℝ))
    (a17 : -(h 0) < (-1926518/9004269 : ℝ))
    : False := by
  by_cases p0 : h 0 ≤ (2/9 : ℝ)
  swap
  · have f0 : -(h 0) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact second_node_107 h delta _ctx _hno a16 f0
  by_cases p1 : h 1 ≤ (1/9 : ℝ)
  swap
  · have f1 : -(h 1) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact second_node_108 h delta _ctx _hno a16 a17 f1
  apply _hno 1
  change (h 0 ≤ (2/9 : ℝ)) ∧ (h 1 ≤ (1/9 : ℝ))
  exact ⟨p0, p1⟩

theorem second_node_105 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 2) < (-83/758 : ℝ))
    : False := by
  by_cases p0 : h 0 ≤ (1926518/9004269 : ℝ)
  swap
  · have f0 : -(h 0) < (-1926518/9004269 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact second_node_106 h delta _ctx _hno a16 f0
  by_cases p1 : h 1 ≤ (1074905/9004269 : ℝ)
  swap
  · have f1 : -(h 1) < (-1074905/9004269 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact second_node_109 h delta _ctx _hno a16 f1
  by_cases p2 : h 2 ≤ (8475655/72034152 : ℝ)
  swap
  · have f2 : -(h 2) < (-8475655/72034152 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact second_node_118 h delta _ctx _hno f2
  by_cases p3 : h 3 ≤ (344405/3001423 : ℝ)
  swap
  · have f3 : -(h 3) < (-344405/3001423 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact second_node_119 h delta _ctx _hno f3
  by_cases p4 : h 4 ≤ (963259/9004269 : ℝ)
  swap
  · have f4 : -(h 4) < (-963259/9004269 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact second_node_120 h delta _ctx _hno a16 f4
  apply _hno 14
  change (h 0 ≤ (1926518/9004269 : ℝ)) ∧ (h 1 ≤ (1074905/9004269 : ℝ)) ∧ (h 2 ≤ (8475655/72034152 : ℝ)) ∧ (h 3 ≤ (344405/3001423 : ℝ)) ∧ (h 4 ≤ (963259/9004269 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem second_node_104 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 1) < (-47/379 : ℝ))
    (a17 : -(h 2) < (-10339/95614 : ℝ))
    (a18 : -(h 3) < (-89368829179067/857912907441924 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order4 + (2/3 : ℝ) * _ctx.min + (5/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * _ctx.markL + (1/3 : ℝ) * a16 + (1/3 : ℝ) * a17 + (1/3 : ℝ) * a18 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_103 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 1) < (-47/379 : ℝ))
    (a18 : -(h 2) < (-24915904083856/214478226860481 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/2 : ℝ) * _ctx.order3 + (1 : ℝ) * _ctx.order4 + (3/2 : ℝ) * _ctx.min + (3 : ℝ) * _ctx.lower + (1/2 : ℝ) * _ctx.markL + (1/2 : ℝ) * a16 + (1/2 : ℝ) * a18 + (1/2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_102 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a17 : -(h 2) < (-10339/95614 : ℝ))
    (a18 : -(h 1) < (-53616655394587/428956453720962 : ℝ))
    (a19 : -(h 3) < (-136053119/1322848068 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order4 + (2/3 : ℝ) * _ctx.min + (5/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * _ctx.markL + (1/3 : ℝ) * a17 + (1/3 : ℝ) * a18 + (1/3 : ℝ) * a19 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_101 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a18 : -(h 1) < (-53616655394587/428956453720962 : ℝ))
    (a19 : -(h 2) < (-294532961/2645696136 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/2 : ℝ) * _ctx.order3 + (1 : ℝ) * _ctx.order4 + (3/2 : ℝ) * _ctx.min + (3 : ℝ) * _ctx.lower + (1/2 : ℝ) * _ctx.markL + (1/2 : ℝ) * a18 + (1/2 : ℝ) * a19 + (1/2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_100 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a17 : -(h 2) < (-10339/95614 : ℝ))
    (a19 : -(h 1) < (-84421559/661424034 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/2 : ℝ) * _ctx.order3 + (1 : ℝ) * _ctx.order4 + (3/2 : ℝ) * _ctx.min + (3 : ℝ) * _ctx.lower + (1/2 : ℝ) * _ctx.markL + (1/2 : ℝ) * a17 + (1/2 : ℝ) * a19 + (1/2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_99 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a17 : -(h 2) < (-10339/95614 : ℝ))
    (a18 : -(h 1) < (-53616655394587/428956453720962 : ℝ))
    (a19 : -(h 0) < (-136053119/661424034 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order3 + (2/3 : ℝ) * _ctx.order4 + (1 : ℝ) * _ctx.min + (4/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * a17 + (1/3 : ℝ) * a18 + (1/3 : ℝ) * a19 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_98 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a17 : -(h 2) < (-10339/95614 : ℝ))
    (a18 : -(h 1) < (-53616655394587/428956453720962 : ℝ))
    : False := by
  by_cases p0 : h 0 ≤ (136053119/661424034 : ℝ)
  swap
  · have f0 : -(h 0) < (-136053119/661424034 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact second_node_99 h delta _ctx _hno a17 a18 f0
  by_cases p1 : h 1 ≤ (84421559/661424034 : ℝ)
  swap
  · have f1 : -(h 1) < (-84421559/661424034 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact second_node_100 h delta _ctx _hno a17 f1
  by_cases p2 : h 2 ≤ (294532961/2645696136 : ℝ)
  swap
  · have f2 : -(h 2) < (-294532961/2645696136 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact second_node_101 h delta _ctx _hno a18 f2
  by_cases p3 : h 3 ≤ (136053119/1322848068 : ℝ)
  swap
  · have f3 : -(h 3) < (-136053119/1322848068 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact second_node_102 h delta _ctx _hno a17 a18 f3
  apply _hno 11
  change (h 0 ≤ (136053119/661424034 : ℝ)) ∧ (h 1 ≤ (84421559/661424034 : ℝ)) ∧ (h 2 ≤ (294532961/2645696136 : ℝ)) ∧ (h 3 ≤ (136053119/1322848068 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem second_node_97 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 1) < (-47/379 : ℝ))
    (a17 : -(h 2) < (-10339/95614 : ℝ))
    (a18 : -(h 0) < (-89368829179067/428956453720962 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order3 + (2/3 : ℝ) * _ctx.order4 + (1 : ℝ) * _ctx.min + (4/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * a16 + (1/3 : ℝ) * a17 + (1/3 : ℝ) * a18 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_96 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 1) < (-47/379 : ℝ))
    (a17 : -(h 2) < (-10339/95614 : ℝ))
    : False := by
  by_cases p0 : h 0 ≤ (89368829179067/428956453720962 : ℝ)
  swap
  · have f0 : -(h 0) < (-89368829179067/428956453720962 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact second_node_97 h delta _ctx _hno a16 a17 f0
  by_cases p1 : h 1 ≤ (53616655394587/428956453720962 : ℝ)
  swap
  · have f1 : -(h 1) < (-53616655394587/428956453720962 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact second_node_98 h delta _ctx _hno a17 f1
  by_cases p2 : h 2 ≤ (24915904083856/214478226860481 : ℝ)
  swap
  · have f2 : -(h 2) < (-24915904083856/214478226860481 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact second_node_103 h delta _ctx _hno a16 f2
  by_cases p3 : h 3 ≤ (89368829179067/857912907441924 : ℝ)
  swap
  · have f3 : -(h 3) < (-89368829179067/857912907441924 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact second_node_104 h delta _ctx _hno a16 a17 f3
  apply _hno 13
  change (h 0 ≤ (89368829179067/428956453720962 : ℝ)) ∧ (h 1 ≤ (53616655394587/428956453720962 : ℝ)) ∧ (h 2 ≤ (24915904083856/214478226860481 : ℝ)) ∧ (h 3 ≤ (89368829179067/857912907441924 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem second_node_95 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a17 : -(h 1) < (-6451/47807 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * _ctx.order2 + (2 : ℝ) * _ctx.order3 + (3 : ℝ) * _ctx.order4 + (4 : ℝ) * _ctx.min + (7 : ℝ) * _ctx.lower + (1 : ℝ) * _ctx.markL + (1 : ℝ) * a17 + (1 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_94 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 1) < (-47/379 : ℝ))
    (a17 : -(h 0) < (-10339/47807 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/2 : ℝ) * _ctx.order2 + (1 : ℝ) * _ctx.order3 + (3/2 : ℝ) * _ctx.order4 + (2 : ℝ) * _ctx.min + (5/2 : ℝ) * _ctx.lower + (1/2 : ℝ) * a16 + (1/2 : ℝ) * a17 + (1/2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_93 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 1) < (-47/379 : ℝ))
    : False := by
  by_cases p0 : h 0 ≤ (10339/47807 : ℝ)
  swap
  · have f0 : -(h 0) < (-10339/47807 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact second_node_94 h delta _ctx _hno a16 f0
  by_cases p1 : h 1 ≤ (6451/47807 : ℝ)
  swap
  · have f1 : -(h 1) < (-6451/47807 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact second_node_95 h delta _ctx _hno f1
  by_cases p2 : h 2 ≤ (10339/95614 : ℝ)
  swap
  · have f2 : -(h 2) < (-10339/95614 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact second_node_96 h delta _ctx _hno a16 f2
  apply _hno 10
  change (h 0 ≤ (10339/47807 : ℝ)) ∧ (h 1 ≤ (6451/47807 : ℝ)) ∧ (h 2 ≤ (10339/95614 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem second_node_92 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 0) < (-83/379 : ℝ))
    (a18 : -(h 1) < (-1/9 : ℝ))
    (a19 : -(h 2) < (-4886233/47230299 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order3 + (2/3 : ℝ) * _ctx.order4 + (1 : ℝ) * _ctx.min + (4/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * a16 + (1/3 : ℝ) * a18 + (1/3 : ℝ) * a19 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_91 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 0) < (-83/379 : ℝ))
    (a19 : -(h 1) < (-5389160/47230299 : ℝ))
    (a20 : -(h 2) < (-817990337/8055209811 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order3 + (2/3 : ℝ) * _ctx.order4 + (1 : ℝ) * _ctx.min + (4/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * a16 + (1/3 : ℝ) * a19 + (1/3 : ℝ) * a20 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_90 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 0) < (-83/379 : ℝ))
    (a20 : -(h 1) < (-933539800/8055209811 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/2 : ℝ) * _ctx.order2 + (1 : ℝ) * _ctx.order3 + (3/2 : ℝ) * _ctx.order4 + (2 : ℝ) * _ctx.min + (5/2 : ℝ) * _ctx.lower + (1/2 : ℝ) * a16 + (1/2 : ℝ) * a20 + (1/2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_89 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 0) < (-83/379 : ℝ))
    (a19 : -(h 1) < (-5389160/47230299 : ℝ))
    (a20 : ((-2 : ℝ) * (delta)) < (-1635980674/8055209811 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/9 : ℝ) * _ctx.order2 + (4/9 : ℝ) * _ctx.order3 + (2/3 : ℝ) * _ctx.order4 + (8/9 : ℝ) * _ctx.min + (2/9 : ℝ) * a16 + (2/9 : ℝ) * a19 + (5/9 : ℝ) * a20 + (2/9 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_88 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a19 : -(h 1) < (-5389160/47230299 : ℝ))
    (a20 : -(h 0) < (-352893426530/1586876332767 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/2 : ℝ) * _ctx.order2 + (1 : ℝ) * _ctx.order3 + (3/2 : ℝ) * _ctx.order4 + (2 : ℝ) * _ctx.min + (5/2 : ℝ) * _ctx.lower + (1/2 : ℝ) * a19 + (1/2 : ℝ) * a20 + (1/2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_87 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 0) < (-83/379 : ℝ))
    (a19 : -(h 1) < (-5389160/47230299 : ℝ))
    : False := by
  by_cases p0 : h 0 ≤ (352893426530/1586876332767 : ℝ)
  swap
  · have f0 : -(h 0) < (-352893426530/1586876332767 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact second_node_88 h delta _ctx _hno a19 f0
  by_cases p1 : ((2 : ℝ) * (delta)) ≤ (1635980674/8055209811 : ℝ)
  swap
  · have f1 : ((-2 : ℝ) * (delta)) < (-1635980674/8055209811 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact second_node_89 h delta _ctx _hno a16 a19 f1
  by_cases p2 : h 1 ≤ (933539800/8055209811 : ℝ)
  swap
  · have f2 : -(h 1) < (-933539800/8055209811 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact second_node_90 h delta _ctx _hno a16 f2
  by_cases p3 : h 2 ≤ (817990337/8055209811 : ℝ)
  swap
  · have f3 : -(h 2) < (-817990337/8055209811 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact second_node_91 h delta _ctx _hno a16 a19 f3
  apply _hno 9
  change (h 0 ≤ (352893426530/1586876332767 : ℝ)) ∧ (((2 : ℝ) * (delta)) ≤ (1635980674/8055209811 : ℝ)) ∧ (h 1 ≤ (933539800/8055209811 : ℝ)) ∧ (h 2 ≤ (817990337/8055209811 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem second_node_86 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 0) < (-83/379 : ℝ))
    (a18 : -(h 1) < (-1/9 : ℝ))
    (a19 : ((-2 : ℝ) * (delta)) < (-9772466/47230299 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/9 : ℝ) * _ctx.order2 + (4/9 : ℝ) * _ctx.order3 + (2/3 : ℝ) * _ctx.order4 + (8/9 : ℝ) * _ctx.min + (2/9 : ℝ) * a16 + (2/9 : ℝ) * a18 + (5/9 : ℝ) * a19 + (2/9 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_85 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a18 : -(h 1) < (-1/9 : ℝ))
    (a19 : -(h 0) < (-10857200/47230299 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/2 : ℝ) * _ctx.order2 + (1 : ℝ) * _ctx.order3 + (3/2 : ℝ) * _ctx.order4 + (2 : ℝ) * _ctx.min + (5/2 : ℝ) * _ctx.lower + (1/2 : ℝ) * a18 + (1/2 : ℝ) * a19 + (1/2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_84 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 0) < (-83/379 : ℝ))
    (a18 : -(h 1) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : h 0 ≤ (10857200/47230299 : ℝ)
  swap
  · have f0 : -(h 0) < (-10857200/47230299 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact second_node_85 h delta _ctx _hno a18 f0
  by_cases p1 : ((2 : ℝ) * (delta)) ≤ (9772466/47230299 : ℝ)
  swap
  · have f1 : ((-2 : ℝ) * (delta)) < (-9772466/47230299 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact second_node_86 h delta _ctx _hno a16 a18 f1
  by_cases p2 : h 1 ≤ (5389160/47230299 : ℝ)
  swap
  · have f2 : -(h 1) < (-5389160/47230299 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact second_node_87 h delta _ctx _hno a16 f2
  by_cases p3 : h 2 ≤ (4886233/47230299 : ℝ)
  swap
  · have f3 : -(h 2) < (-4886233/47230299 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact second_node_92 h delta _ctx _hno a16 a18 f3
  apply _hno 6
  change (h 0 ≤ (10857200/47230299 : ℝ)) ∧ (((2 : ℝ) * (delta)) ≤ (9772466/47230299 : ℝ)) ∧ (h 1 ≤ (5389160/47230299 : ℝ)) ∧ (h 2 ≤ (4886233/47230299 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem second_node_83 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a17 : -(h 1) < (-73/689 : ℝ))
    (a18 : -(h 0) < (-2/9 : ℝ))
    (a20 : -(h 3) < (-1247718281/12059888669 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.order2 + (1/4 : ℝ) * _ctx.order4 + (1/2 : ℝ) * _ctx.min + (3/4 : ℝ) * _ctx.lower + (1/4 : ℝ) * a17 + (1/4 : ℝ) * a18 + (1/2 : ℝ) * a20 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_82 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a18 : -(h 0) < (-2/9 : ℝ))
    (a20 : -(h 2) < (-3879780526/36179666007 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order1 + (1/3 : ℝ) * _ctx.order3 + (2/3 : ℝ) * _ctx.order4 + (1 : ℝ) * _ctx.min + (4/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * a18 + (2/3 : ℝ) * a20 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_81 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a18 : -(h 0) < (-2/9 : ℝ))
    (a19 : -(h 2) < (-4886233/47230299 : ℝ))
    (a20 : -(h 1) < (-1323923842/12059888669 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order3 + (2/3 : ℝ) * _ctx.order4 + (1 : ℝ) * _ctx.min + (4/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * a18 + (1/3 : ℝ) * a19 + (1/3 : ℝ) * a20 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_80 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a17 : -(h 1) < (-73/689 : ℝ))
    (a18 : -(h 0) < (-2/9 : ℝ))
    (a20 : ((-2 : ℝ) * (delta)) < (-2495436562/12059888669 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/9 : ℝ) * _ctx.order2 + (4/9 : ℝ) * _ctx.order3 + (2/3 : ℝ) * _ctx.order4 + (8/9 : ℝ) * _ctx.min + (2/9 : ℝ) * a17 + (2/9 : ℝ) * a18 + (5/9 : ℝ) * a20 + (2/9 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_79 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a17 : -(h 1) < (-73/689 : ℝ))
    (a19 : -(h 2) < (-4886233/47230299 : ℝ))
    (a20 : -(h 0) < (-8316733826/36179666007 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order3 + (2/3 : ℝ) * _ctx.order4 + (1 : ℝ) * _ctx.min + (4/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * a17 + (1/3 : ℝ) * a19 + (1/3 : ℝ) * a20 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_78 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a17 : -(h 1) < (-73/689 : ℝ))
    (a18 : -(h 0) < (-2/9 : ℝ))
    (a19 : -(h 2) < (-4886233/47230299 : ℝ))
    : False := by
  by_cases p0 : h 0 ≤ (8316733826/36179666007 : ℝ)
  swap
  · have f0 : -(h 0) < (-8316733826/36179666007 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact second_node_79 h delta _ctx _hno a17 a19 f0
  by_cases p1 : ((2 : ℝ) * (delta)) ≤ (2495436562/12059888669 : ℝ)
  swap
  · have f1 : ((-2 : ℝ) * (delta)) < (-2495436562/12059888669 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact second_node_80 h delta _ctx _hno a17 a18 f1
  by_cases p2 : h 1 ≤ (1323923842/12059888669 : ℝ)
  swap
  · have f2 : -(h 1) < (-1323923842/12059888669 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact second_node_81 h delta _ctx _hno a18 a19 f2
  by_cases p3 : h 2 ≤ (3879780526/36179666007 : ℝ)
  swap
  · have f3 : -(h 2) < (-3879780526/36179666007 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact second_node_82 h delta _ctx _hno a18 f3
  by_cases p4 : h 3 ≤ (1247718281/12059888669 : ℝ)
  swap
  · have f4 : -(h 3) < (-1247718281/12059888669 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact second_node_83 h delta _ctx _hno a17 a18 f4
  apply _hno 7
  change (h 0 ≤ (8316733826/36179666007 : ℝ)) ∧ (((2 : ℝ) * (delta)) ≤ (2495436562/12059888669 : ℝ)) ∧ (h 1 ≤ (1323923842/12059888669 : ℝ)) ∧ (h 2 ≤ (3879780526/36179666007 : ℝ)) ∧ (h 3 ≤ (1247718281/12059888669 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem second_node_77 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a18 : -(h 0) < (-2/9 : ℝ))
    (a19 : -(h 1) < (-5389160/47230299 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/2 : ℝ) * _ctx.order2 + (1 : ℝ) * _ctx.order3 + (3/2 : ℝ) * _ctx.order4 + (2 : ℝ) * _ctx.min + (5/2 : ℝ) * _ctx.lower + (1/2 : ℝ) * a18 + (1/2 : ℝ) * a19 + (1/2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_76 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a17 : -(h 1) < (-73/689 : ℝ))
    (a18 : -(h 0) < (-2/9 : ℝ))
    (a19 : ((-2 : ℝ) * (delta)) < (-9772466/47230299 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/9 : ℝ) * _ctx.order2 + (4/9 : ℝ) * _ctx.order3 + (2/3 : ℝ) * _ctx.order4 + (8/9 : ℝ) * _ctx.min + (2/9 : ℝ) * a17 + (2/9 : ℝ) * a18 + (5/9 : ℝ) * a19 + (2/9 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_75 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a17 : -(h 1) < (-73/689 : ℝ))
    (a19 : -(h 0) < (-10857200/47230299 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/2 : ℝ) * _ctx.order2 + (1 : ℝ) * _ctx.order3 + (3/2 : ℝ) * _ctx.order4 + (2 : ℝ) * _ctx.min + (5/2 : ℝ) * _ctx.lower + (1/2 : ℝ) * a17 + (1/2 : ℝ) * a19 + (1/2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_74 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a17 : -(h 1) < (-73/689 : ℝ))
    (a18 : -(h 0) < (-2/9 : ℝ))
    : False := by
  by_cases p0 : h 0 ≤ (10857200/47230299 : ℝ)
  swap
  · have f0 : -(h 0) < (-10857200/47230299 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact second_node_75 h delta _ctx _hno a17 f0
  by_cases p1 : ((2 : ℝ) * (delta)) ≤ (9772466/47230299 : ℝ)
  swap
  · have f1 : ((-2 : ℝ) * (delta)) < (-9772466/47230299 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact second_node_76 h delta _ctx _hno a17 a18 f1
  by_cases p2 : h 1 ≤ (5389160/47230299 : ℝ)
  swap
  · have f2 : -(h 1) < (-5389160/47230299 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact second_node_77 h delta _ctx _hno a18 f2
  by_cases p3 : h 2 ≤ (4886233/47230299 : ℝ)
  swap
  · have f3 : -(h 2) < (-4886233/47230299 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact second_node_78 h delta _ctx _hno a17 a18 f3
  apply _hno 6
  change (h 0 ≤ (10857200/47230299 : ℝ)) ∧ (((2 : ℝ) * (delta)) ≤ (9772466/47230299 : ℝ)) ∧ (h 1 ≤ (5389160/47230299 : ℝ)) ∧ (h 2 ≤ (4886233/47230299 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem second_node_73 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 0) < (-83/379 : ℝ))
    (a17 : -(h 1) < (-73/689 : ℝ))
    : False := by
  by_cases p0 : h 0 ≤ (2/9 : ℝ)
  swap
  · have f0 : -(h 0) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact second_node_74 h delta _ctx _hno a17 f0
  by_cases p1 : h 1 ≤ (1/9 : ℝ)
  swap
  · have f1 : -(h 1) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact second_node_84 h delta _ctx _hno a16 f1
  apply _hno 1
  change (h 0 ≤ (2/9 : ℝ)) ∧ (h 1 ≤ (1/9 : ℝ))
  exact ⟨p0, p1⟩

theorem second_node_72 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 0) < (-83/379 : ℝ))
    (a17 : ((-2 : ℝ) * (delta)) < (-146/689 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.order1 + (1/2 : ℝ) * _ctx.order2 + (3/4 : ℝ) * _ctx.order3 + (1 : ℝ) * _ctx.order4 + (5/4 : ℝ) * _ctx.min + (1/4 : ℝ) * a16 + (3/4 : ℝ) * a17 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_71 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a17 : -(h 0) < (-162/689 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * _ctx.order1 + (2 : ℝ) * _ctx.order2 + (3 : ℝ) * _ctx.order3 + (4 : ℝ) * _ctx.order4 + (5 : ℝ) * _ctx.min + (6 : ℝ) * _ctx.lower + (1 : ℝ) * a17 + (1 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_70 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 0) < (-83/379 : ℝ))
    : False := by
  by_cases p0 : h 0 ≤ (162/689 : ℝ)
  swap
  · have f0 : -(h 0) < (-162/689 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact second_node_71 h delta _ctx _hno f0
  by_cases p1 : ((2 : ℝ) * (delta)) ≤ (146/689 : ℝ)
  swap
  · have f1 : ((-2 : ℝ) * (delta)) < (-146/689 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact second_node_72 h delta _ctx _hno a16 f1
  by_cases p2 : h 1 ≤ (73/689 : ℝ)
  swap
  · have f2 : -(h 1) < (-73/689 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact second_node_73 h delta _ctx _hno a16 f2
  apply _hno 4
  change (h 0 ≤ (162/689 : ℝ)) ∧ (((2 : ℝ) * (delta)) ≤ (146/689 : ℝ)) ∧ (h 1 ≤ (73/689 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem second_node_69 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    : False := by
  by_cases p0 : h 0 ≤ (83/379 : ℝ)
  swap
  · have f0 : -(h 0) < (-83/379 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact second_node_70 h delta _ctx _hno f0
  by_cases p1 : h 1 ≤ (47/379 : ℝ)
  swap
  · have f1 : -(h 1) < (-47/379 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact second_node_93 h delta _ctx _hno f1
  by_cases p2 : h 2 ≤ (83/758 : ℝ)
  swap
  · have f2 : -(h 2) < (-83/758 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact second_node_105 h delta _ctx _hno f2
  apply _hno 8
  change (h 0 ≤ (83/379 : ℝ)) ∧ (h 1 ≤ (47/379 : ℝ)) ∧ (h 2 ≤ (83/758 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem second_node_68 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a15 : -(h 1) < (-1/8 : ℝ))
    (a16 : -(h 2) < (-10339/95614 : ℝ))
    (a17 : -(h 3) < (-136053119/1322848068 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order4 + (2/3 : ℝ) * _ctx.min + (5/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * _ctx.markL + (1/3 : ℝ) * a15 + (1/3 : ℝ) * a16 + (1/3 : ℝ) * a17 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_67 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a15 : -(h 1) < (-1/8 : ℝ))
    (a17 : -(h 2) < (-294532961/2645696136 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/2 : ℝ) * _ctx.order3 + (1 : ℝ) * _ctx.order4 + (3/2 : ℝ) * _ctx.min + (3 : ℝ) * _ctx.lower + (1/2 : ℝ) * _ctx.markL + (1/2 : ℝ) * a15 + (1/2 : ℝ) * a17 + (1/2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_66 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 2) < (-10339/95614 : ℝ))
    (a17 : -(h 1) < (-84421559/661424034 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/2 : ℝ) * _ctx.order3 + (1 : ℝ) * _ctx.order4 + (3/2 : ℝ) * _ctx.min + (3 : ℝ) * _ctx.lower + (1/2 : ℝ) * _ctx.markL + (1/2 : ℝ) * a16 + (1/2 : ℝ) * a17 + (1/2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_65 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a15 : -(h 1) < (-1/8 : ℝ))
    (a16 : -(h 2) < (-10339/95614 : ℝ))
    (a17 : -(h 0) < (-136053119/661424034 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order3 + (2/3 : ℝ) * _ctx.order4 + (1 : ℝ) * _ctx.min + (4/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * a15 + (1/3 : ℝ) * a16 + (1/3 : ℝ) * a17 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_64 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a15 : -(h 1) < (-1/8 : ℝ))
    (a16 : -(h 2) < (-10339/95614 : ℝ))
    : False := by
  by_cases p0 : h 0 ≤ (136053119/661424034 : ℝ)
  swap
  · have f0 : -(h 0) < (-136053119/661424034 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact second_node_65 h delta _ctx _hno a15 a16 f0
  by_cases p1 : h 1 ≤ (84421559/661424034 : ℝ)
  swap
  · have f1 : -(h 1) < (-84421559/661424034 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact second_node_66 h delta _ctx _hno a16 f1
  by_cases p2 : h 2 ≤ (294532961/2645696136 : ℝ)
  swap
  · have f2 : -(h 2) < (-294532961/2645696136 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact second_node_67 h delta _ctx _hno a15 f2
  by_cases p3 : h 3 ≤ (136053119/1322848068 : ℝ)
  swap
  · have f3 : -(h 3) < (-136053119/1322848068 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact second_node_68 h delta _ctx _hno a15 a16 f3
  apply _hno 11
  change (h 0 ≤ (136053119/661424034 : ℝ)) ∧ (h 1 ≤ (84421559/661424034 : ℝ)) ∧ (h 2 ≤ (294532961/2645696136 : ℝ)) ∧ (h 3 ≤ (136053119/1322848068 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem second_node_63 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 1) < (-6451/47807 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * _ctx.order2 + (2 : ℝ) * _ctx.order3 + (3 : ℝ) * _ctx.order4 + (4 : ℝ) * _ctx.min + (7 : ℝ) * _ctx.lower + (1 : ℝ) * _ctx.markL + (1 : ℝ) * a16 + (1 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_62 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a15 : -(h 1) < (-1/8 : ℝ))
    (a16 : -(h 0) < (-10339/47807 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/2 : ℝ) * _ctx.order2 + (1 : ℝ) * _ctx.order3 + (3/2 : ℝ) * _ctx.order4 + (2 : ℝ) * _ctx.min + (5/2 : ℝ) * _ctx.lower + (1/2 : ℝ) * a15 + (1/2 : ℝ) * a16 + (1/2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_61 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a15 : -(h 1) < (-1/8 : ℝ))
    : False := by
  by_cases p0 : h 0 ≤ (10339/47807 : ℝ)
  swap
  · have f0 : -(h 0) < (-10339/47807 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact second_node_62 h delta _ctx _hno a15 f0
  by_cases p1 : h 1 ≤ (6451/47807 : ℝ)
  swap
  · have f1 : -(h 1) < (-6451/47807 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact second_node_63 h delta _ctx _hno f1
  by_cases p2 : h 2 ≤ (10339/95614 : ℝ)
  swap
  · have f2 : -(h 2) < (-10339/95614 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact second_node_64 h delta _ctx _hno a15 f2
  apply _hno 10
  change (h 0 ≤ (10339/47807 : ℝ)) ∧ (h 1 ≤ (6451/47807 : ℝ)) ∧ (h 2 ≤ (10339/95614 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem second_node_60 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 1) < (-1/9 : ℝ))
    (a17 : -(h 2) < (-83/758 : ℝ))
    (a19 : -(h 4) < (-963259/9004269 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.order3 + (1/4 : ℝ) * _ctx.min + (1 : ℝ) * _ctx.lower + (1/4 : ℝ) * _ctx.markL + (1/4 : ℝ) * a16 + (1/4 : ℝ) * a17 + (1/2 : ℝ) * a19 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_59 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a19 : -(h 3) < (-344405/3001423 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order1 + (2/3 : ℝ) * _ctx.order2 + (1/3 : ℝ) * _ctx.order4 + (2/3 : ℝ) * _ctx.min + (5/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * _ctx.markL + (1 : ℝ) * a19 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_58 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a18 : -(h 3) < (-2159/20223 : ℝ))
    (a19 : -(h 2) < (-8475655/72034152 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order1 + (1/3 : ℝ) * _ctx.order4 + (2/3 : ℝ) * _ctx.min + (5/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * _ctx.markL + (1/3 : ℝ) * a18 + (2/3 : ℝ) * a19 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_57 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a17 : -(h 2) < (-83/758 : ℝ))
    (a18 : -(h 3) < (-2159/20223 : ℝ))
    (a19 : -(h 1) < (-1074905/9004269 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order4 + (2/3 : ℝ) * _ctx.min + (5/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * _ctx.markL + (1/3 : ℝ) * a17 + (1/3 : ℝ) * a18 + (1/3 : ℝ) * a19 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_56 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 1) < (-1/9 : ℝ))
    (a17 : -(h 2) < (-83/758 : ℝ))
    (a18 : -(h 3) < (-2159/20223 : ℝ))
    (a19 : -(h 0) < (-1926518/9004269 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.order4 + (1/2 : ℝ) * _ctx.min + (3/4 : ℝ) * _ctx.lower + (1/4 : ℝ) * a16 + (1/4 : ℝ) * a17 + (1/4 : ℝ) * a18 + (1/4 : ℝ) * a19 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_55 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 1) < (-1/9 : ℝ))
    (a17 : -(h 2) < (-83/758 : ℝ))
    (a18 : -(h 3) < (-2159/20223 : ℝ))
    : False := by
  by_cases p0 : h 0 ≤ (1926518/9004269 : ℝ)
  swap
  · have f0 : -(h 0) < (-1926518/9004269 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact second_node_56 h delta _ctx _hno a16 a17 a18 f0
  by_cases p1 : h 1 ≤ (1074905/9004269 : ℝ)
  swap
  · have f1 : -(h 1) < (-1074905/9004269 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact second_node_57 h delta _ctx _hno a17 a18 f1
  by_cases p2 : h 2 ≤ (8475655/72034152 : ℝ)
  swap
  · have f2 : -(h 2) < (-8475655/72034152 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact second_node_58 h delta _ctx _hno a18 f2
  by_cases p3 : h 3 ≤ (344405/3001423 : ℝ)
  swap
  · have f3 : -(h 3) < (-344405/3001423 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact second_node_59 h delta _ctx _hno f3
  by_cases p4 : h 4 ≤ (963259/9004269 : ℝ)
  swap
  · have f4 : -(h 4) < (-963259/9004269 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact second_node_60 h delta _ctx _hno a16 a17 f4
  apply _hno 14
  change (h 0 ≤ (1926518/9004269 : ℝ)) ∧ (h 1 ≤ (1074905/9004269 : ℝ)) ∧ (h 2 ≤ (8475655/72034152 : ℝ)) ∧ (h 3 ≤ (344405/3001423 : ℝ)) ∧ (h 4 ≤ (963259/9004269 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem second_node_54 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a18 : -(h 2) < (-19109/161784 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/2 : ℝ) * _ctx.order1 + (1/2 : ℝ) * _ctx.order3 + (1 : ℝ) * _ctx.order4 + (3/2 : ℝ) * _ctx.min + (3 : ℝ) * _ctx.lower + (1/2 : ℝ) * _ctx.markL + (1 : ℝ) * a18 + (1/2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_53 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a17 : -(h 2) < (-83/758 : ℝ))
    (a18 : -(h 1) < (-2423/20223 : ℝ))
    (a20 : -(h 3) < (-89368829179067/857912907441924 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order4 + (2/3 : ℝ) * _ctx.min + (5/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * _ctx.markL + (1/3 : ℝ) * a17 + (1/3 : ℝ) * a18 + (1/3 : ℝ) * a20 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_52 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a18 : -(h 1) < (-2423/20223 : ℝ))
    (a19 : -(h 3) < (-136053119/1322848068 : ℝ))
    (a20 : -(h 2) < (-24915904083856/214478226860481 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order4 + (2/3 : ℝ) * _ctx.min + (5/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * _ctx.markL + (1/3 : ℝ) * a18 + (1/3 : ℝ) * a19 + (1/3 : ℝ) * a20 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_51 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a17 : -(h 2) < (-83/758 : ℝ))
    (a19 : -(h 3) < (-136053119/1322848068 : ℝ))
    (a20 : -(h 1) < (-53616655394587/428956453720962 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order4 + (2/3 : ℝ) * _ctx.min + (5/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * _ctx.markL + (1/3 : ℝ) * a17 + (1/3 : ℝ) * a19 + (1/3 : ℝ) * a20 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_50 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a17 : -(h 2) < (-83/758 : ℝ))
    (a18 : -(h 1) < (-2423/20223 : ℝ))
    (a19 : -(h 3) < (-136053119/1322848068 : ℝ))
    (a20 : -(h 0) < (-89368829179067/428956453720962 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.order4 + (1/2 : ℝ) * _ctx.min + (3/4 : ℝ) * _ctx.lower + (1/4 : ℝ) * a17 + (1/4 : ℝ) * a18 + (1/4 : ℝ) * a19 + (1/4 : ℝ) * a20 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_49 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a17 : -(h 2) < (-83/758 : ℝ))
    (a18 : -(h 1) < (-2423/20223 : ℝ))
    (a19 : -(h 3) < (-136053119/1322848068 : ℝ))
    : False := by
  by_cases p0 : h 0 ≤ (89368829179067/428956453720962 : ℝ)
  swap
  · have f0 : -(h 0) < (-89368829179067/428956453720962 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact second_node_50 h delta _ctx _hno a17 a18 a19 f0
  by_cases p1 : h 1 ≤ (53616655394587/428956453720962 : ℝ)
  swap
  · have f1 : -(h 1) < (-53616655394587/428956453720962 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact second_node_51 h delta _ctx _hno a17 a19 f1
  by_cases p2 : h 2 ≤ (24915904083856/214478226860481 : ℝ)
  swap
  · have f2 : -(h 2) < (-24915904083856/214478226860481 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact second_node_52 h delta _ctx _hno a18 a19 f2
  by_cases p3 : h 3 ≤ (89368829179067/857912907441924 : ℝ)
  swap
  · have f3 : -(h 3) < (-89368829179067/857912907441924 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact second_node_53 h delta _ctx _hno a17 a18 f3
  apply _hno 13
  change (h 0 ≤ (89368829179067/428956453720962 : ℝ)) ∧ (h 1 ≤ (53616655394587/428956453720962 : ℝ)) ∧ (h 2 ≤ (24915904083856/214478226860481 : ℝ)) ∧ (h 3 ≤ (89368829179067/857912907441924 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem second_node_48 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a18 : -(h 1) < (-2423/20223 : ℝ))
    (a19 : -(h 2) < (-294532961/2645696136 : ℝ))
    (a20 : -(h 3) < (-89368829179067/857912907441924 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order4 + (2/3 : ℝ) * _ctx.min + (5/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * _ctx.markL + (1/3 : ℝ) * a18 + (1/3 : ℝ) * a19 + (1/3 : ℝ) * a20 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_47 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a18 : -(h 1) < (-2423/20223 : ℝ))
    (a20 : -(h 2) < (-24915904083856/214478226860481 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/2 : ℝ) * _ctx.order3 + (1 : ℝ) * _ctx.order4 + (3/2 : ℝ) * _ctx.min + (3 : ℝ) * _ctx.lower + (1/2 : ℝ) * _ctx.markL + (1/2 : ℝ) * a18 + (1/2 : ℝ) * a20 + (1/2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_46 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a19 : -(h 2) < (-294532961/2645696136 : ℝ))
    (a20 : -(h 1) < (-53616655394587/428956453720962 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/2 : ℝ) * _ctx.order3 + (1 : ℝ) * _ctx.order4 + (3/2 : ℝ) * _ctx.min + (3 : ℝ) * _ctx.lower + (1/2 : ℝ) * _ctx.markL + (1/2 : ℝ) * a19 + (1/2 : ℝ) * a20 + (1/2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_45 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a18 : -(h 1) < (-2423/20223 : ℝ))
    (a19 : -(h 2) < (-294532961/2645696136 : ℝ))
    (a20 : -(h 0) < (-89368829179067/428956453720962 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order3 + (2/3 : ℝ) * _ctx.order4 + (1 : ℝ) * _ctx.min + (4/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * a18 + (1/3 : ℝ) * a19 + (1/3 : ℝ) * a20 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_44 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a18 : -(h 1) < (-2423/20223 : ℝ))
    (a19 : -(h 2) < (-294532961/2645696136 : ℝ))
    : False := by
  by_cases p0 : h 0 ≤ (89368829179067/428956453720962 : ℝ)
  swap
  · have f0 : -(h 0) < (-89368829179067/428956453720962 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact second_node_45 h delta _ctx _hno a18 a19 f0
  by_cases p1 : h 1 ≤ (53616655394587/428956453720962 : ℝ)
  swap
  · have f1 : -(h 1) < (-53616655394587/428956453720962 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact second_node_46 h delta _ctx _hno a19 f1
  by_cases p2 : h 2 ≤ (24915904083856/214478226860481 : ℝ)
  swap
  · have f2 : -(h 2) < (-24915904083856/214478226860481 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact second_node_47 h delta _ctx _hno a18 f2
  by_cases p3 : h 3 ≤ (89368829179067/857912907441924 : ℝ)
  swap
  · have f3 : -(h 3) < (-89368829179067/857912907441924 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact second_node_48 h delta _ctx _hno a18 a19 f3
  apply _hno 13
  change (h 0 ≤ (89368829179067/428956453720962 : ℝ)) ∧ (h 1 ≤ (53616655394587/428956453720962 : ℝ)) ∧ (h 2 ≤ (24915904083856/214478226860481 : ℝ)) ∧ (h 3 ≤ (89368829179067/857912907441924 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem second_node_43 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a17 : -(h 2) < (-83/758 : ℝ))
    (a19 : -(h 1) < (-84421559/661424034 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/2 : ℝ) * _ctx.order3 + (1 : ℝ) * _ctx.order4 + (3/2 : ℝ) * _ctx.min + (3 : ℝ) * _ctx.lower + (1/2 : ℝ) * _ctx.markL + (1/2 : ℝ) * a17 + (1/2 : ℝ) * a19 + (1/2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_42 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a17 : -(h 2) < (-83/758 : ℝ))
    (a18 : -(h 1) < (-2423/20223 : ℝ))
    (a19 : -(h 0) < (-136053119/661424034 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order3 + (2/3 : ℝ) * _ctx.order4 + (1 : ℝ) * _ctx.min + (4/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * a17 + (1/3 : ℝ) * a18 + (1/3 : ℝ) * a19 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_41 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a17 : -(h 2) < (-83/758 : ℝ))
    (a18 : -(h 1) < (-2423/20223 : ℝ))
    : False := by
  by_cases p0 : h 0 ≤ (136053119/661424034 : ℝ)
  swap
  · have f0 : -(h 0) < (-136053119/661424034 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact second_node_42 h delta _ctx _hno a17 a18 f0
  by_cases p1 : h 1 ≤ (84421559/661424034 : ℝ)
  swap
  · have f1 : -(h 1) < (-84421559/661424034 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact second_node_43 h delta _ctx _hno a17 f1
  by_cases p2 : h 2 ≤ (294532961/2645696136 : ℝ)
  swap
  · have f2 : -(h 2) < (-294532961/2645696136 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact second_node_44 h delta _ctx _hno a18 f2
  by_cases p3 : h 3 ≤ (136053119/1322848068 : ℝ)
  swap
  · have f3 : -(h 3) < (-136053119/1322848068 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact second_node_49 h delta _ctx _hno a17 a18 f3
  apply _hno 11
  change (h 0 ≤ (136053119/661424034 : ℝ)) ∧ (h 1 ≤ (84421559/661424034 : ℝ)) ∧ (h 2 ≤ (294532961/2645696136 : ℝ)) ∧ (h 3 ≤ (136053119/1322848068 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem second_node_40 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 1) < (-1/9 : ℝ))
    (a17 : -(h 2) < (-83/758 : ℝ))
    (a18 : -(h 0) < (-4318/20223 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order3 + (2/3 : ℝ) * _ctx.order4 + (1 : ℝ) * _ctx.min + (4/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * a16 + (1/3 : ℝ) * a17 + (1/3 : ℝ) * a18 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_39 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 1) < (-1/9 : ℝ))
    (a17 : -(h 2) < (-83/758 : ℝ))
    : False := by
  by_cases p0 : h 0 ≤ (4318/20223 : ℝ)
  swap
  · have f0 : -(h 0) < (-4318/20223 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact second_node_40 h delta _ctx _hno a16 a17 f0
  by_cases p1 : h 1 ≤ (2423/20223 : ℝ)
  swap
  · have f1 : -(h 1) < (-2423/20223 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact second_node_41 h delta _ctx _hno a17 f1
  by_cases p2 : h 2 ≤ (19109/161784 : ℝ)
  swap
  · have f2 : -(h 2) < (-19109/161784 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact second_node_54 h delta _ctx _hno f2
  by_cases p3 : h 3 ≤ (2159/20223 : ℝ)
  swap
  · have f3 : -(h 3) < (-2159/20223 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact second_node_55 h delta _ctx _hno a16 a17 f3
  apply _hno 12
  change (h 0 ≤ (4318/20223 : ℝ)) ∧ (h 1 ≤ (2423/20223 : ℝ)) ∧ (h 2 ≤ (19109/161784 : ℝ)) ∧ (h 3 ≤ (2159/20223 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem second_node_38 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a17 : -(h 1) < (-47/379 : ℝ))
    (a18 : -(h 2) < (-10339/95614 : ℝ))
    (a19 : -(h 3) < (-136053119/1322848068 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order4 + (2/3 : ℝ) * _ctx.min + (5/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * _ctx.markL + (1/3 : ℝ) * a17 + (1/3 : ℝ) * a18 + (1/3 : ℝ) * a19 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_37 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a17 : -(h 1) < (-47/379 : ℝ))
    (a19 : -(h 2) < (-294532961/2645696136 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/2 : ℝ) * _ctx.order3 + (1 : ℝ) * _ctx.order4 + (3/2 : ℝ) * _ctx.min + (3 : ℝ) * _ctx.lower + (1/2 : ℝ) * _ctx.markL + (1/2 : ℝ) * a17 + (1/2 : ℝ) * a19 + (1/2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_36 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a18 : -(h 2) < (-10339/95614 : ℝ))
    (a19 : -(h 1) < (-84421559/661424034 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/2 : ℝ) * _ctx.order3 + (1 : ℝ) * _ctx.order4 + (3/2 : ℝ) * _ctx.min + (3 : ℝ) * _ctx.lower + (1/2 : ℝ) * _ctx.markL + (1/2 : ℝ) * a18 + (1/2 : ℝ) * a19 + (1/2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_35 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a17 : -(h 1) < (-47/379 : ℝ))
    (a18 : -(h 2) < (-10339/95614 : ℝ))
    (a19 : -(h 0) < (-136053119/661424034 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order3 + (2/3 : ℝ) * _ctx.order4 + (1 : ℝ) * _ctx.min + (4/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * a17 + (1/3 : ℝ) * a18 + (1/3 : ℝ) * a19 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_34 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a17 : -(h 1) < (-47/379 : ℝ))
    (a18 : -(h 2) < (-10339/95614 : ℝ))
    : False := by
  by_cases p0 : h 0 ≤ (136053119/661424034 : ℝ)
  swap
  · have f0 : -(h 0) < (-136053119/661424034 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact second_node_35 h delta _ctx _hno a17 a18 f0
  by_cases p1 : h 1 ≤ (84421559/661424034 : ℝ)
  swap
  · have f1 : -(h 1) < (-84421559/661424034 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact second_node_36 h delta _ctx _hno a18 f1
  by_cases p2 : h 2 ≤ (294532961/2645696136 : ℝ)
  swap
  · have f2 : -(h 2) < (-294532961/2645696136 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact second_node_37 h delta _ctx _hno a17 f2
  by_cases p3 : h 3 ≤ (136053119/1322848068 : ℝ)
  swap
  · have f3 : -(h 3) < (-136053119/1322848068 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact second_node_38 h delta _ctx _hno a17 a18 f3
  apply _hno 11
  change (h 0 ≤ (136053119/661424034 : ℝ)) ∧ (h 1 ≤ (84421559/661424034 : ℝ)) ∧ (h 2 ≤ (294532961/2645696136 : ℝ)) ∧ (h 3 ≤ (136053119/1322848068 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem second_node_33 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a18 : -(h 1) < (-6451/47807 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * _ctx.order2 + (2 : ℝ) * _ctx.order3 + (3 : ℝ) * _ctx.order4 + (4 : ℝ) * _ctx.min + (7 : ℝ) * _ctx.lower + (1 : ℝ) * _ctx.markL + (1 : ℝ) * a18 + (1 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_32 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a17 : -(h 1) < (-47/379 : ℝ))
    (a18 : -(h 0) < (-10339/47807 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/2 : ℝ) * _ctx.order2 + (1 : ℝ) * _ctx.order3 + (3/2 : ℝ) * _ctx.order4 + (2 : ℝ) * _ctx.min + (5/2 : ℝ) * _ctx.lower + (1/2 : ℝ) * a17 + (1/2 : ℝ) * a18 + (1/2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_31 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a17 : -(h 1) < (-47/379 : ℝ))
    : False := by
  by_cases p0 : h 0 ≤ (10339/47807 : ℝ)
  swap
  · have f0 : -(h 0) < (-10339/47807 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact second_node_32 h delta _ctx _hno a17 f0
  by_cases p1 : h 1 ≤ (6451/47807 : ℝ)
  swap
  · have f1 : -(h 1) < (-6451/47807 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact second_node_33 h delta _ctx _hno f1
  by_cases p2 : h 2 ≤ (10339/95614 : ℝ)
  swap
  · have f2 : -(h 2) < (-10339/95614 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact second_node_34 h delta _ctx _hno a17 f2
  apply _hno 10
  change (h 0 ≤ (10339/47807 : ℝ)) ∧ (h 1 ≤ (6451/47807 : ℝ)) ∧ (h 2 ≤ (10339/95614 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem second_node_30 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 1) < (-1/9 : ℝ))
    (a17 : -(h 0) < (-83/379 : ℝ))
    (a18 : -(h 2) < (-4886233/47230299 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order3 + (2/3 : ℝ) * _ctx.order4 + (1 : ℝ) * _ctx.min + (4/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * a16 + (1/3 : ℝ) * a17 + (1/3 : ℝ) * a18 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_29 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a17 : -(h 0) < (-83/379 : ℝ))
    (a18 : -(h 1) < (-5389160/47230299 : ℝ))
    (a19 : -(h 2) < (-817990337/8055209811 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order3 + (2/3 : ℝ) * _ctx.order4 + (1 : ℝ) * _ctx.min + (4/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * a17 + (1/3 : ℝ) * a18 + (1/3 : ℝ) * a19 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_28 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a17 : -(h 0) < (-83/379 : ℝ))
    (a19 : -(h 1) < (-933539800/8055209811 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/2 : ℝ) * _ctx.order2 + (1 : ℝ) * _ctx.order3 + (3/2 : ℝ) * _ctx.order4 + (2 : ℝ) * _ctx.min + (5/2 : ℝ) * _ctx.lower + (1/2 : ℝ) * a17 + (1/2 : ℝ) * a19 + (1/2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_27 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a17 : -(h 0) < (-83/379 : ℝ))
    (a18 : -(h 1) < (-5389160/47230299 : ℝ))
    (a19 : ((-2 : ℝ) * (delta)) < (-1635980674/8055209811 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/9 : ℝ) * _ctx.order2 + (4/9 : ℝ) * _ctx.order3 + (2/3 : ℝ) * _ctx.order4 + (8/9 : ℝ) * _ctx.min + (2/9 : ℝ) * a17 + (2/9 : ℝ) * a18 + (5/9 : ℝ) * a19 + (2/9 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

end RealPinwheel.WeakSevenBandData
