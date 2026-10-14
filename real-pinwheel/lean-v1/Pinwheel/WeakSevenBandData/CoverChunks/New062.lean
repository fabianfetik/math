import Pinwheel.WeakSevenBandData.CoverChunks.New061

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem new_node_8154 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : -(h 2) < (-3/25 : ℝ))
    (a37 : -(h 4) < (-3/28 : ℝ))
    (a39 : -(h 0) < (-5/33 : ℝ))
    (a42 : -(h 1) < (-8/55 : ℝ))
    (a52 : -(h 3) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a26 + (1/5 : ℝ) * a37 + (1/5 : ℝ) * a39 + (1/5 : ℝ) * a42 + (1/5 : ℝ) * a52 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8153 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a36 : h 2 ≤ (1/8 : ℝ))
    (a51 : -(h 2) < (-6/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a36 + (1 : ℝ) * a51
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8152 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : -(h 2) < (-3/25 : ℝ))
    (a37 : -(h 4) < (-3/28 : ℝ))
    (a47 : -(h 3) < (-4/37 : ℝ))
    (a50 : -(h 1) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order0 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a26 + (1/5 : ℝ) * a37 + (1/5 : ℝ) * a47 + (2/5 : ℝ) * a50 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8151 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a41 : h 0 ≤ (2/13 : ℝ))
    (a49 : -(h 0) < (-4/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a41 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8150 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a48 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8149 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a26 : -(h 2) < (-3/25 : ℝ))
    (a36 : h 2 ≤ (1/8 : ℝ))
    (a37 : -(h 4) < (-3/28 : ℝ))
    (a39 : -(h 0) < (-5/33 : ℝ))
    (a41 : h 0 ≤ (2/13 : ℝ))
    (a42 : -(h 1) < (-8/55 : ℝ))
    (a47 : -(h 3) < (-4/37 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_8150 h delta _ctx _hno a16 f0
  by_cases p1 : h 0 ≤ (4/25 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/25 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_8151 h delta _ctx _hno a41 f1
  by_cases p2 : h 1 ≤ (2/13 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_8152 h delta _ctx _hno a26 a37 a47 f2
  by_cases p3 : h 2 ≤ (6/47 : ℝ)
  swap
  · have f3 : -(h 2) < (-6/47 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_8153 h delta _ctx _hno a36 f3
  by_cases p4 : h 3 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_8154 h delta _ctx _hno a26 a37 a39 a42 f4
  by_cases p5 : h 4 ≤ (5/46 : ℝ)
  swap
  · have f5 : -(h 4) < (-5/46 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_8155 h delta _ctx _hno a26 a39 a42 f5
  apply _hno 157
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (6/47 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ)) ∧ (h 4 ≤ (5/46 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_8148 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a37 : -(h 4) < (-3/28 : ℝ))
    (a39 : -(h 0) < (-5/33 : ℝ))
    (a42 : -(h 1) < (-8/55 : ℝ))
    (a46 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (2/5 : ℝ) * a37 + (1/5 : ℝ) * a39 + (1/5 : ℝ) * a42 + (1/5 : ℝ) * a46 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8147 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : h 1 ≤ (2/13 : ℝ))
    (a45 : -(h 1) < (-4/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a25 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8146 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a41 : h 0 ≤ (2/13 : ℝ))
    (a44 : -(h 0) < (-6/37 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a41 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8145 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-8/37 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8144 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : -(h 2) < (-3/25 : ℝ))
    (a29 : -(h 1) < (-1/7 : ℝ))
    (a41 : -(h 0) < (-2/13 : ℝ))
    (a52 : -(h 4) < (-5/46 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a26 + (1/5 : ℝ) * a29 + (1/5 : ℝ) * a41 + (2/5 : ℝ) * a52 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8143 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : -(h 2) < (-3/25 : ℝ))
    (a29 : -(h 1) < (-1/7 : ℝ))
    (a37 : -(h 4) < (-3/28 : ℝ))
    (a41 : -(h 0) < (-2/13 : ℝ))
    (a51 : -(h 3) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a26 + (1/5 : ℝ) * a29 + (1/5 : ℝ) * a37 + (1/5 : ℝ) * a41 + (1/5 : ℝ) * a51 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8142 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a36 : h 2 ≤ (1/8 : ℝ))
    (a50 : -(h 2) < (-6/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a36 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8141 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : -(h 2) < (-3/25 : ℝ))
    (a37 : -(h 4) < (-3/28 : ℝ))
    (a41 : -(h 0) < (-2/13 : ℝ))
    (a46 : -(h 3) < (-4/37 : ℝ))
    (a49 : -(h 1) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a26 + (1/5 : ℝ) * a37 + (1/5 : ℝ) * a41 + (1/5 : ℝ) * a46 + (1/5 : ℝ) * a49 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8140 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a31 : h 0 ≤ (3/19 : ℝ))
    (a48 : -(h 0) < (-4/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8139 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a47 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8138 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a26 : -(h 2) < (-3/25 : ℝ))
    (a29 : -(h 1) < (-1/7 : ℝ))
    (a31 : h 0 ≤ (3/19 : ℝ))
    (a36 : h 2 ≤ (1/8 : ℝ))
    (a37 : -(h 4) < (-3/28 : ℝ))
    (a41 : -(h 0) < (-2/13 : ℝ))
    (a46 : -(h 3) < (-4/37 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_8139 h delta _ctx _hno a16 f0
  by_cases p1 : h 0 ≤ (4/25 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/25 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_8140 h delta _ctx _hno a31 f1
  by_cases p2 : h 1 ≤ (2/13 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_8141 h delta _ctx _hno a26 a37 a41 a46 f2
  by_cases p3 : h 2 ≤ (6/47 : ℝ)
  swap
  · have f3 : -(h 2) < (-6/47 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_8142 h delta _ctx _hno a36 f3
  by_cases p4 : h 3 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_8143 h delta _ctx _hno a26 a29 a37 a41 f4
  by_cases p5 : h 4 ≤ (5/46 : ℝ)
  swap
  · have f5 : -(h 4) < (-5/46 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_8144 h delta _ctx _hno a26 a29 a41 f5
  apply _hno 157
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (6/47 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ)) ∧ (h 4 ≤ (5/46 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_8137 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a29 : -(h 1) < (-1/7 : ℝ))
    (a37 : -(h 4) < (-3/28 : ℝ))
    (a41 : -(h 0) < (-2/13 : ℝ))
    (a45 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a29 + (2/5 : ℝ) * a37 + (1/5 : ℝ) * a41 + (1/5 : ℝ) * a45 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8136 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : h 1 ≤ (2/13 : ℝ))
    (a44 : -(h 1) < (-4/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a25 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8135 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a31 : h 0 ≤ (3/19 : ℝ))
    (a43 : -(h 0) < (-6/37 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8134 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a42 : ((-2 : ℝ) * (delta)) < (-8/37 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8133 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a26 : -(h 2) < (-3/25 : ℝ))
    (a29 : -(h 1) < (-1/7 : ℝ))
    (a36 : h 2 ≤ (1/8 : ℝ))
    (a39 : -(h 0) < (-5/33 : ℝ))
    (a44 : h 3 ≤ (6/55 : ℝ))
    (a45 : -(h 4) < (-5/46 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (14/69 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-14/69 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_8174 h delta _ctx _hno a16 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_8175 h delta _ctx _hno a26 a29 a45 f1
  by_cases p2 : h 2 ≤ (5/39 : ℝ)
  swap
  · have f2 : -(h 2) < (-5/39 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_8176 h delta _ctx _hno a36 f2
  by_cases p3 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f3 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_8177 h delta _ctx _hno a44 f3
  by_cases p4 : h 4 ≤ (9/79 : ℝ)
  swap
  · have f4 : -(h 4) < (-9/79 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_8178 h delta _ctx _hno a44 f4
  by_cases p5 : h 5 ≤ (3/29 : ℝ)
  swap
  · have f5 : -(h 5) < (-3/29 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_8179 h delta _ctx _hno a26 a29 a39 a45 f5
  apply _hno 208
  change (((2 : ℝ) * (delta)) ≤ (14/69 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (5/39 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 4 ≤ (9/79 : ℝ)) ∧ (h 5 ≤ (3/29 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_8132 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a26 : -(h 2) < (-3/25 : ℝ))
    (a29 : -(h 1) < (-1/7 : ℝ))
    (a36 : h 2 ≤ (1/8 : ℝ))
    (a37 : -(h 4) < (-3/28 : ℝ))
    (a39 : -(h 0) < (-5/33 : ℝ))
    (a41 : h 0 ≤ (2/13 : ℝ))
    (a42 : h 1 ≤ (8/55 : ℝ))
    (a44 : -(h 3) < (-6/55 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_8156 h delta _ctx _hno a16 f0
  by_cases p1 : h 0 ≤ (4/25 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/25 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_8157 h delta _ctx _hno a41 f1
  by_cases p2 : h 1 ≤ (2/13 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_8158 h delta _ctx _hno a42 f2
  by_cases p3 : h 2 ≤ (6/47 : ℝ)
  swap
  · have f3 : -(h 2) < (-6/47 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_8159 h delta _ctx _hno a36 f3
  by_cases p4 : h 3 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_8160 h delta _ctx _hno a16 a26 a29 a36 a37 a39 f4
  by_cases p5 : h 4 ≤ (5/46 : ℝ)
  swap
  · have f5 : -(h 4) < (-5/46 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_8161 h delta _ctx _hno a16 a26 a29 a36 a39 a44 p4 f5
  apply _hno 157
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (6/47 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ)) ∧ (h 4 ≤ (5/46 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_8131 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a36 : h 2 ≤ (1/8 : ℝ))
    (a43 : -(h 2) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a36 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8130 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a25 : h 1 ≤ (2/13 : ℝ))
    (a26 : -(h 2) < (-3/25 : ℝ))
    (a36 : h 2 ≤ (1/8 : ℝ))
    (a37 : -(h 4) < (-3/28 : ℝ))
    (a39 : -(h 0) < (-5/33 : ℝ))
    (a41 : h 0 ≤ (2/13 : ℝ))
    (a42 : -(h 1) < (-8/55 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (8/37 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-8/37 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_8145 h delta _ctx _hno a16 f0
  by_cases p1 : h 0 ≤ (6/37 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/37 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_8146 h delta _ctx _hno a41 f1
  by_cases p2 : h 1 ≤ (4/25 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/25 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_8147 h delta _ctx _hno a25 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_8148 h delta _ctx _hno a37 a39 a42 f3
  by_cases p4 : h 3 ≤ (4/37 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/37 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_8149 h delta _ctx _hno a16 a26 a36 a37 a39 a41 a42 f4
  apply _hno 26
  change (((2 : ℝ) * (delta)) ≤ (8/37 : ℝ)) ∧ (h 0 ≤ (6/37 : ℝ)) ∧ (h 1 ≤ (4/25 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (4/37 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_8129 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a25 : h 1 ≤ (2/13 : ℝ))
    (a26 : -(h 2) < (-3/25 : ℝ))
    (a29 : -(h 1) < (-1/7 : ℝ))
    (a31 : h 0 ≤ (3/19 : ℝ))
    (a36 : h 2 ≤ (1/8 : ℝ))
    (a37 : -(h 4) < (-3/28 : ℝ))
    (a41 : -(h 0) < (-2/13 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (8/37 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-8/37 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_8134 h delta _ctx _hno a16 f0
  by_cases p1 : h 0 ≤ (6/37 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/37 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_8135 h delta _ctx _hno a31 f1
  by_cases p2 : h 1 ≤ (4/25 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/25 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_8136 h delta _ctx _hno a25 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_8137 h delta _ctx _hno a29 a37 a41 f3
  by_cases p4 : h 3 ≤ (4/37 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/37 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_8138 h delta _ctx _hno a16 a26 a29 a31 a36 a37 a41 f4
  apply _hno 26
  change (((2 : ℝ) * (delta)) ≤ (8/37 : ℝ)) ∧ (h 0 ≤ (6/37 : ℝ)) ∧ (h 1 ≤ (4/25 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (4/37 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_8128 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a40 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8127 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a22 : -(h 0) < (-3/20 : ℝ))
    (a26 : -(h 2) < (-3/25 : ℝ))
    (a29 : -(h 1) < (-1/7 : ℝ))
    (a43 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a22 + (1/5 : ℝ) * a26 + (1/5 : ℝ) * a29 + (2/5 : ℝ) * a43 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8126 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : h 3 ≤ (3/25 : ℝ))
    (a42 : -(h 3) < (-7/57 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a19 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8125 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a36 : h 2 ≤ (1/8 : ℝ))
    (a41 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a36 + (1 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8124 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a22 : -(h 0) < (-3/20 : ℝ))
    (a26 : -(h 2) < (-3/25 : ℝ))
    (a37 : -(h 4) < (-3/28 : ℝ))
    (a40 : -(h 1) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a22 + (1/5 : ℝ) * a26 + (2/5 : ℝ) * a37 + (1/5 : ℝ) * a40 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8123 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a25 : h 1 ≤ (2/13 : ℝ))
    (a26 : -(h 2) < (-3/25 : ℝ))
    (a29 : -(h 1) < (-1/7 : ℝ))
    (a31 : h 0 ≤ (3/19 : ℝ))
    (a36 : h 2 ≤ (1/8 : ℝ))
    (a37 : -(h 4) < (-3/28 : ℝ))
    (a39 : -(h 0) < (-5/33 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_8128 h delta _ctx _hno a16 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_8129 h delta _ctx _hno a16 a25 a26 a29 a31 a36 a37 f1
  by_cases p2 : h 1 ≤ (8/55 : ℝ)
  swap
  · have f2 : -(h 1) < (-8/55 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_8130 h delta _ctx _hno a16 a25 a26 a36 a37 a39 p1 f2
  by_cases p3 : h 2 ≤ (1/7 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_8131 h delta _ctx _hno a36 f3
  by_cases p4 : h 3 ≤ (6/55 : ℝ)
  swap
  · have f4 : -(h 3) < (-6/55 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_8132 h delta _ctx _hno a16 a26 a29 a36 a37 a39 p1 p2 f4
  by_cases p5 : h 4 ≤ (5/46 : ℝ)
  swap
  · have f5 : -(h 4) < (-5/46 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_8133 h delta _ctx _hno a16 a26 a29 a36 a39 p4 f5
  apply _hno 82
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (8/55 : ℝ)) ∧ (h 2 ≤ (1/7 : ℝ)) ∧ (h 3 ≤ (6/55 : ℝ)) ∧ (h 4 ≤ (5/46 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_8122 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a38 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a38
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8121 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a29 : -(h 1) < (-1/7 : ℝ))
    (a36 : -(h 2) < (-1/8 : ℝ))
    (a52 : -(h 0) < (-8/53 : ℝ))
    (a57 : -(h 3) < (-6/55 : ℝ))
    (a63 : -(h 4) < (-5/46 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a29 + (1/5 : ℝ) * a36 + (1/5 : ℝ) * a52 + (1/5 : ℝ) * a57 + (1/5 : ℝ) * a63 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8120 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a29 : -(h 1) < (-1/7 : ℝ))
    (a36 : -(h 2) < (-1/8 : ℝ))
    (a50 : -(h 4) < (-2/19 : ℝ))
    (a52 : -(h 0) < (-8/53 : ℝ))
    (a62 : -(h 3) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a29 + (1/5 : ℝ) * a36 + (1/5 : ℝ) * a50 + (1/5 : ℝ) * a52 + (1/5 : ℝ) * a62 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8119 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a29 : -(h 1) < (-1/7 : ℝ))
    (a50 : -(h 4) < (-2/19 : ℝ))
    (a52 : -(h 0) < (-8/53 : ℝ))
    (a57 : -(h 3) < (-6/55 : ℝ))
    (a61 : -(h 2) < (-6/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a29 + (1/5 : ℝ) * a50 + (1/5 : ℝ) * a52 + (1/5 : ℝ) * a57 + (1/5 : ℝ) * a61 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8118 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a55 : h 1 ≤ (8/55 : ℝ))
    (a60 : -(h 1) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a55 + (1 : ℝ) * a60
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8117 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a38 : h 0 ≤ (2/13 : ℝ))
    (a59 : -(h 0) < (-4/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a38 + (1 : ℝ) * a59
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8116 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a58 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a58
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8115 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a29 : -(h 1) < (-1/7 : ℝ))
    (a36 : -(h 2) < (-1/8 : ℝ))
    (a52 : -(h 0) < (-8/53 : ℝ))
    (a58 : -(h 4) < (-5/46 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a29 + (1/5 : ℝ) * a36 + (1/5 : ℝ) * a52 + (2/5 : ℝ) * a58 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8114 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a29 : -(h 1) < (-1/7 : ℝ))
    (a36 : -(h 2) < (-1/8 : ℝ))
    (a38 : h 0 ≤ (2/13 : ℝ))
    (a50 : -(h 4) < (-2/19 : ℝ))
    (a52 : -(h 0) < (-8/53 : ℝ))
    (a55 : h 1 ≤ (8/55 : ℝ))
    (a57 : -(h 3) < (-6/55 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_8116 h delta _ctx _hno a16 f0
  by_cases p1 : h 0 ≤ (4/25 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/25 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_8117 h delta _ctx _hno a38 f1
  by_cases p2 : h 1 ≤ (2/13 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_8118 h delta _ctx _hno a55 f2
  by_cases p3 : h 2 ≤ (6/47 : ℝ)
  swap
  · have f3 : -(h 2) < (-6/47 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_8119 h delta _ctx _hno a29 a50 a52 a57 f3
  by_cases p4 : h 3 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_8120 h delta _ctx _hno a29 a36 a50 a52 f4
  by_cases p5 : h 4 ≤ (5/46 : ℝ)
  swap
  · have f5 : -(h 4) < (-5/46 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_8121 h delta _ctx _hno a29 a36 a52 a57 f5
  apply _hno 157
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (6/47 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ)) ∧ (h 4 ≤ (5/46 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_8113 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a49 : h 2 ≤ (5/38 : ℝ))
    (a56 : -(h 2) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a49 + (1 : ℝ) * a56
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8112 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a36 : -(h 2) < (-1/8 : ℝ))
    (a45 : -(h 3) < (-3/28 : ℝ))
    (a50 : -(h 4) < (-2/19 : ℝ))
    (a52 : -(h 0) < (-8/53 : ℝ))
    (a55 : -(h 1) < (-8/55 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a36 + (1/5 : ℝ) * a45 + (1/5 : ℝ) * a50 + (1/5 : ℝ) * a52 + (1/5 : ℝ) * a55 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8111 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a29 : -(h 1) < (-1/7 : ℝ))
    (a36 : -(h 2) < (-1/8 : ℝ))
    (a45 : -(h 3) < (-3/28 : ℝ))
    (a50 : -(h 4) < (-2/19 : ℝ))
    (a54 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a29 + (1/5 : ℝ) * a36 + (1/5 : ℝ) * a45 + (1/5 : ℝ) * a50 + (1/5 : ℝ) * a54 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8110 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a53 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a53
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8109 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a22 : -(h 0) < (-3/20 : ℝ))
    (a29 : -(h 1) < (-1/7 : ℝ))
    (a36 : -(h 2) < (-1/8 : ℝ))
    (a54 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/3 : ℝ) * _ctx.order4 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a22 + (1/6 : ℝ) * a29 + (1/6 : ℝ) * a36 + (1/2 : ℝ) * a54 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8108 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a22 : -(h 0) < (-3/20 : ℝ))
    (a29 : -(h 1) < (-1/7 : ℝ))
    (a36 : -(h 2) < (-1/8 : ℝ))
    (a50 : -(h 4) < (-2/19 : ℝ))
    (a53 : -(h 3) < (-6/53 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a22 + (1/5 : ℝ) * a29 + (1/5 : ℝ) * a36 + (1/5 : ℝ) * a50 + (1/5 : ℝ) * a53 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8107 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a29 : -(h 1) < (-1/7 : ℝ))
    (a36 : -(h 2) < (-1/8 : ℝ))
    (a38 : h 0 ≤ (2/13 : ℝ))
    (a45 : -(h 3) < (-3/28 : ℝ))
    (a49 : h 2 ≤ (5/38 : ℝ))
    (a50 : -(h 4) < (-2/19 : ℝ))
    (a52 : -(h 0) < (-8/53 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_8110 h delta _ctx _hno a16 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_8111 h delta _ctx _hno a29 a36 a45 a50 f1
  by_cases p2 : h 1 ≤ (8/55 : ℝ)
  swap
  · have f2 : -(h 1) < (-8/55 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_8112 h delta _ctx _hno a36 a45 a50 a52 f2
  by_cases p3 : h 2 ≤ (1/7 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_8113 h delta _ctx _hno a49 f3
  by_cases p4 : h 3 ≤ (6/55 : ℝ)
  swap
  · have f4 : -(h 3) < (-6/55 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_8114 h delta _ctx _hno a16 a29 a36 a38 a50 a52 p2 f4
  by_cases p5 : h 4 ≤ (5/46 : ℝ)
  swap
  · have f5 : -(h 4) < (-5/46 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_8115 h delta _ctx _hno a29 a36 a52 f5
  apply _hno 82
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (8/55 : ℝ)) ∧ (h 2 ≤ (1/7 : ℝ)) ∧ (h 3 ≤ (6/55 : ℝ)) ∧ (h 4 ≤ (5/46 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_8106 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a51 : ((-2 : ℝ) * (delta)) < (-1/5 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a51
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8105 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a22 : -(h 0) < (-3/20 : ℝ))
    (a29 : -(h 1) < (-1/7 : ℝ))
    (a36 : -(h 2) < (-1/8 : ℝ))
    (a38 : h 0 ≤ (2/13 : ℝ))
    (a45 : -(h 3) < (-3/28 : ℝ))
    (a49 : h 2 ≤ (5/38 : ℝ))
    (a50 : -(h 4) < (-2/19 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-1/5 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_8106 h delta _ctx _hno a16 f0
  by_cases p1 : h 0 ≤ (8/53 : ℝ)
  swap
  · have f1 : -(h 0) < (-8/53 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_8107 h delta _ctx _hno a16 a29 a36 a38 a45 a49 a50 f1
  by_cases p2 : h 3 ≤ (6/53 : ℝ)
  swap
  · have f2 : -(h 3) < (-6/53 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_8108 h delta _ctx _hno a22 a29 a36 a50 f2
  by_cases p3 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f3 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_8109 h delta _ctx _hno a22 a29 a36 f3
  apply _hno 75
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 0 ≤ (8/53 : ℝ)) ∧ (h 3 ≤ (6/53 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_8104 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a22 : -(h 0) < (-3/20 : ℝ))
    (a29 : -(h 1) < (-1/7 : ℝ))
    (a40 : -(h 4) < (-4/39 : ℝ))
    (a45 : -(h 3) < (-3/28 : ℝ))
    (a49 : -(h 2) < (-5/38 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a22 + (1/5 : ℝ) * a29 + (1/5 : ℝ) * a40 + (1/5 : ℝ) * a45 + (1/5 : ℝ) * a49 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8103 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a36 : -(h 2) < (-1/8 : ℝ))
    (a40 : -(h 4) < (-4/39 : ℝ))
    (a45 : -(h 3) < (-3/28 : ℝ))
    (a48 : -(h 1) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order0 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a36 + (1/5 : ℝ) * a40 + (1/5 : ℝ) * a45 + (2/5 : ℝ) * a48 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8102 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a38 : h 0 ≤ (2/13 : ℝ))
    (a47 : -(h 0) < (-3/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a38 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8101 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a46 : ((-2 : ℝ) * (delta)) < (-1/5 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8100 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a22 : -(h 0) < (-3/20 : ℝ))
    (a29 : -(h 1) < (-1/7 : ℝ))
    (a36 : -(h 2) < (-1/8 : ℝ))
    (a38 : h 0 ≤ (2/13 : ℝ))
    (a40 : -(h 4) < (-4/39 : ℝ))
    (a45 : -(h 3) < (-3/28 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-1/5 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_8101 h delta _ctx _hno a16 f0
  by_cases p1 : h 0 ≤ (3/19 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/19 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_8102 h delta _ctx _hno a38 f1
  by_cases p2 : h 1 ≤ (2/13 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_8103 h delta _ctx _hno a36 a40 a45 f2
  by_cases p3 : h 2 ≤ (5/38 : ℝ)
  swap
  · have f3 : -(h 2) < (-5/38 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_8104 h delta _ctx _hno a22 a29 a40 a45 f3
  by_cases p4 : h 4 ≤ (2/19 : ℝ)
  swap
  · have f4 : -(h 4) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_8105 h delta _ctx _hno a16 a22 a29 a36 a38 a45 p3 f4
  apply _hno 28
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (5/38 : ℝ)) ∧ (h 4 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_8099 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a29 : -(h 1) < (-1/7 : ℝ))
    (a32 : -(h 3) < (-2/19 : ℝ))
    (a44 : -(h 2) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/13 : ℝ) * _ctx.min + (8/13 : ℝ) * _ctx.lower + (1/13 : ℝ) * _ctx.fail2 + (4/13 : ℝ) * a29 + (4/13 : ℝ) * a32 + (4/13 : ℝ) * a44 + (4/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8098 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : h 1 ≤ (2/13 : ℝ))
    (a43 : -(h 1) < (-7/44 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a25 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8097 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a38 : h 0 ≤ (2/13 : ℝ))
    (a42 : -(h 0) < (-4/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a38 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8096 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8095 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a29 : -(h 1) < (-1/7 : ℝ))
    (a36 : -(h 2) < (-1/8 : ℝ))
    (a38 : -(h 0) < (-2/13 : ℝ))
    (a43 : -(h 3) < (-3/28 : ℝ))
    (a48 : -(h 4) < (-2/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a29 + (1/5 : ℝ) * a36 + (1/5 : ℝ) * a38 + (1/5 : ℝ) * a43 + (1/5 : ℝ) * a48 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8094 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a29 : -(h 1) < (-1/7 : ℝ))
    (a38 : -(h 0) < (-2/13 : ℝ))
    (a43 : -(h 3) < (-3/28 : ℝ))
    (a47 : -(h 2) < (-5/38 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.order4 + (1/2 : ℝ) * _ctx.min + (3/4 : ℝ) * _ctx.lower + (1/4 : ℝ) * a29 + (1/4 : ℝ) * a38 + (1/4 : ℝ) * a43 + (1/4 : ℝ) * a47 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8093 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a36 : -(h 2) < (-1/8 : ℝ))
    (a38 : -(h 0) < (-2/13 : ℝ))
    (a43 : -(h 3) < (-3/28 : ℝ))
    (a46 : -(h 1) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.order4 + (1/2 : ℝ) * _ctx.min + (3/4 : ℝ) * _ctx.lower + (1/4 : ℝ) * a36 + (1/4 : ℝ) * a38 + (1/4 : ℝ) * a43 + (1/4 : ℝ) * a46 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8092 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a31 : h 0 ≤ (3/19 : ℝ))
    (a45 : -(h 0) < (-3/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8091 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a44 : ((-2 : ℝ) * (delta)) < (-1/5 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8090 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a29 : -(h 1) < (-1/7 : ℝ))
    (a31 : h 0 ≤ (3/19 : ℝ))
    (a36 : -(h 2) < (-1/8 : ℝ))
    (a38 : -(h 0) < (-2/13 : ℝ))
    (a43 : -(h 3) < (-3/28 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-1/5 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_8091 h delta _ctx _hno a16 f0
  by_cases p1 : h 0 ≤ (3/19 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/19 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_8092 h delta _ctx _hno a31 f1
  by_cases p2 : h 1 ≤ (2/13 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_8093 h delta _ctx _hno a36 a38 a43 f2
  by_cases p3 : h 2 ≤ (5/38 : ℝ)
  swap
  · have f3 : -(h 2) < (-5/38 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_8094 h delta _ctx _hno a29 a38 a43 f3
  by_cases p4 : h 4 ≤ (2/19 : ℝ)
  swap
  · have f4 : -(h 4) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_8095 h delta _ctx _hno a29 a36 a38 a43 f4
  apply _hno 28
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (5/38 : ℝ)) ∧ (h 4 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_8089 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a32 : -(h 3) < (-2/19 : ℝ))
    (a38 : -(h 0) < (-2/13 : ℝ))
    (a42 : -(h 2) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.order1 + (1/4 : ℝ) * _ctx.order4 + (1/2 : ℝ) * _ctx.min + (3/4 : ℝ) * _ctx.lower + (1/4 : ℝ) * a32 + (1/4 : ℝ) * a38 + (1/2 : ℝ) * a42 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8088 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : h 1 ≤ (2/13 : ℝ))
    (a41 : -(h 1) < (-7/44 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a25 + (1 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8087 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a31 : h 0 ≤ (3/19 : ℝ))
    (a40 : -(h 0) < (-4/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8086 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a39 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8085 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a22 : -(h 0) < (-3/20 : ℝ))
    (a25 : h 1 ≤ (2/13 : ℝ))
    (a29 : -(h 1) < (-1/7 : ℝ))
    (a32 : -(h 3) < (-2/19 : ℝ))
    (a36 : -(h 2) < (-1/8 : ℝ))
    (a38 : h 0 ≤ (2/13 : ℝ))
    (a40 : -(h 4) < (-4/39 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_8096 h delta _ctx _hno a16 f0
  by_cases p1 : h 0 ≤ (4/25 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/25 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_8097 h delta _ctx _hno a38 f1
  by_cases p2 : h 1 ≤ (7/44 : ℝ)
  swap
  · have f2 : -(h 1) < (-7/44 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_8098 h delta _ctx _hno a25 f2
  by_cases p3 : h 2 ≤ (1/7 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_8099 h delta _ctx _hno a29 a32 f3
  by_cases p4 : h 3 ≤ (3/28 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_8100 h delta _ctx _hno a16 a22 a29 a36 a38 a40 f4
  apply _hno 88
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (7/44 : ℝ)) ∧ (h 2 ≤ (1/7 : ℝ)) ∧ (h 3 ≤ (3/28 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_8084 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : h 3 ≤ (3/25 : ℝ))
    (a39 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a19 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8083 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a25 : h 1 ≤ (2/13 : ℝ))
    (a29 : -(h 1) < (-1/7 : ℝ))
    (a31 : h 0 ≤ (3/19 : ℝ))
    (a32 : -(h 3) < (-2/19 : ℝ))
    (a36 : -(h 2) < (-1/8 : ℝ))
    (a38 : -(h 0) < (-2/13 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_8086 h delta _ctx _hno a16 f0
  by_cases p1 : h 0 ≤ (4/25 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/25 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_8087 h delta _ctx _hno a31 f1
  by_cases p2 : h 1 ≤ (7/44 : ℝ)
  swap
  · have f2 : -(h 1) < (-7/44 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_8088 h delta _ctx _hno a25 f2
  by_cases p3 : h 2 ≤ (1/7 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_8089 h delta _ctx _hno a32 a38 f3
  by_cases p4 : h 3 ≤ (3/28 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_8090 h delta _ctx _hno a16 a29 a31 a36 a38 f4
  apply _hno 88
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (7/44 : ℝ)) ∧ (h 2 ≤ (1/7 : ℝ)) ∧ (h 3 ≤ (3/28 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_8082 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a37 : ((-2 : ℝ) * (delta)) < (-1/5 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a37
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8081 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a19 : h 3 ≤ (3/25 : ℝ))
    (a22 : -(h 0) < (-3/20 : ℝ))
    (a25 : h 1 ≤ (2/13 : ℝ))
    (a26 : -(h 2) < (-3/25 : ℝ))
    (a29 : -(h 1) < (-1/7 : ℝ))
    (a31 : h 0 ≤ (3/19 : ℝ))
    (a36 : h 2 ≤ (1/8 : ℝ))
    (a37 : -(h 4) < (-3/28 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_8122 h delta _ctx _hno a16 f0
  by_cases p1 : h 0 ≤ (5/33 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/33 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_8123 h delta _ctx _hno a16 a25 a26 a29 a31 a36 a37 f1
  by_cases p2 : h 1 ≤ (3/20 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_8124 h delta _ctx _hno a22 a26 a37 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_8125 h delta _ctx _hno a36 f3
  by_cases p4 : h 3 ≤ (7/57 : ℝ)
  swap
  · have f4 : -(h 3) < (-7/57 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_8126 h delta _ctx _hno a19 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_8127 h delta _ctx _hno a22 a26 a29 f5
  apply _hno 119
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (5/33 : ℝ)) ∧ (h 1 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (7/57 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_8080 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a19 : h 3 ≤ (3/25 : ℝ))
    (a22 : -(h 0) < (-3/20 : ℝ))
    (a25 : h 1 ≤ (2/13 : ℝ))
    (a29 : -(h 1) < (-1/7 : ℝ))
    (a31 : h 0 ≤ (3/19 : ℝ))
    (a32 : -(h 3) < (-2/19 : ℝ))
    (a36 : -(h 2) < (-1/8 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-1/5 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_8082 h delta _ctx _hno a16 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_8083 h delta _ctx _hno a16 a25 a29 a31 a32 a36 f1
  by_cases p2 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_8084 h delta _ctx _hno a19 f2
  by_cases p3 : h 4 ≤ (4/39 : ℝ)
  swap
  · have f3 : -(h 4) < (-4/39 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_8085 h delta _ctx _hno a16 a22 a25 a29 a32 a36 p1 f3
  apply _hno 33
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (4/39 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_8079 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : h 1 ≤ (2/13 : ℝ))
    (a35 : -(h 1) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a25 + (1 : ℝ) * a35
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8078 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a31 : h 0 ≤ (3/19 : ℝ))
    (a34 : -(h 0) < (-4/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a34
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8077 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a33 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a33
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8076 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a45 : h 4 ≤ (4/39 : ℝ))
    (a52 : -(h 4) < (-5/46 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a45 + (1 : ℝ) * a52
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8075 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a29 : -(h 1) < (-1/7 : ℝ))
    (a31 : -(h 0) < (-3/19 : ℝ))
    (a40 : -(h 2) < (-1/8 : ℝ))
    (a51 : -(h 3) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.order4 + (1/2 : ℝ) * _ctx.min + (3/4 : ℝ) * _ctx.lower + (1/4 : ℝ) * a29 + (1/4 : ℝ) * a31 + (1/4 : ℝ) * a40 + (1/4 : ℝ) * a51 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

end RealPinwheel.WeakSevenBandData
