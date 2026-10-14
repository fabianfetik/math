import Pinwheel.WeakSevenBandData.CoverChunks.New161

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem new_node_154 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a18 : -(h 1) < (-1/8 : ℝ))
    (a20 : -(h 0) < (-5/27 : ℝ))
    (a33 : ((-2 : ℝ) * (delta)) < (-11/54 : ℝ))
    (a37 : -(h 2) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (2/5 : ℝ) * _ctx.order4 + (3/5 : ℝ) * _ctx.min + (1/5 : ℝ) * a18 + (1/5 : ℝ) * a20 + (2/5 : ℝ) * a33 + (1/5 : ℝ) * a37 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_153 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a20 : -(h 0) < (-5/27 : ℝ))
    (a32 : -(h 2) < (-3/26 : ℝ))
    (a33 : ((-2 : ℝ) * (delta)) < (-11/54 : ℝ))
    (a36 : -(h 1) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (2/5 : ℝ) * _ctx.order4 + (3/5 : ℝ) * _ctx.min + (1/5 : ℝ) * a20 + (1/5 : ℝ) * a32 + (2/5 : ℝ) * a33 + (1/5 : ℝ) * a36 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_152 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : h 0 ≤ (3/16 : ℝ))
    (a35 : -(h 0) < (-8/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a35
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_151 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a25 + (1 : ℝ) * a34
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_150 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a18 : -(h 1) < (-1/8 : ℝ))
    (a20 : -(h 0) < (-5/27 : ℝ))
    (a32 : -(h 2) < (-3/26 : ℝ))
    (a36 : -(h 3) < (-2/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/11 : ℝ) * _ctx.order4 + (4/11 : ℝ) * _ctx.min + (3/11 : ℝ) * a13 + (2/11 : ℝ) * a18 + (2/11 : ℝ) * a20 + (2/11 : ℝ) * a32 + (2/11 : ℝ) * a36 + (2/11 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_149 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a20 : -(h 0) < (-5/27 : ℝ))
    (a32 : -(h 2) < (-3/26 : ℝ))
    (a35 : -(h 1) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (2/5 : ℝ) * _ctx.order4 + (3/5 : ℝ) * _ctx.min + (2/5 : ℝ) * a13 + (1/5 : ℝ) * a20 + (1/5 : ℝ) * a32 + (1/5 : ℝ) * a35 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_148 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : h 0 ≤ (3/16 : ℝ))
    (a34 : -(h 0) < (-1/5 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a34
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_147 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : h 0 ≤ (3/16 : ℝ))
    (a18 : -(h 1) < (-1/8 : ℝ))
    (a20 : -(h 0) < (-5/27 : ℝ))
    (a25 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ))
    (a32 : -(h 2) < (-3/26 : ℝ))
    (a33 : ((-2 : ℝ) * (delta)) < (-11/54 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_151 h delta _ctx _hno a25 f0
  by_cases p1 : h 0 ≤ (8/41 : ℝ)
  swap
  · have f1 : -(h 0) < (-8/41 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_152 h delta _ctx _hno a17 f1
  by_cases p2 : h 1 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_153 h delta _ctx _hno a20 a32 a33 f2
  by_cases p3 : h 2 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_154 h delta _ctx _hno a18 a20 a33 f3
  by_cases p4 : h 3 ≤ (5/46 : ℝ)
  swap
  · have f4 : -(h 3) < (-5/46 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_155 h delta _ctx _hno a18 a20 a32 a33 f4
  by_cases p5 : h 4 ≤ (3/28 : ℝ)
  swap
  · have f5 : -(h 4) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_156 h delta _ctx _hno a18 a20 a32 a33 f5
  apply _hno 53
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (8/41 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 3 ≤ (5/46 : ℝ)) ∧ (h 4 ≤ (3/28 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_146 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a18 : -(h 1) < (-1/8 : ℝ))
    (a20 : -(h 0) < (-5/27 : ℝ))
    (a28 : -(h 2) < (-6/53 : ℝ))
    (a34 : -(h 4) < (-3/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a18 + (1/6 : ℝ) * a20 + (1/6 : ℝ) * a28 + (1/3 : ℝ) * a34 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_145 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a18 : -(h 1) < (-1/8 : ℝ))
    (a20 : -(h 0) < (-5/27 : ℝ))
    (a28 : -(h 2) < (-6/53 : ℝ))
    (a33 : -(h 3) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/11 : ℝ) * _ctx.order4 + (4/11 : ℝ) * _ctx.min + (3/11 : ℝ) * a13 + (2/11 : ℝ) * a18 + (2/11 : ℝ) * a20 + (2/11 : ℝ) * a28 + (2/11 : ℝ) * a33 + (2/11 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_144 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a17 : h 0 ≤ (3/16 : ℝ))
    (a18 : -(h 1) < (-1/8 : ℝ))
    (a20 : -(h 0) < (-5/27 : ℝ))
    (a25 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ))
    (a32 : -(h 2) < (-3/26 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (11/54 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-11/54 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_147 h delta _ctx _hno a17 a18 a20 a25 a32 f0
  by_cases p1 : h 0 ≤ (1/5 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/5 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_148 h delta _ctx _hno a17 f1
  by_cases p2 : h 1 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_149 h delta _ctx _hno a13 a20 a32 f2
  by_cases p3 : h 3 ≤ (2/19 : ℝ)
  swap
  · have f3 : -(h 3) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_150 h delta _ctx _hno a13 a18 a20 a32 f3
  apply _hno 141
  change (((2 : ℝ) * (delta)) ≤ (11/54 : ℝ)) ∧ (h 0 ≤ (1/5 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_143 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : h 1 ≤ (7/53 : ℝ))
    (a31 : -(h 1) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a31
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_142 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : h 0 ≤ (3/16 : ℝ))
    (a30 : -(h 0) < (-5/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a30
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_141 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ))
    (a29 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a25 + (1 : ℝ) * a29
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_140 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a18 : -(h 1) < (-1/8 : ℝ))
    (a20 : -(h 0) < (-5/27 : ℝ))
    (a24 : -(h 2) < (-1/9 : ℝ))
    (a25 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ))
    (a37 : -(h 4) < (-3/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a18 + (1/6 : ℝ) * a20 + (1/6 : ℝ) * a24 + (1/6 : ℝ) * a25 + (1/3 : ℝ) * a37 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_139 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a18 : -(h 1) < (-1/8 : ℝ))
    (a20 : -(h 0) < (-5/27 : ℝ))
    (a24 : -(h 2) < (-1/9 : ℝ))
    (a25 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ))
    (a31 : -(h 4) < (-3/29 : ℝ))
    (a36 : -(h 3) < (-5/46 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a18 + (1/6 : ℝ) * a20 + (1/6 : ℝ) * a24 + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a31 + (1/6 : ℝ) * a36 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_138 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a29 : h 2 ≤ (3/26 : ℝ))
    (a35 : -(h 2) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a35
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_137 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a20 : -(h 0) < (-5/27 : ℝ))
    (a24 : -(h 2) < (-1/9 : ℝ))
    (a25 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ))
    (a31 : -(h 4) < (-3/29 : ℝ))
    (a34 : -(h 1) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a20 + (1/6 : ℝ) * a24 + (1/6 : ℝ) * a25 + (1/3 : ℝ) * a31 + (1/6 : ℝ) * a34 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_136 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : h 0 ≤ (3/16 : ℝ))
    (a33 : -(h 0) < (-8/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a33
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_135 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : ((2 : ℝ) * (delta)) ≤ (7/34 : ℝ))
    (a32 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a26 + (1 : ℝ) * a32
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_134 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a18 : -(h 1) < (-1/8 : ℝ))
    (a20 : -(h 0) < (-5/27 : ℝ))
    (a24 : -(h 2) < (-1/9 : ℝ))
    (a26 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a32 : -(h 4) < (-3/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a18 + (1/6 : ℝ) * a20 + (1/6 : ℝ) * a24 + (1/6 : ℝ) * a26 + (1/3 : ℝ) * a32 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_133 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a18 : -(h 1) < (-1/8 : ℝ))
    (a20 : -(h 0) < (-5/27 : ℝ))
    (a24 : -(h 2) < (-1/9 : ℝ))
    (a26 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a31 : -(h 3) < (-5/46 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/11 : ℝ) * _ctx.order4 + (4/11 : ℝ) * _ctx.min + (2/11 : ℝ) * a18 + (2/11 : ℝ) * a20 + (2/11 : ℝ) * a24 + (3/11 : ℝ) * a26 + (2/11 : ℝ) * a31 + (2/11 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_132 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a18 : -(h 1) < (-1/8 : ℝ))
    (a20 : -(h 0) < (-5/27 : ℝ))
    (a26 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a30 : -(h 2) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (2/5 : ℝ) * _ctx.order4 + (3/5 : ℝ) * _ctx.min + (1/5 : ℝ) * a18 + (1/5 : ℝ) * a20 + (2/5 : ℝ) * a26 + (1/5 : ℝ) * a30 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_131 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a20 : -(h 0) < (-5/27 : ℝ))
    (a24 : -(h 2) < (-1/9 : ℝ))
    (a26 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a29 : -(h 1) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (2/5 : ℝ) * _ctx.order4 + (3/5 : ℝ) * _ctx.min + (1/5 : ℝ) * a20 + (1/5 : ℝ) * a24 + (2/5 : ℝ) * a26 + (1/5 : ℝ) * a29 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_130 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : h 0 ≤ (3/16 : ℝ))
    (a28 : -(h 0) < (-8/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a28
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_129 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a27
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_128 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : h 0 ≤ (3/16 : ℝ))
    (a18 : -(h 1) < (-1/8 : ℝ))
    (a20 : -(h 0) < (-5/27 : ℝ))
    (a24 : -(h 2) < (-1/9 : ℝ))
    (a25 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ))
    (a26 : ((2 : ℝ) * (delta)) ≤ (7/34 : ℝ))
    (a29 : h 2 ≤ (3/26 : ℝ))
    (a31 : -(h 4) < (-3/29 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_135 h delta _ctx _hno a26 f0
  by_cases p1 : h 0 ≤ (8/41 : ℝ)
  swap
  · have f1 : -(h 0) < (-8/41 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_136 h delta _ctx _hno a17 f1
  by_cases p2 : h 1 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_137 h delta _ctx _hno a20 a24 a25 a31 f2
  by_cases p3 : h 2 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_138 h delta _ctx _hno a29 f3
  by_cases p4 : h 3 ≤ (5/46 : ℝ)
  swap
  · have f4 : -(h 3) < (-5/46 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_139 h delta _ctx _hno a18 a20 a24 a25 a31 f4
  by_cases p5 : h 4 ≤ (3/28 : ℝ)
  swap
  · have f5 : -(h 4) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_140 h delta _ctx _hno a18 a20 a24 a25 f5
  apply _hno 53
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (8/41 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 3 ≤ (5/46 : ℝ)) ∧ (h 4 ≤ (3/28 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_127 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a18 : -(h 1) < (-1/8 : ℝ))
    (a20 : -(h 0) < (-5/27 : ℝ))
    (a24 : -(h 2) < (-1/9 : ℝ))
    (a25 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ))
    (a30 : -(h 3) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/11 : ℝ) * _ctx.order4 + (4/11 : ℝ) * _ctx.min + (2/11 : ℝ) * a18 + (2/11 : ℝ) * a20 + (2/11 : ℝ) * a24 + (3/11 : ℝ) * a25 + (2/11 : ℝ) * a30 + (2/11 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_126 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a18 : -(h 1) < (-1/8 : ℝ))
    (a20 : -(h 0) < (-5/27 : ℝ))
    (a25 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ))
    (a29 : -(h 2) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (2/5 : ℝ) * _ctx.order4 + (3/5 : ℝ) * _ctx.min + (1/5 : ℝ) * a18 + (1/5 : ℝ) * a20 + (2/5 : ℝ) * a25 + (1/5 : ℝ) * a29 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_125 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : h 1 ≤ (1/7 : ℝ))
    (a28 : -(h 1) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a23 + (1 : ℝ) * a28
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_124 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : h 0 ≤ (3/16 : ℝ))
    (a27 : -(h 0) < (-5/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a27
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_123 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : h 0 ≤ (3/16 : ℝ))
    (a18 : -(h 1) < (-1/8 : ℝ))
    (a20 : -(h 0) < (-5/27 : ℝ))
    (a24 : -(h 2) < (-1/9 : ℝ))
    (a26 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_129 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (8/41 : ℝ)
  swap
  · have f1 : -(h 0) < (-8/41 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_130 h delta _ctx _hno a17 f1
  by_cases p2 : h 1 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_131 h delta _ctx _hno a20 a24 a26 f2
  by_cases p3 : h 2 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_132 h delta _ctx _hno a18 a20 a26 f3
  by_cases p4 : h 3 ≤ (5/46 : ℝ)
  swap
  · have f4 : -(h 3) < (-5/46 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_133 h delta _ctx _hno a18 a20 a24 a26 f4
  by_cases p5 : h 4 ≤ (3/28 : ℝ)
  swap
  · have f5 : -(h 4) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_134 h delta _ctx _hno a18 a20 a24 a26 f5
  apply _hno 53
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (8/41 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 3 ≤ (5/46 : ℝ)) ∧ (h 4 ≤ (3/28 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_122 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a18 : -(h 1) < (-1/8 : ℝ))
    (a20 : -(h 0) < (-5/27 : ℝ))
    (a24 : -(h 2) < (-1/9 : ℝ))
    (a29 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a18 + (1/6 : ℝ) * a20 + (1/6 : ℝ) * a24 + (1/3 : ℝ) * a29 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_121 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a17 : h 0 ≤ (3/16 : ℝ))
    (a18 : -(h 1) < (-1/8 : ℝ))
    (a20 : -(h 0) < (-5/27 : ℝ))
    (a25 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ))
    (a27 : h 1 ≤ (7/53 : ℝ))
    (a28 : -(h 2) < (-6/53 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_141 h delta _ctx _hno a25 f0
  by_cases p1 : h 0 ≤ (5/26 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/26 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_142 h delta _ctx _hno a17 f1
  by_cases p2 : h 1 ≤ (2/13 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_143 h delta _ctx _hno a27 f2
  by_cases p3 : h 2 ≤ (3/26 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_144 h delta _ctx _hno a13 a17 a18 a20 a25 f3
  by_cases p4 : h 3 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_145 h delta _ctx _hno a13 a18 a20 a28 f4
  by_cases p5 : h 4 ≤ (3/29 : ℝ)
  swap
  · have f5 : -(h 4) < (-3/29 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_146 h delta _ctx _hno a13 a18 a20 a28 f5
  apply _hno 166
  change (((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)) ∧ (h 0 ≤ (5/26 : ℝ)) ∧ (h 1 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (3/26 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ)) ∧ (h 4 ≤ (3/29 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_120 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a20 : -(h 0) < (-5/27 : ℝ))
    (a24 : -(h 2) < (-1/9 : ℝ))
    (a27 : -(h 1) < (-7/53 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (2/5 : ℝ) * _ctx.order4 + (3/5 : ℝ) * _ctx.min + (2/5 : ℝ) * a13 + (1/5 : ℝ) * a20 + (1/5 : ℝ) * a24 + (1/5 : ℝ) * a27 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_119 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : h 0 ≤ (3/16 : ℝ))
    (a26 : -(h 0) < (-1/5 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a26
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_118 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : h 0 ≤ (3/16 : ℝ))
    (a18 : -(h 1) < (-1/8 : ℝ))
    (a20 : -(h 0) < (-5/27 : ℝ))
    (a23 : h 1 ≤ (1/7 : ℝ))
    (a24 : -(h 2) < (-1/9 : ℝ))
    (a25 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_123 h delta _ctx _hno a17 a18 a20 a24 f0
  by_cases p1 : h 0 ≤ (5/26 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/26 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_124 h delta _ctx _hno a17 f1
  by_cases p2 : h 1 ≤ (2/13 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_125 h delta _ctx _hno a23 f2
  by_cases p3 : h 2 ≤ (3/26 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_126 h delta _ctx _hno a18 a20 a25 f3
  by_cases p4 : h 3 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_127 h delta _ctx _hno a18 a20 a24 a25 f4
  by_cases p5 : h 4 ≤ (3/29 : ℝ)
  swap
  · have f5 : -(h 4) < (-3/29 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_128 h delta _ctx _hno a17 a18 a20 a24 a25 p0 p3 f5
  apply _hno 166
  change (((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)) ∧ (h 0 ≤ (5/26 : ℝ)) ∧ (h 1 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (3/26 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ)) ∧ (h 4 ≤ (3/29 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_117 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a17 : h 0 ≤ (3/16 : ℝ))
    (a18 : -(h 1) < (-1/8 : ℝ))
    (a20 : -(h 0) < (-5/27 : ℝ))
    (a23 : h 1 ≤ (1/7 : ℝ))
    (a24 : -(h 2) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_118 h delta _ctx _hno a17 a18 a20 a23 a24 f0
  by_cases p1 : h 0 ≤ (1/5 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/5 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_119 h delta _ctx _hno a17 f1
  by_cases p2 : h 1 ≤ (7/53 : ℝ)
  swap
  · have f2 : -(h 1) < (-7/53 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_120 h delta _ctx _hno a13 a20 a24 f2
  by_cases p3 : h 2 ≤ (6/53 : ℝ)
  swap
  · have f3 : -(h 2) < (-6/53 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_121 h delta _ctx _hno a13 a17 a18 a20 p0 p2 f3
  by_cases p4 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_122 h delta _ctx _hno a13 a18 a20 a24 f4
  apply _hno 74
  change (((2 : ℝ) * (delta)) ≤ (8/39 : ℝ)) ∧ (h 0 ≤ (1/5 : ℝ)) ∧ (h 1 ≤ (7/53 : ℝ)) ∧ (h 2 ≤ (6/53 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_116 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a20 : -(h 0) < (-5/27 : ℝ))
    (a23 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.order3 + (12/23 : ℝ) * _ctx.order4 + (18/23 : ℝ) * _ctx.min + (1/23 : ℝ) * _ctx.fail1 + (12/23 : ℝ) * a13 + (4/23 : ℝ) * a20 + (6/23 : ℝ) * a23 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_115 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : h 0 ≤ (3/16 : ℝ))
    (a22 : -(h 0) < (-3/16 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a22
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_114 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a21 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a21
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_113 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a15 : -(h 0) < (-1/6 : ℝ))
    (a18 : -(h 1) < (-1/8 : ℝ))
    (a20 : h 0 ≤ (5/27 : ℝ))
    (a21 : h 1 ≤ (4/27 : ℝ))
    (a22 : -(h 2) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_167 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (8/45 : ℝ)
  swap
  · have f1 : -(h 0) < (-8/45 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_168 h delta _ctx _hno a13 a18 a20 a21 a22 f1
  by_cases p2 : h 1 ≤ (5/38 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/38 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_169 h delta _ctx _hno a13 a15 a21 a22 p1 f2
  by_cases p3 : h 2 ≤ (3/23 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_170 h delta _ctx _hno a13 a15 f3
  by_cases p4 : h 3 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_171 h delta _ctx _hno a13 a15 a18 a22 p1 p2 f4
  apply _hno 51
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (8/45 : ℝ)) ∧ (h 1 ≤ (5/38 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_112 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a15 : -(h 0) < (-1/6 : ℝ))
    (a21 : -(h 1) < (-4/27 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_157 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (3/17 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/17 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_158 h delta _ctx _hno a13 a21 f1
  by_cases p2 : h 1 ≤ (8/53 : ℝ)
  swap
  · have f2 : -(h 1) < (-8/53 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_159 h delta _ctx _hno a13 a15 f2
  by_cases p3 : h 2 ≤ (1/9 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_160 h delta _ctx _hno a13 a15 a21 p1 p2
  apply _hno 115
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (3/17 : ℝ)) ∧ (h 1 ≤ (8/53 : ℝ)) ∧ (h 2 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_111 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a17 : h 0 ≤ (3/16 : ℝ))
    (a18 : -(h 1) < (-1/8 : ℝ))
    (a20 : -(h 0) < (-5/27 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_114 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (3/16 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/16 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_115 h delta _ctx _hno a17 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_116 h delta _ctx _hno a13 a20 f2
  by_cases p3 : h 2 ≤ (1/9 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_117 h delta _ctx _hno a13 a17 a18 a20 p2 f3
  apply _hno 100
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/16 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_110 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a19
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_109 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a17 : -(h 0) < (-3/16 : ℝ))
    (a20 : -(h 4) < (-5/48 : ℝ))
    (a27 : -(h 2) < (-1/9 : ℝ))
    (a33 : -(h 1) < (-7/57 : ℝ))
    (a38 : -(h 3) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a17 + (1/6 : ℝ) * a20 + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a38 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_108 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a17 : -(h 0) < (-3/16 : ℝ))
    (a20 : -(h 4) < (-5/48 : ℝ))
    (a33 : -(h 1) < (-7/57 : ℝ))
    (a37 : -(h 2) < (-9/80 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a17 + (1/3 : ℝ) * a20 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_107 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a17 : -(h 0) < (-3/16 : ℝ))
    (a20 : -(h 4) < (-5/48 : ℝ))
    (a27 : -(h 2) < (-1/9 : ℝ))
    (a36 : -(h 1) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a17 + (1/3 : ℝ) * a20 + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a36 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_106 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a29 : h 0 ≤ (4/21 : ℝ))
    (a35 : -(h 0) < (-1/5 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a35
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_105 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a34
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_104 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a17 : -(h 0) < (-3/16 : ℝ))
    (a27 : -(h 2) < (-1/9 : ℝ))
    (a30 : -(h 1) < (-2/17 : ℝ))
    (a37 : -(h 5) < (-5/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order3 + (4/13 : ℝ) * _ctx.order4 + (1/13 : ℝ) * a13 + (2/13 : ℝ) * a17 + (2/13 : ℝ) * a27 + (2/13 : ℝ) * a30 + (6/13 : ℝ) * a37 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_103 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a17 : -(h 0) < (-3/16 : ℝ))
    (a27 : -(h 2) < (-1/9 : ℝ))
    (a30 : -(h 1) < (-2/17 : ℝ))
    (a36 : -(h 4) < (-3/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a17 + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a30 + (1/3 : ℝ) * a36 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_102 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 0) < (-3/16 : ℝ))
    (a35 : -(h 3) < (-4/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.order1 + (1/2 : ℝ) * _ctx.order2 + (1/4 : ℝ) * _ctx.order4 + (1/2 : ℝ) * _ctx.min + (3/4 : ℝ) * _ctx.lower + (1/4 : ℝ) * a17 + (3/4 : ℝ) * a35 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_101 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a17 : -(h 0) < (-3/16 : ℝ))
    (a20 : -(h 4) < (-5/48 : ℝ))
    (a34 : -(h 2) < (-5/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order1 + (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a17 + (1/3 : ℝ) * a20 + (1/3 : ℝ) * a34 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_100 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a17 : -(h 0) < (-3/16 : ℝ))
    (a20 : -(h 4) < (-5/48 : ℝ))
    (a27 : -(h 2) < (-1/9 : ℝ))
    (a29 : h 0 ≤ (4/21 : ℝ))
    (a33 : -(h 1) < (-7/57 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_105 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (1/5 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/5 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_106 h delta _ctx _hno a29 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_107 h delta _ctx _hno a13 a17 a20 a27 f2
  by_cases p3 : h 2 ≤ (9/80 : ℝ)
  swap
  · have f3 : -(h 2) < (-9/80 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_108 h delta _ctx _hno a13 a17 a20 a33 f3
  by_cases p4 : h 3 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_109 h delta _ctx _hno a13 a17 a20 a27 a33 f4
  apply _hno 135
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (1/5 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 2 ≤ (9/80 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_99 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a29 : h 0 ≤ (4/21 : ℝ))
    (a32 : -(h 0) < (-1/5 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a32
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_98 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a31 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a31
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_97 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a23 : -(h 1) < (-3/26 : ℝ))
    (a27 : -(h 2) < (-1/9 : ℝ))
    (a29 : -(h 0) < (-4/21 : ℝ))
    (a36 : -(h 5) < (-5/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order3 + (4/13 : ℝ) * _ctx.order4 + (1/13 : ℝ) * a13 + (2/13 : ℝ) * a23 + (2/13 : ℝ) * a27 + (2/13 : ℝ) * a29 + (6/13 : ℝ) * a36 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_96 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a23 : -(h 1) < (-3/26 : ℝ))
    (a27 : -(h 2) < (-1/9 : ℝ))
    (a29 : -(h 0) < (-4/21 : ℝ))
    (a35 : -(h 4) < (-3/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a23 + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a29 + (1/3 : ℝ) * a35 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_95 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a29 : -(h 0) < (-4/21 : ℝ))
    (a34 : -(h 3) < (-4/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.order1 + (1/2 : ℝ) * _ctx.order2 + (1/4 : ℝ) * _ctx.order4 + (1/2 : ℝ) * _ctx.min + (3/4 : ℝ) * _ctx.lower + (1/4 : ℝ) * a29 + (3/4 : ℝ) * a34 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_94 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a20 : -(h 4) < (-5/48 : ℝ))
    (a29 : -(h 0) < (-4/21 : ℝ))
    (a33 : -(h 2) < (-5/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order1 + (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/3 : ℝ) * a20 + (1/6 : ℝ) * a29 + (1/3 : ℝ) * a33 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_93 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a20 : -(h 4) < (-5/48 : ℝ))
    (a27 : -(h 2) < (-1/9 : ℝ))
    (a29 : -(h 0) < (-4/21 : ℝ))
    (a32 : -(h 1) < (-7/57 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/3 : ℝ) * a20 + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a29 + (1/6 : ℝ) * a32 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_92 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a22 : h 0 ≤ (5/26 : ℝ))
    (a31 : -(h 0) < (-1/5 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a22 + (1 : ℝ) * a31
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_91 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a30 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a30
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_90 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a17 : -(h 0) < (-3/16 : ℝ))
    (a20 : -(h 4) < (-5/48 : ℝ))
    (a27 : -(h 2) < (-1/9 : ℝ))
    (a29 : h 0 ≤ (4/21 : ℝ))
    (a30 : -(h 1) < (-2/17 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_98 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (1/5 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/5 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_99 h delta _ctx _hno a29 f1
  by_cases p2 : h 1 ≤ (7/57 : ℝ)
  swap
  · have f2 : -(h 1) < (-7/57 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_100 h delta _ctx _hno a13 a17 a20 a27 a29 f2
  by_cases p3 : h 2 ≤ (5/41 : ℝ)
  swap
  · have f3 : -(h 2) < (-5/41 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_101 h delta _ctx _hno a13 a17 a20 f3
  by_cases p4 : h 3 ≤ (4/33 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_102 h delta _ctx _hno a17 f4
  by_cases p5 : h 4 ≤ (3/28 : ℝ)
  swap
  · have f5 : -(h 4) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_103 h delta _ctx _hno a13 a17 a27 a30 f5
  by_cases p6 : h 5 ≤ (5/47 : ℝ)
  swap
  · have f6 : -(h 5) < (-5/47 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact new_node_104 h delta _ctx _hno a13 a17 a27 a30 f6
  apply _hno 106
  change (((2 : ℝ) * (delta)) ≤ (10/47 : ℝ)) ∧ (h 0 ≤ (1/5 : ℝ)) ∧ (h 1 ≤ (7/57 : ℝ)) ∧ (h 2 ≤ (5/41 : ℝ)) ∧ (h 3 ≤ (4/33 : ℝ)) ∧ (h 4 ≤ (3/28 : ℝ)) ∧ (h 5 ≤ (5/47 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem new_node_89 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a20 : -(h 4) < (-5/48 : ℝ))
    (a22 : h 0 ≤ (5/26 : ℝ))
    (a23 : -(h 1) < (-3/26 : ℝ))
    (a27 : -(h 2) < (-1/9 : ℝ))
    (a29 : -(h 0) < (-4/21 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_91 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (1/5 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/5 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_92 h delta _ctx _hno a22 f1
  by_cases p2 : h 1 ≤ (7/57 : ℝ)
  swap
  · have f2 : -(h 1) < (-7/57 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_93 h delta _ctx _hno a13 a20 a27 a29 f2
  by_cases p3 : h 2 ≤ (5/41 : ℝ)
  swap
  · have f3 : -(h 2) < (-5/41 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_94 h delta _ctx _hno a13 a20 a29 f3
  by_cases p4 : h 3 ≤ (4/33 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_95 h delta _ctx _hno a29 f4
  by_cases p5 : h 4 ≤ (3/28 : ℝ)
  swap
  · have f5 : -(h 4) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_96 h delta _ctx _hno a13 a23 a27 a29 f5
  by_cases p6 : h 5 ≤ (5/47 : ℝ)
  swap
  · have f6 : -(h 5) < (-5/47 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact new_node_97 h delta _ctx _hno a13 a23 a27 a29 f6
  apply _hno 106
  change (((2 : ℝ) * (delta)) ≤ (10/47 : ℝ)) ∧ (h 0 ≤ (1/5 : ℝ)) ∧ (h 1 ≤ (7/57 : ℝ)) ∧ (h 2 ≤ (5/41 : ℝ)) ∧ (h 3 ≤ (4/33 : ℝ)) ∧ (h 4 ≤ (3/28 : ℝ)) ∧ (h 5 ≤ (5/47 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem new_node_88 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a28 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a28
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_87 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a17 : -(h 0) < (-3/16 : ℝ))
    (a20 : -(h 4) < (-5/48 : ℝ))
    (a22 : h 0 ≤ (5/26 : ℝ))
    (a23 : -(h 1) < (-3/26 : ℝ))
    (a27 : -(h 2) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_88 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (4/21 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/21 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_89 h delta _ctx _hno a13 a20 a22 a23 a27 f1
  by_cases p2 : h 1 ≤ (2/17 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_90 h delta _ctx _hno a13 a17 a20 a27 p1 f2
  apply _hno 43
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (4/21 : ℝ)) ∧ (h 1 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem new_node_86 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : h 1 ≤ (1/8 : ℝ))
    (a26 : -(h 1) < (-5/36 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a19 + (1 : ℝ) * a26
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_85 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a22 : h 0 ≤ (5/26 : ℝ))
    (a25 : -(h 0) < (-5/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a22 + (1 : ℝ) * a25
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_84 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a24
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_83 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a22 : -(h 0) < (-5/26 : ℝ))
    (a27 : -(h 3) < (-1/9 : ℝ))
    (a34 : -(h 5) < (-5/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order1 + (4/13 : ℝ) * _ctx.order2 + (2/13 : ℝ) * _ctx.order4 + (1/13 : ℝ) * a13 + (2/13 : ℝ) * a22 + (6/13 : ℝ) * a27 + (4/13 : ℝ) * a34 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_82 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a22 : -(h 0) < (-5/26 : ℝ))
    (a27 : -(h 3) < (-1/9 : ℝ))
    (a33 : -(h 4) < (-3/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order1 + (1/3 : ℝ) * _ctx.order2 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a22 + (1/2 : ℝ) * a27 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_81 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : h 2 ≤ (9/80 : ℝ))
    (a32 : -(h 3) < (-4/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * _ctx.order2 + (1 : ℝ) * a26 + (1 : ℝ) * a32
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_80 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : h 2 ≤ (9/80 : ℝ))
    (a31 : -(h 2) < (-5/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a26 + (1 : ℝ) * a31
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_79 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a20 : -(h 4) < (-5/48 : ℝ))
    (a22 : -(h 0) < (-5/26 : ℝ))
    (a27 : -(h 3) < (-1/9 : ℝ))
    (a30 : -(h 1) < (-7/57 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order2 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a20 + (1/6 : ℝ) * a22 + (1/3 : ℝ) * a27 + (1/6 : ℝ) * a30 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_78 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a20 : -(h 4) < (-5/48 : ℝ))
    (a27 : -(h 3) < (-1/9 : ℝ))
    (a29 : -(h 0) < (-1/5 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order1 + (1/3 : ℝ) * _ctx.order2 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a20 + (1/2 : ℝ) * a27 + (1/6 : ℝ) * a29 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_77 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a28 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a28
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_76 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a22 : -(h 0) < (-5/26 : ℝ))
    (a26 : -(h 2) < (-9/80 : ℝ))
    (a33 : -(h 5) < (-5/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order1 + (2/13 : ℝ) * _ctx.order3 + (4/13 : ℝ) * _ctx.order4 + (1/13 : ℝ) * a13 + (2/13 : ℝ) * a22 + (4/13 : ℝ) * a26 + (6/13 : ℝ) * a33 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_75 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a22 : -(h 0) < (-5/26 : ℝ))
    (a26 : -(h 2) < (-9/80 : ℝ))
    (a32 : -(h 4) < (-3/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order1 + (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a22 + (1/3 : ℝ) * a26 + (1/3 : ℝ) * a32 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

end RealPinwheel.WeakSevenBandData
