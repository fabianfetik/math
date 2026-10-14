import Pinwheel.WeakSevenBandData.CoverChunks.New059

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem new_node_8314 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : h 3 ≤ (3/25 : ℝ))
    (a51 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a19 + (1 : ℝ) * a51
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8313 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a35 : h 2 ≤ (1/8 : ℝ))
    (a50 : -(h 2) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a35 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8312 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a22 : -(h 0) < (-3/20 : ℝ))
    (a31 : -(h 3) < (-4/35 : ℝ))
    (a38 : h 0 ≤ (5/33 : ℝ))
    (a42 : -(h 4) < (-1/9 : ℝ))
    (a46 : -(h 2) < (-4/33 : ℝ))
    (a49 : -(h 1) < (-3/22 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_8317 h delta _ctx _hno a16 f0
  by_cases p1 : h 0 ≤ (7/46 : ℝ)
  swap
  · have f1 : -(h 0) < (-7/46 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_8318 h delta _ctx _hno a38 f1
  by_cases p2 : h 1 ≤ (4/29 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/29 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_8319 h delta _ctx _hno a22 a31 a42 a46 f2
  by_cases p3 : h 2 ≤ (8/65 : ℝ)
  swap
  · have f3 : -(h 2) < (-8/65 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_8320 h delta _ctx _hno a22 a31 a42 a49 f3
  by_cases p4 : h 3 ≤ (8/69 : ℝ)
  swap
  · have f4 : -(h 3) < (-8/69 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_8321 h delta _ctx _hno a22 a42 a46 a49 f4
  by_cases p5 : h 4 ≤ (5/44 : ℝ)
  swap
  · have f5 : -(h 4) < (-5/44 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_8322 h delta _ctx _hno a22 a31 a46 a49 f5
  by_cases p6 : h 5 ≤ (3/29 : ℝ)
  swap
  · have f6 : -(h 5) < (-3/29 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact new_node_8323 h delta _ctx _hno a22 a31 a42 a46 a49 f6
  apply _hno 247
  change (((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)) ∧ (h 0 ≤ (7/46 : ℝ)) ∧ (h 1 ≤ (4/29 : ℝ)) ∧ (h 2 ≤ (8/65 : ℝ)) ∧ (h 3 ≤ (8/69 : ℝ)) ∧ (h 4 ≤ (5/44 : ℝ)) ∧ (h 5 ≤ (3/29 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem new_node_8311 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a38 : h 0 ≤ (5/33 : ℝ))
    (a48 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a38 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8310 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a47 : ((-2 : ℝ) * (delta)) < (-1/5 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8309 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : -(h 1) < (-8/59 : ℝ))
    (a22 : -(h 0) < (-3/20 : ℝ))
    (a48 : -(h 5) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.order3 + (12/29 : ℝ) * _ctx.order4 + (6/29 : ℝ) * _ctx.lower + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a15 + (4/29 : ℝ) * a22 + (18/29 : ℝ) * a48 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8308 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : -(h 1) < (-8/59 : ℝ))
    (a22 : -(h 0) < (-3/20 : ℝ))
    (a26 : -(h 2) < (-3/25 : ℝ))
    (a42 : -(h 4) < (-1/9 : ℝ))
    (a47 : -(h 3) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a15 + (1/5 : ℝ) * a22 + (1/5 : ℝ) * a26 + (1/5 : ℝ) * a42 + (1/5 : ℝ) * a47 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8307 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : -(h 1) < (-8/59 : ℝ))
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a19 : h 3 ≤ (3/25 : ℝ))
    (a22 : -(h 0) < (-3/20 : ℝ))
    (a31 : -(h 3) < (-4/35 : ℝ))
    (a35 : h 2 ≤ (1/8 : ℝ))
    (a38 : h 0 ≤ (5/33 : ℝ))
    (a42 : -(h 4) < (-1/9 : ℝ))
    (a46 : -(h 2) < (-4/33 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-1/5 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_8310 h delta _ctx _hno a16 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_8311 h delta _ctx _hno a38 f1
  by_cases p2 : h 1 ≤ (3/22 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_8312 h delta _ctx _hno a16 a22 a31 a38 a42 a46 f2
  by_cases p3 : h 2 ≤ (3/23 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_8313 h delta _ctx _hno a35 f3
  by_cases p4 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_8314 h delta _ctx _hno a19 f4
  by_cases p5 : h 4 ≤ (5/44 : ℝ)
  swap
  · have f5 : -(h 4) < (-5/44 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_8315 h delta _ctx _hno a15 a22 a31 a46 f5
  by_cases p6 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f6 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact new_node_8316 h delta _ctx _hno a15 a22 a31 a42 a46 f6
  apply _hno 49
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (5/44 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem new_node_8306 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a29 : h 1 ≤ (1/7 : ℝ))
    (a45 : -(h 1) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8305 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a38 : h 0 ≤ (5/33 : ℝ))
    (a44 : -(h 0) < (-5/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a38 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8304 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-7/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8303 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : -(h 2) < (-3/25 : ℝ))
    (a31 : -(h 3) < (-4/35 : ℝ))
    (a38 : -(h 0) < (-5/33 : ℝ))
    (a44 : -(h 4) < (-1/9 : ℝ))
    (a47 : -(h 1) < (-3/22 : ℝ))
    (a54 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a26 + (1/6 : ℝ) * a31 + (1/6 : ℝ) * a38 + (1/6 : ℝ) * a44 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * a54 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8302 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : -(h 2) < (-3/25 : ℝ))
    (a31 : -(h 3) < (-4/35 : ℝ))
    (a38 : -(h 0) < (-5/33 : ℝ))
    (a47 : -(h 1) < (-3/22 : ℝ))
    (a53 : -(h 4) < (-5/44 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a26 + (1/5 : ℝ) * a31 + (1/5 : ℝ) * a38 + (1/5 : ℝ) * a47 + (1/5 : ℝ) * a53 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8301 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : -(h 2) < (-3/25 : ℝ))
    (a38 : -(h 0) < (-5/33 : ℝ))
    (a44 : -(h 4) < (-1/9 : ℝ))
    (a47 : -(h 1) < (-3/22 : ℝ))
    (a52 : -(h 3) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a26 + (1/5 : ℝ) * a38 + (1/5 : ℝ) * a44 + (1/5 : ℝ) * a47 + (1/5 : ℝ) * a52 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8300 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a31 : -(h 3) < (-4/35 : ℝ))
    (a38 : -(h 0) < (-5/33 : ℝ))
    (a44 : -(h 4) < (-1/9 : ℝ))
    (a47 : -(h 1) < (-3/22 : ℝ))
    (a51 : -(h 2) < (-4/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a31 + (1/5 : ℝ) * a38 + (1/5 : ℝ) * a44 + (1/5 : ℝ) * a47 + (1/5 : ℝ) * a51 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8299 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a41 : h 1 ≤ (6/43 : ℝ))
    (a50 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a41 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8298 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a46 : h 0 ≤ (2/13 : ℝ))
    (a49 : -(h 0) < (-7/45 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a46 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8297 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a48 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8296 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : -(h 1) < (-8/59 : ℝ))
    (a26 : -(h 2) < (-3/25 : ℝ))
    (a31 : -(h 3) < (-4/35 : ℝ))
    (a38 : -(h 0) < (-5/33 : ℝ))
    (a44 : -(h 4) < (-1/9 : ℝ))
    (a51 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a15 + (1/6 : ℝ) * a26 + (1/6 : ℝ) * a31 + (1/6 : ℝ) * a38 + (1/6 : ℝ) * a44 + (1/6 : ℝ) * a51 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8295 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : -(h 1) < (-8/59 : ℝ))
    (a26 : -(h 2) < (-3/25 : ℝ))
    (a31 : -(h 3) < (-4/35 : ℝ))
    (a38 : -(h 0) < (-5/33 : ℝ))
    (a50 : -(h 4) < (-5/44 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a15 + (1/5 : ℝ) * a26 + (1/5 : ℝ) * a31 + (1/5 : ℝ) * a38 + (1/5 : ℝ) * a50 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8294 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a43 : h 3 ≤ (5/43 : ℝ))
    (a49 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a43 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8293 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a35 : h 2 ≤ (1/8 : ℝ))
    (a48 : -(h 2) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a35 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8292 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a26 : -(h 2) < (-3/25 : ℝ))
    (a31 : -(h 3) < (-4/35 : ℝ))
    (a38 : -(h 0) < (-5/33 : ℝ))
    (a41 : h 1 ≤ (6/43 : ℝ))
    (a44 : -(h 4) < (-1/9 : ℝ))
    (a46 : h 0 ≤ (2/13 : ℝ))
    (a47 : -(h 1) < (-3/22 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_8297 h delta _ctx _hno a16 f0
  by_cases p1 : h 0 ≤ (7/45 : ℝ)
  swap
  · have f1 : -(h 0) < (-7/45 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_8298 h delta _ctx _hno a46 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_8299 h delta _ctx _hno a41 f2
  by_cases p3 : h 2 ≤ (4/33 : ℝ)
  swap
  · have f3 : -(h 2) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_8300 h delta _ctx _hno a31 a38 a44 a47 f3
  by_cases p4 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_8301 h delta _ctx _hno a26 a38 a44 a47 f4
  by_cases p5 : h 4 ≤ (5/44 : ℝ)
  swap
  · have f5 : -(h 4) < (-5/44 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_8302 h delta _ctx _hno a26 a31 a38 a47 f5
  by_cases p6 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f6 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact new_node_8303 h delta _ctx _hno a26 a31 a38 a44 a47 f6
  apply _hno 244
  change (((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)) ∧ (h 0 ≤ (7/45 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (4/33 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 4 ≤ (5/44 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem new_node_8291 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : -(h 1) < (-8/59 : ℝ))
    (a26 : -(h 2) < (-3/25 : ℝ))
    (a31 : -(h 3) < (-4/35 : ℝ))
    (a44 : -(h 4) < (-1/9 : ℝ))
    (a46 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a15 + (1/5 : ℝ) * a26 + (1/5 : ℝ) * a31 + (1/5 : ℝ) * a44 + (1/5 : ℝ) * a46 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8290 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a45 : ((-2 : ℝ) * (delta)) < (-1/5 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8289 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : -(h 2) < (-3/25 : ℝ))
    (a38 : -(h 0) < (-5/33 : ℝ))
    (a43 : -(h 3) < (-5/43 : ℝ))
    (a46 : -(h 1) < (-3/22 : ℝ))
    (a51 : -(h 4) < (-6/55 : ℝ))
    (a58 : -(h 5) < (-7/66 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a26 + (1/6 : ℝ) * a38 + (1/6 : ℝ) * a43 + (1/6 : ℝ) * a46 + (1/6 : ℝ) * a51 + (1/6 : ℝ) * a58 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8288 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : -(h 2) < (-3/25 : ℝ))
    (a38 : -(h 0) < (-5/33 : ℝ))
    (a43 : -(h 3) < (-5/43 : ℝ))
    (a46 : -(h 1) < (-3/22 : ℝ))
    (a57 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a26 + (1/5 : ℝ) * a38 + (1/5 : ℝ) * a43 + (1/5 : ℝ) * a46 + (1/5 : ℝ) * a57 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8287 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : -(h 2) < (-3/25 : ℝ))
    (a38 : -(h 0) < (-5/33 : ℝ))
    (a46 : -(h 1) < (-3/22 : ℝ))
    (a51 : -(h 4) < (-6/55 : ℝ))
    (a56 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a26 + (1/5 : ℝ) * a38 + (1/5 : ℝ) * a46 + (1/5 : ℝ) * a51 + (1/5 : ℝ) * a56 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8286 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a38 : -(h 0) < (-5/33 : ℝ))
    (a43 : -(h 3) < (-5/43 : ℝ))
    (a46 : -(h 1) < (-3/22 : ℝ))
    (a51 : -(h 4) < (-6/55 : ℝ))
    (a55 : -(h 2) < (-7/58 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a38 + (1/5 : ℝ) * a43 + (1/5 : ℝ) * a46 + (1/5 : ℝ) * a51 + (1/5 : ℝ) * a55 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8285 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : -(h 2) < (-3/25 : ℝ))
    (a38 : -(h 0) < (-5/33 : ℝ))
    (a43 : -(h 3) < (-5/43 : ℝ))
    (a51 : -(h 4) < (-6/55 : ℝ))
    (a54 : -(h 1) < (-5/36 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a26 + (1/5 : ℝ) * a38 + (1/5 : ℝ) * a43 + (1/5 : ℝ) * a51 + (1/5 : ℝ) * a54 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8284 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a48 : h 0 ≤ (2/13 : ℝ))
    (a53 : -(h 0) < (-3/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a48 + (1 : ℝ) * a53
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8283 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a52 : ((-2 : ℝ) * (delta)) < (-16/79 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a52
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8282 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : -(h 2) < (-3/25 : ℝ))
    (a36 : -(h 4) < (-3/28 : ℝ))
    (a38 : -(h 0) < (-5/33 : ℝ))
    (a43 : -(h 3) < (-5/43 : ℝ))
    (a46 : -(h 1) < (-3/22 : ℝ))
    (a52 : -(h 5) < (-3/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a26 + (1/6 : ℝ) * a36 + (1/6 : ℝ) * a38 + (1/6 : ℝ) * a43 + (1/6 : ℝ) * a46 + (1/6 : ℝ) * a52 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8281 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a26 : -(h 2) < (-3/25 : ℝ))
    (a38 : -(h 0) < (-5/33 : ℝ))
    (a43 : -(h 3) < (-5/43 : ℝ))
    (a46 : -(h 1) < (-3/22 : ℝ))
    (a48 : h 0 ≤ (2/13 : ℝ))
    (a51 : -(h 4) < (-6/55 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (16/79 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-16/79 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_8283 h delta _ctx _hno a16 f0
  by_cases p1 : h 0 ≤ (3/19 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/19 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_8284 h delta _ctx _hno a48 f1
  by_cases p2 : h 1 ≤ (5/36 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/36 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_8285 h delta _ctx _hno a26 a38 a43 a51 f2
  by_cases p3 : h 2 ≤ (7/58 : ℝ)
  swap
  · have f3 : -(h 2) < (-7/58 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_8286 h delta _ctx _hno a38 a43 a46 a51 f3
  by_cases p4 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_8287 h delta _ctx _hno a26 a38 a46 a51 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_8288 h delta _ctx _hno a26 a38 a43 a46 f5
  by_cases p6 : h 5 ≤ (7/66 : ℝ)
  swap
  · have f6 : -(h 5) < (-7/66 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact new_node_8289 h delta _ctx _hno a26 a38 a43 a46 a51 f6
  apply _hno 245
  change (((2 : ℝ) * (delta)) ≤ (16/79 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (5/36 : ℝ)) ∧ (h 2 ≤ (7/58 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ)) ∧ (h 5 ≤ (7/66 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem new_node_8280 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a36 : -(h 4) < (-3/28 : ℝ))
    (a38 : -(h 0) < (-5/33 : ℝ))
    (a43 : -(h 3) < (-5/43 : ℝ))
    (a46 : -(h 1) < (-3/22 : ℝ))
    (a50 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a36 + (1/5 : ℝ) * a38 + (1/5 : ℝ) * a43 + (1/5 : ℝ) * a46 + (1/5 : ℝ) * a50 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8279 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a41 : h 1 ≤ (6/43 : ℝ))
    (a49 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a41 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8278 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : -(h 2) < (-3/25 : ℝ))
    (a36 : -(h 4) < (-3/28 : ℝ))
    (a43 : -(h 3) < (-5/43 : ℝ))
    (a46 : -(h 1) < (-3/22 : ℝ))
    (a48 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a26 + (1/5 : ℝ) * a36 + (1/5 : ℝ) * a43 + (1/5 : ℝ) * a46 + (1/5 : ℝ) * a48 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8277 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a47 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8276 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : -(h 1) < (-8/59 : ℝ))
    (a26 : -(h 2) < (-3/25 : ℝ))
    (a38 : -(h 0) < (-5/33 : ℝ))
    (a43 : -(h 3) < (-5/43 : ℝ))
    (a49 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a15 + (1/5 : ℝ) * a26 + (1/5 : ℝ) * a38 + (1/5 : ℝ) * a43 + (1/5 : ℝ) * a49 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8275 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : h 3 ≤ (3/25 : ℝ))
    (a48 : -(h 3) < (-7/57 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a19 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8274 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : -(h 1) < (-8/59 : ℝ))
    (a36 : -(h 4) < (-3/28 : ℝ))
    (a38 : -(h 0) < (-5/33 : ℝ))
    (a43 : -(h 3) < (-5/43 : ℝ))
    (a47 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a15 + (1/5 : ℝ) * a36 + (1/5 : ℝ) * a38 + (1/5 : ℝ) * a43 + (1/5 : ℝ) * a47 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8273 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a26 : -(h 2) < (-3/25 : ℝ))
    (a36 : -(h 4) < (-3/28 : ℝ))
    (a38 : -(h 0) < (-5/33 : ℝ))
    (a41 : h 1 ≤ (6/43 : ℝ))
    (a43 : -(h 3) < (-5/43 : ℝ))
    (a46 : -(h 1) < (-3/22 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_8277 h delta _ctx _hno a16 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_8278 h delta _ctx _hno a26 a36 a43 a46 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_8279 h delta _ctx _hno a41 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_8280 h delta _ctx _hno a36 a38 a43 a46 f3
  by_cases p4 : h 4 ≤ (6/55 : ℝ)
  swap
  · have f4 : -(h 4) < (-6/55 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_8281 h delta _ctx _hno a16 a26 a38 a43 a46 p1 f4
  by_cases p5 : h 5 ≤ (3/28 : ℝ)
  swap
  · have f5 : -(h 5) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_8282 h delta _ctx _hno a26 a36 a38 a43 a46 f5
  apply _hno 104
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (6/55 : ℝ)) ∧ (h 5 ≤ (3/28 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_8272 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : h 0 ≤ (4/25 : ℝ))
    (a45 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8271 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a44 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8270 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : -(h 2) < (-3/25 : ℝ))
    (a31 : -(h 3) < (-4/35 : ℝ))
    (a36 : -(h 4) < (-3/28 : ℝ))
    (a38 : -(h 0) < (-5/33 : ℝ))
    (a41 : -(h 1) < (-6/43 : ℝ))
    (a47 : -(h 5) < (-3/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a26 + (1/6 : ℝ) * a31 + (1/6 : ℝ) * a36 + (1/6 : ℝ) * a38 + (1/6 : ℝ) * a41 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8269 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : -(h 2) < (-3/25 : ℝ))
    (a31 : -(h 3) < (-4/35 : ℝ))
    (a38 : -(h 0) < (-5/33 : ℝ))
    (a41 : -(h 1) < (-6/43 : ℝ))
    (a46 : -(h 4) < (-6/55 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a26 + (1/5 : ℝ) * a31 + (1/5 : ℝ) * a38 + (1/5 : ℝ) * a41 + (1/5 : ℝ) * a46 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8268 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a31 : -(h 3) < (-4/35 : ℝ))
    (a36 : -(h 4) < (-3/28 : ℝ))
    (a38 : -(h 0) < (-5/33 : ℝ))
    (a41 : -(h 1) < (-6/43 : ℝ))
    (a45 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a31 + (1/5 : ℝ) * a36 + (1/5 : ℝ) * a38 + (1/5 : ℝ) * a41 + (1/5 : ℝ) * a45 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8267 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : -(h 2) < (-3/25 : ℝ))
    (a31 : -(h 3) < (-4/35 : ℝ))
    (a36 : -(h 4) < (-3/28 : ℝ))
    (a38 : -(h 0) < (-5/33 : ℝ))
    (a44 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a26 + (1/5 : ℝ) * a31 + (1/5 : ℝ) * a36 + (1/5 : ℝ) * a38 + (1/5 : ℝ) * a44 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8266 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : -(h 2) < (-3/25 : ℝ))
    (a31 : -(h 3) < (-4/35 : ℝ))
    (a36 : -(h 4) < (-3/28 : ℝ))
    (a41 : -(h 1) < (-6/43 : ℝ))
    (a43 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a26 + (1/5 : ℝ) * a31 + (1/5 : ℝ) * a36 + (1/5 : ℝ) * a41 + (1/5 : ℝ) * a43 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8265 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a42 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8264 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : -(h 1) < (-8/59 : ℝ))
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a26 : -(h 2) < (-3/25 : ℝ))
    (a31 : -(h 3) < (-4/35 : ℝ))
    (a35 : h 2 ≤ (1/8 : ℝ))
    (a38 : -(h 0) < (-5/33 : ℝ))
    (a41 : h 1 ≤ (6/43 : ℝ))
    (a43 : h 3 ≤ (5/43 : ℝ))
    (a44 : -(h 4) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-1/5 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_8290 h delta _ctx _hno a16 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_8291 h delta _ctx _hno a15 a26 a31 a44 f1
  by_cases p2 : h 1 ≤ (3/22 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_8292 h delta _ctx _hno a16 a26 a31 a38 a41 a44 p1 f2
  by_cases p3 : h 2 ≤ (3/23 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_8293 h delta _ctx _hno a35 f3
  by_cases p4 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_8294 h delta _ctx _hno a43 f4
  by_cases p5 : h 4 ≤ (5/44 : ℝ)
  swap
  · have f5 : -(h 4) < (-5/44 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_8295 h delta _ctx _hno a15 a26 a31 a38 f5
  by_cases p6 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f6 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact new_node_8296 h delta _ctx _hno a15 a26 a31 a38 a44 f6
  apply _hno 49
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (5/44 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem new_node_8263 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : -(h 1) < (-8/59 : ℝ))
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a17 : h 0 ≤ (4/25 : ℝ))
    (a19 : h 3 ≤ (3/25 : ℝ))
    (a26 : -(h 2) < (-3/25 : ℝ))
    (a36 : -(h 4) < (-3/28 : ℝ))
    (a38 : -(h 0) < (-5/33 : ℝ))
    (a41 : h 1 ≤ (6/43 : ℝ))
    (a43 : -(h 3) < (-5/43 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_8271 h delta _ctx _hno a16 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_8272 h delta _ctx _hno a17 f1
  by_cases p2 : h 1 ≤ (3/22 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_8273 h delta _ctx _hno a16 a26 a36 a38 a41 a43 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_8274 h delta _ctx _hno a15 a36 a38 a43 f3
  by_cases p4 : h 3 ≤ (7/57 : ℝ)
  swap
  · have f4 : -(h 3) < (-7/57 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_8275 h delta _ctx _hno a19 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_8276 h delta _ctx _hno a15 a26 a38 a43 f5
  apply _hno 121
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (7/57 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_8262 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a35 : h 2 ≤ (1/8 : ℝ))
    (a42 : -(h 2) < (-3/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a35 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8261 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a26 : -(h 2) < (-3/25 : ℝ))
    (a31 : -(h 3) < (-4/35 : ℝ))
    (a36 : -(h 4) < (-3/28 : ℝ))
    (a38 : -(h 0) < (-5/33 : ℝ))
    (a41 : -(h 1) < (-6/43 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_8265 h delta _ctx _hno a16 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_8266 h delta _ctx _hno a26 a31 a36 a41 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_8267 h delta _ctx _hno a26 a31 a36 a38 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_8268 h delta _ctx _hno a31 a36 a38 a41 f3
  by_cases p4 : h 4 ≤ (6/55 : ℝ)
  swap
  · have f4 : -(h 4) < (-6/55 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_8269 h delta _ctx _hno a26 a31 a38 a41 f4
  by_cases p5 : h 5 ≤ (3/28 : ℝ)
  swap
  · have f5 : -(h 5) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_8270 h delta _ctx _hno a26 a31 a36 a38 a41 f5
  apply _hno 104
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (6/55 : ℝ)) ∧ (h 5 ≤ (3/28 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_8260 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : h 0 ≤ (4/25 : ℝ))
    (a40 : -(h 0) < (-5/31 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8259 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a39 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8258 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : -(h 1) < (-8/59 : ℝ))
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a19 : h 3 ≤ (3/25 : ℝ))
    (a22 : -(h 0) < (-3/20 : ℝ))
    (a26 : -(h 2) < (-3/25 : ℝ))
    (a29 : h 1 ≤ (1/7 : ℝ))
    (a31 : -(h 3) < (-4/35 : ℝ))
    (a35 : h 2 ≤ (1/8 : ℝ))
    (a38 : h 0 ≤ (5/33 : ℝ))
    (a42 : -(h 4) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/33 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/33 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_8304 h delta _ctx _hno a16 f0
  by_cases p1 : h 0 ≤ (5/33 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/33 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_8305 h delta _ctx _hno a38 f1
  by_cases p2 : h 1 ≤ (3/20 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_8306 h delta _ctx _hno a29 f2
  by_cases p3 : h 2 ≤ (4/33 : ℝ)
  swap
  · have f3 : -(h 2) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_8307 h delta _ctx _hno a15 a16 a19 a22 a31 a35 a38 a42 f3
  by_cases p4 : h 3 ≤ (3/25 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_8308 h delta _ctx _hno a15 a22 a26 a42 f4
  by_cases p5 : h 5 ≤ (2/17 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_8309 h delta _ctx _hno a15 a22 f5
  apply _hno 11
  change (((2 : ℝ) * (delta)) ≤ (7/33 : ℝ)) ∧ (h 0 ≤ (5/33 : ℝ)) ∧ (h 1 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (4/33 : ℝ)) ∧ (h 3 ≤ (3/25 : ℝ)) ∧ (h 5 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_8257 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : h 3 ≤ (3/25 : ℝ))
    (a41 : -(h 3) < (-7/57 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a19 + (1 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8256 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a35 : h 2 ≤ (1/8 : ℝ))
    (a40 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a35 + (1 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8255 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a29 : h 1 ≤ (1/7 : ℝ))
    (a39 : -(h 1) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8254 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : -(h 1) < (-8/59 : ℝ))
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a17 : h 0 ≤ (4/25 : ℝ))
    (a19 : h 3 ≤ (3/25 : ℝ))
    (a26 : -(h 2) < (-3/25 : ℝ))
    (a31 : -(h 3) < (-4/35 : ℝ))
    (a35 : h 2 ≤ (1/8 : ℝ))
    (a36 : -(h 4) < (-3/28 : ℝ))
    (a38 : -(h 0) < (-5/33 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_8259 h delta _ctx _hno a16 f0
  by_cases p1 : h 0 ≤ (5/31 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/31 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_8260 h delta _ctx _hno a17 f1
  by_cases p2 : h 1 ≤ (6/43 : ℝ)
  swap
  · have f2 : -(h 1) < (-6/43 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_8261 h delta _ctx _hno a16 a26 a31 a36 a38 f2
  by_cases p3 : h 2 ≤ (3/22 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_8262 h delta _ctx _hno a35 f3
  by_cases p4 : h 3 ≤ (5/43 : ℝ)
  swap
  · have f4 : -(h 3) < (-5/43 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_8263 h delta _ctx _hno a15 a16 a17 a19 a26 a36 a38 p2 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_8264 h delta _ctx _hno a15 a16 a26 a31 a35 a38 p2 p4 f5
  apply _hno 228
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (5/31 : ℝ)) ∧ (h 1 ≤ (6/43 : ℝ)) ∧ (h 2 ≤ (3/22 : ℝ)) ∧ (h 3 ≤ (5/43 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_8253 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a37 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a37
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8252 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a22 : -(h 0) < (-3/20 : ℝ))
    (a35 : -(h 2) < (-1/8 : ℝ))
    (a49 : -(h 3) < (-5/43 : ℝ))
    (a52 : -(h 1) < (-3/22 : ℝ))
    (a59 : -(h 5) < (-3/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order4 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a22 + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a49 + (1/6 : ℝ) * a52 + (1/3 : ℝ) * a59 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8251 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a22 : -(h 0) < (-3/20 : ℝ))
    (a35 : -(h 2) < (-1/8 : ℝ))
    (a49 : -(h 3) < (-5/43 : ℝ))
    (a52 : -(h 1) < (-3/22 : ℝ))
    (a58 : -(h 4) < (-5/46 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a22 + (1/5 : ℝ) * a35 + (1/5 : ℝ) * a49 + (1/5 : ℝ) * a52 + (1/5 : ℝ) * a58 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8250 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : h 3 ≤ (3/25 : ℝ))
    (a57 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a19 + (1 : ℝ) * a57
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8249 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a43 : h 2 ≤ (5/38 : ℝ))
    (a56 : -(h 2) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a43 + (1 : ℝ) * a56
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8248 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a22 : -(h 0) < (-3/20 : ℝ))
    (a35 : -(h 2) < (-1/8 : ℝ))
    (a44 : -(h 4) < (-2/19 : ℝ))
    (a49 : -(h 3) < (-5/43 : ℝ))
    (a55 : -(h 1) < (-4/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a22 + (1/5 : ℝ) * a35 + (1/5 : ℝ) * a44 + (1/5 : ℝ) * a49 + (1/5 : ℝ) * a55 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8247 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a51 : h 0 ≤ (2/13 : ℝ))
    (a54 : -(h 0) < (-5/32 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a51 + (1 : ℝ) * a54
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8246 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a53 : ((-2 : ℝ) * (delta)) < (-1/5 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a53
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8245 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : -(h 1) < (-8/59 : ℝ))
    (a22 : -(h 0) < (-3/20 : ℝ))
    (a35 : -(h 2) < (-1/8 : ℝ))
    (a49 : -(h 3) < (-5/43 : ℝ))
    (a56 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order4 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a15 + (1/6 : ℝ) * a22 + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a49 + (1/3 : ℝ) * a56 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8244 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : -(h 1) < (-8/59 : ℝ))
    (a22 : -(h 0) < (-3/20 : ℝ))
    (a35 : -(h 2) < (-1/8 : ℝ))
    (a49 : -(h 3) < (-5/43 : ℝ))
    (a55 : -(h 4) < (-5/44 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a15 + (1/5 : ℝ) * a22 + (1/5 : ℝ) * a35 + (1/5 : ℝ) * a49 + (1/5 : ℝ) * a55 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8243 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : h 3 ≤ (3/25 : ℝ))
    (a54 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a19 + (1 : ℝ) * a54
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8242 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : -(h 1) < (-8/59 : ℝ))
    (a22 : -(h 0) < (-3/20 : ℝ))
    (a44 : -(h 4) < (-2/19 : ℝ))
    (a49 : -(h 3) < (-5/43 : ℝ))
    (a53 : -(h 2) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a15 + (1/5 : ℝ) * a22 + (1/5 : ℝ) * a44 + (1/5 : ℝ) * a49 + (1/5 : ℝ) * a53 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8241 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a19 : h 3 ≤ (3/25 : ℝ))
    (a22 : -(h 0) < (-3/20 : ℝ))
    (a35 : -(h 2) < (-1/8 : ℝ))
    (a43 : h 2 ≤ (5/38 : ℝ))
    (a44 : -(h 4) < (-2/19 : ℝ))
    (a49 : -(h 3) < (-5/43 : ℝ))
    (a51 : h 0 ≤ (2/13 : ℝ))
    (a52 : -(h 1) < (-3/22 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-1/5 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_8246 h delta _ctx _hno a16 f0
  by_cases p1 : h 0 ≤ (5/32 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/32 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_8247 h delta _ctx _hno a51 f1
  by_cases p2 : h 1 ≤ (4/29 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/29 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_8248 h delta _ctx _hno a22 a35 a44 a49 f2
  by_cases p3 : h 2 ≤ (2/15 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_8249 h delta _ctx _hno a43 f3
  by_cases p4 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_8250 h delta _ctx _hno a19 f4
  by_cases p5 : h 4 ≤ (5/46 : ℝ)
  swap
  · have f5 : -(h 4) < (-5/46 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_8251 h delta _ctx _hno a22 a35 a49 a52 f5
  by_cases p6 : h 5 ≤ (3/28 : ℝ)
  swap
  · have f6 : -(h 5) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact new_node_8252 h delta _ctx _hno a22 a35 a49 a52 f6
  apply _hno 105
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 0 ≤ (5/32 : ℝ)) ∧ (h 1 ≤ (4/29 : ℝ)) ∧ (h 2 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (5/46 : ℝ)) ∧ (h 5 ≤ (3/28 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem new_node_8240 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : -(h 1) < (-8/59 : ℝ))
    (a35 : -(h 2) < (-1/8 : ℝ))
    (a44 : -(h 4) < (-2/19 : ℝ))
    (a49 : -(h 3) < (-5/43 : ℝ))
    (a51 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a15 + (1/5 : ℝ) * a35 + (1/5 : ℝ) * a44 + (1/5 : ℝ) * a49 + (1/5 : ℝ) * a51 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8239 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a50 : ((-2 : ℝ) * (delta)) < (-1/5 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8238 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : -(h 1) < (-8/59 : ℝ))
    (a22 : -(h 0) < (-3/20 : ℝ))
    (a31 : -(h 3) < (-4/35 : ℝ))
    (a35 : -(h 2) < (-1/8 : ℝ))
    (a50 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a15 + (1/5 : ℝ) * a22 + (1/5 : ℝ) * a31 + (1/5 : ℝ) * a35 + (1/5 : ℝ) * a50 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8237 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : -(h 1) < (-8/59 : ℝ))
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a19 : h 3 ≤ (3/25 : ℝ))
    (a22 : -(h 0) < (-3/20 : ℝ))
    (a35 : -(h 2) < (-1/8 : ℝ))
    (a43 : h 2 ≤ (5/38 : ℝ))
    (a44 : -(h 4) < (-2/19 : ℝ))
    (a49 : -(h 3) < (-5/43 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-1/5 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_8239 h delta _ctx _hno a16 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_8240 h delta _ctx _hno a15 a35 a44 a49 f1
  by_cases p2 : h 1 ≤ (3/22 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_8241 h delta _ctx _hno a16 a19 a22 a35 a43 a44 a49 p1 f2
  by_cases p3 : h 2 ≤ (3/23 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_8242 h delta _ctx _hno a15 a22 a44 a49 f3
  by_cases p4 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_8243 h delta _ctx _hno a19 f4
  by_cases p5 : h 4 ≤ (5/44 : ℝ)
  swap
  · have f5 : -(h 4) < (-5/44 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_8244 h delta _ctx _hno a15 a22 a35 a49 f5
  by_cases p6 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f6 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact new_node_8245 h delta _ctx _hno a15 a22 a35 a49 f6
  apply _hno 49
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (5/44 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem new_node_8236 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a43 : h 2 ≤ (5/38 : ℝ))
    (a48 : -(h 2) < (-3/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a43 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8235 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a38 : h 1 ≤ (4/29 : ℝ))
    (a47 : -(h 1) < (-6/43 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a38 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

end RealPinwheel.WeakSevenBandData
