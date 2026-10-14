import Pinwheel.WeakSevenBandData.CoverChunks.New021

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem new_node_11354 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a47 : ((-2 : ℝ) * (delta)) < (-1/5 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11353 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a14 : h 0 ≤ (7/38 : ℝ))
    (a15 : h 1 ≤ (8/59 : ℝ))
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a22 : -(h 0) < (-2/11 : ℝ))
    (a29 : -(h 2) < (-1/9 : ℝ))
    (a35 : -(h 1) < (-7/53 : ℝ))
    (a44 : h 2 ≤ (3/26 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-1/5 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_11354 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (8/43 : ℝ)
  swap
  · have f1 : -(h 0) < (-8/43 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_11355 h delta _ctx _hno a14 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_11356 h delta _ctx _hno a15 f2
  by_cases p3 : h 2 ≤ (3/25 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_11357 h delta _ctx _hno a44 f3
  by_cases p4 : h 4 ≤ (5/48 : ℝ)
  swap
  · have f4 : -(h 4) < (-5/48 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_11358 h delta _ctx _hno a22 a29 a35 f4
  apply _hno 62
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 0 ≤ (8/43 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 4 ≤ (5/48 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_11352 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : -(h 4) < (-6/59 : ℝ))
    (a22 : -(h 0) < (-2/11 : ℝ))
    (a29 : -(h 2) < (-1/9 : ℝ))
    (a35 : -(h 1) < (-7/53 : ℝ))
    (a45 : -(h 3) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a16 + (1/5 : ℝ) * a22 + (1/5 : ℝ) * a29 + (1/5 : ℝ) * a35 + (1/5 : ℝ) * a45 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11351 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : -(h 4) < (-6/59 : ℝ))
    (a22 : -(h 0) < (-2/11 : ℝ))
    (a35 : -(h 1) < (-7/53 : ℝ))
    (a40 : -(h 3) < (-3/29 : ℝ))
    (a44 : -(h 2) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a16 + (1/5 : ℝ) * a22 + (1/5 : ℝ) * a35 + (1/5 : ℝ) * a40 + (1/5 : ℝ) * a44 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11350 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : h 1 ≤ (8/59 : ℝ))
    (a43 : -(h 1) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a15 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11349 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a14 : h 0 ≤ (7/38 : ℝ))
    (a42 : -(h 0) < (-5/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a14 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11348 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11347 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a14 : h 0 ≤ (7/38 : ℝ))
    (a15 : h 1 ≤ (8/59 : ℝ))
    (a16 : -(h 4) < (-6/59 : ℝ))
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a22 : -(h 0) < (-2/11 : ℝ))
    (a29 : -(h 2) < (-1/9 : ℝ))
    (a35 : -(h 1) < (-7/53 : ℝ))
    (a40 : -(h 3) < (-3/29 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_11348 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (5/26 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/26 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_11349 h delta _ctx _hno a14 f1
  by_cases p2 : h 1 ≤ (2/13 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_11350 h delta _ctx _hno a15 f2
  by_cases p3 : h 2 ≤ (3/26 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_11351 h delta _ctx _hno a16 a22 a35 a40 f3
  by_cases p4 : h 3 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_11352 h delta _ctx _hno a16 a22 a29 a35 f4
  by_cases p5 : h 4 ≤ (3/29 : ℝ)
  swap
  · have f5 : -(h 4) < (-3/29 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_11353 h delta _ctx _hno a14 a15 a17 a22 a29 a35 p3
  apply _hno 166
  change (((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)) ∧ (h 0 ≤ (5/26 : ℝ)) ∧ (h 1 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (3/26 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ)) ∧ (h 4 ≤ (3/29 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_11346 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a22 : -(h 0) < (-2/11 : ℝ))
    (a39 : -(h 2) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order1 + (1/3 : ℝ) * _ctx.order3 + (2/3 : ℝ) * _ctx.order4 + (1 : ℝ) * _ctx.min + (4/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * a22 + (2/3 : ℝ) * a39 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11345 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : h 1 ≤ (8/59 : ℝ))
    (a38 : -(h 1) < (-4/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a15 + (1 : ℝ) * a38
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11344 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a14 : h 0 ≤ (7/38 : ℝ))
    (a37 : -(h 0) < (-1/5 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a14 + (1 : ℝ) * a37
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11343 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a36 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a36
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11342 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a22 : -(h 0) < (-2/11 : ℝ))
    (a29 : -(h 2) < (-1/9 : ℝ))
    (a32 : -(h 1) < (-7/54 : ℝ))
    (a37 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a22 + (1/5 : ℝ) * a29 + (1/5 : ℝ) * a32 + (2/5 : ℝ) * a37 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11341 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a14 : h 0 ≤ (7/38 : ℝ))
    (a16 : -(h 4) < (-6/59 : ℝ))
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a22 : -(h 0) < (-2/11 : ℝ))
    (a32 : -(h 1) < (-7/54 : ℝ))
    (a35 : h 1 ≤ (7/53 : ℝ))
    (a36 : -(h 2) < (-6/53 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_11359 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (1/5 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/5 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_11360 h delta _ctx _hno a14 f1
  by_cases p2 : h 1 ≤ (4/29 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/29 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_11361 h delta _ctx _hno a35 f2
  by_cases p3 : h 2 ≤ (2/15 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_11362 h delta _ctx _hno a22 f3
  by_cases p4 : h 3 ≤ (3/29 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/29 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_11363 h delta _ctx _hno a14 a16 a17 a22 a32 a35 a36 f4
  apply _hno 232
  change (((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)) ∧ (h 0 ≤ (1/5 : ℝ)) ∧ (h 1 ≤ (4/29 : ℝ)) ∧ (h 2 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (3/29 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_11340 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a14 : h 0 ≤ (7/38 : ℝ))
    (a15 : h 1 ≤ (8/59 : ℝ))
    (a16 : -(h 4) < (-6/59 : ℝ))
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a22 : -(h 0) < (-2/11 : ℝ))
    (a29 : -(h 2) < (-1/9 : ℝ))
    (a35 : -(h 1) < (-7/53 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_11343 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (1/5 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/5 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_11344 h delta _ctx _hno a14 f1
  by_cases p2 : h 1 ≤ (4/29 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/29 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_11345 h delta _ctx _hno a15 f2
  by_cases p3 : h 2 ≤ (2/15 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_11346 h delta _ctx _hno a22 f3
  by_cases p4 : h 3 ≤ (3/29 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/29 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_11347 h delta _ctx _hno a14 a15 a16 a17 a22 a29 a35 f4
  apply _hno 232
  change (((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)) ∧ (h 0 ≤ (1/5 : ℝ)) ∧ (h 1 ≤ (4/29 : ℝ)) ∧ (h 2 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (3/29 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_11339 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a14 : h 0 ≤ (7/38 : ℝ))
    (a34 : -(h 0) < (-1/5 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a14 + (1 : ℝ) * a34
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11338 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a33 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a33
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11337 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a14 : h 0 ≤ (7/38 : ℝ))
    (a16 : -(h 4) < (-6/59 : ℝ))
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a22 : -(h 0) < (-2/11 : ℝ))
    (a25 : -(h 1) < (-1/8 : ℝ))
    (a29 : -(h 2) < (-1/9 : ℝ))
    (a32 : h 1 ≤ (7/54 : ℝ))
    (a33 : -(h 3) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-1/5 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_11395 h delta _ctx _hno a17 f0
  by_cases p1 : h 1 ≤ (3/23 : ℝ)
  swap
  · have f1 : -(h 1) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_11396 h delta _ctx _hno a32 f1
  by_cases p2 : h 2 ≤ (2/17 : ℝ)
  swap
  · have f2 : -(h 2) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_11397 h delta _ctx _hno a16 a22 a25 a33 f2
  by_cases p3 : h 5 ≤ (6/59 : ℝ)
  swap
  · have f3 : -(h 5) < (-6/59 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_11398 h delta _ctx _hno a14 a16 a17 a22 a25 a29 a32 a33 f3
  apply _hno 93
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (6/59 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_11336 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a14 : h 0 ≤ (7/38 : ℝ))
    (a15 : h 1 ≤ (8/59 : ℝ))
    (a16 : -(h 4) < (-6/59 : ℝ))
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a22 : -(h 0) < (-2/11 : ℝ))
    (a29 : -(h 2) < (-1/9 : ℝ))
    (a32 : -(h 1) < (-7/54 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_11338 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (1/5 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/5 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_11339 h delta _ctx _hno a14 f1
  by_cases p2 : h 1 ≤ (7/53 : ℝ)
  swap
  · have f2 : -(h 1) < (-7/53 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_11340 h delta _ctx _hno a14 a15 a16 a17 a22 a29 f2
  by_cases p3 : h 2 ≤ (6/53 : ℝ)
  swap
  · have f3 : -(h 2) < (-6/53 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_11341 h delta _ctx _hno a14 a16 a17 a22 a32 p2 f3
  by_cases p4 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_11342 h delta _ctx _hno a22 a29 a32 f4
  apply _hno 74
  change (((2 : ℝ) * (delta)) ≤ (8/39 : ℝ)) ∧ (h 0 ≤ (1/5 : ℝ)) ∧ (h 1 ≤ (7/53 : ℝ)) ∧ (h 2 ≤ (6/53 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_11335 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a14 : h 0 ≤ (7/38 : ℝ))
    (a31 : -(h 0) < (-5/27 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a14 + (1 : ℝ) * a31
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11334 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a30 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a30
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11333 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a14 : h 0 ≤ (7/38 : ℝ))
    (a15 : h 1 ≤ (8/59 : ℝ))
    (a16 : -(h 4) < (-6/59 : ℝ))
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a22 : -(h 0) < (-2/11 : ℝ))
    (a25 : -(h 1) < (-1/8 : ℝ))
    (a29 : -(h 2) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_11334 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (5/27 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/27 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_11335 h delta _ctx _hno a14 f1
  by_cases p2 : h 1 ≤ (7/54 : ℝ)
  swap
  · have f2 : -(h 1) < (-7/54 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_11336 h delta _ctx _hno a14 a15 a16 a17 a22 a29 f2
  by_cases p3 : h 3 ≤ (1/9 : ℝ)
  swap
  · have f3 : -(h 3) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_11337 h delta _ctx _hno a14 a16 a17 a22 a25 a29 p2 f3
  apply _hno 78
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (5/27 : ℝ)) ∧ (h 1 ≤ (7/54 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_11332 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : h 1 ≤ (8/59 : ℝ))
    (a28 : -(h 1) < (-4/27 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a15 + (1 : ℝ) * a28
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11331 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a14 : h 0 ≤ (7/38 : ℝ))
    (a27 : -(h 0) < (-5/27 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a14 + (1 : ℝ) * a27
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11330 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a26 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a26
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11329 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a14 : h 0 ≤ (7/38 : ℝ))
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a22 : -(h 0) < (-2/11 : ℝ))
    (a25 : h 1 ≤ (1/8 : ℝ))
    (a26 : -(h 4) < (-7/64 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-1/5 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_11404 h delta _ctx _hno a17 f0
  by_cases p1 : h 1 ≤ (3/25 : ℝ)
  swap
  · have f1 : -(h 1) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_11405 h delta _ctx _hno a14 a17 a22 a25 a26 f1
  apply _hno 2
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 1 ≤ (3/25 : ℝ))
  exact ⟨p0, p1⟩

theorem new_node_11328 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a14 : h 0 ≤ (7/38 : ℝ))
    (a15 : h 1 ≤ (8/59 : ℝ))
    (a16 : -(h 4) < (-6/59 : ℝ))
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a22 : -(h 0) < (-2/11 : ℝ))
    (a25 : -(h 1) < (-1/8 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_11330 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (5/27 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/27 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_11331 h delta _ctx _hno a14 f1
  by_cases p2 : h 1 ≤ (4/27 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/27 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_11332 h delta _ctx _hno a15 f2
  by_cases p3 : h 2 ≤ (1/9 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_11333 h delta _ctx _hno a14 a15 a16 a17 a22 a25 f3
  apply _hno 79
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (5/27 : ℝ)) ∧ (h 1 ≤ (4/27 : ℝ)) ∧ (h 2 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_11327 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a14 : h 0 ≤ (7/38 : ℝ))
    (a24 : -(h 0) < (-3/16 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a14 + (1 : ℝ) * a24
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11326 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a23 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a23
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11325 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : h 1 ≤ (8/59 : ℝ))
    (a16 : -(h 4) < (-6/59 : ℝ))
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a20 : -(h 0) < (-1/6 : ℝ))
    (a22 : h 0 ≤ (2/11 : ℝ))
    (a23 : -(h 1) < (-5/41 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_11414 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (5/27 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/27 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_11415 h delta _ctx _hno a22 f1
  by_cases p2 : h 1 ≤ (4/27 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/27 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_11416 h delta _ctx _hno a15 f2
  by_cases p3 : h 2 ≤ (1/9 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_11417 h delta _ctx _hno a15 a16 a17 a20 a22 a23 f3
  apply _hno 79
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (5/27 : ℝ)) ∧ (h 1 ≤ (4/27 : ℝ)) ∧ (h 2 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_11324 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a14 : h 0 ≤ (7/38 : ℝ))
    (a15 : h 1 ≤ (8/59 : ℝ))
    (a16 : -(h 4) < (-6/59 : ℝ))
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a22 : -(h 0) < (-2/11 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_11326 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (3/16 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/16 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_11327 h delta _ctx _hno a14 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_11328 h delta _ctx _hno a14 a15 a16 a17 a22 f2
  by_cases p3 : h 4 ≤ (7/64 : ℝ)
  swap
  · have f3 : -(h 4) < (-7/64 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_11329 h delta _ctx _hno a14 a17 a22 p2 f3
  apply _hno 101
  change (((2 : ℝ) * (delta)) ≤ (7/32 : ℝ)) ∧ (h 0 ≤ (3/16 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (7/64 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_11323 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a21 : ((-2 : ℝ) * (delta)) < (-10/49 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a21
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11322 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : h 1 ≤ (8/59 : ℝ))
    (a16 : -(h 4) < (-6/59 : ℝ))
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a18 : -(h 0) < (-3/20 : ℝ))
    (a20 : h 0 ≤ (1/6 : ℝ))
    (a21 : -(h 1) < (-1/8 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-1/5 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_11971 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (4/25 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/25 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_11972 h delta _ctx _hno a15 a16 a17 a20 a21 f1
  by_cases p2 : h 1 ≤ (2/13 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_11973 h delta _ctx _hno a15 f2
  by_cases p3 : h 2 ≤ (3/25 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_11974 h delta _ctx _hno a15 a17 a18 a21 p1 f3
  by_cases p4 : h 4 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 4) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_11975 h delta _ctx _hno a15 a17 a18 a21 p1 p3 f4
  apply _hno 127
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_11321 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a14 : h 0 ≤ (7/38 : ℝ))
    (a15 : h 1 ≤ (8/59 : ℝ))
    (a16 : -(h 4) < (-6/59 : ℝ))
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a20 : -(h 0) < (-1/6 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (10/49 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-10/49 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_11323 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (2/11 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/11 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_11324 h delta _ctx _hno a14 a15 a16 a17 f1
  by_cases p2 : h 1 ≤ (5/41 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/41 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_11325 h delta _ctx _hno a15 a16 a17 a20 p1 f2
  apply _hno 65
  change (((2 : ℝ) * (delta)) ≤ (10/49 : ℝ)) ∧ (h 0 ≤ (2/11 : ℝ)) ∧ (h 1 ≤ (5/41 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem new_node_11320 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a19 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a19
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11319 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : -(h 3) < (-3/25 : ℝ))
    (a36 : -(h 0) < (-7/48 : ℝ))
    (a43 : -(h 4) < (-7/62 : ℝ))
    (a52 : -(h 1) < (-9/70 : ℝ))
    (a58 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order2 + (1/6 : ℝ) * _ctx.lower + (1/3 : ℝ) * a34 + (1/6 : ℝ) * a36 + (1/6 : ℝ) * a43 + (1/6 : ℝ) * a52 + (1/6 : ℝ) * a58 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11318 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : -(h 3) < (-3/25 : ℝ))
    (a36 : -(h 0) < (-7/48 : ℝ))
    (a49 : -(h 5) < (-2/19 : ℝ))
    (a52 : -(h 1) < (-9/70 : ℝ))
    (a57 : -(h 4) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order2 + (1/6 : ℝ) * _ctx.lower + (1/3 : ℝ) * a34 + (1/6 : ℝ) * a36 + (1/6 : ℝ) * a49 + (1/6 : ℝ) * a52 + (1/6 : ℝ) * a57 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11317 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a33 : h 2 ≤ (4/33 : ℝ))
    (a56 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a56
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11316 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a42 : h 1 ≤ (3/23 : ℝ))
    (a55 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a42 + (1 : ℝ) * a55
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11315 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : -(h 3) < (-3/25 : ℝ))
    (a43 : -(h 4) < (-7/62 : ℝ))
    (a49 : -(h 5) < (-2/19 : ℝ))
    (a52 : -(h 1) < (-9/70 : ℝ))
    (a54 : -(h 0) < (-4/27 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order2 + (1/6 : ℝ) * _ctx.lower + (1/3 : ℝ) * a34 + (1/6 : ℝ) * a43 + (1/6 : ℝ) * a49 + (1/6 : ℝ) * a52 + (1/6 : ℝ) * a54 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11314 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a53 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a53
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11313 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : -(h 3) < (-3/25 : ℝ))
    (a36 : -(h 0) < (-7/48 : ℝ))
    (a39 : -(h 1) < (-5/39 : ℝ))
    (a49 : -(h 5) < (-2/19 : ℝ))
    (a54 : -(h 4) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order2 + (1/6 : ℝ) * _ctx.lower + (1/3 : ℝ) * a34 + (1/6 : ℝ) * a36 + (1/6 : ℝ) * a39 + (1/6 : ℝ) * a49 + (1/6 : ℝ) * a54 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11312 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a33 : h 2 ≤ (4/33 : ℝ))
    (a53 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a53
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11311 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a33 : h 2 ≤ (4/33 : ℝ))
    (a34 : -(h 3) < (-3/25 : ℝ))
    (a36 : -(h 0) < (-7/48 : ℝ))
    (a42 : h 1 ≤ (3/23 : ℝ))
    (a43 : -(h 4) < (-7/62 : ℝ))
    (a49 : -(h 5) < (-2/19 : ℝ))
    (a52 : -(h 1) < (-9/70 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_11314 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (4/27 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/27 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_11315 h delta _ctx _hno a34 a43 a49 a52 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_11316 h delta _ctx _hno a42 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_11317 h delta _ctx _hno a33 f3
  by_cases p4 : h 4 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 4) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_11318 h delta _ctx _hno a34 a36 a49 a52 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_11319 h delta _ctx _hno a34 a36 a43 a52 f5
  apply _hno 262
  change (((2 : ℝ) * (delta)) ≤ (8/39 : ℝ)) ∧ (h 0 ≤ (4/27 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_11310 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a41 : h 0 ≤ (3/20 : ℝ))
    (a51 : -(h 0) < (-7/45 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a41 + (1 : ℝ) * a51
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11309 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a50 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11308 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a33 : h 2 ≤ (4/33 : ℝ))
    (a34 : -(h 3) < (-3/25 : ℝ))
    (a36 : -(h 0) < (-7/48 : ℝ))
    (a39 : -(h 1) < (-5/39 : ℝ))
    (a41 : h 0 ≤ (3/20 : ℝ))
    (a42 : h 1 ≤ (3/23 : ℝ))
    (a43 : -(h 4) < (-7/62 : ℝ))
    (a49 : -(h 5) < (-2/19 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_11309 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (7/45 : ℝ)
  swap
  · have f1 : -(h 0) < (-7/45 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_11310 h delta _ctx _hno a41 f1
  by_cases p2 : h 1 ≤ (9/70 : ℝ)
  swap
  · have f2 : -(h 1) < (-9/70 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_11311 h delta _ctx _hno a13 a33 a34 a36 a42 a43 a49 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_11312 h delta _ctx _hno a33 f3
  by_cases p4 : h 4 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 4) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_11313 h delta _ctx _hno a34 a36 a39 a49 f4
  apply _hno 111
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (7/45 : ℝ)) ∧ (h 1 ≤ (9/70 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (4/35 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_11307 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a33 : h 2 ≤ (4/33 : ℝ))
    (a48 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * _ctx.order2 + (1 : ℝ) * a33 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11306 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a33 : h 2 ≤ (4/33 : ℝ))
    (a47 : -(h 2) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11305 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a42 : h 1 ≤ (3/23 : ℝ))
    (a46 : -(h 1) < (-5/38 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a42 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11304 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a41 : h 0 ≤ (3/20 : ℝ))
    (a45 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a41 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11303 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a44 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11302 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : -(h 4) < (-1/9 : ℝ))
    (a34 : -(h 3) < (-3/25 : ℝ))
    (a36 : -(h 0) < (-7/48 : ℝ))
    (a42 : -(h 1) < (-3/23 : ℝ))
    (a54 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order2 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a26 + (1/3 : ℝ) * a34 + (1/6 : ℝ) * a36 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a54 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11301 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : -(h 3) < (-3/25 : ℝ))
    (a36 : -(h 0) < (-7/48 : ℝ))
    (a42 : -(h 1) < (-3/23 : ℝ))
    (a48 : -(h 5) < (-2/19 : ℝ))
    (a53 : -(h 4) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order2 + (1/6 : ℝ) * _ctx.lower + (1/3 : ℝ) * a34 + (1/6 : ℝ) * a36 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a48 + (1/6 : ℝ) * a53 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11300 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a33 : h 2 ≤ (4/33 : ℝ))
    (a52 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a52
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11299 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a45 : h 1 ≤ (5/38 : ℝ))
    (a51 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a45 + (1 : ℝ) * a51
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11298 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : -(h 4) < (-1/9 : ℝ))
    (a34 : -(h 3) < (-3/25 : ℝ))
    (a42 : -(h 1) < (-3/23 : ℝ))
    (a48 : -(h 5) < (-2/19 : ℝ))
    (a50 : -(h 0) < (-4/27 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order2 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a26 + (1/3 : ℝ) * a34 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a48 + (1/6 : ℝ) * a50 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11297 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a49 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11296 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : -(h 4) < (-1/9 : ℝ))
    (a34 : -(h 3) < (-3/25 : ℝ))
    (a45 : -(h 1) < (-5/38 : ℝ))
    (a47 : -(h 0) < (-4/27 : ℝ))
    (a54 : -(h 5) < (-2/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order2 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a26 + (1/3 : ℝ) * a34 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * a54 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11295 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : -(h 3) < (-3/25 : ℝ))
    (a45 : -(h 1) < (-5/38 : ℝ))
    (a47 : -(h 0) < (-4/27 : ℝ))
    (a53 : -(h 4) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order2 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (2/5 : ℝ) * a34 + (1/5 : ℝ) * a45 + (1/5 : ℝ) * a47 + (1/5 : ℝ) * a53 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11294 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a33 : h 2 ≤ (4/33 : ℝ))
    (a52 : -(h 3) < (-5/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * _ctx.order2 + (1 : ℝ) * a33 + (1 : ℝ) * a52
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11293 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a33 : h 2 ≤ (4/33 : ℝ))
    (a51 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a51
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11292 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : h 1 ≤ (2/15 : ℝ))
    (a50 : -(h 1) < (-3/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a24 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11291 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a41 : h 0 ≤ (3/20 : ℝ))
    (a49 : -(h 0) < (-5/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a41 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11290 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a48 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11289 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : -(h 4) < (-1/9 : ℝ))
    (a34 : -(h 3) < (-3/25 : ℝ))
    (a36 : -(h 0) < (-7/48 : ℝ))
    (a45 : -(h 1) < (-5/38 : ℝ))
    (a51 : -(h 5) < (-2/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order2 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a26 + (1/3 : ℝ) * a34 + (1/6 : ℝ) * a36 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a51 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11288 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : -(h 3) < (-3/25 : ℝ))
    (a36 : -(h 0) < (-7/48 : ℝ))
    (a45 : -(h 1) < (-5/38 : ℝ))
    (a50 : -(h 4) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order2 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (2/5 : ℝ) * a34 + (1/5 : ℝ) * a36 + (1/5 : ℝ) * a45 + (1/5 : ℝ) * a50 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11287 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a33 : h 2 ≤ (4/33 : ℝ))
    (a49 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11286 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : h 1 ≤ (2/15 : ℝ))
    (a48 : -(h 1) < (-6/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a24 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11285 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a24 : h 1 ≤ (2/15 : ℝ))
    (a26 : -(h 4) < (-1/9 : ℝ))
    (a33 : h 2 ≤ (4/33 : ℝ))
    (a34 : -(h 3) < (-3/25 : ℝ))
    (a41 : h 0 ≤ (3/20 : ℝ))
    (a45 : -(h 1) < (-5/38 : ℝ))
    (a47 : -(h 0) < (-4/27 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_11290 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (5/33 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/33 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_11291 h delta _ctx _hno a41 f1
  by_cases p2 : h 1 ≤ (3/22 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_11292 h delta _ctx _hno a24 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_11293 h delta _ctx _hno a33 f3
  by_cases p4 : h 3 ≤ (5/41 : ℝ)
  swap
  · have f4 : -(h 3) < (-5/41 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_11294 h delta _ctx _hno a33 f4
  by_cases p5 : h 4 ≤ (2/17 : ℝ)
  swap
  · have f5 : -(h 4) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_11295 h delta _ctx _hno a34 a45 a47 f5
  by_cases p6 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f6 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact new_node_11296 h delta _ctx _hno a26 a34 a45 a47 f6
  apply _hno 229
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (5/33 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (5/41 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem new_node_11284 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a46 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11283 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a26 : -(h 4) < (-1/9 : ℝ))
    (a33 : h 2 ≤ (4/33 : ℝ))
    (a34 : -(h 3) < (-3/25 : ℝ))
    (a36 : -(h 0) < (-7/48 : ℝ))
    (a42 : -(h 1) < (-3/23 : ℝ))
    (a45 : h 1 ≤ (5/38 : ℝ))
    (a48 : -(h 5) < (-2/19 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_11297 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (4/27 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/27 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_11298 h delta _ctx _hno a26 a34 a42 a48 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_11299 h delta _ctx _hno a45 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_11300 h delta _ctx _hno a33 f3
  by_cases p4 : h 4 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 4) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_11301 h delta _ctx _hno a34 a36 a42 a48 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_11302 h delta _ctx _hno a26 a34 a36 a42 f5
  apply _hno 262
  change (((2 : ℝ) * (delta)) ≤ (8/39 : ℝ)) ∧ (h 0 ≤ (4/27 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_11282 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a33 : h 2 ≤ (4/33 : ℝ))
    (a47 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * _ctx.order2 + (1 : ℝ) * a33 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11281 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a33 : h 2 ≤ (4/33 : ℝ))
    (a46 : -(h 2) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11280 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a24 : h 1 ≤ (2/15 : ℝ))
    (a26 : -(h 4) < (-1/9 : ℝ))
    (a33 : h 2 ≤ (4/33 : ℝ))
    (a34 : -(h 3) < (-3/25 : ℝ))
    (a36 : -(h 0) < (-7/48 : ℝ))
    (a41 : h 0 ≤ (3/20 : ℝ))
    (a45 : -(h 1) < (-5/38 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_11284 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (4/27 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/27 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_11285 h delta _ctx _hno a13 a24 a26 a33 a34 a41 a45 f1
  by_cases p2 : h 1 ≤ (6/41 : ℝ)
  swap
  · have f2 : -(h 1) < (-6/41 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_11286 h delta _ctx _hno a24 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_11287 h delta _ctx _hno a33 f3
  by_cases p4 : h 4 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 4) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_11288 h delta _ctx _hno a34 a36 a45 f4
  by_cases p5 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_11289 h delta _ctx _hno a26 a34 a36 a45 f5
  apply _hno 61
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (4/27 : ℝ)) ∧ (h 1 ≤ (6/41 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_11279 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a41 : h 0 ≤ (3/20 : ℝ))
    (a44 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a41 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11278 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11277 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : -(h 4) < (-1/9 : ℝ))
    (a34 : -(h 3) < (-3/25 : ℝ))
    (a41 : -(h 0) < (-3/20 : ℝ))
    (a44 : -(h 1) < (-5/38 : ℝ))
    (a51 : -(h 5) < (-2/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order2 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a26 + (1/3 : ℝ) * a34 + (1/6 : ℝ) * a41 + (1/6 : ℝ) * a44 + (1/6 : ℝ) * a51 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11276 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : -(h 3) < (-3/25 : ℝ))
    (a41 : -(h 0) < (-3/20 : ℝ))
    (a44 : -(h 1) < (-5/38 : ℝ))
    (a50 : -(h 4) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order2 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (2/5 : ℝ) * a34 + (1/5 : ℝ) * a41 + (1/5 : ℝ) * a44 + (1/5 : ℝ) * a50 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11275 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a33 : h 2 ≤ (4/33 : ℝ))
    (a49 : -(h 3) < (-5/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * _ctx.order2 + (1 : ℝ) * a33 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

end RealPinwheel.WeakSevenBandData
