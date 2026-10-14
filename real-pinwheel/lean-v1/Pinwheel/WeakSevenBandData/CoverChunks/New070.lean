import Pinwheel.WeakSevenBandData.CoverChunks.New069

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem new_node_7514 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a34
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7513 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : -(h 1) < (-8/59 : ℝ))
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a23 : -(h 0) < (-6/35 : ℝ))
    (a30 : h 1 ≤ (1/7 : ℝ))
    (a31 : -(h 3) < (-3/28 : ℝ))
    (a33 : h 0 ≤ (4/23 : ℝ))
    (a36 : h 4 ≤ (4/39 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_7525 h delta _ctx _hno a16 f0
  by_cases p1 : h 0 ≤ (4/23 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/23 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_7526 h delta _ctx _hno a33 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_7527 h delta _ctx _hno a30 f2
  by_cases p3 : h 2 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_7528 h delta _ctx _hno a15 a16 a23 a31 a33 a36 f3
  by_cases p4 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_7529 h delta _ctx _hno a15 a23 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_7530 h delta _ctx _hno a36 f5
  apply _hno 13
  change (((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)) ∧ (h 0 ≤ (4/23 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_7512 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : -(h 1) < (-8/59 : ℝ))
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a23 : -(h 0) < (-6/35 : ℝ))
    (a27 : -(h 2) < (-1/9 : ℝ))
    (a31 : -(h 3) < (-3/28 : ℝ))
    (a33 : h 0 ≤ (4/23 : ℝ))
    (a36 : -(h 4) < (-4/39 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_7519 h delta _ctx _hno a16 f0
  by_cases p1 : h 0 ≤ (4/23 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/23 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_7520 h delta _ctx _hno a33 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_7521 h delta _ctx _hno a23 a27 a31 a36 f2
  by_cases p3 : h 2 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_7522 h delta _ctx _hno a15 a23 a31 a36 f3
  by_cases p4 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_7523 h delta _ctx _hno a15 a23 a36 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_7524 h delta _ctx _hno a15 a23 f5
  apply _hno 13
  change (((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)) ∧ (h 0 ≤ (4/23 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_7511 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a20 : h 2 ≤ (1/8 : ℝ))
    (a35 : -(h 2) < (-5/39 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a20 + (1 : ℝ) * a35
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7510 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a30 : h 1 ≤ (1/7 : ℝ))
    (a34 : -(h 1) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a34
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7509 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : -(h 1) < (-8/59 : ℝ))
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a27 : -(h 2) < (-1/9 : ℝ))
    (a29 : h 0 ≤ (5/28 : ℝ))
    (a31 : -(h 3) < (-3/28 : ℝ))
    (a33 : -(h 0) < (-4/23 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_7514 h delta _ctx _hno a16 f0
  by_cases p1 : h 0 ≤ (5/28 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/28 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_7515 h delta _ctx _hno a29 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_7516 h delta _ctx _hno a27 a31 a33 f2
  by_cases p3 : h 2 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_7517 h delta _ctx _hno a15 a31 a33 f3
  by_cases p4 : h 4 ≤ (3/28 : ℝ)
  swap
  · have f4 : -(h 4) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_7518 h delta _ctx _hno a15 a27 a31 a33 f4
  apply _hno 83
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (5/28 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (3/28 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_7508 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a32 : ((-2 : ℝ) * (delta)) < (-1/5 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a32
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7507 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : -(h 0) < (-6/35 : ℝ))
    (a30 : -(h 1) < (-1/7 : ℝ))
    (a45 : -(h 2) < (-3/26 : ℝ))
    (a55 : -(h 3) < (-2/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.order4 + (1/2 : ℝ) * _ctx.min + (3/4 : ℝ) * _ctx.lower + (1/4 : ℝ) * a23 + (1/4 : ℝ) * a30 + (1/4 : ℝ) * a45 + (1/4 : ℝ) * a55 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7506 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : -(h 0) < (-6/35 : ℝ))
    (a30 : -(h 1) < (-1/7 : ℝ))
    (a50 : -(h 3) < (-3/29 : ℝ))
    (a54 : -(h 2) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.order4 + (1/2 : ℝ) * _ctx.min + (3/4 : ℝ) * _ctx.lower + (1/4 : ℝ) * a23 + (1/4 : ℝ) * a30 + (1/4 : ℝ) * a50 + (1/4 : ℝ) * a54 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7505 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : h 1 ≤ (4/27 : ℝ))
    (a53 : -(h 1) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a26 + (1 : ℝ) * a53
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7504 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a47 : h 0 ≤ (5/29 : ℝ))
    (a52 : -(h 0) < (-3/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a47 + (1 : ℝ) * a52
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7503 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a51 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a51
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7502 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a30 : -(h 1) < (-1/7 : ℝ))
    (a45 : -(h 2) < (-3/26 : ℝ))
    (a47 : -(h 0) < (-5/29 : ℝ))
    (a52 : -(h 3) < (-2/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.order4 + (1/2 : ℝ) * _ctx.min + (3/4 : ℝ) * _ctx.lower + (1/4 : ℝ) * a30 + (1/4 : ℝ) * a45 + (1/4 : ℝ) * a47 + (1/4 : ℝ) * a52 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7501 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a30 : -(h 1) < (-1/7 : ℝ))
    (a41 : -(h 3) < (-4/39 : ℝ))
    (a47 : -(h 0) < (-5/29 : ℝ))
    (a51 : -(h 2) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.order4 + (1/2 : ℝ) * _ctx.min + (3/4 : ℝ) * _ctx.lower + (1/4 : ℝ) * a30 + (1/4 : ℝ) * a41 + (1/4 : ℝ) * a47 + (1/4 : ℝ) * a51 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7500 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : h 1 ≤ (4/27 : ℝ))
    (a50 : -(h 1) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a26 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7499 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a32 : h 0 ≤ (4/23 : ℝ))
    (a49 : -(h 0) < (-3/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a32 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7498 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a48 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7497 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a23 : -(h 0) < (-6/35 : ℝ))
    (a26 : h 1 ≤ (4/27 : ℝ))
    (a30 : -(h 1) < (-1/7 : ℝ))
    (a45 : -(h 2) < (-3/26 : ℝ))
    (a47 : h 0 ≤ (5/29 : ℝ))
    (a50 : -(h 3) < (-3/29 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_7503 h delta _ctx _hno a16 f0
  by_cases p1 : h 0 ≤ (3/17 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/17 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_7504 h delta _ctx _hno a47 f1
  by_cases p2 : h 1 ≤ (1/6 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_7505 h delta _ctx _hno a26 f2
  by_cases p3 : h 2 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_7506 h delta _ctx _hno a23 a30 a50 f3
  by_cases p4 : h 3 ≤ (2/19 : ℝ)
  swap
  · have f4 : -(h 3) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_7507 h delta _ctx _hno a23 a30 a45 f4
  apply _hno 163
  change (((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)) ∧ (h 0 ≤ (3/17 : ℝ)) ∧ (h 1 ≤ (1/6 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 3 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_7496 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a20 : h 2 ≤ (1/8 : ℝ))
    (a49 : -(h 2) < (-3/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a20 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7495 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : h 1 ≤ (4/27 : ℝ))
    (a48 : -(h 1) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a26 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7494 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a26 : h 1 ≤ (4/27 : ℝ))
    (a30 : -(h 1) < (-1/7 : ℝ))
    (a32 : h 0 ≤ (4/23 : ℝ))
    (a41 : -(h 3) < (-4/39 : ℝ))
    (a45 : -(h 2) < (-3/26 : ℝ))
    (a47 : -(h 0) < (-5/29 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_7498 h delta _ctx _hno a16 f0
  by_cases p1 : h 0 ≤ (3/17 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/17 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_7499 h delta _ctx _hno a32 f1
  by_cases p2 : h 1 ≤ (1/6 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_7500 h delta _ctx _hno a26 f2
  by_cases p3 : h 2 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_7501 h delta _ctx _hno a30 a41 a47 f3
  by_cases p4 : h 3 ≤ (2/19 : ℝ)
  swap
  · have f4 : -(h 3) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_7502 h delta _ctx _hno a30 a45 a47 f4
  apply _hno 163
  change (((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)) ∧ (h 0 ≤ (3/17 : ℝ)) ∧ (h 1 ≤ (1/6 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 3 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_7493 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a46 : ((-2 : ℝ) * (delta)) < (-1/5 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7492 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a35 : h 4 ≤ (4/39 : ℝ))
    (a47 : -(h 4) < (-3/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a35 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7491 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : -(h 0) < (-6/35 : ℝ))
    (a27 : -(h 2) < (-1/9 : ℝ))
    (a30 : -(h 1) < (-1/7 : ℝ))
    (a46 : -(h 3) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.order4 + (1/2 : ℝ) * _ctx.min + (3/4 : ℝ) * _ctx.lower + (1/4 : ℝ) * a23 + (1/4 : ℝ) * a27 + (1/4 : ℝ) * a30 + (1/4 : ℝ) * a46 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7490 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a20 : h 2 ≤ (1/8 : ℝ))
    (a23 : -(h 0) < (-6/35 : ℝ))
    (a26 : h 1 ≤ (4/27 : ℝ))
    (a30 : -(h 1) < (-1/7 : ℝ))
    (a32 : h 0 ≤ (4/23 : ℝ))
    (a41 : -(h 3) < (-4/39 : ℝ))
    (a45 : -(h 2) < (-3/26 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-1/5 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_7493 h delta _ctx _hno a16 f0
  by_cases p1 : h 0 ≤ (5/29 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/29 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_7494 h delta _ctx _hno a16 a26 a30 a32 a41 a45 f1
  by_cases p2 : h 1 ≤ (1/6 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_7495 h delta _ctx _hno a26 f2
  by_cases p3 : h 2 ≤ (3/22 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_7496 h delta _ctx _hno a20 f3
  by_cases p4 : h 3 ≤ (3/29 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/29 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_7497 h delta _ctx _hno a16 a23 a26 a30 a45 p1 f4
  apply _hno 6
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 0 ≤ (5/29 : ℝ)) ∧ (h 1 ≤ (1/6 : ℝ)) ∧ (h 2 ≤ (3/22 : ℝ)) ∧ (h 3 ≤ (3/29 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_7489 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : h 1 ≤ (4/27 : ℝ))
    (a44 : -(h 1) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a26 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7488 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a32 : h 0 ≤ (4/23 : ℝ))
    (a43 : -(h 0) < (-5/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a32 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7487 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a42 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7486 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a20 : h 2 ≤ (1/8 : ℝ))
    (a23 : -(h 0) < (-6/35 : ℝ))
    (a26 : h 1 ≤ (4/27 : ℝ))
    (a27 : -(h 2) < (-1/9 : ℝ))
    (a30 : -(h 1) < (-1/7 : ℝ))
    (a32 : h 0 ≤ (4/23 : ℝ))
    (a35 : h 4 ≤ (4/39 : ℝ))
    (a41 : -(h 3) < (-4/39 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_7487 h delta _ctx _hno a16 f0
  by_cases p1 : h 0 ≤ (5/26 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/26 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_7488 h delta _ctx _hno a32 f1
  by_cases p2 : h 1 ≤ (2/13 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_7489 h delta _ctx _hno a26 f2
  by_cases p3 : h 2 ≤ (3/26 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_7490 h delta _ctx _hno a16 a20 a23 a26 a30 a32 a41 f3
  by_cases p4 : h 3 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_7491 h delta _ctx _hno a23 a27 a30 f4
  by_cases p5 : h 4 ≤ (3/29 : ℝ)
  swap
  · have f5 : -(h 4) < (-3/29 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_7492 h delta _ctx _hno a35 f5
  apply _hno 166
  change (((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)) ∧ (h 0 ≤ (5/26 : ℝ)) ∧ (h 1 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (3/26 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ)) ∧ (h 4 ≤ (3/29 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_7485 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a20 : h 2 ≤ (1/8 : ℝ))
    (a40 : -(h 2) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a20 + (1 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7484 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : h 1 ≤ (4/27 : ℝ))
    (a39 : -(h 1) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a26 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7483 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a32 : h 0 ≤ (4/23 : ℝ))
    (a38 : -(h 0) < (-3/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a32 + (1 : ℝ) * a38
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7482 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a37 : ((-2 : ℝ) * (delta)) < (-1/5 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a37
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7481 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : -(h 0) < (-6/35 : ℝ))
    (a27 : -(h 2) < (-1/9 : ℝ))
    (a30 : -(h 1) < (-1/7 : ℝ))
    (a46 : -(h 4) < (-3/29 : ℝ))
    (a51 : -(h 3) < (-2/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a23 + (1/5 : ℝ) * a27 + (1/5 : ℝ) * a30 + (1/5 : ℝ) * a46 + (1/5 : ℝ) * a51 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7480 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a44 : h 2 ≤ (3/26 : ℝ))
    (a50 : -(h 2) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a44 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7479 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : h 1 ≤ (4/27 : ℝ))
    (a49 : -(h 1) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a26 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7478 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a37 : h 0 ≤ (5/29 : ℝ))
    (a48 : -(h 0) < (-3/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a37 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7477 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a47 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7476 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a23 : -(h 0) < (-6/35 : ℝ))
    (a26 : h 1 ≤ (4/27 : ℝ))
    (a27 : -(h 2) < (-1/9 : ℝ))
    (a30 : -(h 1) < (-1/7 : ℝ))
    (a37 : h 0 ≤ (5/29 : ℝ))
    (a44 : h 2 ≤ (3/26 : ℝ))
    (a46 : -(h 4) < (-3/29 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_7477 h delta _ctx _hno a16 f0
  by_cases p1 : h 0 ≤ (3/17 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/17 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_7478 h delta _ctx _hno a37 f1
  by_cases p2 : h 1 ≤ (1/6 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_7479 h delta _ctx _hno a26 f2
  by_cases p3 : h 2 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_7480 h delta _ctx _hno a44 f3
  by_cases p4 : h 3 ≤ (2/19 : ℝ)
  swap
  · have f4 : -(h 3) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_7481 h delta _ctx _hno a23 a27 a30 a46 f4
  apply _hno 163
  change (((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)) ∧ (h 0 ≤ (3/17 : ℝ)) ∧ (h 1 ≤ (1/6 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 3 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_7475 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : -(h 0) < (-6/35 : ℝ))
    (a27 : -(h 2) < (-1/9 : ℝ))
    (a30 : -(h 1) < (-1/7 : ℝ))
    (a35 : -(h 4) < (-4/39 : ℝ))
    (a45 : -(h 3) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a23 + (1/5 : ℝ) * a27 + (1/5 : ℝ) * a30 + (1/5 : ℝ) * a35 + (1/5 : ℝ) * a45 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7474 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : -(h 0) < (-6/35 : ℝ))
    (a30 : -(h 1) < (-1/7 : ℝ))
    (a35 : -(h 4) < (-4/39 : ℝ))
    (a40 : -(h 3) < (-3/29 : ℝ))
    (a44 : -(h 2) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a23 + (1/5 : ℝ) * a30 + (1/5 : ℝ) * a35 + (1/5 : ℝ) * a40 + (1/5 : ℝ) * a44 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7473 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : h 1 ≤ (4/27 : ℝ))
    (a43 : -(h 1) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a26 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7472 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a37 : h 0 ≤ (5/29 : ℝ))
    (a42 : -(h 0) < (-5/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a37 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7471 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7470 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : -(h 2) < (-1/9 : ℝ))
    (a30 : -(h 1) < (-1/7 : ℝ))
    (a37 : -(h 0) < (-5/29 : ℝ))
    (a43 : -(h 4) < (-3/29 : ℝ))
    (a48 : -(h 3) < (-2/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a27 + (1/5 : ℝ) * a30 + (1/5 : ℝ) * a37 + (1/5 : ℝ) * a43 + (1/5 : ℝ) * a48 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7469 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a41 : h 2 ≤ (3/26 : ℝ))
    (a47 : -(h 2) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a41 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7468 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : h 1 ≤ (4/27 : ℝ))
    (a46 : -(h 1) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a26 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7467 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a32 : h 0 ≤ (4/23 : ℝ))
    (a45 : -(h 0) < (-3/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a32 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7466 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a44 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7465 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a26 : h 1 ≤ (4/27 : ℝ))
    (a27 : -(h 2) < (-1/9 : ℝ))
    (a30 : -(h 1) < (-1/7 : ℝ))
    (a32 : h 0 ≤ (4/23 : ℝ))
    (a37 : -(h 0) < (-5/29 : ℝ))
    (a41 : h 2 ≤ (3/26 : ℝ))
    (a43 : -(h 4) < (-3/29 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_7466 h delta _ctx _hno a16 f0
  by_cases p1 : h 0 ≤ (3/17 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/17 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_7467 h delta _ctx _hno a32 f1
  by_cases p2 : h 1 ≤ (1/6 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_7468 h delta _ctx _hno a26 f2
  by_cases p3 : h 2 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_7469 h delta _ctx _hno a41 f3
  by_cases p4 : h 3 ≤ (2/19 : ℝ)
  swap
  · have f4 : -(h 3) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_7470 h delta _ctx _hno a27 a30 a37 a43 f4
  apply _hno 163
  change (((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)) ∧ (h 0 ≤ (3/17 : ℝ)) ∧ (h 1 ≤ (1/6 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 3 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_7464 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : -(h 2) < (-1/9 : ℝ))
    (a30 : -(h 1) < (-1/7 : ℝ))
    (a35 : -(h 4) < (-4/39 : ℝ))
    (a37 : -(h 0) < (-5/29 : ℝ))
    (a42 : -(h 3) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a27 + (1/5 : ℝ) * a30 + (1/5 : ℝ) * a35 + (1/5 : ℝ) * a37 + (1/5 : ℝ) * a42 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7463 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a30 : -(h 1) < (-1/7 : ℝ))
    (a35 : -(h 4) < (-4/39 : ℝ))
    (a37 : -(h 0) < (-5/29 : ℝ))
    (a41 : -(h 2) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a30 + (2/5 : ℝ) * a35 + (1/5 : ℝ) * a37 + (1/5 : ℝ) * a41 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7462 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : h 1 ≤ (4/27 : ℝ))
    (a40 : -(h 1) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a26 + (1 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7461 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a32 : h 0 ≤ (4/23 : ℝ))
    (a39 : -(h 0) < (-5/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a32 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7460 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a38 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a38
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7459 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a23 : -(h 0) < (-6/35 : ℝ))
    (a26 : h 1 ≤ (4/27 : ℝ))
    (a27 : -(h 2) < (-1/9 : ℝ))
    (a30 : -(h 1) < (-1/7 : ℝ))
    (a35 : -(h 4) < (-4/39 : ℝ))
    (a37 : h 0 ≤ (5/29 : ℝ))
    (a40 : -(h 3) < (-3/29 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_7471 h delta _ctx _hno a16 f0
  by_cases p1 : h 0 ≤ (5/26 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/26 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_7472 h delta _ctx _hno a37 f1
  by_cases p2 : h 1 ≤ (2/13 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_7473 h delta _ctx _hno a26 f2
  by_cases p3 : h 2 ≤ (3/26 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_7474 h delta _ctx _hno a23 a30 a35 a40 f3
  by_cases p4 : h 3 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_7475 h delta _ctx _hno a23 a27 a30 a35 f4
  by_cases p5 : h 4 ≤ (3/29 : ℝ)
  swap
  · have f5 : -(h 4) < (-3/29 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_7476 h delta _ctx _hno a16 a23 a26 a27 a30 a37 p3 f5
  apply _hno 166
  change (((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)) ∧ (h 0 ≤ (5/26 : ℝ)) ∧ (h 1 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (3/26 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ)) ∧ (h 4 ≤ (3/29 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_7458 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a20 : h 2 ≤ (1/8 : ℝ))
    (a39 : -(h 2) < (-3/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a20 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7457 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : h 1 ≤ (4/27 : ℝ))
    (a38 : -(h 1) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a26 + (1 : ℝ) * a38
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7456 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a26 : h 1 ≤ (4/27 : ℝ))
    (a27 : -(h 2) < (-1/9 : ℝ))
    (a30 : -(h 1) < (-1/7 : ℝ))
    (a32 : h 0 ≤ (4/23 : ℝ))
    (a35 : -(h 4) < (-4/39 : ℝ))
    (a37 : -(h 0) < (-5/29 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_7460 h delta _ctx _hno a16 f0
  by_cases p1 : h 0 ≤ (5/26 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/26 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_7461 h delta _ctx _hno a32 f1
  by_cases p2 : h 1 ≤ (2/13 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_7462 h delta _ctx _hno a26 f2
  by_cases p3 : h 2 ≤ (3/26 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_7463 h delta _ctx _hno a30 a35 a37 f3
  by_cases p4 : h 3 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_7464 h delta _ctx _hno a27 a30 a35 a37 f4
  by_cases p5 : h 4 ≤ (3/29 : ℝ)
  swap
  · have f5 : -(h 4) < (-3/29 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_7465 h delta _ctx _hno a16 a26 a27 a30 a32 a37 p3 f5
  apply _hno 166
  change (((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)) ∧ (h 0 ≤ (5/26 : ℝ)) ∧ (h 1 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (3/26 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ)) ∧ (h 4 ≤ (3/29 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_7455 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a36 : ((-2 : ℝ) * (delta)) < (-1/5 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a36
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7454 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : -(h 2) < (-1/9 : ℝ))
    (a30 : -(h 1) < (-1/7 : ℝ))
    (a32 : -(h 0) < (-4/23 : ℝ))
    (a43 : -(h 4) < (-3/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a27 + (1/5 : ℝ) * a30 + (1/5 : ℝ) * a32 + (2/5 : ℝ) * a43 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7453 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : -(h 2) < (-1/9 : ℝ))
    (a30 : -(h 1) < (-1/7 : ℝ))
    (a32 : -(h 0) < (-4/23 : ℝ))
    (a42 : -(h 3) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.order4 + (1/2 : ℝ) * _ctx.min + (3/4 : ℝ) * _ctx.lower + (1/4 : ℝ) * a27 + (1/4 : ℝ) * a30 + (1/4 : ℝ) * a32 + (1/4 : ℝ) * a42 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7452 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a30 : -(h 1) < (-1/7 : ℝ))
    (a32 : -(h 0) < (-4/23 : ℝ))
    (a37 : -(h 3) < (-4/39 : ℝ))
    (a41 : -(h 2) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.order4 + (1/2 : ℝ) * _ctx.min + (3/4 : ℝ) * _ctx.lower + (1/4 : ℝ) * a30 + (1/4 : ℝ) * a32 + (1/4 : ℝ) * a37 + (1/4 : ℝ) * a41 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7451 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : h 1 ≤ (4/27 : ℝ))
    (a40 : -(h 1) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a26 + (1 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7450 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : h 0 ≤ (3/17 : ℝ))
    (a39 : -(h 0) < (-5/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7449 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a38 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a38
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7448 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : -(h 2) < (-1/9 : ℝ))
    (a30 : -(h 1) < (-1/7 : ℝ))
    (a34 : -(h 0) < (-3/17 : ℝ))
    (a40 : -(h 4) < (-3/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a27 + (1/5 : ℝ) * a30 + (1/5 : ℝ) * a34 + (2/5 : ℝ) * a40 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7447 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : -(h 2) < (-1/9 : ℝ))
    (a30 : -(h 1) < (-1/7 : ℝ))
    (a34 : -(h 0) < (-3/17 : ℝ))
    (a39 : -(h 3) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.order4 + (1/2 : ℝ) * _ctx.min + (3/4 : ℝ) * _ctx.lower + (1/4 : ℝ) * a27 + (1/4 : ℝ) * a30 + (1/4 : ℝ) * a34 + (1/4 : ℝ) * a39 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7446 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a30 : -(h 1) < (-1/7 : ℝ))
    (a34 : -(h 0) < (-3/17 : ℝ))
    (a38 : -(h 2) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order3 + (2/3 : ℝ) * _ctx.order4 + (1 : ℝ) * _ctx.min + (4/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * a30 + (1/3 : ℝ) * a34 + (1/3 : ℝ) * a38 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7445 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : h 1 ≤ (4/27 : ℝ))
    (a37 : -(h 1) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a26 + (1 : ℝ) * a37
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7444 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a29 : h 0 ≤ (5/28 : ℝ))
    (a36 : -(h 0) < (-5/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a36
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7443 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a35 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a35
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7442 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a26 : h 1 ≤ (4/27 : ℝ))
    (a27 : -(h 2) < (-1/9 : ℝ))
    (a30 : -(h 1) < (-1/7 : ℝ))
    (a32 : -(h 0) < (-4/23 : ℝ))
    (a34 : h 0 ≤ (3/17 : ℝ))
    (a37 : -(h 3) < (-4/39 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_7449 h delta _ctx _hno a16 f0
  by_cases p1 : h 0 ≤ (5/26 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/26 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_7450 h delta _ctx _hno a34 f1
  by_cases p2 : h 1 ≤ (2/13 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_7451 h delta _ctx _hno a26 f2
  by_cases p3 : h 2 ≤ (3/26 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_7452 h delta _ctx _hno a30 a32 a37 f3
  by_cases p4 : h 3 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_7453 h delta _ctx _hno a27 a30 a32 f4
  by_cases p5 : h 4 ≤ (3/29 : ℝ)
  swap
  · have f5 : -(h 4) < (-3/29 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_7454 h delta _ctx _hno a27 a30 a32 f5
  apply _hno 166
  change (((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)) ∧ (h 0 ≤ (5/26 : ℝ)) ∧ (h 1 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (3/26 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ)) ∧ (h 4 ≤ (3/29 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_7441 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a20 : h 2 ≤ (1/8 : ℝ))
    (a36 : -(h 2) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a20 + (1 : ℝ) * a36
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7440 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : h 1 ≤ (4/27 : ℝ))
    (a35 : -(h 1) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a26 + (1 : ℝ) * a35
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7439 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a26 : h 1 ≤ (4/27 : ℝ))
    (a27 : -(h 2) < (-1/9 : ℝ))
    (a29 : h 0 ≤ (5/28 : ℝ))
    (a30 : -(h 1) < (-1/7 : ℝ))
    (a34 : -(h 0) < (-3/17 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_7443 h delta _ctx _hno a16 f0
  by_cases p1 : h 0 ≤ (5/26 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/26 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_7444 h delta _ctx _hno a29 f1
  by_cases p2 : h 1 ≤ (2/13 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_7445 h delta _ctx _hno a26 f2
  by_cases p3 : h 2 ≤ (3/26 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_7446 h delta _ctx _hno a30 a34 f3
  by_cases p4 : h 3 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_7447 h delta _ctx _hno a27 a30 a34 f4
  by_cases p5 : h 4 ≤ (3/29 : ℝ)
  swap
  · have f5 : -(h 4) < (-3/29 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_7448 h delta _ctx _hno a27 a30 a34 f5
  apply _hno 166
  change (((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)) ∧ (h 0 ≤ (5/26 : ℝ)) ∧ (h 1 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (3/26 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ)) ∧ (h 4 ≤ (3/29 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_7438 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a33 : ((-2 : ℝ) * (delta)) < (-1/5 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a33
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_7437 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a20 : h 2 ≤ (1/8 : ℝ))
    (a23 : -(h 0) < (-6/35 : ℝ))
    (a26 : h 1 ≤ (4/27 : ℝ))
    (a27 : -(h 2) < (-1/9 : ℝ))
    (a30 : -(h 1) < (-1/7 : ℝ))
    (a32 : h 0 ≤ (4/23 : ℝ))
    (a35 : h 4 ≤ (4/39 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-1/5 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_7482 h delta _ctx _hno a16 f0
  by_cases p1 : h 0 ≤ (3/17 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/17 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_7483 h delta _ctx _hno a32 f1
  by_cases p2 : h 1 ≤ (2/13 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_7484 h delta _ctx _hno a26 f2
  by_cases p3 : h 2 ≤ (1/7 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_7485 h delta _ctx _hno a20 f3
  by_cases p4 : h 3 ≤ (4/39 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/39 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_7486 h delta _ctx _hno a16 a20 a23 a26 a27 a30 a32 a35 f4
  apply _hno 34
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 0 ≤ (3/17 : ℝ)) ∧ (h 1 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (1/7 : ℝ)) ∧ (h 3 ≤ (4/39 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_7436 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a20 : h 2 ≤ (1/8 : ℝ))
    (a23 : -(h 0) < (-6/35 : ℝ))
    (a26 : h 1 ≤ (4/27 : ℝ))
    (a27 : -(h 2) < (-1/9 : ℝ))
    (a30 : -(h 1) < (-1/7 : ℝ))
    (a32 : h 0 ≤ (4/23 : ℝ))
    (a35 : -(h 4) < (-4/39 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-1/5 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_7455 h delta _ctx _hno a16 f0
  by_cases p1 : h 0 ≤ (5/29 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/29 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_7456 h delta _ctx _hno a16 a26 a27 a30 a32 a35 f1
  by_cases p2 : h 1 ≤ (1/6 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_7457 h delta _ctx _hno a26 f2
  by_cases p3 : h 2 ≤ (3/22 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_7458 h delta _ctx _hno a20 f3
  by_cases p4 : h 3 ≤ (3/29 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/29 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_7459 h delta _ctx _hno a16 a23 a26 a27 a30 a35 p1 f4
  apply _hno 6
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 0 ≤ (5/29 : ℝ)) ∧ (h 1 ≤ (1/6 : ℝ)) ∧ (h 2 ≤ (3/22 : ℝ)) ∧ (h 3 ≤ (3/29 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_7435 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a20 : h 2 ≤ (1/8 : ℝ))
    (a34 : -(h 2) < (-5/39 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a20 + (1 : ℝ) * a34
  exact (lt_irrefl (0 : ℝ)) hbad

end RealPinwheel.WeakSevenBandData
