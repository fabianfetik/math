import Pinwheel.WeakSevenBandData.CoverChunks.New043

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem new_node_9594 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : -(h 1) < (-2/15 : ℝ))
    (a30 : -(h 4) < (-1/9 : ℝ))
    (a44 : -(h 0) < (-4/25 : ℝ))
    (a48 : -(h 2) < (-2/17 : ℝ))
    (a54 : -(h 5) < (-3/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a24 + (1/3 : ℝ) * a30 + (1/6 : ℝ) * a44 + (1/6 : ℝ) * a48 + (1/6 : ℝ) * a54 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9593 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : -(h 1) < (-2/15 : ℝ))
    (a30 : -(h 4) < (-1/9 : ℝ))
    (a44 : -(h 0) < (-4/25 : ℝ))
    (a48 : -(h 2) < (-2/17 : ℝ))
    (a53 : -(h 3) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a24 + (1/5 : ℝ) * a30 + (1/5 : ℝ) * a44 + (1/5 : ℝ) * a48 + (1/5 : ℝ) * a53 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9592 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : -(h 1) < (-2/15 : ℝ))
    (a30 : -(h 4) < (-1/9 : ℝ))
    (a44 : -(h 0) < (-4/25 : ℝ))
    (a52 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a24 + (2/5 : ℝ) * a30 + (1/5 : ℝ) * a44 + (1/5 : ℝ) * a52 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9591 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a47 : h 1 ≤ (5/37 : ℝ))
    (a51 : -(h 1) < (-4/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a47 + (1 : ℝ) * a51
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9590 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : h 0 ≤ (1/6 : ℝ))
    (a50 : -(h 0) < (-5/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a19 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9589 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a49 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9588 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a30 : -(h 4) < (-1/9 : ℝ))
    (a42 : -(h 2) < (-4/35 : ℝ))
    (a44 : -(h 0) < (-4/25 : ℝ))
    (a47 : -(h 1) < (-5/37 : ℝ))
    (a53 : -(h 5) < (-3/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.lower + (1/3 : ℝ) * a30 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a44 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * a53 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9587 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a30 : -(h 4) < (-1/9 : ℝ))
    (a42 : -(h 2) < (-4/35 : ℝ))
    (a44 : -(h 0) < (-4/25 : ℝ))
    (a47 : -(h 1) < (-5/37 : ℝ))
    (a52 : -(h 3) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a30 + (1/5 : ℝ) * a42 + (1/5 : ℝ) * a44 + (1/5 : ℝ) * a47 + (1/5 : ℝ) * a52 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9586 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a30 : -(h 4) < (-1/9 : ℝ))
    (a44 : -(h 0) < (-4/25 : ℝ))
    (a47 : -(h 1) < (-5/37 : ℝ))
    (a51 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (2/5 : ℝ) * a30 + (1/5 : ℝ) * a44 + (1/5 : ℝ) * a47 + (1/5 : ℝ) * a51 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9585 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : h 1 ≤ (8/59 : ℝ))
    (a50 : -(h 1) < (-4/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a15 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9584 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : h 0 ≤ (1/6 : ℝ))
    (a49 : -(h 0) < (-5/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a19 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9583 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a48 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9582 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : -(h 1) < (-2/15 : ℝ))
    (a30 : -(h 4) < (-1/9 : ℝ))
    (a44 : -(h 0) < (-4/25 : ℝ))
    (a51 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.order3 + (6/29 : ℝ) * _ctx.lower + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a24 + (12/29 : ℝ) * a30 + (4/29 : ℝ) * a44 + (6/29 : ℝ) * a51 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9581 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : -(h 1) < (-2/15 : ℝ))
    (a42 : -(h 2) < (-4/35 : ℝ))
    (a44 : -(h 0) < (-4/25 : ℝ))
    (a50 : -(h 4) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a24 + (1/5 : ℝ) * a42 + (1/5 : ℝ) * a44 + (2/5 : ℝ) * a50 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9580 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : -(h 1) < (-2/15 : ℝ))
    (a30 : -(h 4) < (-1/9 : ℝ))
    (a44 : -(h 0) < (-4/25 : ℝ))
    (a49 : -(h 3) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order2 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a24 + (1/5 : ℝ) * a30 + (1/5 : ℝ) * a44 + (2/5 : ℝ) * a49 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9579 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a19 : h 0 ≤ (1/6 : ℝ))
    (a24 : -(h 1) < (-2/15 : ℝ))
    (a30 : -(h 4) < (-1/9 : ℝ))
    (a44 : -(h 0) < (-4/25 : ℝ))
    (a47 : h 1 ≤ (5/37 : ℝ))
    (a48 : -(h 2) < (-2/17 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_9589 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (5/29 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/29 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_9590 h delta _ctx _hno a19 f1
  by_cases p2 : h 1 ≤ (4/29 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/29 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_9591 h delta _ctx _hno a47 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_9592 h delta _ctx _hno a24 a30 a44 f3
  by_cases p4 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_9593 h delta _ctx _hno a24 a30 a44 a48 f4
  by_cases p5 : h 5 ≤ (3/29 : ℝ)
  swap
  · have f5 : -(h 5) < (-3/29 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_9594 h delta _ctx _hno a24 a30 a44 a48 f5
  apply _hno 89
  change (((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)) ∧ (h 0 ≤ (5/29 : ℝ)) ∧ (h 1 ≤ (4/29 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (3/29 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_9578 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a15 : h 1 ≤ (8/59 : ℝ))
    (a19 : h 0 ≤ (1/6 : ℝ))
    (a30 : -(h 4) < (-1/9 : ℝ))
    (a42 : -(h 2) < (-4/35 : ℝ))
    (a44 : -(h 0) < (-4/25 : ℝ))
    (a47 : -(h 1) < (-5/37 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_9583 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (5/29 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/29 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_9584 h delta _ctx _hno a19 f1
  by_cases p2 : h 1 ≤ (4/29 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/29 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_9585 h delta _ctx _hno a15 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_9586 h delta _ctx _hno a30 a44 a47 f3
  by_cases p4 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_9587 h delta _ctx _hno a30 a42 a44 a47 f4
  by_cases p5 : h 5 ≤ (3/29 : ℝ)
  swap
  · have f5 : -(h 5) < (-3/29 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_9588 h delta _ctx _hno a30 a42 a44 a47 f5
  apply _hno 89
  change (((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)) ∧ (h 0 ≤ (5/29 : ℝ)) ∧ (h 1 ≤ (4/29 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (3/29 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_9577 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : h 0 ≤ (1/6 : ℝ))
    (a46 : -(h 0) < (-4/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a19 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9576 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a45 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9575 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a21 : -(h 3) < (-1/9 : ℝ))
    (a24 : -(h 1) < (-2/15 : ℝ))
    (a30 : -(h 4) < (-1/9 : ℝ))
    (a38 : -(h 0) < (-8/51 : ℝ))
    (a44 : h 0 ≤ (4/25 : ℝ))
    (a47 : -(h 5) < (-2/19 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_9608 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (4/23 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/23 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_9609 h delta _ctx _hno a44 f1
  by_cases p2 : h 1 ≤ (5/37 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/37 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_9610 h delta _ctx _hno a21 a30 a38 a47 f2
  by_cases p3 : h 2 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_9611 h delta _ctx _hno a21 a24 a30 a38 a47 f3
  by_cases p4 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_9612 h delta _ctx _hno a24 a30 a38 a47 f4
  by_cases p5 : h 4 ≤ (4/35 : ℝ)
  swap
  · have f5 : -(h 4) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_9613 h delta _ctx _hno a24 a38 a47 f5
  by_cases p6 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f6 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact new_node_9614 h delta _ctx _hno a24 a30 a38 f6
  apply _hno 67
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (4/23 : ℝ)) ∧ (h 1 ≤ (5/37 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 4 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem new_node_9574 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a15 : h 1 ≤ (8/59 : ℝ))
    (a24 : -(h 1) < (-2/15 : ℝ))
    (a30 : -(h 4) < (-1/9 : ℝ))
    (a38 : -(h 0) < (-8/51 : ℝ))
    (a44 : h 0 ≤ (4/25 : ℝ))
    (a46 : -(h 2) < (-2/17 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_9595 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (5/29 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/29 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_9596 h delta _ctx _hno a44 f1
  by_cases p2 : h 1 ≤ (4/29 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/29 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_9597 h delta _ctx _hno a15 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_9598 h delta _ctx _hno a24 a30 a38 f3
  by_cases p4 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_9599 h delta _ctx _hno a13 a15 a24 a30 a38 a46 f4
  by_cases p5 : h 5 ≤ (3/29 : ℝ)
  swap
  · have f5 : -(h 5) < (-3/29 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_9600 h delta _ctx _hno a24 a30 a38 a46 f5
  apply _hno 89
  change (((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)) ∧ (h 0 ≤ (5/29 : ℝ)) ∧ (h 1 ≤ (4/29 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (3/29 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_9573 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : h 1 ≤ (8/59 : ℝ))
    (a45 : -(h 1) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a15 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9572 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a15 : h 1 ≤ (8/59 : ℝ))
    (a19 : h 0 ≤ (1/6 : ℝ))
    (a24 : -(h 1) < (-2/15 : ℝ))
    (a30 : -(h 4) < (-1/9 : ℝ))
    (a42 : -(h 2) < (-4/35 : ℝ))
    (a44 : -(h 0) < (-4/25 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_9576 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (4/23 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/23 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_9577 h delta _ctx _hno a19 f1
  by_cases p2 : h 1 ≤ (5/37 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/37 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_9578 h delta _ctx _hno a13 a15 a19 a30 a42 a44 f2
  by_cases p3 : h 2 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_9579 h delta _ctx _hno a13 a19 a24 a30 a44 p2 f3
  by_cases p4 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_9580 h delta _ctx _hno a24 a30 a44 f4
  by_cases p5 : h 4 ≤ (4/35 : ℝ)
  swap
  · have f5 : -(h 4) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_9581 h delta _ctx _hno a24 a42 a44 f5
  by_cases p6 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f6 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact new_node_9582 h delta _ctx _hno a24 a30 a44 f6
  apply _hno 67
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (4/23 : ℝ)) ∧ (h 1 ≤ (5/37 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 4 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem new_node_9571 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9570 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a21 : -(h 3) < (-1/9 : ℝ))
    (a24 : -(h 1) < (-2/15 : ℝ))
    (a30 : -(h 4) < (-1/9 : ℝ))
    (a42 : h 2 ≤ (4/35 : ℝ))
    (a43 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/9 : ℝ) * _ctx.lower + (1/9 : ℝ) * _ctx.fail1 + (2/9 : ℝ) * a21 + (2/9 : ℝ) * a24 + (2/9 : ℝ) * a30 + (4/9 : ℝ) * a42 + (2/9 : ℝ) * a43 + (2/9 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9569 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a15 : h 1 ≤ (8/59 : ℝ))
    (a19 : h 0 ≤ (1/6 : ℝ))
    (a21 : -(h 3) < (-1/9 : ℝ))
    (a24 : -(h 1) < (-2/15 : ℝ))
    (a30 : -(h 4) < (-1/9 : ℝ))
    (a38 : -(h 0) < (-8/51 : ℝ))
    (a42 : -(h 2) < (-4/35 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_9571 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (4/25 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/25 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_9572 h delta _ctx _hno a13 a15 a19 a24 a30 a42 f1
  by_cases p2 : h 1 ≤ (2/13 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_9573 h delta _ctx _hno a15 f2
  by_cases p3 : h 2 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_9574 h delta _ctx _hno a13 a15 a24 a30 a38 p1 f3
  by_cases p4 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f4 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_9575 h delta _ctx _hno a13 a21 a24 a30 a38 p1 f4
  apply _hno 212
  change (((2 : ℝ) * (delta)) ≤ (12/59 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_9568 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : h 1 ≤ (8/59 : ℝ))
    (a41 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a15 + (1 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9567 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : h 0 ≤ (1/6 : ℝ))
    (a40 : -(h 0) < (-6/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a19 + (1 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9566 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a39 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9565 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : -(h 1) < (-2/15 : ℝ))
    (a36 : -(h 0) < (-5/33 : ℝ))
    (a42 : -(h 5) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.order3 + (12/29 : ℝ) * _ctx.order4 + (6/29 : ℝ) * _ctx.lower + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a24 + (4/29 : ℝ) * a36 + (18/29 : ℝ) * a42 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9564 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a15 : h 1 ≤ (8/59 : ℝ))
    (a24 : -(h 1) < (-2/15 : ℝ))
    (a30 : -(h 4) < (-1/9 : ℝ))
    (a38 : h 0 ≤ (8/51 : ℝ))
    (a40 : h 2 ≤ (2/17 : ℝ))
    (a41 : -(h 3) < (-5/43 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_9692 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_9693 h delta _ctx _hno a15 a24 a30 a38 a40 a41 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_9694 h delta _ctx _hno a15 f2
  by_cases p3 : h 2 ≤ (3/25 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_9695 h delta _ctx _hno a40 f3
  apply _hno 198
  change (((2 : ℝ) * (delta)) ≤ (8/39 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_9563 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a15 : h 1 ≤ (8/59 : ℝ))
    (a21 : -(h 3) < (-1/9 : ℝ))
    (a24 : -(h 1) < (-2/15 : ℝ))
    (a28 : h 2 ≤ (1/8 : ℝ))
    (a30 : -(h 4) < (-1/9 : ℝ))
    (a36 : -(h 0) < (-5/33 : ℝ))
    (a38 : h 0 ≤ (8/51 : ℝ))
    (a40 : -(h 2) < (-2/17 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_9615 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_9616 h delta _ctx _hno a13 a15 a21 a24 a30 a38 a40 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_9617 h delta _ctx _hno a15 f2
  by_cases p3 : h 2 ≤ (3/25 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_9618 h delta _ctx _hno a13 a15 a24 a28 a30 a36 p1 f3
  apply _hno 198
  change (((2 : ℝ) * (delta)) ≤ (8/39 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_9562 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : h 1 ≤ (8/59 : ℝ))
    (a39 : -(h 1) < (-5/32 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a15 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9561 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a15 : h 1 ≤ (8/59 : ℝ))
    (a19 : h 0 ≤ (1/6 : ℝ))
    (a21 : -(h 3) < (-1/9 : ℝ))
    (a24 : -(h 1) < (-2/15 : ℝ))
    (a30 : -(h 4) < (-1/9 : ℝ))
    (a38 : -(h 0) < (-8/51 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_9566 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (6/35 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/35 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_9567 h delta _ctx _hno a19 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_9568 h delta _ctx _hno a15 f2
  by_cases p3 : h 2 ≤ (4/35 : ℝ)
  swap
  · have f3 : -(h 2) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_9569 h delta _ctx _hno a13 a15 a19 a21 a24 a30 a38 f3
  by_cases p4 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_9570 h delta _ctx _hno a21 a24 a30 p3 f4
  apply _hno 19
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (6/35 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_9560 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a37 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a37
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9559 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : -(h 1) < (-2/15 : ℝ))
    (a34 : -(h 0) < (-7/48 : ℝ))
    (a40 : -(h 5) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.order3 + (12/29 : ℝ) * _ctx.order4 + (6/29 : ℝ) * _ctx.lower + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a24 + (4/29 : ℝ) * a34 + (18/29 : ℝ) * a40 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9558 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a15 : h 1 ≤ (8/59 : ℝ))
    (a24 : -(h 1) < (-2/15 : ℝ))
    (a30 : -(h 4) < (-1/9 : ℝ))
    (a34 : -(h 0) < (-7/48 : ℝ))
    (a38 : h 2 ≤ (4/33 : ℝ))
    (a39 : -(h 3) < (-3/25 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_9813 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (4/27 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/27 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_9814 h delta _ctx _hno a13 a15 a24 a30 a38 a39 f1
  by_cases p2 : h 1 ≤ (6/41 : ℝ)
  swap
  · have f2 : -(h 1) < (-6/41 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_9815 h delta _ctx _hno a15 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_9816 h delta _ctx _hno a38 f3
  by_cases p4 : h 4 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 4) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_9817 h delta _ctx _hno a24 a34 a39 f4
  by_cases p5 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_9818 h delta _ctx _hno a24 a30 a34 a39 f5
  apply _hno 61
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (4/27 : ℝ)) ∧ (h 1 ≤ (6/41 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_9557 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a15 : h 1 ≤ (8/59 : ℝ))
    (a24 : -(h 1) < (-2/15 : ℝ))
    (a28 : h 2 ≤ (1/8 : ℝ))
    (a30 : -(h 4) < (-1/9 : ℝ))
    (a34 : -(h 0) < (-7/48 : ℝ))
    (a36 : h 0 ≤ (5/33 : ℝ))
    (a38 : -(h 2) < (-4/33 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_9701 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (4/27 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/27 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_9702 h delta _ctx _hno a13 a15 a24 a28 a30 a36 a38 f1
  by_cases p2 : h 1 ≤ (3/22 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_9703 h delta _ctx _hno a15 f2
  by_cases p3 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_9704 h delta _ctx _hno a13 a15 a24 a28 a30 a34 a38 p1 f3
  by_cases p4 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_9705 h delta _ctx _hno a24 a30 a34 a38 f4
  apply _hno 108
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (4/27 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_9556 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : h 1 ≤ (8/59 : ℝ))
    (a37 : -(h 1) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a15 + (1 : ℝ) * a37
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9555 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a15 : h 1 ≤ (8/59 : ℝ))
    (a19 : h 0 ≤ (1/6 : ℝ))
    (a21 : -(h 3) < (-1/9 : ℝ))
    (a24 : -(h 1) < (-2/15 : ℝ))
    (a28 : h 2 ≤ (1/8 : ℝ))
    (a30 : -(h 4) < (-1/9 : ℝ))
    (a36 : -(h 0) < (-5/33 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_9560 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (8/51 : ℝ)
  swap
  · have f1 : -(h 0) < (-8/51 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_9561 h delta _ctx _hno a13 a15 a19 a21 a24 a30 f1
  by_cases p2 : h 1 ≤ (5/32 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/32 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_9562 h delta _ctx _hno a15 f2
  by_cases p3 : h 2 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_9563 h delta _ctx _hno a13 a15 a21 a24 a28 a30 a36 p1 f3
  by_cases p4 : h 3 ≤ (5/43 : ℝ)
  swap
  · have f4 : -(h 3) < (-5/43 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_9564 h delta _ctx _hno a13 a15 a24 a30 p1 p3 f4
  by_cases p5 : h 5 ≤ (3/26 : ℝ)
  swap
  · have f5 : -(h 5) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_9565 h delta _ctx _hno a24 a36 f5
  apply _hno 226
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (8/51 : ℝ)) ∧ (h 1 ≤ (5/32 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 3 ≤ (5/43 : ℝ)) ∧ (h 5 ≤ (3/26 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_9554 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a35 : ((-2 : ℝ) * (delta)) < (-7/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a35
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9553 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a28 : h 2 ≤ (1/8 : ℝ))
    (a36 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a28 + (1 : ℝ) * a36
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9552 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : h 1 ≤ (8/59 : ℝ))
    (a35 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a15 + (1 : ℝ) * a35
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9551 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a15 : h 1 ≤ (8/59 : ℝ))
    (a19 : h 0 ≤ (1/6 : ℝ))
    (a21 : -(h 3) < (-1/9 : ℝ))
    (a24 : -(h 1) < (-2/15 : ℝ))
    (a28 : h 2 ≤ (1/8 : ℝ))
    (a30 : -(h 4) < (-1/9 : ℝ))
    (a34 : -(h 0) < (-7/48 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/33 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/33 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_9554 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (5/33 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/33 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_9555 h delta _ctx _hno a13 a15 a19 a21 a24 a28 a30 f1
  by_cases p2 : h 1 ≤ (3/20 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_9556 h delta _ctx _hno a15 f2
  by_cases p3 : h 2 ≤ (4/33 : ℝ)
  swap
  · have f3 : -(h 2) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_9557 h delta _ctx _hno a13 a15 a24 a28 a30 a34 p1 f3
  by_cases p4 : h 3 ≤ (3/25 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_9558 h delta _ctx _hno a13 a15 a24 a30 a34 p3 f4
  by_cases p5 : h 5 ≤ (2/17 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_9559 h delta _ctx _hno a24 a34 f5
  apply _hno 11
  change (((2 : ℝ) * (delta)) ≤ (7/33 : ℝ)) ∧ (h 0 ≤ (5/33 : ℝ)) ∧ (h 1 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (4/33 : ℝ)) ∧ (h 3 ≤ (3/25 : ℝ)) ∧ (h 5 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_9550 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a33 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a33
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9549 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a28 : h 2 ≤ (1/8 : ℝ))
    (a33 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a28 + (1 : ℝ) * a33
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9548 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a15 : h 1 ≤ (8/59 : ℝ))
    (a19 : h 0 ≤ (1/6 : ℝ))
    (a21 : -(h 3) < (-1/9 : ℝ))
    (a24 : -(h 1) < (-2/15 : ℝ))
    (a28 : h 2 ≤ (1/8 : ℝ))
    (a30 : -(h 4) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_9550 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (7/48 : ℝ)
  swap
  · have f1 : -(h 0) < (-7/48 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_9551 h delta _ctx _hno a13 a15 a19 a21 a24 a28 a30 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_9552 h delta _ctx _hno a15 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_9553 h delta _ctx _hno a28 f3
  apply _hno 230
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (7/48 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_9547 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a31 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a31
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9546 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : -(h 1) < (-2/15 : ℝ))
    (a29 : -(h 3) < (-7/57 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a35 : -(h 0) < (-1/7 : ℝ))
    (a39 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a24 + (1/5 : ℝ) * a29 + (1/5 : ℝ) * a33 + (1/5 : ℝ) * a35 + (1/5 : ℝ) * a39 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9545 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : h 1 ≤ (8/59 : ℝ))
    (a38 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a15 + (1 : ℝ) * a38
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9544 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : -(h 1) < (-2/15 : ℝ))
    (a29 : -(h 3) < (-7/57 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a37 : -(h 0) < (-7/48 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order2 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a24 + (2/5 : ℝ) * a29 + (1/5 : ℝ) * a33 + (1/5 : ℝ) * a37 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9543 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a36 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a36
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9542 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a28 : h 2 ≤ (1/8 : ℝ))
    (a36 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a28 + (1 : ℝ) * a36
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9541 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a15 : h 1 ≤ (8/59 : ℝ))
    (a24 : -(h 1) < (-2/15 : ℝ))
    (a29 : -(h 3) < (-7/57 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a35 : -(h 0) < (-1/7 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_9543 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (7/48 : ℝ)
  swap
  · have f1 : -(h 0) < (-7/48 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_9544 h delta _ctx _hno a24 a29 a33 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_9545 h delta _ctx _hno a15 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_9546 h delta _ctx _hno a24 a29 a33 a35 f3
  apply _hno 230
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (7/48 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_9540 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a34
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9539 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : -(h 1) < (-2/15 : ℝ))
    (a29 : -(h 3) < (-7/57 : ℝ))
    (a37 : -(h 0) < (-3/20 : ℝ))
    (a43 : -(h 5) < (-3/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order2 + (1/6 : ℝ) * _ctx.order4 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a24 + (1/3 : ℝ) * a29 + (1/6 : ℝ) * a37 + (1/3 : ℝ) * a43 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9538 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : -(h 1) < (-2/15 : ℝ))
    (a29 : -(h 3) < (-7/57 : ℝ))
    (a37 : -(h 0) < (-3/20 : ℝ))
    (a42 : -(h 4) < (-4/37 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order2 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a24 + (2/5 : ℝ) * a29 + (1/5 : ℝ) * a37 + (1/5 : ℝ) * a42 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9537 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a28 : h 2 ≤ (1/8 : ℝ))
    (a41 : -(h 2) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a28 + (1 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9536 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a29 : -(h 3) < (-7/57 : ℝ))
    (a35 : -(h 4) < (-3/29 : ℝ))
    (a37 : -(h 0) < (-3/20 : ℝ))
    (a40 : -(h 1) < (-5/37 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order2 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (2/5 : ℝ) * a29 + (1/5 : ℝ) * a35 + (1/5 : ℝ) * a37 + (1/5 : ℝ) * a40 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9535 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : -(h 1) < (-2/15 : ℝ))
    (a29 : -(h 3) < (-7/57 : ℝ))
    (a35 : -(h 4) < (-3/29 : ℝ))
    (a39 : -(h 0) < (-6/37 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order2 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a24 + (2/5 : ℝ) * a29 + (1/5 : ℝ) * a35 + (1/5 : ℝ) * a39 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9534 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a38 : ((-2 : ℝ) * (delta)) < (-7/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a38
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9533 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : -(h 1) < (-2/15 : ℝ))
    (a29 : -(h 3) < (-7/57 : ℝ))
    (a31 : -(h 0) < (-4/27 : ℝ))
    (a39 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order2 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a24 + (2/5 : ℝ) * a29 + (1/5 : ℝ) * a31 + (1/5 : ℝ) * a39 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9532 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a28 : h 2 ≤ (1/8 : ℝ))
    (a38 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a28 + (1 : ℝ) * a38
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9531 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a24 : -(h 1) < (-2/15 : ℝ))
    (a28 : h 2 ≤ (1/8 : ℝ))
    (a29 : -(h 3) < (-7/57 : ℝ))
    (a35 : -(h 4) < (-3/29 : ℝ))
    (a37 : -(h 0) < (-3/20 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/33 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/33 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_9534 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (6/37 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/37 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_9535 h delta _ctx _hno a24 a29 a35 f1
  by_cases p2 : h 1 ≤ (5/37 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/37 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_9536 h delta _ctx _hno a29 a35 a37 f2
  by_cases p3 : h 2 ≤ (2/15 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_9537 h delta _ctx _hno a28 f3
  by_cases p4 : h 4 ≤ (4/37 : ℝ)
  swap
  · have f4 : -(h 4) < (-4/37 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_9538 h delta _ctx _hno a24 a29 a37 f4
  by_cases p5 : h 5 ≤ (3/28 : ℝ)
  swap
  · have f5 : -(h 5) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_9539 h delta _ctx _hno a24 a29 a37 f5
  apply _hno 249
  change (((2 : ℝ) * (delta)) ≤ (7/33 : ℝ)) ∧ (h 0 ≤ (6/37 : ℝ)) ∧ (h 1 ≤ (5/37 : ℝ)) ∧ (h 2 ≤ (2/15 : ℝ)) ∧ (h 4 ≤ (4/37 : ℝ)) ∧ (h 5 ≤ (3/28 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_9530 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a36 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a36
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9529 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a24 : -(h 1) < (-2/15 : ℝ))
    (a28 : h 2 ≤ (1/8 : ℝ))
    (a29 : -(h 3) < (-7/57 : ℝ))
    (a31 : -(h 0) < (-4/27 : ℝ))
    (a35 : -(h 4) < (-3/29 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_9530 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_9531 h delta _ctx _hno a13 a24 a28 a29 a35 f1
  by_cases p2 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_9532 h delta _ctx _hno a28 f2
  by_cases p3 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f3 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_9533 h delta _ctx _hno a24 a29 a31 f3
  apply _hno 136
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_9528 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : h 1 ≤ (8/59 : ℝ))
    (a34 : -(h 1) < (-4/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a15 + (1 : ℝ) * a34
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9527 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : h 0 ≤ (1/6 : ℝ))
    (a33 : -(h 0) < (-5/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a19 + (1 : ℝ) * a33
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9526 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a32 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a32
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9525 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a15 : h 1 ≤ (8/59 : ℝ))
    (a24 : -(h 1) < (-2/15 : ℝ))
    (a28 : h 2 ≤ (1/8 : ℝ))
    (a29 : -(h 3) < (-7/57 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_9540 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (1/7 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_9541 h delta _ctx _hno a13 a15 a24 a29 a33 f1
  by_cases p2 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_9542 h delta _ctx _hno a28 f2
  apply _hno 84
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem new_node_9524 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a28 : h 2 ≤ (1/8 : ℝ))
    (a32 : -(h 2) < (-7/54 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a28 + (1 : ℝ) * a32
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9523 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a15 : h 1 ≤ (8/59 : ℝ))
    (a19 : h 0 ≤ (1/6 : ℝ))
    (a24 : -(h 1) < (-2/15 : ℝ))
    (a28 : h 2 ≤ (1/8 : ℝ))
    (a29 : -(h 3) < (-7/57 : ℝ))
    (a31 : -(h 0) < (-4/27 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_9526 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (5/29 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/29 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_9527 h delta _ctx _hno a19 f1
  by_cases p2 : h 1 ≤ (4/29 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/29 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_9528 h delta _ctx _hno a15 f2
  by_cases p3 : h 4 ≤ (3/29 : ℝ)
  swap
  · have f3 : -(h 4) < (-3/29 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_9529 h delta _ctx _hno a13 a24 a28 a29 a31 f3
  apply _hno 7
  change (((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)) ∧ (h 0 ≤ (5/29 : ℝ)) ∧ (h 1 ≤ (4/29 : ℝ)) ∧ (h 4 ≤ (3/29 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_9522 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a30 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a30
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9521 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : -(h 1) < (-2/15 : ℝ))
    (a28 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 4) < (-1/9 : ℝ))
    (a47 : -(h 0) < (-10/67 : ℝ))
    (a51 : -(h 3) < (-4/35 : ℝ))
    (a57 : -(h 5) < (-2/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a24 + (1/6 : ℝ) * a28 + (1/6 : ℝ) * a34 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * a51 + (1/6 : ℝ) * a57 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9520 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a33 : h 3 ≤ (5/43 : ℝ))
    (a56 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a56
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9519 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a50 : h 2 ≤ (5/39 : ℝ))
    (a55 : -(h 2) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a50 + (1 : ℝ) * a55
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9518 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a28 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 4) < (-1/9 : ℝ))
    (a47 : -(h 0) < (-10/67 : ℝ))
    (a51 : -(h 3) < (-4/35 : ℝ))
    (a54 : -(h 1) < (-5/37 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a28 + (1/5 : ℝ) * a34 + (1/5 : ℝ) * a47 + (1/5 : ℝ) * a51 + (1/5 : ℝ) * a54 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9517 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : -(h 1) < (-2/15 : ℝ))
    (a28 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 4) < (-1/9 : ℝ))
    (a51 : -(h 3) < (-4/35 : ℝ))
    (a53 : -(h 0) < (-5/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a24 + (1/5 : ℝ) * a28 + (1/5 : ℝ) * a34 + (1/5 : ℝ) * a51 + (1/5 : ℝ) * a53 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9516 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : -(h 1) < (-2/15 : ℝ))
    (a28 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 4) < (-1/9 : ℝ))
    (a47 : -(h 0) < (-10/67 : ℝ))
    (a51 : -(h 3) < (-4/35 : ℝ))
    (a52 : ((-2 : ℝ) * (delta)) < (-13/64 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a24 + (1/6 : ℝ) * a28 + (1/6 : ℝ) * a34 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * a51 + (1/6 : ℝ) * a52 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9515 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : -(h 1) < (-2/15 : ℝ))
    (a28 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 4) < (-1/9 : ℝ))
    (a45 : -(h 3) < (-7/62 : ℝ))
    (a47 : -(h 0) < (-10/67 : ℝ))
    (a53 : -(h 5) < (-3/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a24 + (1/6 : ℝ) * a28 + (1/6 : ℝ) * a34 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * a53 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

end RealPinwheel.WeakSevenBandData
