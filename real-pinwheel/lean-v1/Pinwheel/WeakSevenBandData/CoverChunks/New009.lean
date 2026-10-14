import Pinwheel.WeakSevenBandData.CoverChunks.New008

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem new_node_12394 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a39 : -(h 4) < (-4/37 : ℝ))
    (a53 : -(h 0) < (-5/33 : ℝ))
    (a61 : -(h 3) < (-5/43 : ℝ))
    (a64 : -(h 1) < (-5/38 : ℝ))
    (a68 : -(h 2) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a39 + (1/5 : ℝ) * a53 + (1/5 : ℝ) * a61 + (1/5 : ℝ) * a64 + (1/5 : ℝ) * a68 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12393 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a39 : -(h 4) < (-4/37 : ℝ))
    (a51 : -(h 2) < (-1/8 : ℝ))
    (a53 : -(h 0) < (-5/33 : ℝ))
    (a61 : -(h 3) < (-5/43 : ℝ))
    (a67 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a39 + (1/5 : ℝ) * a51 + (1/5 : ℝ) * a53 + (1/5 : ℝ) * a61 + (1/5 : ℝ) * a67 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12392 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a41 : h 0 ≤ (2/13 : ℝ))
    (a66 : -(h 0) < (-7/45 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a41 + (1 : ℝ) * a66
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12391 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a65 : ((-2 : ℝ) * (delta)) < (-1/5 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a65
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12390 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a39 : -(h 4) < (-4/37 : ℝ))
    (a51 : -(h 2) < (-1/8 : ℝ))
    (a53 : -(h 0) < (-5/33 : ℝ))
    (a56 : -(h 1) < (-7/54 : ℝ))
    (a61 : -(h 3) < (-5/43 : ℝ))
    (a67 : -(h 5) < (-2/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a39 + (1/6 : ℝ) * a51 + (1/6 : ℝ) * a53 + (1/6 : ℝ) * a56 + (1/6 : ℝ) * a61 + (1/6 : ℝ) * a67 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12389 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a39 : -(h 4) < (-4/37 : ℝ))
    (a51 : -(h 2) < (-1/8 : ℝ))
    (a53 : -(h 0) < (-5/33 : ℝ))
    (a56 : -(h 1) < (-7/54 : ℝ))
    (a66 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a39 + (1/5 : ℝ) * a51 + (1/5 : ℝ) * a53 + (1/5 : ℝ) * a56 + (1/5 : ℝ) * a66 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12388 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a39 : -(h 4) < (-4/37 : ℝ))
    (a53 : -(h 0) < (-5/33 : ℝ))
    (a61 : -(h 3) < (-5/43 : ℝ))
    (a65 : -(h 2) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order1 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a39 + (1/5 : ℝ) * a53 + (1/5 : ℝ) * a61 + (2/5 : ℝ) * a65 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12387 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a39 : -(h 4) < (-4/37 : ℝ))
    (a41 : h 0 ≤ (2/13 : ℝ))
    (a51 : -(h 2) < (-1/8 : ℝ))
    (a53 : -(h 0) < (-5/33 : ℝ))
    (a61 : -(h 3) < (-5/43 : ℝ))
    (a64 : -(h 1) < (-5/38 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-1/5 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_12391 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (7/45 : ℝ)
  swap
  · have f1 : -(h 0) < (-7/45 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_12392 h delta _ctx _hno a41 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_12393 h delta _ctx _hno a39 a51 a53 a61 f2
  by_cases p3 : h 2 ≤ (3/23 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_12394 h delta _ctx _hno a39 a53 a61 a64 f3
  by_cases p4 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_12395 h delta _ctx _hno a39 a51 a53 a64 f4
  by_cases p5 : h 5 ≤ (3/28 : ℝ)
  swap
  · have f5 : -(h 5) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_12396 h delta _ctx _hno a39 a51 a53 a61 a64 f5
  apply _hno 50
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 0 ≤ (7/45 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 5 ≤ (3/28 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_12386 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a41 : h 0 ≤ (2/13 : ℝ))
    (a63 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a41 + (1 : ℝ) * a63
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12385 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a62 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a62
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12384 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a47 : -(h 3) < (-4/35 : ℝ))
    (a51 : -(h 2) < (-1/8 : ℝ))
    (a53 : -(h 0) < (-5/33 : ℝ))
    (a56 : -(h 1) < (-7/54 : ℝ))
    (a61 : h 3 ≤ (5/43 : ℝ))
    (a62 : -(h 4) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_12397 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_12398 h delta _ctx _hno a47 a51 a56 a62 f1
  by_cases p2 : h 1 ≤ (5/38 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/38 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_12399 h delta _ctx _hno a47 a51 a53 a62 f2
  by_cases p3 : h 2 ≤ (3/23 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_12400 h delta _ctx _hno a47 a53 a62 f3
  by_cases p4 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_12401 h delta _ctx _hno a61 f4
  by_cases p5 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_12402 h delta _ctx _hno a47 a51 a53 a56 a62 f5
  apply _hno 30
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (5/38 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_12383 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a39 : -(h 4) < (-4/37 : ℝ))
    (a41 : h 0 ≤ (2/13 : ℝ))
    (a51 : -(h 2) < (-1/8 : ℝ))
    (a53 : -(h 0) < (-5/33 : ℝ))
    (a56 : -(h 1) < (-7/54 : ℝ))
    (a61 : -(h 3) < (-5/43 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_12385 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_12386 h delta _ctx _hno a41 f1
  by_cases p2 : h 1 ≤ (5/38 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/38 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_12387 h delta _ctx _hno a17 a39 a41 a51 a53 a61 f2
  by_cases p3 : h 2 ≤ (3/23 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_12388 h delta _ctx _hno a39 a53 a61 f3
  by_cases p4 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_12389 h delta _ctx _hno a39 a51 a53 a56 f4
  by_cases p5 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_12390 h delta _ctx _hno a39 a51 a53 a56 a61 f5
  apply _hno 30
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (5/38 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_12382 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a38 : h 2 ≤ (2/15 : ℝ))
    (a60 : -(h 2) < (-3/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a38 + (1 : ℝ) * a60
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12381 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a28 : h 1 ≤ (2/15 : ℝ))
    (a59 : -(h 1) < (-6/43 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a28 + (1 : ℝ) * a59
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12380 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a41 : h 0 ≤ (2/13 : ℝ))
    (a58 : -(h 0) < (-5/31 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a41 + (1 : ℝ) * a58
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12379 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a57 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a57
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12378 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a41 : h 0 ≤ (2/13 : ℝ))
    (a42 : -(h 1) < (-5/39 : ℝ))
    (a47 : -(h 3) < (-4/35 : ℝ))
    (a51 : -(h 2) < (-1/8 : ℝ))
    (a53 : -(h 0) < (-5/33 : ℝ))
    (a56 : h 1 ≤ (7/54 : ℝ))
    (a58 : -(h 4) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_12403 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_12404 h delta _ctx _hno a41 f1
  by_cases p2 : h 1 ≤ (5/38 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/38 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_12405 h delta _ctx _hno a56 f2
  by_cases p3 : h 2 ≤ (3/23 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_12406 h delta _ctx _hno a47 a53 a58 f3
  by_cases p4 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_12407 h delta _ctx _hno a42 a51 a53 a58 f4
  by_cases p5 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_12408 h delta _ctx _hno a42 a47 a51 a53 a58 f5
  apply _hno 30
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (5/38 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_12377 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a39 : -(h 4) < (-4/37 : ℝ))
    (a42 : -(h 1) < (-5/39 : ℝ))
    (a51 : -(h 2) < (-1/8 : ℝ))
    (a53 : -(h 0) < (-5/33 : ℝ))
    (a57 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a39 + (1/5 : ℝ) * a42 + (1/5 : ℝ) * a51 + (1/5 : ℝ) * a53 + (1/5 : ℝ) * a57 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12376 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a28 : h 1 ≤ (2/15 : ℝ))
    (a38 : h 2 ≤ (2/15 : ℝ))
    (a39 : -(h 4) < (-4/37 : ℝ))
    (a41 : h 0 ≤ (2/13 : ℝ))
    (a47 : -(h 3) < (-4/35 : ℝ))
    (a51 : -(h 2) < (-1/8 : ℝ))
    (a53 : -(h 0) < (-5/33 : ℝ))
    (a56 : -(h 1) < (-7/54 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_12379 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (5/31 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/31 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_12380 h delta _ctx _hno a41 f1
  by_cases p2 : h 1 ≤ (6/43 : ℝ)
  swap
  · have f2 : -(h 1) < (-6/43 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_12381 h delta _ctx _hno a28 f2
  by_cases p3 : h 2 ≤ (3/22 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_12382 h delta _ctx _hno a38 f3
  by_cases p4 : h 3 ≤ (5/43 : ℝ)
  swap
  · have f4 : -(h 3) < (-5/43 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_12383 h delta _ctx _hno a17 a39 a41 a51 a53 a56 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_12384 h delta _ctx _hno a17 a47 a51 a53 a56 p4 f5
  apply _hno 228
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (5/31 : ℝ)) ∧ (h 1 ≤ (6/43 : ℝ)) ∧ (h 2 ≤ (3/22 : ℝ)) ∧ (h 3 ≤ (5/43 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_12375 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a41 : h 0 ≤ (2/13 : ℝ))
    (a55 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a41 + (1 : ℝ) * a55
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12374 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a54 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a54
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12373 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a18 : -(h 0) < (-3/20 : ℝ))
    (a28 : h 1 ≤ (2/15 : ℝ))
    (a39 : -(h 4) < (-4/37 : ℝ))
    (a42 : -(h 1) < (-5/39 : ℝ))
    (a47 : -(h 3) < (-4/35 : ℝ))
    (a51 : -(h 2) < (-1/8 : ℝ))
    (a53 : h 0 ≤ (5/33 : ℝ))
    (a55 : h 2 ≤ (3/23 : ℝ))
    (a56 : -(h 5) < (-2/19 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_12415 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_12416 h delta _ctx _hno a53 f1
  by_cases p2 : h 1 ≤ (7/54 : ℝ)
  swap
  · have f2 : -(h 1) < (-7/54 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_12417 h delta _ctx _hno a17 a18 a28 a39 a47 a51 a53 a55 a56 f2
  by_cases p3 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_12418 h delta _ctx _hno a18 a39 a42 a51 a56 f3
  by_cases p4 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_12419 h delta _ctx _hno a18 a42 a47 a51 a56 f4
  apply _hno 80
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (7/54 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_12372 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a18 : -(h 0) < (-3/20 : ℝ))
    (a28 : h 1 ≤ (2/15 : ℝ))
    (a38 : h 2 ≤ (2/15 : ℝ))
    (a39 : -(h 4) < (-4/37 : ℝ))
    (a47 : -(h 3) < (-4/35 : ℝ))
    (a53 : h 0 ≤ (5/33 : ℝ))
    (a55 : -(h 2) < (-3/23 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_12409 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (5/31 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/31 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_12410 h delta _ctx _hno a53 f1
  by_cases p2 : h 1 ≤ (6/43 : ℝ)
  swap
  · have f2 : -(h 1) < (-6/43 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_12411 h delta _ctx _hno a28 f2
  by_cases p3 : h 2 ≤ (3/22 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_12412 h delta _ctx _hno a38 f3
  by_cases p4 : h 3 ≤ (5/43 : ℝ)
  swap
  · have f4 : -(h 3) < (-5/43 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_12413 h delta _ctx _hno a18 a39 a55 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_12414 h delta _ctx _hno a18 a47 a55 f5
  apply _hno 228
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (5/31 : ℝ)) ∧ (h 1 ≤ (6/43 : ℝ)) ∧ (h 2 ≤ (3/22 : ℝ)) ∧ (h 3 ≤ (5/43 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_12371 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a28 : h 1 ≤ (2/15 : ℝ))
    (a54 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a28 + (1 : ℝ) * a54
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12370 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a28 : h 1 ≤ (2/15 : ℝ))
    (a38 : h 2 ≤ (2/15 : ℝ))
    (a39 : -(h 4) < (-4/37 : ℝ))
    (a41 : h 0 ≤ (2/13 : ℝ))
    (a42 : -(h 1) < (-5/39 : ℝ))
    (a47 : -(h 3) < (-4/35 : ℝ))
    (a51 : -(h 2) < (-1/8 : ℝ))
    (a53 : -(h 0) < (-5/33 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_12374 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_12375 h delta _ctx _hno a41 f1
  by_cases p2 : h 1 ≤ (7/54 : ℝ)
  swap
  · have f2 : -(h 1) < (-7/54 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_12376 h delta _ctx _hno a17 a28 a38 a39 a41 a47 a51 a53 f2
  by_cases p3 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_12377 h delta _ctx _hno a39 a42 a51 a53 f3
  by_cases p4 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_12378 h delta _ctx _hno a17 a41 a42 a47 a51 a53 p2 f4
  apply _hno 80
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (7/54 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_12369 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a52 : ((-2 : ℝ) * (delta)) < (-1/5 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a52
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12368 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a18 : -(h 0) < (-3/20 : ℝ))
    (a25 : -(h 2) < (-3/25 : ℝ))
    (a28 : h 1 ≤ (2/15 : ℝ))
    (a41 : h 0 ≤ (2/13 : ℝ))
    (a42 : -(h 1) < (-5/39 : ℝ))
    (a47 : -(h 3) < (-4/35 : ℝ))
    (a51 : h 2 ≤ (1/8 : ℝ))
    (a52 : -(h 4) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_12426 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_12427 h delta _ctx _hno a41 f1
  by_cases p2 : h 1 ≤ (5/38 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/38 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_12428 h delta _ctx _hno a17 a18 a25 a28 a41 a47 a51 a52 f2
  by_cases p3 : h 2 ≤ (3/23 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_12429 h delta _ctx _hno a51 f3
  by_cases p4 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_12430 h delta _ctx _hno a18 a42 a52 f4
  by_cases p5 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_12431 h delta _ctx _hno a17 a18 a25 a41 a42 a47 a51 a52 p2 f5
  apply _hno 30
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (5/38 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_12367 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a18 : -(h 0) < (-3/20 : ℝ))
    (a28 : h 1 ≤ (2/15 : ℝ))
    (a38 : h 2 ≤ (2/15 : ℝ))
    (a39 : -(h 4) < (-4/37 : ℝ))
    (a41 : h 0 ≤ (2/13 : ℝ))
    (a42 : -(h 1) < (-5/39 : ℝ))
    (a47 : -(h 3) < (-4/35 : ℝ))
    (a51 : -(h 2) < (-1/8 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-1/5 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_12369 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (5/33 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/33 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_12370 h delta _ctx _hno a17 a28 a38 a39 a41 a42 a47 a51 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_12371 h delta _ctx _hno a28 f2
  by_cases p3 : h 2 ≤ (3/23 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_12372 h delta _ctx _hno a17 a18 a28 a38 a39 a47 p1 f3
  by_cases p4 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f4 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_12373 h delta _ctx _hno a17 a18 a28 a39 a42 a47 a51 p1 p3 f4
  apply _hno 150
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 0 ≤ (5/33 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_12366 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a28 : h 1 ≤ (2/15 : ℝ))
    (a50 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a28 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12365 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a41 : h 0 ≤ (2/13 : ℝ))
    (a49 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a41 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12364 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a48 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12363 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a18 : -(h 0) < (-3/20 : ℝ))
    (a25 : -(h 2) < (-3/25 : ℝ))
    (a28 : h 1 ≤ (2/15 : ℝ))
    (a34 : -(h 3) < (-1/9 : ℝ))
    (a41 : h 0 ≤ (2/13 : ℝ))
    (a42 : -(h 1) < (-5/39 : ℝ))
    (a47 : h 3 ≤ (4/35 : ℝ))
    (a48 : -(h 5) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/33 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/33 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_12492 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (5/33 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/33 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_12493 h delta _ctx _hno a17 a25 a34 a41 a42 a48 f1
  by_cases p2 : h 1 ≤ (3/20 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_12494 h delta _ctx _hno a28 f2
  by_cases p3 : h 2 ≤ (4/33 : ℝ)
  swap
  · have f3 : -(h 2) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_12495 h delta _ctx _hno a17 a18 a34 a42 a47 a48 p1 f3
  by_cases p4 : h 3 ≤ (3/25 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_12496 h delta _ctx _hno a47 f4
  by_cases p5 : h 5 ≤ (2/17 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_12497 h delta _ctx _hno a47 f5
  apply _hno 11
  change (((2 : ℝ) * (delta)) ≤ (7/33 : ℝ)) ∧ (h 0 ≤ (5/33 : ℝ)) ∧ (h 1 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (4/33 : ℝ)) ∧ (h 3 ≤ (3/25 : ℝ)) ∧ (h 5 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_12362 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a18 : -(h 0) < (-3/20 : ℝ))
    (a25 : -(h 2) < (-3/25 : ℝ))
    (a28 : h 1 ≤ (2/15 : ℝ))
    (a38 : h 2 ≤ (2/15 : ℝ))
    (a39 : -(h 4) < (-4/37 : ℝ))
    (a41 : h 0 ≤ (2/13 : ℝ))
    (a42 : -(h 1) < (-5/39 : ℝ))
    (a47 : -(h 3) < (-4/35 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_12364 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_12365 h delta _ctx _hno a41 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_12366 h delta _ctx _hno a28 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_12367 h delta _ctx _hno a17 a18 a28 a38 a39 a41 a42 a47 f3
  by_cases p4 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_12368 h delta _ctx _hno a17 a18 a25 a28 a41 a42 a47 p3 f4
  apply _hno 120
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_12361 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a38 : h 2 ≤ (2/15 : ℝ))
    (a46 : -(h 2) < (-3/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a38 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12360 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a28 : h 1 ≤ (2/15 : ℝ))
    (a45 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a28 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12359 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a41 : h 0 ≤ (2/13 : ℝ))
    (a44 : -(h 0) < (-6/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a41 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12358 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-1/5 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12357 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a21 : -(h 1) < (-1/8 : ℝ))
    (a25 : -(h 2) < (-3/25 : ℝ))
    (a41 : -(h 0) < (-2/13 : ℝ))
    (a47 : -(h 5) < (-1/9 : ℝ))
    (a52 : -(h 4) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a21 + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a41 + (1/6 : ℝ) * a47 + (1/3 : ℝ) * a52 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12356 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a21 : -(h 1) < (-1/8 : ℝ))
    (a34 : -(h 3) < (-1/9 : ℝ))
    (a41 : -(h 0) < (-2/13 : ℝ))
    (a47 : -(h 5) < (-1/9 : ℝ))
    (a51 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order4 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a21 + (1/6 : ℝ) * a34 + (1/6 : ℝ) * a41 + (1/3 : ℝ) * a47 + (1/6 : ℝ) * a51 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12355 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 2) < (-3/25 : ℝ))
    (a34 : -(h 3) < (-1/9 : ℝ))
    (a41 : -(h 0) < (-2/13 : ℝ))
    (a47 : -(h 5) < (-1/9 : ℝ))
    (a50 : -(h 1) < (-9/70 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order4 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a34 + (1/6 : ℝ) * a41 + (1/3 : ℝ) * a47 + (1/6 : ℝ) * a50 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12354 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a21 : -(h 1) < (-1/8 : ℝ))
    (a25 : -(h 2) < (-3/25 : ℝ))
    (a34 : -(h 3) < (-1/9 : ℝ))
    (a47 : -(h 5) < (-1/9 : ℝ))
    (a49 : -(h 0) < (-7/45 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order4 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a21 + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a34 + (1/3 : ℝ) * a47 + (1/6 : ℝ) * a49 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12353 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a48 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12352 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a21 : -(h 1) < (-1/8 : ℝ))
    (a25 : -(h 2) < (-3/25 : ℝ))
    (a41 : -(h 0) < (-2/13 : ℝ))
    (a46 : -(h 3) < (-4/35 : ℝ))
    (a56 : -(h 4) < (-4/35 : ℝ))
    (a62 : -(h 5) < (-3/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a21 + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a41 + (1/6 : ℝ) * a46 + (1/6 : ℝ) * a56 + (1/6 : ℝ) * a62 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12351 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a21 : -(h 1) < (-1/8 : ℝ))
    (a41 : -(h 0) < (-2/13 : ℝ))
    (a56 : -(h 4) < (-4/35 : ℝ))
    (a61 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order2 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a21 + (1/5 : ℝ) * a41 + (1/5 : ℝ) * a56 + (2/5 : ℝ) * a61 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12350 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a50 : h 2 ≤ (1/8 : ℝ))
    (a60 : -(h 2) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a50 + (1 : ℝ) * a60
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12349 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a54 : h 1 ≤ (9/70 : ℝ))
    (a59 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a54 + (1 : ℝ) * a59
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12348 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a53 : h 0 ≤ (7/45 : ℝ))
    (a58 : -(h 0) < (-7/45 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a53 + (1 : ℝ) * a58
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12347 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a57 : ((-2 : ℝ) * (delta)) < (-1/5 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a57
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12346 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 2) < (-3/25 : ℝ))
    (a41 : -(h 0) < (-2/13 : ℝ))
    (a46 : -(h 3) < (-4/35 : ℝ))
    (a51 : -(h 4) < (-1/9 : ℝ))
    (a54 : -(h 1) < (-9/70 : ℝ))
    (a60 : -(h 5) < (-3/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a41 + (1/6 : ℝ) * a46 + (1/6 : ℝ) * a51 + (1/6 : ℝ) * a54 + (1/6 : ℝ) * a60 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12345 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a41 : -(h 0) < (-2/13 : ℝ))
    (a51 : -(h 4) < (-1/9 : ℝ))
    (a54 : -(h 1) < (-9/70 : ℝ))
    (a59 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order2 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a41 + (1/5 : ℝ) * a51 + (1/5 : ℝ) * a54 + (2/5 : ℝ) * a59 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12344 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a50 : h 2 ≤ (1/8 : ℝ))
    (a58 : -(h 2) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a50 + (1 : ℝ) * a58
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12343 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a28 : h 1 ≤ (2/15 : ℝ))
    (a57 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a28 + (1 : ℝ) * a57
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12342 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a53 : h 0 ≤ (7/45 : ℝ))
    (a56 : -(h 0) < (-7/45 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a53 + (1 : ℝ) * a56
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12341 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a55 : ((-2 : ℝ) * (delta)) < (-1/5 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a55
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12340 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a21 : -(h 1) < (-1/8 : ℝ))
    (a25 : -(h 2) < (-3/25 : ℝ))
    (a53 : -(h 0) < (-7/45 : ℝ))
    (a66 : -(h 5) < (-2/19 : ℝ))
    (a75 : -(h 4) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a21 + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a53 + (1/6 : ℝ) * a66 + (1/3 : ℝ) * a75 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12339 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a21 : -(h 1) < (-1/8 : ℝ))
    (a51 : -(h 4) < (-1/9 : ℝ))
    (a53 : -(h 0) < (-7/45 : ℝ))
    (a66 : -(h 5) < (-2/19 : ℝ))
    (a74 : -(h 3) < (-4/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order2 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a21 + (1/6 : ℝ) * a51 + (1/6 : ℝ) * a53 + (1/6 : ℝ) * a66 + (1/3 : ℝ) * a74 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12338 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 2) < (-3/25 : ℝ))
    (a51 : -(h 4) < (-1/9 : ℝ))
    (a53 : -(h 0) < (-7/45 : ℝ))
    (a66 : -(h 5) < (-2/19 : ℝ))
    (a70 : -(h 3) < (-3/26 : ℝ))
    (a73 : -(h 1) < (-6/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a51 + (1/6 : ℝ) * a53 + (1/6 : ℝ) * a66 + (1/6 : ℝ) * a70 + (1/6 : ℝ) * a73 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12337 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a55 : h 0 ≤ (3/19 : ℝ))
    (a72 : -(h 0) < (-4/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a55 + (1 : ℝ) * a72
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12336 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a71 : ((-2 : ℝ) * (delta)) < (-10/49 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a71
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12335 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a21 : -(h 1) < (-1/8 : ℝ))
    (a25 : -(h 2) < (-3/25 : ℝ))
    (a51 : -(h 4) < (-1/9 : ℝ))
    (a53 : -(h 0) < (-7/45 : ℝ))
    (a55 : h 0 ≤ (3/19 : ℝ))
    (a66 : -(h 5) < (-2/19 : ℝ))
    (a70 : -(h 3) < (-3/26 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (10/49 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-10/49 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_12336 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (4/25 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/25 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_12337 h delta _ctx _hno a55 f1
  by_cases p2 : h 1 ≤ (6/47 : ℝ)
  swap
  · have f2 : -(h 1) < (-6/47 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_12338 h delta _ctx _hno a25 a51 a53 a66 a70 f2
  by_cases p3 : h 3 ≤ (4/33 : ℝ)
  swap
  · have f3 : -(h 3) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_12339 h delta _ctx _hno a21 a51 a53 a66 f3
  by_cases p4 : h 4 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 4) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_12340 h delta _ctx _hno a21 a25 a53 a66 f4
  apply _hno 156
  change (((2 : ℝ) * (delta)) ≤ (10/49 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (6/47 : ℝ)) ∧ (h 3 ≤ (4/33 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_12334 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a63 : h 1 ≤ (6/47 : ℝ))
    (a69 : -(h 1) < (-4/31 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a63 + (1 : ℝ) * a69
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12333 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a21 : -(h 1) < (-1/8 : ℝ))
    (a25 : -(h 2) < (-3/25 : ℝ))
    (a46 : -(h 3) < (-4/35 : ℝ))
    (a51 : -(h 4) < (-1/9 : ℝ))
    (a66 : -(h 5) < (-2/19 : ℝ))
    (a68 : -(h 0) < (-3/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a21 + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a46 + (1/6 : ℝ) * a51 + (1/6 : ℝ) * a66 + (1/6 : ℝ) * a68 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12332 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a67 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a67
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12331 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 2) < (-3/25 : ℝ))
    (a53 : -(h 0) < (-7/45 : ℝ))
    (a60 : -(h 5) < (-3/29 : ℝ))
    (a63 : -(h 1) < (-6/47 : ℝ))
    (a67 : -(h 3) < (-3/26 : ℝ))
    (a73 : -(h 4) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a53 + (1/6 : ℝ) * a60 + (1/6 : ℝ) * a63 + (1/6 : ℝ) * a67 + (1/6 : ℝ) * a73 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12330 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 2) < (-3/25 : ℝ))
    (a51 : -(h 4) < (-1/9 : ℝ))
    (a53 : -(h 0) < (-7/45 : ℝ))
    (a60 : -(h 5) < (-3/29 : ℝ))
    (a63 : -(h 1) < (-6/47 : ℝ))
    (a72 : -(h 3) < (-5/43 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a51 + (1/6 : ℝ) * a53 + (1/6 : ℝ) * a60 + (1/6 : ℝ) * a63 + (1/6 : ℝ) * a72 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12329 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a50 : h 2 ≤ (1/8 : ℝ))
    (a71 : -(h 2) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a50 + (1 : ℝ) * a71
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12328 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a66 : h 1 ≤ (4/31 : ℝ))
    (a70 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a66 + (1 : ℝ) * a70
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12327 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a55 : h 0 ≤ (3/19 : ℝ))
    (a69 : -(h 0) < (-4/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a55 + (1 : ℝ) * a69
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12326 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a68 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a68
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12325 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a25 : -(h 2) < (-3/25 : ℝ))
    (a50 : h 2 ≤ (1/8 : ℝ))
    (a51 : -(h 4) < (-1/9 : ℝ))
    (a53 : -(h 0) < (-7/45 : ℝ))
    (a55 : h 0 ≤ (3/19 : ℝ))
    (a60 : -(h 5) < (-3/29 : ℝ))
    (a63 : -(h 1) < (-6/47 : ℝ))
    (a66 : h 1 ≤ (4/31 : ℝ))
    (a67 : -(h 3) < (-3/26 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_12326 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (4/25 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/25 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_12327 h delta _ctx _hno a55 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_12328 h delta _ctx _hno a66 f2
  by_cases p3 : h 2 ≤ (3/23 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_12329 h delta _ctx _hno a50 f3
  by_cases p4 : h 3 ≤ (5/43 : ℝ)
  swap
  · have f4 : -(h 3) < (-5/43 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_12330 h delta _ctx _hno a25 a51 a53 a60 a63 f4
  by_cases p5 : h 4 ≤ (4/35 : ℝ)
  swap
  · have f5 : -(h 4) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_12331 h delta _ctx _hno a25 a53 a60 a63 a67 f5
  apply _hno 45
  change (((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (5/43 : ℝ)) ∧ (h 4 ≤ (4/35 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_12324 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 2) < (-3/25 : ℝ))
    (a46 : -(h 3) < (-4/35 : ℝ))
    (a51 : -(h 4) < (-1/9 : ℝ))
    (a53 : -(h 0) < (-7/45 : ℝ))
    (a60 : -(h 5) < (-3/29 : ℝ))
    (a66 : -(h 1) < (-4/31 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a46 + (1/6 : ℝ) * a51 + (1/6 : ℝ) * a53 + (1/6 : ℝ) * a60 + (1/6 : ℝ) * a66 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12323 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 2) < (-3/25 : ℝ))
    (a46 : -(h 3) < (-4/35 : ℝ))
    (a51 : -(h 4) < (-1/9 : ℝ))
    (a60 : -(h 5) < (-3/29 : ℝ))
    (a63 : -(h 1) < (-6/47 : ℝ))
    (a65 : -(h 0) < (-3/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a46 + (1/6 : ℝ) * a51 + (1/6 : ℝ) * a60 + (1/6 : ℝ) * a63 + (1/6 : ℝ) * a65 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12322 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a64 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a64
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12321 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a21 : -(h 1) < (-1/8 : ℝ))
    (a25 : -(h 2) < (-3/25 : ℝ))
    (a46 : -(h 3) < (-4/35 : ℝ))
    (a51 : -(h 4) < (-1/9 : ℝ))
    (a53 : -(h 0) < (-7/45 : ℝ))
    (a55 : h 0 ≤ (3/19 : ℝ))
    (a63 : h 1 ≤ (6/47 : ℝ))
    (a66 : -(h 5) < (-2/19 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_12332 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (3/19 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/19 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_12333 h delta _ctx _hno a21 a25 a46 a51 a66 f1
  by_cases p2 : h 1 ≤ (4/31 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/31 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_12334 h delta _ctx _hno a63 f2
  by_cases p3 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f3 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_12335 h delta _ctx _hno a17 a21 a25 a51 a53 a55 a66 f3
  apply _hno 154
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (4/31 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_12320 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a21 : -(h 1) < (-1/8 : ℝ))
    (a25 : -(h 2) < (-3/25 : ℝ))
    (a53 : -(h 0) < (-7/45 : ℝ))
    (a60 : -(h 5) < (-3/29 : ℝ))
    (a65 : -(h 4) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a21 + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a53 + (1/6 : ℝ) * a60 + (1/3 : ℝ) * a65 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12319 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a21 : -(h 1) < (-1/8 : ℝ))
    (a46 : -(h 3) < (-4/35 : ℝ))
    (a51 : -(h 4) < (-1/9 : ℝ))
    (a53 : -(h 0) < (-7/45 : ℝ))
    (a60 : -(h 5) < (-3/29 : ℝ))
    (a64 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a21 + (1/6 : ℝ) * a46 + (1/6 : ℝ) * a51 + (1/6 : ℝ) * a53 + (1/6 : ℝ) * a60 + (1/6 : ℝ) * a64 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12318 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a25 : -(h 2) < (-3/25 : ℝ))
    (a46 : -(h 3) < (-4/35 : ℝ))
    (a50 : h 2 ≤ (1/8 : ℝ))
    (a51 : -(h 4) < (-1/9 : ℝ))
    (a53 : -(h 0) < (-7/45 : ℝ))
    (a55 : h 0 ≤ (3/19 : ℝ))
    (a60 : -(h 5) < (-3/29 : ℝ))
    (a63 : -(h 1) < (-6/47 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_12322 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (3/19 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/19 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_12323 h delta _ctx _hno a25 a46 a51 a60 a63 f1
  by_cases p2 : h 1 ≤ (4/31 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/31 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_12324 h delta _ctx _hno a25 a46 a51 a53 a60 f2
  by_cases p3 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f3 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_12325 h delta _ctx _hno a17 a25 a50 a51 a53 a55 a60 a63 p2 f3
  apply _hno 154
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (4/31 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_12317 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a55 : h 0 ≤ (3/19 : ℝ))
    (a62 : -(h 0) < (-8/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a55 + (1 : ℝ) * a62
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12316 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a61 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a61
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12315 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 2) < (-3/25 : ℝ))
    (a46 : -(h 3) < (-4/35 : ℝ))
    (a53 : -(h 0) < (-7/45 : ℝ))
    (a56 : -(h 1) < (-5/38 : ℝ))
    (a62 : -(h 4) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a25 + (1/5 : ℝ) * a46 + (1/5 : ℝ) * a53 + (1/5 : ℝ) * a56 + (1/5 : ℝ) * a62 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

end RealPinwheel.WeakSevenBandData
