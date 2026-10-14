import Pinwheel.WeakSevenBandData.CoverChunks.New099

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem new_node_5114 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a22 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a22
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5113 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a20 : -(h 0) < (-4/21 : ℝ))
    (a25 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 1) < (-3/26 : ℝ))
    (a35 : -(h 5) < (-5/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order2 + (1/6 : ℝ) * _ctx.order4 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a20 + (1/3 : ℝ) * a25 + (1/6 : ℝ) * a28 + (1/3 : ℝ) * a35 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5112 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a20 : -(h 0) < (-4/21 : ℝ))
    (a25 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 1) < (-3/26 : ℝ))
    (a34 : -(h 4) < (-3/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order2 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a20 + (2/5 : ℝ) * a25 + (1/5 : ℝ) * a28 + (1/5 : ℝ) * a34 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5111 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : h 2 ≤ (9/80 : ℝ))
    (a33 : -(h 3) < (-4/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * _ctx.order2 + (1 : ℝ) * a24 + (1 : ℝ) * a33
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5110 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : h 2 ≤ (9/80 : ℝ))
    (a32 : -(h 2) < (-5/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a24 + (1 : ℝ) * a32
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5109 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 4) < (-5/48 : ℝ))
    (a20 : -(h 0) < (-4/21 : ℝ))
    (a25 : -(h 3) < (-1/9 : ℝ))
    (a31 : -(h 1) < (-7/57 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order2 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a17 + (1/5 : ℝ) * a20 + (2/5 : ℝ) * a25 + (1/5 : ℝ) * a31 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5108 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : h 0 ≤ (5/26 : ℝ))
    (a30 : -(h 0) < (-1/5 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a30
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5107 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a29 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a29
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5106 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : -(h 0) < (-5/26 : ℝ))
    (a38 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order1 + (2/5 : ℝ) * _ctx.order2 + (3/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a27 + (4/5 : ℝ) * a38 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5105 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 3) < (-1/9 : ℝ))
    (a27 : -(h 0) < (-5/26 : ℝ))
    (a33 : -(h 4) < (-3/28 : ℝ))
    (a37 : -(h 2) < (-6/53 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order1 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a25 + (1/5 : ℝ) * a27 + (1/5 : ℝ) * a33 + (2/5 : ℝ) * a37 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5104 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a30 : h 1 ≤ (7/57 : ℝ))
    (a36 : -(h 1) < (-7/53 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a36
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5103 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 3) < (-1/9 : ℝ))
    (a33 : -(h 4) < (-3/28 : ℝ))
    (a35 : -(h 0) < (-1/5 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order1 + (2/5 : ℝ) * _ctx.order2 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (3/5 : ℝ) * a25 + (1/5 : ℝ) * a33 + (1/5 : ℝ) * a35 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5102 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a34
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5101 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 3) < (-1/9 : ℝ))
    (a27 : -(h 0) < (-5/26 : ℝ))
    (a34 : -(h 5) < (-5/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order1 + (1/3 : ℝ) * _ctx.order2 + (1/6 : ℝ) * _ctx.order4 + (1/6 : ℝ) * _ctx.lower + (1/2 : ℝ) * a25 + (1/6 : ℝ) * a27 + (1/3 : ℝ) * a34 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5100 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a25 : -(h 3) < (-1/9 : ℝ))
    (a27 : -(h 0) < (-5/26 : ℝ))
    (a30 : h 1 ≤ (7/57 : ℝ))
    (a33 : -(h 4) < (-3/28 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_5102 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (1/5 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/5 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_5103 h delta _ctx _hno a25 a33 f1
  by_cases p2 : h 1 ≤ (7/53 : ℝ)
  swap
  · have f2 : -(h 1) < (-7/53 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_5104 h delta _ctx _hno a30 f2
  by_cases p3 : h 2 ≤ (6/53 : ℝ)
  swap
  · have f3 : -(h 2) < (-6/53 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_5105 h delta _ctx _hno a25 a27 a33 f3
  by_cases p4 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_5106 h delta _ctx _hno a27 f4
  apply _hno 74
  change (((2 : ℝ) * (delta)) ≤ (8/39 : ℝ)) ∧ (h 0 ≤ (1/5 : ℝ)) ∧ (h 1 ≤ (7/53 : ℝ)) ∧ (h 2 ≤ (6/53 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_5099 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : h 2 ≤ (9/80 : ℝ))
    (a32 : -(h 3) < (-4/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * _ctx.order2 + (1 : ℝ) * a24 + (1 : ℝ) * a32
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5098 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : h 2 ≤ (9/80 : ℝ))
    (a31 : -(h 2) < (-5/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a24 + (1 : ℝ) * a31
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5097 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 4) < (-5/48 : ℝ))
    (a25 : -(h 3) < (-1/9 : ℝ))
    (a27 : -(h 0) < (-5/26 : ℝ))
    (a30 : -(h 1) < (-7/57 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order2 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a17 + (2/5 : ℝ) * a25 + (1/5 : ℝ) * a27 + (1/5 : ℝ) * a30 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5096 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 4) < (-5/48 : ℝ))
    (a25 : -(h 3) < (-1/9 : ℝ))
    (a29 : -(h 0) < (-1/5 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order1 + (2/5 : ℝ) * _ctx.order2 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a17 + (3/5 : ℝ) * a25 + (1/5 : ℝ) * a29 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5095 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a28 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a28
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5094 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a17 : -(h 4) < (-5/48 : ℝ))
    (a20 : -(h 0) < (-4/21 : ℝ))
    (a24 : h 2 ≤ (9/80 : ℝ))
    (a25 : -(h 3) < (-1/9 : ℝ))
    (a27 : h 0 ≤ (5/26 : ℝ))
    (a28 : -(h 1) < (-3/26 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_5107 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (1/5 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/5 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_5108 h delta _ctx _hno a27 f1
  by_cases p2 : h 1 ≤ (7/57 : ℝ)
  swap
  · have f2 : -(h 1) < (-7/57 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_5109 h delta _ctx _hno a17 a20 a25 f2
  by_cases p3 : h 2 ≤ (5/41 : ℝ)
  swap
  · have f3 : -(h 2) < (-5/41 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_5110 h delta _ctx _hno a24 f3
  by_cases p4 : h 3 ≤ (4/33 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_5111 h delta _ctx _hno a24 f4
  by_cases p5 : h 4 ≤ (3/28 : ℝ)
  swap
  · have f5 : -(h 4) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_5112 h delta _ctx _hno a20 a25 a28 f5
  by_cases p6 : h 5 ≤ (5/47 : ℝ)
  swap
  · have f6 : -(h 5) < (-5/47 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact new_node_5113 h delta _ctx _hno a20 a25 a28 f6
  apply _hno 106
  change (((2 : ℝ) * (delta)) ≤ (10/47 : ℝ)) ∧ (h 0 ≤ (1/5 : ℝ)) ∧ (h 1 ≤ (7/57 : ℝ)) ∧ (h 2 ≤ (5/41 : ℝ)) ∧ (h 3 ≤ (4/33 : ℝ)) ∧ (h 4 ≤ (3/28 : ℝ)) ∧ (h 5 ≤ (5/47 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem new_node_5093 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a17 : -(h 4) < (-5/48 : ℝ))
    (a24 : h 2 ≤ (9/80 : ℝ))
    (a25 : -(h 3) < (-1/9 : ℝ))
    (a27 : -(h 0) < (-5/26 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_5095 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (1/5 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/5 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_5096 h delta _ctx _hno a17 a25 f1
  by_cases p2 : h 1 ≤ (7/57 : ℝ)
  swap
  · have f2 : -(h 1) < (-7/57 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_5097 h delta _ctx _hno a17 a25 a27 f2
  by_cases p3 : h 2 ≤ (5/41 : ℝ)
  swap
  · have f3 : -(h 2) < (-5/41 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_5098 h delta _ctx _hno a24 f3
  by_cases p4 : h 3 ≤ (4/33 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_5099 h delta _ctx _hno a24 f4
  by_cases p5 : h 4 ≤ (3/28 : ℝ)
  swap
  · have f5 : -(h 4) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_5100 h delta _ctx _hno a13 a25 a27 p2 f5
  by_cases p6 : h 5 ≤ (5/47 : ℝ)
  swap
  · have f6 : -(h 5) < (-5/47 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact new_node_5101 h delta _ctx _hno a25 a27 f6
  apply _hno 106
  change (((2 : ℝ) * (delta)) ≤ (10/47 : ℝ)) ∧ (h 0 ≤ (1/5 : ℝ)) ∧ (h 1 ≤ (7/57 : ℝ)) ∧ (h 2 ≤ (5/41 : ℝ)) ∧ (h 3 ≤ (4/33 : ℝ)) ∧ (h 4 ≤ (3/28 : ℝ)) ∧ (h 5 ≤ (5/47 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem new_node_5092 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a26 : ((-2 : ℝ) * (delta)) < (-3/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a26
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5091 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a20 : -(h 0) < (-4/21 : ℝ))
    (a24 : -(h 2) < (-9/80 : ℝ))
    (a27 : -(h 1) < (-3/26 : ℝ))
    (a38 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a20 + (1/5 : ℝ) * a24 + (1/5 : ℝ) * a27 + (2/5 : ℝ) * a38 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5090 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a20 : -(h 0) < (-4/21 : ℝ))
    (a27 : -(h 1) < (-3/26 : ℝ))
    (a33 : -(h 4) < (-3/28 : ℝ))
    (a37 : -(h 2) < (-6/53 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a20 + (1/5 : ℝ) * a27 + (2/5 : ℝ) * a33 + (1/5 : ℝ) * a37 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5089 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a30 : h 1 ≤ (7/57 : ℝ))
    (a36 : -(h 1) < (-7/53 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a36
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5088 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : h 0 ≤ (5/26 : ℝ))
    (a35 : -(h 0) < (-1/5 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a26 + (1 : ℝ) * a35
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5087 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a34
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5086 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a20 : -(h 0) < (-4/21 : ℝ))
    (a24 : -(h 2) < (-9/80 : ℝ))
    (a27 : -(h 1) < (-3/26 : ℝ))
    (a34 : -(h 5) < (-5/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/3 : ℝ) * _ctx.order4 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a20 + (1/6 : ℝ) * a24 + (1/6 : ℝ) * a27 + (1/2 : ℝ) * a34 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5085 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a20 : -(h 0) < (-4/21 : ℝ))
    (a24 : -(h 2) < (-9/80 : ℝ))
    (a26 : h 0 ≤ (5/26 : ℝ))
    (a27 : -(h 1) < (-3/26 : ℝ))
    (a30 : h 1 ≤ (7/57 : ℝ))
    (a33 : -(h 4) < (-3/28 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_5087 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (1/5 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/5 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_5088 h delta _ctx _hno a26 f1
  by_cases p2 : h 1 ≤ (7/53 : ℝ)
  swap
  · have f2 : -(h 1) < (-7/53 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_5089 h delta _ctx _hno a30 f2
  by_cases p3 : h 2 ≤ (6/53 : ℝ)
  swap
  · have f3 : -(h 2) < (-6/53 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_5090 h delta _ctx _hno a20 a27 a33 f3
  by_cases p4 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_5091 h delta _ctx _hno a20 a24 a27 f4
  apply _hno 74
  change (((2 : ℝ) * (delta)) ≤ (8/39 : ℝ)) ∧ (h 0 ≤ (1/5 : ℝ)) ∧ (h 1 ≤ (7/53 : ℝ)) ∧ (h 2 ≤ (6/53 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_5084 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a20 : -(h 0) < (-4/21 : ℝ))
    (a32 : -(h 3) < (-4/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.order1 + (1/2 : ℝ) * _ctx.order2 + (1/4 : ℝ) * _ctx.order4 + (1/2 : ℝ) * _ctx.min + (3/4 : ℝ) * _ctx.lower + (1/4 : ℝ) * a20 + (3/4 : ℝ) * a32 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5083 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 4) < (-5/48 : ℝ))
    (a20 : -(h 0) < (-4/21 : ℝ))
    (a31 : -(h 2) < (-5/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order1 + (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (2/5 : ℝ) * a17 + (1/5 : ℝ) * a20 + (2/5 : ℝ) * a31 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5082 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 4) < (-5/48 : ℝ))
    (a20 : -(h 0) < (-4/21 : ℝ))
    (a24 : -(h 2) < (-9/80 : ℝ))
    (a30 : -(h 1) < (-7/57 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (2/5 : ℝ) * a17 + (1/5 : ℝ) * a20 + (1/5 : ℝ) * a24 + (1/5 : ℝ) * a30 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5081 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : h 0 ≤ (5/26 : ℝ))
    (a29 : -(h 0) < (-1/5 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a26 + (1 : ℝ) * a29
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5080 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a28 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a28
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5079 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : -(h 0) < (-5/26 : ℝ))
    (a36 : -(h 2) < (-6/53 : ℝ))
    (a42 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order1 + (1/6 : ℝ) * _ctx.order3 + (1/3 : ℝ) * _ctx.order4 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a26 + (1/3 : ℝ) * a36 + (1/2 : ℝ) * a42 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5078 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : -(h 0) < (-5/26 : ℝ))
    (a32 : -(h 4) < (-3/28 : ℝ))
    (a36 : -(h 2) < (-6/53 : ℝ))
    (a41 : -(h 3) < (-6/53 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order1 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a26 + (1/5 : ℝ) * a32 + (2/5 : ℝ) * a36 + (1/5 : ℝ) * a41 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5077 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : -(h 0) < (-5/26 : ℝ))
    (a32 : -(h 4) < (-3/28 : ℝ))
    (a40 : -(h 2) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order1 + (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a26 + (2/5 : ℝ) * a32 + (2/5 : ℝ) * a40 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5076 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : -(h 0) < (-5/26 : ℝ))
    (a32 : -(h 4) < (-3/28 : ℝ))
    (a36 : -(h 2) < (-6/53 : ℝ))
    (a39 : -(h 1) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a26 + (2/5 : ℝ) * a32 + (1/5 : ℝ) * a36 + (1/5 : ℝ) * a39 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5075 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a32 : -(h 4) < (-3/28 : ℝ))
    (a36 : -(h 2) < (-6/53 : ℝ))
    (a38 : -(h 0) < (-1/5 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order1 + (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (2/5 : ℝ) * a32 + (2/5 : ℝ) * a36 + (1/5 : ℝ) * a38 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5074 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a37 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a37
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5073 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : -(h 2) < (-9/80 : ℝ))
    (a26 : -(h 0) < (-5/26 : ℝ))
    (a37 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order1 + (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (2/5 : ℝ) * a24 + (1/5 : ℝ) * a26 + (2/5 : ℝ) * a37 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5072 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a26 : -(h 0) < (-5/26 : ℝ))
    (a32 : -(h 4) < (-3/28 : ℝ))
    (a36 : -(h 2) < (-6/53 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_5074 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (1/5 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/5 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_5075 h delta _ctx _hno a32 a36 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_5076 h delta _ctx _hno a26 a32 a36 f2
  by_cases p3 : h 2 ≤ (4/35 : ℝ)
  swap
  · have f3 : -(h 2) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_5077 h delta _ctx _hno a26 a32 f3
  by_cases p4 : h 3 ≤ (6/53 : ℝ)
  swap
  · have f4 : -(h 3) < (-6/53 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_5078 h delta _ctx _hno a26 a32 a36 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_5079 h delta _ctx _hno a26 a36 f5
  apply _hno 112
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (1/5 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 2 ≤ (4/35 : ℝ)) ∧ (h 3 ≤ (6/53 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_5071 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a29 : h 1 ≤ (7/57 : ℝ))
    (a35 : -(h 1) < (-7/53 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a35
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5070 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : -(h 2) < (-9/80 : ℝ))
    (a32 : -(h 4) < (-3/28 : ℝ))
    (a34 : -(h 0) < (-1/5 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order1 + (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (2/5 : ℝ) * a24 + (2/5 : ℝ) * a32 + (1/5 : ℝ) * a34 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5069 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a33 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a33
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5068 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : -(h 2) < (-9/80 : ℝ))
    (a26 : -(h 0) < (-5/26 : ℝ))
    (a33 : -(h 5) < (-5/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order1 + (1/6 : ℝ) * _ctx.order3 + (1/3 : ℝ) * _ctx.order4 + (1/6 : ℝ) * _ctx.lower + (1/3 : ℝ) * a24 + (1/6 : ℝ) * a26 + (1/2 : ℝ) * a33 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5067 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a24 : -(h 2) < (-9/80 : ℝ))
    (a26 : -(h 0) < (-5/26 : ℝ))
    (a29 : h 1 ≤ (7/57 : ℝ))
    (a32 : -(h 4) < (-3/28 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_5069 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (1/5 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/5 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_5070 h delta _ctx _hno a24 a32 f1
  by_cases p2 : h 1 ≤ (7/53 : ℝ)
  swap
  · have f2 : -(h 1) < (-7/53 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_5071 h delta _ctx _hno a29 f2
  by_cases p3 : h 2 ≤ (6/53 : ℝ)
  swap
  · have f3 : -(h 2) < (-6/53 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_5072 h delta _ctx _hno a13 a26 a32 f3
  by_cases p4 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_5073 h delta _ctx _hno a24 a26 f4
  apply _hno 74
  change (((2 : ℝ) * (delta)) ≤ (8/39 : ℝ)) ∧ (h 0 ≤ (1/5 : ℝ)) ∧ (h 1 ≤ (7/53 : ℝ)) ∧ (h 2 ≤ (6/53 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_5066 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : -(h 0) < (-5/26 : ℝ))
    (a31 : -(h 3) < (-4/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.order1 + (1/2 : ℝ) * _ctx.order2 + (1/4 : ℝ) * _ctx.order4 + (1/2 : ℝ) * _ctx.min + (3/4 : ℝ) * _ctx.lower + (1/4 : ℝ) * a26 + (3/4 : ℝ) * a31 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5065 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 4) < (-5/48 : ℝ))
    (a26 : -(h 0) < (-5/26 : ℝ))
    (a30 : -(h 2) < (-5/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order1 + (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (2/5 : ℝ) * a17 + (1/5 : ℝ) * a26 + (2/5 : ℝ) * a30 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5064 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 4) < (-5/48 : ℝ))
    (a24 : -(h 2) < (-9/80 : ℝ))
    (a26 : -(h 0) < (-5/26 : ℝ))
    (a29 : -(h 1) < (-7/57 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (2/5 : ℝ) * a17 + (1/5 : ℝ) * a24 + (1/5 : ℝ) * a26 + (1/5 : ℝ) * a29 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5063 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 4) < (-5/48 : ℝ))
    (a24 : -(h 2) < (-9/80 : ℝ))
    (a28 : -(h 0) < (-1/5 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order1 + (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (2/5 : ℝ) * a17 + (2/5 : ℝ) * a24 + (1/5 : ℝ) * a28 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5062 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a27
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5061 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a17 : -(h 4) < (-5/48 : ℝ))
    (a20 : -(h 0) < (-4/21 : ℝ))
    (a24 : -(h 2) < (-9/80 : ℝ))
    (a26 : h 0 ≤ (5/26 : ℝ))
    (a27 : -(h 1) < (-3/26 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_5080 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (1/5 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/5 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_5081 h delta _ctx _hno a26 f1
  by_cases p2 : h 1 ≤ (7/57 : ℝ)
  swap
  · have f2 : -(h 1) < (-7/57 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_5082 h delta _ctx _hno a17 a20 a24 f2
  by_cases p3 : h 2 ≤ (5/41 : ℝ)
  swap
  · have f3 : -(h 2) < (-5/41 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_5083 h delta _ctx _hno a17 a20 f3
  by_cases p4 : h 3 ≤ (4/33 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_5084 h delta _ctx _hno a20 f4
  by_cases p5 : h 4 ≤ (3/28 : ℝ)
  swap
  · have f5 : -(h 4) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_5085 h delta _ctx _hno a13 a20 a24 a26 a27 p2 f5
  by_cases p6 : h 5 ≤ (5/47 : ℝ)
  swap
  · have f6 : -(h 5) < (-5/47 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact new_node_5086 h delta _ctx _hno a20 a24 a27 f6
  apply _hno 106
  change (((2 : ℝ) * (delta)) ≤ (10/47 : ℝ)) ∧ (h 0 ≤ (1/5 : ℝ)) ∧ (h 1 ≤ (7/57 : ℝ)) ∧ (h 2 ≤ (5/41 : ℝ)) ∧ (h 3 ≤ (4/33 : ℝ)) ∧ (h 4 ≤ (3/28 : ℝ)) ∧ (h 5 ≤ (5/47 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem new_node_5060 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a17 : -(h 4) < (-5/48 : ℝ))
    (a24 : -(h 2) < (-9/80 : ℝ))
    (a26 : -(h 0) < (-5/26 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_5062 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (1/5 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/5 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_5063 h delta _ctx _hno a17 a24 f1
  by_cases p2 : h 1 ≤ (7/57 : ℝ)
  swap
  · have f2 : -(h 1) < (-7/57 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_5064 h delta _ctx _hno a17 a24 a26 f2
  by_cases p3 : h 2 ≤ (5/41 : ℝ)
  swap
  · have f3 : -(h 2) < (-5/41 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_5065 h delta _ctx _hno a17 a26 f3
  by_cases p4 : h 3 ≤ (4/33 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_5066 h delta _ctx _hno a26 f4
  by_cases p5 : h 4 ≤ (3/28 : ℝ)
  swap
  · have f5 : -(h 4) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_5067 h delta _ctx _hno a13 a24 a26 p2 f5
  by_cases p6 : h 5 ≤ (5/47 : ℝ)
  swap
  · have f6 : -(h 5) < (-5/47 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact new_node_5068 h delta _ctx _hno a24 a26 f6
  apply _hno 106
  change (((2 : ℝ) * (delta)) ≤ (10/47 : ℝ)) ∧ (h 0 ≤ (1/5 : ℝ)) ∧ (h 1 ≤ (7/57 : ℝ)) ∧ (h 2 ≤ (5/41 : ℝ)) ∧ (h 3 ≤ (4/33 : ℝ)) ∧ (h 4 ≤ (3/28 : ℝ)) ∧ (h 5 ≤ (5/47 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem new_node_5059 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a25 : ((-2 : ℝ) * (delta)) < (-3/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a25
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5058 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a22 : -(h 0) < (-1/5 : ℝ))
    (a30 : -(h 2) < (-7/64 : ℝ))
    (a32 : -(h 1) < (-3/26 : ℝ))
    (a37 : -(h 5) < (-2/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/3 : ℝ) * _ctx.order4 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a22 + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a32 + (1/2 : ℝ) * a37 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5057 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 4) < (-5/48 : ℝ))
    (a22 : -(h 0) < (-1/5 : ℝ))
    (a30 : -(h 2) < (-7/64 : ℝ))
    (a32 : -(h 1) < (-3/26 : ℝ))
    (a36 : -(h 3) < (-3/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a17 + (1/5 : ℝ) * a22 + (1/5 : ℝ) * a30 + (1/5 : ℝ) * a32 + (1/5 : ℝ) * a36 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5056 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 4) < (-5/48 : ℝ))
    (a22 : -(h 0) < (-1/5 : ℝ))
    (a32 : -(h 1) < (-3/26 : ℝ))
    (a35 : -(h 2) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (2/5 : ℝ) * a17 + (1/5 : ℝ) * a22 + (1/5 : ℝ) * a32 + (1/5 : ℝ) * a35 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5055 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 4) < (-5/48 : ℝ))
    (a22 : -(h 0) < (-1/5 : ℝ))
    (a30 : -(h 2) < (-7/64 : ℝ))
    (a34 : -(h 1) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (2/5 : ℝ) * a17 + (1/5 : ℝ) * a22 + (1/5 : ℝ) * a30 + (1/5 : ℝ) * a34 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5054 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a33 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a33
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5053 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a22 : -(h 0) < (-1/5 : ℝ))
    (a27 : -(h 1) < (-6/53 : ℝ))
    (a30 : -(h 2) < (-7/64 : ℝ))
    (a33 : -(h 4) < (-3/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a22 + (1/5 : ℝ) * a27 + (1/5 : ℝ) * a30 + (2/5 : ℝ) * a33 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5052 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a17 : -(h 4) < (-5/48 : ℝ))
    (a22 : -(h 0) < (-1/5 : ℝ))
    (a30 : -(h 2) < (-7/64 : ℝ))
    (a32 : -(h 1) < (-3/26 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_5054 h delta _ctx _hno a13 f0
  by_cases p1 : h 1 ≤ (2/17 : ℝ)
  swap
  · have f1 : -(h 1) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_5055 h delta _ctx _hno a17 a22 a30 f1
  by_cases p2 : h 2 ≤ (1/9 : ℝ)
  swap
  · have f2 : -(h 2) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_5056 h delta _ctx _hno a17 a22 a32 f2
  by_cases p3 : h 3 ≤ (3/28 : ℝ)
  swap
  · have f3 : -(h 3) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_5057 h delta _ctx _hno a17 a22 a30 a32 f3
  by_cases p4 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f4 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_5058 h delta _ctx _hno a22 a30 a32 f4
  apply _hno 235
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 1 ≤ (2/17 : ℝ)) ∧ (h 2 ≤ (1/9 : ℝ)) ∧ (h 3 ≤ (3/28 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_5051 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a31 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a31
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5050 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 4) < (-5/48 : ℝ))
    (a22 : -(h 0) < (-1/5 : ℝ))
    (a25 : -(h 2) < (-3/28 : ℝ))
    (a29 : -(h 1) < (-2/17 : ℝ))
    (a33 : -(h 3) < (-2/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a17 + (1/5 : ℝ) * a22 + (1/5 : ℝ) * a25 + (1/5 : ℝ) * a29 + (1/5 : ℝ) * a33 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5049 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 4) < (-5/48 : ℝ))
    (a22 : -(h 0) < (-1/5 : ℝ))
    (a29 : -(h 1) < (-2/17 : ℝ))
    (a32 : -(h 2) < (-5/46 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (2/5 : ℝ) * a17 + (1/5 : ℝ) * a22 + (1/5 : ℝ) * a29 + (1/5 : ℝ) * a32 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5048 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : h 1 ≤ (1/8 : ℝ))
    (a31 : -(h 1) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a31
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5047 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a30 : ((-2 : ℝ) * (delta)) < (-7/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a30
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5046 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a17 : -(h 4) < (-5/48 : ℝ))
    (a22 : -(h 0) < (-1/5 : ℝ))
    (a27 : -(h 1) < (-6/53 : ℝ))
    (a30 : -(h 2) < (-7/64 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_5051 h delta _ctx _hno a13 f0
  by_cases p1 : h 1 ≤ (3/26 : ℝ)
  swap
  · have f1 : -(h 1) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_5052 h delta _ctx _hno a13 a17 a22 a30 f1
  by_cases p2 : h 4 ≤ (3/28 : ℝ)
  swap
  · have f2 : -(h 4) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_5053 h delta _ctx _hno a22 a27 a30 f2
  apply _hno 234
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 1 ≤ (3/26 : ℝ)) ∧ (h 4 ≤ (3/28 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem new_node_5045 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a16 : h 1 ≤ (1/8 : ℝ))
    (a17 : -(h 4) < (-5/48 : ℝ))
    (a22 : -(h 0) < (-1/5 : ℝ))
    (a25 : -(h 2) < (-3/28 : ℝ))
    (a29 : -(h 1) < (-2/17 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/33 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/33 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_5047 h delta _ctx _hno a13 f0
  by_cases p1 : h 1 ≤ (3/23 : ℝ)
  swap
  · have f1 : -(h 1) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_5048 h delta _ctx _hno a16 f1
  by_cases p2 : h 2 ≤ (5/46 : ℝ)
  swap
  · have f2 : -(h 2) < (-5/46 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_5049 h delta _ctx _hno a17 a22 a29 f2
  by_cases p3 : h 3 ≤ (2/19 : ℝ)
  swap
  · have f3 : -(h 3) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_5050 h delta _ctx _hno a17 a22 a25 a29 f3
  apply _hno 231
  change (((2 : ℝ) * (delta)) ≤ (7/33 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 2 ≤ (5/46 : ℝ)) ∧ (h 3 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_5044 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a28 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a28
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5043 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 4) < (-5/48 : ℝ))
    (a22 : -(h 0) < (-1/5 : ℝ))
    (a28 : -(h 2) < (-7/62 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order1 + (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (2/5 : ℝ) * a17 + (1/5 : ℝ) * a22 + (2/5 : ℝ) * a28 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5042 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a16 : h 1 ≤ (1/8 : ℝ))
    (a17 : -(h 4) < (-5/48 : ℝ))
    (a22 : -(h 0) < (-1/5 : ℝ))
    (a25 : -(h 2) < (-3/28 : ℝ))
    (a27 : -(h 1) < (-6/53 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_5044 h delta _ctx _hno a13 f0
  by_cases p1 : h 1 ≤ (2/17 : ℝ)
  swap
  · have f1 : -(h 1) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_5045 h delta _ctx _hno a13 a16 a17 a22 a25 f1
  by_cases p2 : h 2 ≤ (7/64 : ℝ)
  swap
  · have f2 : -(h 2) < (-7/64 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_5046 h delta _ctx _hno a13 a17 a22 a27 f2
  apply _hno 219
  change (((2 : ℝ) * (delta)) ≤ (7/32 : ℝ)) ∧ (h 1 ≤ (2/17 : ℝ)) ∧ (h 2 ≤ (7/64 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem new_node_5041 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a26 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a26
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5040 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a16 : h 1 ≤ (1/8 : ℝ))
    (a17 : -(h 4) < (-5/48 : ℝ))
    (a22 : -(h 0) < (-1/5 : ℝ))
    (a25 : -(h 2) < (-3/28 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_5041 h delta _ctx _hno a13 f0
  by_cases p1 : h 1 ≤ (6/53 : ℝ)
  swap
  · have f1 : -(h 1) < (-6/53 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_5042 h delta _ctx _hno a13 a16 a17 a22 a25 f1
  by_cases p2 : h 2 ≤ (7/62 : ℝ)
  swap
  · have f2 : -(h 2) < (-7/62 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_5043 h delta _ctx _hno a17 a22 f2
  apply _hno 220
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 1 ≤ (6/53 : ℝ)) ∧ (h 2 ≤ (7/62 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem new_node_5039 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : h 1 ≤ (1/8 : ℝ))
    (a24 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a24
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5038 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a23 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a23
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5037 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a17 : -(h 4) < (-5/48 : ℝ))
    (a20 : -(h 0) < (-4/21 : ℝ))
    (a24 : h 2 ≤ (9/80 : ℝ))
    (a25 : -(h 3) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/13 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_5092 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (5/26 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/26 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_5093 h delta _ctx _hno a13 a17 a24 a25 f1
  by_cases p2 : h 1 ≤ (3/26 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_5094 h delta _ctx _hno a13 a17 a20 a24 a25 p1 f2
  apply _hno 3
  change (((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)) ∧ (h 0 ≤ (5/26 : ℝ)) ∧ (h 1 ≤ (3/26 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem new_node_5036 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a17 : -(h 4) < (-5/48 : ℝ))
    (a20 : -(h 0) < (-4/21 : ℝ))
    (a24 : -(h 2) < (-9/80 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/13 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_5059 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (5/26 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/26 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_5060 h delta _ctx _hno a13 a17 a24 f1
  by_cases p2 : h 1 ≤ (3/26 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_5061 h delta _ctx _hno a13 a17 a20 a24 p1 f2
  apply _hno 3
  change (((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)) ∧ (h 0 ≤ (5/26 : ℝ)) ∧ (h 1 ≤ (3/26 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem new_node_5035 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : h 1 ≤ (1/8 : ℝ))
    (a23 : -(h 1) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a23
  exact (lt_irrefl (0 : ℝ)) hbad

end RealPinwheel.WeakSevenBandData
