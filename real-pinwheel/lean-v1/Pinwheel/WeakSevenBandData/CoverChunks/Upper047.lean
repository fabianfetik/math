import Pinwheel.WeakSevenBandData.CoverChunks.Upper046

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem upper_node_547 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a33 : -(h 0) < (-7/45 : ℝ))
    (a37 : -(h 2) < (-7/60 : ℝ))
    (a40 : -(h 1) < (-9/71 : ℝ))
    (a45 : -(h 3) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (1/20 : ℝ) * a14 + (1/5 : ℝ) * a28 + (3/20 : ℝ) * a33 + (1/5 : ℝ) * a37 + (1/5 : ℝ) * a40 + (1/5 : ℝ) * a45 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_546 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a33 : -(h 0) < (-7/45 : ℝ))
    (a40 : -(h 1) < (-9/71 : ℝ))
    (a44 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (1/20 : ℝ) * a14 + (1/5 : ℝ) * a23 + (1/5 : ℝ) * a28 + (3/20 : ℝ) * a33 + (1/5 : ℝ) * a40 + (1/5 : ℝ) * a44 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_545 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a33 : -(h 0) < (-7/45 : ℝ))
    (a37 : -(h 2) < (-7/60 : ℝ))
    (a43 : -(h 1) < (-4/31 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (1/20 : ℝ) * a14 + (1/5 : ℝ) * a23 + (1/5 : ℝ) * a28 + (3/20 : ℝ) * a33 + (1/5 : ℝ) * a37 + (1/5 : ℝ) * a43 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_544 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a37 : -(h 2) < (-7/60 : ℝ))
    (a40 : -(h 1) < (-9/71 : ℝ))
    (a42 : -(h 0) < (-3/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (1/20 : ℝ) * a14 + (1/5 : ℝ) * a23 + (1/5 : ℝ) * a28 + (1/5 : ℝ) * a37 + (1/5 : ℝ) * a40 + (3/20 : ℝ) * a42 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_543 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a33 : -(h 0) < (-7/45 : ℝ))
    (a37 : -(h 2) < (-7/60 : ℝ))
    (a40 : -(h 1) < (-9/71 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a23 + (1/6 : ℝ) * a28 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a40 + (1/6 : ℝ) * a41 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_542 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a33 : -(h 0) < (-7/45 : ℝ))
    (a37 : -(h 2) < (-7/60 : ℝ))
    (a40 : -(h 1) < (-9/71 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_543 h delta _ctx _hno a23 a28 a33 a37 a40 f0
  by_cases p1 : h 0 ≤ (3/19 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/19 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_544 h delta _ctx _hno a14 a23 a28 a37 a40 f1
  by_cases p2 : h 1 ≤ (4/31 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/31 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_545 h delta _ctx _hno a14 a23 a28 a33 a37 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_546 h delta _ctx _hno a14 a23 a28 a33 a40 f3
  by_cases p4 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_547 h delta _ctx _hno a14 a28 a33 a37 a40 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_548 h delta _ctx _hno a14 a23 a28 a33 a37 a40 f5
  apply _hno 85
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (4/31 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_541 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : h 0 ≤ (3/19 : ℝ))
    (a39 : -(h 0) < (-4/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_540 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a31 : -(h 1) < (-1/8 : ℝ))
    (a33 : -(h 0) < (-7/45 : ℝ))
    (a37 : -(h 2) < (-7/60 : ℝ))
    (a38 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a23 + (1/6 : ℝ) * a28 + (1/6 : ℝ) * a31 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a38 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_539 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a30 : h 0 ≤ (3/19 : ℝ))
    (a31 : -(h 1) < (-1/8 : ℝ))
    (a33 : -(h 0) < (-7/45 : ℝ))
    (a37 : -(h 2) < (-7/60 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_540 h delta _ctx _hno a23 a28 a31 a33 a37 f0
  by_cases p1 : h 0 ≤ (4/25 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/25 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_541 h delta _ctx _hno a30 f1
  by_cases p2 : h 1 ≤ (9/71 : ℝ)
  swap
  · have f2 : -(h 1) < (-9/71 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_542 h delta _ctx _hno a14 a23 a28 a33 a37 f2
  by_cases p3 : h 2 ≤ (3/25 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_549 h delta _ctx _hno a14 a23 a28 a31 a33 f3
  by_cases p4 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_550 h delta _ctx _hno a14 a28 a31 a33 a37 f4
  by_cases p5 : h 4 ≤ (6/53 : ℝ)
  swap
  · have f5 : -(h 4) < (-6/53 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_551 h delta _ctx _hno a14 a31 a33 a37 f5
  by_cases p6 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f6 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact upper_node_552 h delta _ctx _hno a14 a31 a33 a37 f6
  apply _hno 82
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (9/71 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 4 ≤ (6/53 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem upper_node_538 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a21 : h 1 ≤ (5/38 : ℝ))
    (a36 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a21 + (1 : ℝ) * a36
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_537 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : h 0 ≤ (3/19 : ℝ))
    (a35 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a35
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_536 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a19 + (1 : ℝ) * a34
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_535 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a19 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a21 : h 1 ≤ (5/38 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a30 : h 0 ≤ (3/19 : ℝ))
    (a31 : -(h 1) < (-1/8 : ℝ))
    (a33 : -(h 0) < (-7/45 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_536 h delta _ctx _hno a19 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_537 h delta _ctx _hno a30 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_538 h delta _ctx _hno a21 f2
  by_cases p3 : h 2 ≤ (7/60 : ℝ)
  swap
  · have f3 : -(h 2) < (-7/60 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_539 h delta _ctx _hno a14 a23 a28 a30 a31 a33 f3
  by_cases p4 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_553 h delta _ctx _hno a14 a28 a31 a33 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_554 h delta _ctx _hno a14 a23 a28 a31 a33 f5
  apply _hno 54
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (7/60 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_534 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a32 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a19 + (1 : ℝ) * a32
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_533 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a18 : -(h 0) < (-2/13 : ℝ))
    (a19 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a21 : h 1 ≤ (5/38 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a30 : h 0 ≤ (3/19 : ℝ))
    (a31 : -(h 1) < (-1/8 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_534 h delta _ctx _hno a19 f0
  by_cases p1 : h 0 ≤ (7/45 : ℝ)
  swap
  · have f1 : -(h 0) < (-7/45 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_535 h delta _ctx _hno a14 a19 a21 a23 a28 a30 a31 f1
  by_cases p2 : h 1 ≤ (9/70 : ℝ)
  swap
  · have f2 : -(h 1) < (-9/70 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_555 h delta _ctx _hno a14 a18 a19 a21 a23 a28 p1 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_574 h delta _ctx _hno a14 a18 a23 a28 f3
  by_cases p4 : h 4 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 4) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_575 h delta _ctx _hno a14 a18 a31 f4
  apply _hno 55
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (7/45 : ℝ)) ∧ (h 1 ≤ (9/70 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (4/35 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_532 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a34 : h 4 ≤ (5/44 : ℝ))
    (a40 : -(h 4) < (-8/67 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_531 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a19 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a30 : -(h 0) < (-3/19 : ℝ))
    (a35 : -(h 5) < (-1/9 : ℝ))
    (a39 : -(h 3) < (-11/92 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/16 : ℝ) * _ctx.order2 + (1/16 : ℝ) * a13 + (3/32 : ℝ) * a19 + (3/16 : ℝ) * a28 + (3/16 : ℝ) * a30 + (3/16 : ℝ) * a35 + (3/8 : ℝ) * a39 + (3/16 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_530 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a30 : -(h 0) < (-3/19 : ℝ))
    (a35 : -(h 5) < (-1/9 : ℝ))
    (a38 : -(h 1) < (-3/25 : ℝ))
    (a42 : -(h 2) < (-3/26 : ℝ))
    (a46 : -(h 3) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/34 : ℝ) * a13 + (3/17 : ℝ) * a28 + (3/17 : ℝ) * a30 + (3/17 : ℝ) * a35 + (3/34 : ℝ) * a38 + (3/17 : ℝ) * a42 + (3/17 : ℝ) * a46 + (3/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_529 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a41 : h 1 ≤ (4/33 : ℝ))
    (a45 : -(h 1) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a41 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_528 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a19 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a35 : -(h 5) < (-1/9 : ℝ))
    (a42 : -(h 2) < (-3/26 : ℝ))
    (a44 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/16 : ℝ) * a13 + (3/32 : ℝ) * a19 + (3/16 : ℝ) * a23 + (3/16 : ℝ) * a28 + (3/16 : ℝ) * a35 + (3/16 : ℝ) * a42 + (3/16 : ℝ) * a44 + (3/16 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_527 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a19 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_526 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a19 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a30 : -(h 0) < (-3/19 : ℝ))
    (a35 : -(h 5) < (-1/9 : ℝ))
    (a38 : -(h 1) < (-3/25 : ℝ))
    (a41 : h 1 ≤ (4/33 : ℝ))
    (a42 : -(h 2) < (-3/26 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_527 h delta _ctx _hno a19 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_528 h delta _ctx _hno a13 a19 a23 a28 a35 a42 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_529 h delta _ctx _hno a41 f2
  by_cases p3 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f3 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_530 h delta _ctx _hno a13 a28 a30 a35 a38 a42 f3
  apply _hno 84
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_525 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a30 : -(h 0) < (-3/19 : ℝ))
    (a35 : -(h 5) < (-1/9 : ℝ))
    (a44 : -(h 1) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/29 : ℝ) * _ctx.fail1 + (3/116 : ℝ) * a14 + (6/29 : ℝ) * a23 + (6/29 : ℝ) * a28 + (13/116 : ℝ) * a30 + (6/29 : ℝ) * a35 + (6/29 : ℝ) * a44 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_524 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a35 : -(h 5) < (-1/9 : ℝ))
    (a41 : -(h 1) < (-4/33 : ℝ))
    (a43 : -(h 0) < (-4/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/27 : ℝ) * _ctx.fail1 + (1/27 : ℝ) * a13 + (2/9 : ℝ) * a23 + (2/9 : ℝ) * a28 + (2/9 : ℝ) * a35 + (1/9 : ℝ) * a41 + (4/27 : ℝ) * a43 + (2/9 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_523 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a30 : -(h 0) < (-3/19 : ℝ))
    (a35 : -(h 5) < (-1/9 : ℝ))
    (a41 : -(h 1) < (-4/33 : ℝ))
    (a46 : -(h 3) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/27 : ℝ) * _ctx.fail1 + (1/27 : ℝ) * a13 + (2/9 : ℝ) * a28 + (4/27 : ℝ) * a30 + (2/9 : ℝ) * a35 + (1/9 : ℝ) * a41 + (2/9 : ℝ) * a46 + (2/9 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_522 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a30 : -(h 0) < (-3/19 : ℝ))
    (a35 : -(h 5) < (-1/9 : ℝ))
    (a42 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a45 : -(h 1) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/32 : ℝ) * _ctx.fail1 + (3/16 : ℝ) * a23 + (3/16 : ℝ) * a28 + (1/8 : ℝ) * a30 + (3/16 : ℝ) * a35 + (3/32 : ℝ) * a42 + (3/16 : ℝ) * a45 + (3/16 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_521 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a35 : -(h 5) < (-1/9 : ℝ))
    (a41 : -(h 1) < (-4/33 : ℝ))
    (a44 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/27 : ℝ) * _ctx.fail1 + (1/27 : ℝ) * a13 + (2/9 : ℝ) * a23 + (2/9 : ℝ) * a28 + (2/9 : ℝ) * a35 + (1/9 : ℝ) * a41 + (4/27 : ℝ) * a44 + (2/9 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_520 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a19 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_519 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a19 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a30 : -(h 0) < (-3/19 : ℝ))
    (a35 : -(h 5) < (-1/9 : ℝ))
    (a41 : -(h 1) < (-4/33 : ℝ))
    (a42 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_520 h delta _ctx _hno a19 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_521 h delta _ctx _hno a13 a23 a28 a35 a41 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_522 h delta _ctx _hno a23 a28 a30 a35 a42 f2
  by_cases p3 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f3 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_523 h delta _ctx _hno a13 a28 a30 a35 a41 f3
  apply _hno 84
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_518 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a19 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a30 : -(h 0) < (-3/19 : ℝ))
    (a35 : -(h 5) < (-1/9 : ℝ))
    (a41 : -(h 1) < (-4/33 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_519 h delta _ctx _hno a13 a19 a23 a28 a30 a35 a41 f0
  by_cases p1 : h 0 ≤ (4/25 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/25 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_524 h delta _ctx _hno a13 a23 a28 a35 a41 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_525 h delta _ctx _hno a14 a23 a28 a30 a35 f2
  apply _hno 83
  change (((2 : ℝ) * (delta)) ≤ (10/47 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem upper_node_517 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a35 : -(h 5) < (-1/9 : ℝ))
    (a38 : -(h 1) < (-3/25 : ℝ))
    (a40 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/27 : ℝ) * _ctx.fail1 + (1/27 : ℝ) * a13 + (2/9 : ℝ) * a23 + (2/9 : ℝ) * a28 + (2/9 : ℝ) * a35 + (1/9 : ℝ) * a38 + (4/27 : ℝ) * a40 + (2/9 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_516 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a39 : ((-2 : ℝ) * (delta)) < (-3/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a19 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_515 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a19 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a30 : -(h 0) < (-3/19 : ℝ))
    (a35 : -(h 5) < (-1/9 : ℝ))
    (a38 : -(h 1) < (-3/25 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/13 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_516 h delta _ctx _hno a19 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_517 h delta _ctx _hno a13 a23 a28 a35 a38 f1
  by_cases p2 : h 1 ≤ (4/33 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_518 h delta _ctx _hno a13 a14 a19 a23 a28 a30 a35 f2
  by_cases p3 : h 2 ≤ (3/26 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_526 h delta _ctx _hno a13 a19 a23 a28 a30 a35 a38 p2 f3
  apply _hno 59
  change (((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (4/33 : ℝ)) ∧ (h 2 ≤ (3/26 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_514 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a19 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a35 : -(h 5) < (-1/9 : ℝ))
    (a37 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/25 : ℝ) * _ctx.fail1 + (2/25 : ℝ) * a13 + (3/25 : ℝ) * a19 + (6/25 : ℝ) * a23 + (6/25 : ℝ) * a28 + (6/25 : ℝ) * a35 + (4/25 : ℝ) * a37 + (6/25 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_513 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a36 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a19 + (1 : ℝ) * a36
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_512 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a19 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a30 : -(h 0) < (-3/19 : ℝ))
    (a34 : h 4 ≤ (5/44 : ℝ))
    (a35 : -(h 5) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_513 h delta _ctx _hno a19 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_514 h delta _ctx _hno a13 a19 a23 a28 a35 f1
  by_cases p2 : h 1 ≤ (3/25 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_515 h delta _ctx _hno a13 a14 a19 a23 a28 a30 a35 f2
  by_cases p3 : h 3 ≤ (11/92 : ℝ)
  swap
  · have f3 : -(h 3) < (-11/92 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_531 h delta _ctx _hno a13 a19 a28 a30 a35 f3
  by_cases p4 : h 4 ≤ (8/67 : ℝ)
  swap
  · have f4 : -(h 4) < (-8/67 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_532 h delta _ctx _hno a34 f4
  apply _hno 60
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (11/92 : ℝ)) ∧ (h 4 ≤ (8/67 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_511 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a19 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a30 : -(h 0) < (-3/19 : ℝ))
    (a34 : -(h 4) < (-5/44 : ℝ))
    (a40 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/25 : ℝ) * _ctx.order3 + (1/25 : ℝ) * _ctx.fail1 + (2/25 : ℝ) * a13 + (3/25 : ℝ) * a19 + (4/25 : ℝ) * a30 + (12/25 : ℝ) * a34 + (6/25 : ℝ) * a40 + (6/25 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_510 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a30 : -(h 0) < (-3/19 : ℝ))
    (a34 : -(h 4) < (-5/44 : ℝ))
    (a39 : -(h 3) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/13 : ℝ) * _ctx.order2 + (3/13 : ℝ) * _ctx.min + (1/13 : ℝ) * a13 + (3/13 : ℝ) * a30 + (3/13 : ℝ) * a34 + (6/13 : ℝ) * a39 + (3/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_509 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a30 : -(h 0) < (-3/19 : ℝ))
    (a34 : -(h 4) < (-5/44 : ℝ))
    (a38 : -(h 2) < (-7/60 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/13 : ℝ) * _ctx.order3 + (3/13 : ℝ) * _ctx.min + (1/13 : ℝ) * a13 + (3/13 : ℝ) * a30 + (6/13 : ℝ) * a34 + (3/13 : ℝ) * a38 + (3/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_508 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : h 1 ≤ (1/8 : ℝ))
    (a37 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a37
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_507 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a34 : -(h 4) < (-5/44 : ℝ))
    (a36 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/13 : ℝ) * _ctx.order2 + (6/13 : ℝ) * _ctx.order3 + (3/13 : ℝ) * _ctx.min + (1/13 : ℝ) * a13 + (9/13 : ℝ) * a34 + (3/13 : ℝ) * a36 + (3/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_506 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a35 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a19 + (1 : ℝ) * a35
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_505 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a19 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a30 : -(h 0) < (-3/19 : ℝ))
    (a33 : h 1 ≤ (1/8 : ℝ))
    (a34 : -(h 4) < (-5/44 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_506 h delta _ctx _hno a19 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_507 h delta _ctx _hno a13 a34 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_508 h delta _ctx _hno a33 f2
  by_cases p3 : h 2 ≤ (7/60 : ℝ)
  swap
  · have f3 : -(h 2) < (-7/60 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_509 h delta _ctx _hno a13 a30 a34 f3
  by_cases p4 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_510 h delta _ctx _hno a13 a30 a34 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_511 h delta _ctx _hno a13 a19 a30 a34 f5
  apply _hno 54
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (7/60 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_504 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a30 : -(h 0) < (-3/19 : ℝ))
    (a33 : -(h 1) < (-1/8 : ℝ))
    (a39 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/29 : ℝ) * _ctx.fail1 + (3/116 : ℝ) * a14 + (6/29 : ℝ) * a23 + (6/29 : ℝ) * a28 + (13/116 : ℝ) * a30 + (6/29 : ℝ) * a33 + (6/29 : ℝ) * a39 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_503 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a30 : -(h 0) < (-3/19 : ℝ))
    (a33 : -(h 1) < (-1/8 : ℝ))
    (a38 : -(h 3) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order2 + (1/5 : ℝ) * _ctx.min + (1/20 : ℝ) * a14 + (1/5 : ℝ) * a28 + (3/20 : ℝ) * a30 + (1/5 : ℝ) * a33 + (2/5 : ℝ) * a38 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_502 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a33 : -(h 1) < (-1/8 : ℝ))
    (a37 : -(h 2) < (-7/60 : ℝ))
    (a38 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a44 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/3 : ℝ) * _ctx.order4 + (1/6 : ℝ) * a14 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a37 + (7/12 : ℝ) * a38 + (1/2 : ℝ) * a44 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_501 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a30 : -(h 0) < (-3/19 : ℝ))
    (a33 : -(h 1) < (-1/8 : ℝ))
    (a37 : -(h 2) < (-7/60 : ℝ))
    (a43 : -(h 4) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (1/20 : ℝ) * a14 + (3/20 : ℝ) * a30 + (1/5 : ℝ) * a33 + (1/5 : ℝ) * a37 + (2/5 : ℝ) * a43 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_500 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a30 : -(h 0) < (-3/19 : ℝ))
    (a33 : -(h 1) < (-1/8 : ℝ))
    (a37 : -(h 2) < (-7/60 : ℝ))
    (a42 : -(h 3) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (1/20 : ℝ) * a14 + (1/5 : ℝ) * a28 + (3/20 : ℝ) * a30 + (1/5 : ℝ) * a33 + (1/5 : ℝ) * a37 + (1/5 : ℝ) * a42 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_499 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a30 : -(h 0) < (-3/19 : ℝ))
    (a33 : -(h 1) < (-1/8 : ℝ))
    (a41 : -(h 2) < (-2/17 : ℝ))
    (a48 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/3 : ℝ) * _ctx.order4 + (1/48 : ℝ) * a14 + (7/48 : ℝ) * a30 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a41 + (1/2 : ℝ) * a48 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_498 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a30 : -(h 0) < (-3/19 : ℝ))
    (a33 : -(h 1) < (-1/8 : ℝ))
    (a41 : -(h 2) < (-2/17 : ℝ))
    (a47 : -(h 4) < (-6/53 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (1/20 : ℝ) * a14 + (3/20 : ℝ) * a30 + (1/5 : ℝ) * a33 + (1/5 : ℝ) * a41 + (2/5 : ℝ) * a47 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_497 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a30 : -(h 0) < (-3/19 : ℝ))
    (a33 : -(h 1) < (-1/8 : ℝ))
    (a41 : -(h 2) < (-2/17 : ℝ))
    (a46 : -(h 3) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (1/20 : ℝ) * a14 + (1/5 : ℝ) * a28 + (3/20 : ℝ) * a30 + (1/5 : ℝ) * a33 + (1/5 : ℝ) * a41 + (1/5 : ℝ) * a46 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_496 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a30 : -(h 0) < (-3/19 : ℝ))
    (a33 : -(h 1) < (-1/8 : ℝ))
    (a45 : -(h 2) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (1/20 : ℝ) * a14 + (1/5 : ℝ) * a23 + (1/5 : ℝ) * a28 + (3/20 : ℝ) * a30 + (1/5 : ℝ) * a33 + (1/5 : ℝ) * a45 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_495 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a30 : -(h 0) < (-3/19 : ℝ))
    (a41 : -(h 2) < (-2/17 : ℝ))
    (a44 : -(h 1) < (-9/71 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (1/20 : ℝ) * a14 + (1/5 : ℝ) * a23 + (1/5 : ℝ) * a28 + (3/20 : ℝ) * a30 + (1/5 : ℝ) * a41 + (1/5 : ℝ) * a44 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_494 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a33 : -(h 1) < (-1/8 : ℝ))
    (a41 : -(h 2) < (-2/17 : ℝ))
    (a43 : -(h 0) < (-4/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (1/20 : ℝ) * a14 + (1/5 : ℝ) * a23 + (1/5 : ℝ) * a28 + (1/5 : ℝ) * a33 + (1/5 : ℝ) * a41 + (3/20 : ℝ) * a43 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_493 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a38 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a42 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a38 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_492 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a30 : -(h 0) < (-3/19 : ℝ))
    (a33 : -(h 1) < (-1/8 : ℝ))
    (a38 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a41 : -(h 2) < (-2/17 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_493 h delta _ctx _hno a38 f0
  by_cases p1 : h 0 ≤ (4/25 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/25 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_494 h delta _ctx _hno a14 a23 a28 a33 a41 f1
  by_cases p2 : h 1 ≤ (9/71 : ℝ)
  swap
  · have f2 : -(h 1) < (-9/71 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_495 h delta _ctx _hno a14 a23 a28 a30 a41 f2
  by_cases p3 : h 2 ≤ (3/25 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_496 h delta _ctx _hno a14 a23 a28 a30 a33 f3
  by_cases p4 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_497 h delta _ctx _hno a14 a28 a30 a33 a41 f4
  by_cases p5 : h 4 ≤ (6/53 : ℝ)
  swap
  · have f5 : -(h 4) < (-6/53 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_498 h delta _ctx _hno a14 a30 a33 a41 f5
  by_cases p6 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f6 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact upper_node_499 h delta _ctx _hno a14 a30 a33 a41 f6
  apply _hno 82
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (9/71 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 4 ≤ (6/53 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem upper_node_491 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a30 : -(h 0) < (-3/19 : ℝ))
    (a37 : -(h 2) < (-7/60 : ℝ))
    (a40 : -(h 1) < (-4/31 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (1/20 : ℝ) * a14 + (1/5 : ℝ) * a23 + (1/5 : ℝ) * a28 + (3/20 : ℝ) * a30 + (1/5 : ℝ) * a37 + (1/5 : ℝ) * a40 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_490 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : h 0 ≤ (1/6 : ℝ))
    (a39 : -(h 0) < (-4/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a25 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_489 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a30 : -(h 0) < (-3/19 : ℝ))
    (a33 : -(h 1) < (-1/8 : ℝ))
    (a37 : -(h 2) < (-7/60 : ℝ))
    (a45 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/3 : ℝ) * _ctx.order4 + (1/48 : ℝ) * a14 + (7/48 : ℝ) * a30 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a37 + (1/2 : ℝ) * a45 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_488 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a30 : -(h 0) < (-3/19 : ℝ))
    (a33 : -(h 1) < (-1/8 : ℝ))
    (a37 : -(h 2) < (-7/60 : ℝ))
    (a44 : -(h 4) < (-6/53 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (1/20 : ℝ) * a14 + (3/20 : ℝ) * a30 + (1/5 : ℝ) * a33 + (1/5 : ℝ) * a37 + (2/5 : ℝ) * a44 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_487 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a30 : -(h 0) < (-3/19 : ℝ))
    (a33 : -(h 1) < (-1/8 : ℝ))
    (a37 : -(h 2) < (-7/60 : ℝ))
    (a43 : -(h 3) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (1/20 : ℝ) * a14 + (1/5 : ℝ) * a28 + (3/20 : ℝ) * a30 + (1/5 : ℝ) * a33 + (1/5 : ℝ) * a37 + (1/5 : ℝ) * a43 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_486 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a30 : -(h 0) < (-3/19 : ℝ))
    (a33 : -(h 1) < (-1/8 : ℝ))
    (a42 : -(h 2) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (1/20 : ℝ) * a14 + (1/5 : ℝ) * a23 + (1/5 : ℝ) * a28 + (3/20 : ℝ) * a30 + (1/5 : ℝ) * a33 + (1/5 : ℝ) * a42 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_485 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a30 : -(h 0) < (-3/19 : ℝ))
    (a37 : -(h 2) < (-7/60 : ℝ))
    (a41 : -(h 1) < (-9/71 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (1/20 : ℝ) * a14 + (1/5 : ℝ) * a23 + (1/5 : ℝ) * a28 + (3/20 : ℝ) * a30 + (1/5 : ℝ) * a37 + (1/5 : ℝ) * a41 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_484 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a33 : -(h 1) < (-1/8 : ℝ))
    (a37 : -(h 2) < (-7/60 : ℝ))
    (a38 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a40 : -(h 0) < (-4/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a23 + (1/6 : ℝ) * a28 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a38 + (1/6 : ℝ) * a40 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_483 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a30 : -(h 0) < (-3/19 : ℝ))
    (a33 : -(h 1) < (-1/8 : ℝ))
    (a37 : -(h 2) < (-7/60 : ℝ))
    (a39 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a23 + (1/6 : ℝ) * a28 + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a39 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_482 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a30 : -(h 0) < (-3/19 : ℝ))
    (a33 : -(h 1) < (-1/8 : ℝ))
    (a37 : -(h 2) < (-7/60 : ℝ))
    (a38 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_483 h delta _ctx _hno a23 a28 a30 a33 a37 f0
  by_cases p1 : h 0 ≤ (4/25 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/25 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_484 h delta _ctx _hno a23 a28 a33 a37 a38 f1
  by_cases p2 : h 1 ≤ (9/71 : ℝ)
  swap
  · have f2 : -(h 1) < (-9/71 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_485 h delta _ctx _hno a14 a23 a28 a30 a37 f2
  by_cases p3 : h 2 ≤ (3/25 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_486 h delta _ctx _hno a14 a23 a28 a30 a33 f3
  by_cases p4 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_487 h delta _ctx _hno a14 a28 a30 a33 a37 f4
  by_cases p5 : h 4 ≤ (6/53 : ℝ)
  swap
  · have f5 : -(h 4) < (-6/53 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_488 h delta _ctx _hno a14 a30 a33 a37 f5
  by_cases p6 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f6 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact upper_node_489 h delta _ctx _hno a14 a30 a33 a37 f6
  apply _hno 82
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (9/71 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 4 ≤ (6/53 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem upper_node_481 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a25 : h 0 ≤ (1/6 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a30 : -(h 0) < (-3/19 : ℝ))
    (a33 : -(h 1) < (-1/8 : ℝ))
    (a37 : -(h 2) < (-7/60 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_482 h delta _ctx _hno a14 a23 a28 a30 a33 a37 f0
  by_cases p1 : h 0 ≤ (4/23 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/23 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_490 h delta _ctx _hno a25 f1
  by_cases p2 : h 1 ≤ (4/31 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/31 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_491 h delta _ctx _hno a14 a23 a28 a30 a37 f2
  by_cases p3 : h 2 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_492 h delta _ctx _hno a14 a23 a28 a30 a33 p0 f3
  by_cases p4 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_500 h delta _ctx _hno a14 a28 a30 a33 a37 f4
  by_cases p5 : h 4 ≤ (4/35 : ℝ)
  swap
  · have f5 : -(h 4) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_501 h delta _ctx _hno a14 a30 a33 a37 f5
  by_cases p6 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f6 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact upper_node_502 h delta _ctx _hno a14 a33 a37 p0 f6
  apply _hno 80
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (4/23 : ℝ)) ∧ (h 1 ≤ (4/31 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 4 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem upper_node_480 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a21 : h 1 ≤ (5/38 : ℝ))
    (a36 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a21 + (1 : ℝ) * a36
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_479 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a35 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/19 : ℝ) * _ctx.min + (1/19 : ℝ) * _ctx.fail1 + (2/19 : ℝ) * a13 + (6/19 : ℝ) * a23 + (6/19 : ℝ) * a28 + (4/19 : ℝ) * a35 + (6/19 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_478 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a19 + (1 : ℝ) * a34
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_477 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a19 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a21 : h 1 ≤ (5/38 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a25 : h 0 ≤ (1/6 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a30 : -(h 0) < (-3/19 : ℝ))
    (a33 : -(h 1) < (-1/8 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_478 h delta _ctx _hno a19 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_479 h delta _ctx _hno a13 a23 a28 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_480 h delta _ctx _hno a21 f2
  by_cases p3 : h 2 ≤ (7/60 : ℝ)
  swap
  · have f3 : -(h 2) < (-7/60 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_481 h delta _ctx _hno a14 a23 a25 a28 a30 a33 f3
  by_cases p4 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_503 h delta _ctx _hno a14 a28 a30 a33 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_504 h delta _ctx _hno a14 a23 a28 a30 a33 f5
  apply _hno 54
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (7/60 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_476 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a32 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/19 : ℝ) * _ctx.min + (1/19 : ℝ) * _ctx.fail1 + (2/19 : ℝ) * a13 + (6/19 : ℝ) * a23 + (6/19 : ℝ) * a28 + (4/19 : ℝ) * a32 + (6/19 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_475 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a31 : ((-2 : ℝ) * (delta)) < (-5/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a19 + (1 : ℝ) * a31
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_474 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a19 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a21 : h 1 ≤ (5/38 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a25 : h 0 ≤ (1/6 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a30 : -(h 0) < (-3/19 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/22 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/22 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_475 h delta _ctx _hno a19 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_476 h delta _ctx _hno a13 a23 a28 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_477 h delta _ctx _hno a13 a14 a19 a21 a23 a25 a28 a30 f2
  by_cases p3 : h 4 ≤ (5/44 : ℝ)
  swap
  · have f3 : -(h 4) < (-5/44 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_505 h delta _ctx _hno a13 a19 a30 p2 f3
  by_cases p4 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_512 h delta _ctx _hno a13 a14 a19 a23 a28 a30 p3 f4
  apply _hno 58
  change (((2 : ℝ) * (delta)) ≤ (5/22 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (5/44 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_473 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a29 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a19 + (1 : ℝ) * a29
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_472 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a18 : -(h 0) < (-2/13 : ℝ))
    (a19 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a21 : h 1 ≤ (5/38 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a25 : h 0 ≤ (1/6 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_473 h delta _ctx _hno a19 f0
  by_cases p1 : h 0 ≤ (3/19 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/19 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_474 h delta _ctx _hno a13 a14 a19 a21 a23 a25 a28 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_533 h delta _ctx _hno a14 a18 a19 a21 a23 a28 p1 f2
  by_cases p3 : h 4 ≤ (13/112 : ℝ)
  swap
  · have f3 : -(h 4) < (-13/112 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_576 h delta _ctx _hno a13 a18 f3
  apply _hno 4
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (13/112 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_471 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a18 : -(h 0) < (-2/13 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a27 : -(h 2) < (-1/8 : ℝ))
    (a32 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order1 + (1/5 : ℝ) * _ctx.min + (1/20 : ℝ) * a14 + (3/20 : ℝ) * a18 + (1/5 : ℝ) * a23 + (2/5 : ℝ) * a27 + (1/5 : ℝ) * a32 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_470 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a18 : -(h 0) < (-2/13 : ℝ))
    (a27 : -(h 2) < (-1/8 : ℝ))
    (a31 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.order1 + (1/4 : ℝ) * _ctx.order4 + (1/2 : ℝ) * _ctx.min + (3/32 : ℝ) * a14 + (5/32 : ℝ) * a18 + (1/2 : ℝ) * a27 + (1/4 : ℝ) * a31 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_469 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a18 : -(h 0) < (-2/13 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a27 : -(h 2) < (-1/8 : ℝ))
    (a30 : -(h 1) < (-7/54 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.order4 + (1/2 : ℝ) * _ctx.min + (3/32 : ℝ) * a14 + (5/32 : ℝ) * a18 + (1/4 : ℝ) * a23 + (1/4 : ℝ) * a27 + (1/4 : ℝ) * a30 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_468 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a27 : -(h 2) < (-1/8 : ℝ))
    (a29 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/10 : ℝ) * _ctx.order4 + (3/5 : ℝ) * _ctx.min + (3/10 : ℝ) * _ctx.lower + (1/10 : ℝ) * a13 + (3/10 : ℝ) * a23 + (3/10 : ℝ) * a27 + (3/10 : ℝ) * a29 + (3/10 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

end RealPinwheel.WeakSevenBandData
