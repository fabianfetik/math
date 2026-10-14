import Pinwheel.WeakSevenBandData.CoverChunks.Upper008

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem upper_node_3587 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a31 : h 2 ≤ (1/8 : ℝ))
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a33 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a36 : -(h 1) < (-1/8 : ℝ))
    (a38 : -(h 0) < (-11/80 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3588 h delta _ctx _hno a14 a38 f0
  by_cases p1 : h 0 ≤ (6/41 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/41 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3589 h delta _ctx _hno a30 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3590 h delta _ctx _hno a32 a33 f2
  by_cases p3 : h 2 ≤ (4/33 : ℝ)
  swap
  · have f3 : -(h 2) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3591 h delta _ctx _hno a14 a30 a31 a32 a33 a36 a38 f3
  by_cases p4 : h 3 ≤ (3/25 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3653 h delta _ctx _hno a14 a30 a32 a33 a36 a38 p3 f4
  by_cases p5 : h 5 ≤ (2/17 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_3677 h delta _ctx _hno a33 a36 a38 f5
  apply _hno 137
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (6/41 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (4/33 : ℝ)) ∧ (h 3 ≤ (3/25 : ℝ)) ∧ (h 5 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_3586 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a37 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/24 : ℝ) * _ctx.fail3 + (1/4 : ℝ) * a14 + (23/24 : ℝ) * a37
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3585 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a31 : h 2 ≤ (1/8 : ℝ))
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a33 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a36 : -(h 1) < (-1/8 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3586 h delta _ctx _hno a14 f0
  by_cases p1 : h 0 ≤ (11/80 : ℝ)
  swap
  · have f1 : -(h 0) < (-11/80 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3587 h delta _ctx _hno a14 a30 a31 a32 a33 a36 f1
  by_cases p2 : h 1 ≤ (7/51 : ℝ)
  swap
  · have f2 : -(h 1) < (-7/51 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3678 h delta _ctx _hno a32 a33 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3679 h delta _ctx _hno a31 f3
  apply _hno 6
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (11/80 : ℝ)) ∧ (h 1 ≤ (7/51 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_3584 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a35
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3583 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/24 : ℝ) * _ctx.fail3 + (1/4 : ℝ) * a14 + (23/24 : ℝ) * a34
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3582 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a31 : h 2 ≤ (1/8 : ℝ))
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a33 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3583 h delta _ctx _hno a14 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3584 h delta _ctx _hno a30 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3585 h delta _ctx _hno a14 a30 a31 a32 a33 f2
  apply _hno 2
  change (((2 : ℝ) * (delta)) ≤ (7/32 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem upper_node_3581 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a31 : h 2 ≤ (1/8 : ℝ))
    (a32 : -(h 4) < (-4/35 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3582 h delta _ctx _hno a14 a30 a31 a32 f0
  by_cases p1 : h 0 ≤ (4/25 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/25 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3680 h delta _ctx _hno a30 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3681 h delta _ctx _hno a13 a30 a31 a32 p0 f2
  apply _hno 83
  change (((2 : ℝ) * (delta)) ≤ (10/47 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem upper_node_3580 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a34 : h 3 ≤ (5/42 : ℝ))
    (a41 : -(h 4) < (-5/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * _ctx.order3 + (1 : ℝ) * a34 + (1 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3579 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a34 : h 3 ≤ (5/42 : ℝ))
    (a40 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3578 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a35 : -(h 4) < (-2/17 : ℝ))
    (a39 : -(h 2) < (-3/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/13 : ℝ) * _ctx.order1 + (4/13 : ℝ) * _ctx.order3 + (4/13 : ℝ) * _ctx.min + (8/13 : ℝ) * _ctx.lower + (1/13 : ℝ) * _ctx.fail2 + (4/13 : ℝ) * a35 + (8/13 : ℝ) * a39 + (4/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3577 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a35 : -(h 4) < (-2/17 : ℝ))
    (a38 : -(h 1) < (-9/65 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order0 + (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a31 + (2/5 : ℝ) * a35 + (2/5 : ℝ) * a38 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3576 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a35 : -(h 4) < (-2/17 : ℝ))
    (a36 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ))
    (a37 : -(h 0) < (-5/36 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/16 : ℝ) * _ctx.order3 + (1/16 : ℝ) * a13 + (3/16 : ℝ) * a31 + (3/8 : ℝ) * a35 + (3/32 : ℝ) * a36 + (3/16 : ℝ) * a37 + (3/16 : ℝ) * a42 + (3/16 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3575 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a34 : h 3 ≤ (5/42 : ℝ))
    (a41 : -(h 4) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * _ctx.order3 + (1 : ℝ) * a34 + (1 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3574 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a35 : -(h 4) < (-2/17 : ℝ))
    (a37 : -(h 0) < (-5/36 : ℝ))
    (a40 : -(h 2) < (-5/38 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order1 + (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (2/5 : ℝ) * a35 + (1/5 : ℝ) * a37 + (2/5 : ℝ) * a40 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3573 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a35 : -(h 4) < (-2/17 : ℝ))
    (a39 : -(h 0) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/13 : ℝ) * _ctx.order3 + (3/13 : ℝ) * _ctx.min + (1/13 : ℝ) * a13 + (3/13 : ℝ) * a31 + (6/13 : ℝ) * a35 + (3/13 : ℝ) * a39 + (3/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3572 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a36 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ))
    (a38 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a36 + (1 : ℝ) * a38
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3571 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a34 : h 3 ≤ (5/42 : ℝ))
    (a35 : -(h 4) < (-2/17 : ℝ))
    (a36 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ))
    (a37 : -(h 0) < (-5/36 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3572 h delta _ctx _hno a36 f0
  by_cases p1 : h 0 ≤ (1/7 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3573 h delta _ctx _hno a13 a31 a35 f1
  by_cases p2 : h 2 ≤ (5/38 : ℝ)
  swap
  · have f2 : -(h 2) < (-5/38 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3574 h delta _ctx _hno a35 a37 f2
  by_cases p3 : h 4 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 4) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3575 h delta _ctx _hno a34 f3
  by_cases p4 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f4 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3576 h delta _ctx _hno a13 a31 a35 a36 a37 f4
  apply _hno 24
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (5/38 : ℝ)) ∧ (h 4 ≤ (1/8 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_3570 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a35 : -(h 4) < (-2/17 : ℝ))
    (a46 : -(h 5) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/47 : ℝ) * _ctx.order1 + (12/47 : ℝ) * _ctx.order3 + (3/47 : ℝ) * _ctx.fail2 + (2/47 : ℝ) * a13 + (18/47 : ℝ) * a31 + (12/47 : ℝ) * a35 + (12/47 : ℝ) * a46 + (12/47 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3569 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a34 : h 3 ≤ (5/42 : ℝ))
    (a45 : -(h 4) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * _ctx.order3 + (1 : ℝ) * a34 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3568 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a34 : h 3 ≤ (5/42 : ℝ))
    (a44 : -(h 3) < (-4/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3567 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a35 : -(h 4) < (-2/17 : ℝ))
    (a43 : -(h 1) < (-6/47 : ℝ))
    (a54 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/17 : ℝ) * _ctx.order3 + (4/17 : ℝ) * _ctx.lower + (1/17 : ℝ) * _ctx.fail2 + (4/17 : ℝ) * a31 + (4/17 : ℝ) * a35 + (4/17 : ℝ) * a43 + (4/17 : ℝ) * a54 + (4/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3566 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a34 : h 3 ≤ (5/42 : ℝ))
    (a53 : -(h 3) < (-4/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a53
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3565 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a35 : -(h 4) < (-2/17 : ℝ))
    (a43 : -(h 1) < (-6/47 : ℝ))
    (a48 : -(h 5) < (-5/46 : ℝ))
    (a52 : -(h 2) < (-7/55 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/17 : ℝ) * _ctx.order3 + (4/17 : ℝ) * _ctx.lower + (1/17 : ℝ) * _ctx.fail2 + (4/17 : ℝ) * a35 + (4/17 : ℝ) * a43 + (4/17 : ℝ) * a48 + (4/17 : ℝ) * a52 + (4/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3564 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a35 : -(h 4) < (-2/17 : ℝ))
    (a48 : -(h 5) < (-5/46 : ℝ))
    (a51 : -(h 1) < (-4/31 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/17 : ℝ) * _ctx.order3 + (4/17 : ℝ) * _ctx.lower + (1/17 : ℝ) * _ctx.fail2 + (4/17 : ℝ) * a31 + (4/17 : ℝ) * a35 + (4/17 : ℝ) * a48 + (4/17 : ℝ) * a51 + (4/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3563 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a35 : -(h 4) < (-2/17 : ℝ))
    (a43 : -(h 1) < (-6/47 : ℝ))
    (a48 : -(h 5) < (-5/46 : ℝ))
    (a50 : -(h 0) < (-7/52 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a31 + (1/3 : ℝ) * a35 + (1/6 : ℝ) * a43 + (1/6 : ℝ) * a48 + (1/6 : ℝ) * a50 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3562 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a35 : -(h 4) < (-2/17 : ℝ))
    (a43 : -(h 1) < (-6/47 : ℝ))
    (a48 : -(h 5) < (-5/46 : ℝ))
    (a49 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/19 : ℝ) * _ctx.order3 + (1/19 : ℝ) * _ctx.fail2 + (4/19 : ℝ) * a31 + (4/19 : ℝ) * a35 + (4/19 : ℝ) * a43 + (4/19 : ℝ) * a48 + (2/19 : ℝ) * a49 + (4/19 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3561 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a34 : h 3 ≤ (5/42 : ℝ))
    (a35 : -(h 4) < (-2/17 : ℝ))
    (a43 : -(h 1) < (-6/47 : ℝ))
    (a48 : -(h 5) < (-5/46 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3562 h delta _ctx _hno a31 a35 a43 a48 f0
  by_cases p1 : h 0 ≤ (7/52 : ℝ)
  swap
  · have f1 : -(h 0) < (-7/52 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3563 h delta _ctx _hno a31 a35 a43 a48 f1
  by_cases p2 : h 1 ≤ (4/31 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/31 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3564 h delta _ctx _hno a31 a35 a48 f2
  by_cases p3 : h 2 ≤ (7/55 : ℝ)
  swap
  · have f3 : -(h 2) < (-7/55 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3565 h delta _ctx _hno a35 a43 a48 f3
  by_cases p4 : h 3 ≤ (4/33 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3566 h delta _ctx _hno a34 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_3567 h delta _ctx _hno a31 a35 a43 f5
  apply _hno 150
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (7/52 : ℝ)) ∧ (h 1 ≤ (4/31 : ℝ)) ∧ (h 2 ≤ (7/55 : ℝ)) ∧ (h 3 ≤ (4/33 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_3560 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a34 : h 3 ≤ (5/42 : ℝ))
    (a47 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3559 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a35 : -(h 4) < (-2/17 : ℝ))
    (a40 : -(h 5) < (-4/37 : ℝ))
    (a46 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/17 : ℝ) * _ctx.order3 + (4/17 : ℝ) * _ctx.lower + (1/17 : ℝ) * _ctx.fail2 + (4/17 : ℝ) * a31 + (4/17 : ℝ) * a35 + (4/17 : ℝ) * a40 + (4/17 : ℝ) * a46 + (4/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3558 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a38 : h 0 ≤ (5/37 : ℝ))
    (a45 : -(h 0) < (-6/43 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a38 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3557 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a37 : ((2 : ℝ) * (delta)) ≤ (7/33 : ℝ))
    (a44 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a37 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3556 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a34 : h 3 ≤ (5/42 : ℝ))
    (a35 : -(h 4) < (-2/17 : ℝ))
    (a37 : ((2 : ℝ) * (delta)) ≤ (7/33 : ℝ))
    (a38 : h 0 ≤ (5/37 : ℝ))
    (a40 : -(h 5) < (-4/37 : ℝ))
    (a43 : -(h 1) < (-6/47 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3557 h delta _ctx _hno a37 f0
  by_cases p1 : h 0 ≤ (6/43 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/43 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3558 h delta _ctx _hno a38 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3559 h delta _ctx _hno a31 a35 a40 f2
  by_cases p3 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3560 h delta _ctx _hno a34 f3
  by_cases p4 : h 5 ≤ (5/46 : ℝ)
  swap
  · have f4 : -(h 5) < (-5/46 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3561 h delta _ctx _hno a31 a34 a35 a43 f4
  apply _hno 20
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (6/43 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 5 ≤ (5/46 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_3555 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a38 : h 0 ≤ (5/37 : ℝ))
    (a42 : -(h 0) < (-6/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a38 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3554 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a37 : ((2 : ℝ) * (delta)) ≤ (7/33 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a37 + (1 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3553 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a34 : h 3 ≤ (5/42 : ℝ))
    (a35 : -(h 4) < (-2/17 : ℝ))
    (a37 : ((2 : ℝ) * (delta)) ≤ (7/33 : ℝ))
    (a38 : h 0 ≤ (5/37 : ℝ))
    (a40 : -(h 5) < (-4/37 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3554 h delta _ctx _hno a37 f0
  by_cases p1 : h 0 ≤ (6/41 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/41 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3555 h delta _ctx _hno a38 f1
  by_cases p2 : h 1 ≤ (6/47 : ℝ)
  swap
  · have f2 : -(h 1) < (-6/47 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3556 h delta _ctx _hno a31 a34 a35 a37 a38 a40 f2
  by_cases p3 : h 3 ≤ (4/33 : ℝ)
  swap
  · have f3 : -(h 3) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3568 h delta _ctx _hno a34 f3
  by_cases p4 : h 4 ≤ (3/25 : ℝ)
  swap
  · have f4 : -(h 4) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3569 h delta _ctx _hno a34 f4
  by_cases p5 : h 5 ≤ (2/17 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_3570 h delta _ctx _hno a13 a31 a35 f5
  apply _hno 145
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (6/41 : ℝ)) ∧ (h 1 ≤ (6/47 : ℝ)) ∧ (h 3 ≤ (4/33 : ℝ)) ∧ (h 4 ≤ (3/25 : ℝ)) ∧ (h 5 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_3552 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a35 : -(h 4) < (-2/17 : ℝ))
    (a39 : -(h 2) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/13 : ℝ) * _ctx.order1 + (4/13 : ℝ) * _ctx.order3 + (4/13 : ℝ) * _ctx.min + (8/13 : ℝ) * _ctx.lower + (1/13 : ℝ) * _ctx.fail2 + (4/13 : ℝ) * a35 + (8/13 : ℝ) * a39 + (4/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3551 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a35 : -(h 4) < (-2/17 : ℝ))
    (a38 : -(h 0) < (-5/37 : ℝ))
    (a54 : -(h 5) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/34 : ℝ) * _ctx.order1 + (3/17 : ℝ) * _ctx.order3 + (1/34 : ℝ) * a13 + (9/34 : ℝ) * a31 + (6/17 : ℝ) * a35 + (3/17 : ℝ) * a38 + (3/17 : ℝ) * a54 + (3/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3550 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a34 : h 3 ≤ (5/42 : ℝ))
    (a53 : -(h 4) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * _ctx.order3 + (1 : ℝ) * a34 + (1 : ℝ) * a53
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3549 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a34 : h 3 ≤ (5/42 : ℝ))
    (a52 : -(h 3) < (-4/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a52
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3548 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a35 : -(h 4) < (-2/17 : ℝ))
    (a38 : -(h 0) < (-5/37 : ℝ))
    (a48 : -(h 5) < (-5/46 : ℝ))
    (a51 : -(h 1) < (-6/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a31 + (1/3 : ℝ) * a35 + (1/6 : ℝ) * a38 + (1/6 : ℝ) * a48 + (1/6 : ℝ) * a51 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3547 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a45 : h 0 ≤ (6/43 : ℝ))
    (a50 : -(h 0) < (-6/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a45 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3546 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a39 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a49 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a39 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3545 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a34 : h 3 ≤ (5/42 : ℝ))
    (a35 : -(h 4) < (-2/17 : ℝ))
    (a38 : -(h 0) < (-5/37 : ℝ))
    (a39 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a45 : h 0 ≤ (6/43 : ℝ))
    (a48 : -(h 5) < (-5/46 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3546 h delta _ctx _hno a39 f0
  by_cases p1 : h 0 ≤ (6/41 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/41 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3547 h delta _ctx _hno a45 f1
  by_cases p2 : h 1 ≤ (6/47 : ℝ)
  swap
  · have f2 : -(h 1) < (-6/47 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3548 h delta _ctx _hno a31 a35 a38 a48 f2
  by_cases p3 : h 3 ≤ (4/33 : ℝ)
  swap
  · have f3 : -(h 3) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3549 h delta _ctx _hno a34 f3
  by_cases p4 : h 4 ≤ (3/25 : ℝ)
  swap
  · have f4 : -(h 4) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3550 h delta _ctx _hno a34 f4
  by_cases p5 : h 5 ≤ (2/17 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_3551 h delta _ctx _hno a13 a31 a35 a38 f5
  apply _hno 145
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (6/41 : ℝ)) ∧ (h 1 ≤ (6/47 : ℝ)) ∧ (h 3 ≤ (4/33 : ℝ)) ∧ (h 4 ≤ (3/25 : ℝ)) ∧ (h 5 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_3544 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a34 : h 3 ≤ (5/42 : ℝ))
    (a47 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3543 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a35 : -(h 4) < (-2/17 : ℝ))
    (a38 : -(h 0) < (-5/37 : ℝ))
    (a43 : -(h 5) < (-2/19 : ℝ))
    (a46 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a31 + (1/3 : ℝ) * a35 + (1/6 : ℝ) * a38 + (1/6 : ℝ) * a43 + (1/6 : ℝ) * a46 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3542 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a35 : -(h 4) < (-2/17 : ℝ))
    (a43 : -(h 5) < (-2/19 : ℝ))
    (a45 : -(h 0) < (-6/43 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/34 : ℝ) * _ctx.order1 + (3/17 : ℝ) * _ctx.order3 + (1/34 : ℝ) * a13 + (9/34 : ℝ) * a31 + (6/17 : ℝ) * a35 + (3/17 : ℝ) * a43 + (3/17 : ℝ) * a45 + (3/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3541 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a39 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a44 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a39 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3540 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a34 : h 3 ≤ (5/42 : ℝ))
    (a35 : -(h 4) < (-2/17 : ℝ))
    (a38 : -(h 0) < (-5/37 : ℝ))
    (a39 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a43 : -(h 5) < (-2/19 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3541 h delta _ctx _hno a39 f0
  by_cases p1 : h 0 ≤ (6/43 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/43 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3542 h delta _ctx _hno a13 a31 a35 a43 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3543 h delta _ctx _hno a31 a35 a38 a43 f2
  by_cases p3 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3544 h delta _ctx _hno a34 f3
  by_cases p4 : h 5 ≤ (5/46 : ℝ)
  swap
  · have f4 : -(h 5) < (-5/46 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3545 h delta _ctx _hno a13 a31 a34 a35 a38 a39 p1 f4
  apply _hno 20
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (6/43 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 5 ≤ (5/46 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_3539 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a34 : h 3 ≤ (5/42 : ℝ))
    (a42 : -(h 4) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * _ctx.order3 + (1 : ℝ) * a34 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3538 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a35 : -(h 4) < (-2/17 : ℝ))
    (a41 : -(h 2) < (-5/38 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/13 : ℝ) * _ctx.order1 + (4/13 : ℝ) * _ctx.order3 + (4/13 : ℝ) * _ctx.min + (8/13 : ℝ) * _ctx.lower + (1/13 : ℝ) * _ctx.fail2 + (4/13 : ℝ) * a35 + (8/13 : ℝ) * a41 + (4/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3537 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a35 : -(h 4) < (-2/17 : ℝ))
    (a40 : -(h 0) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/13 : ℝ) * _ctx.order3 + (3/13 : ℝ) * _ctx.min + (1/13 : ℝ) * a13 + (3/13 : ℝ) * a31 + (6/13 : ℝ) * a35 + (3/13 : ℝ) * a40 + (3/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3536 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a35 : -(h 4) < (-2/17 : ℝ))
    (a38 : -(h 0) < (-5/37 : ℝ))
    (a39 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a44 : -(h 5) < (-5/46 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order1 + (2/13 : ℝ) * _ctx.order3 + (4/13 : ℝ) * a31 + (4/13 : ℝ) * a35 + (2/13 : ℝ) * a38 + (1/13 : ℝ) * a39 + (2/13 : ℝ) * a44 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3535 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a34 : h 3 ≤ (5/42 : ℝ))
    (a43 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3534 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a35 : -(h 4) < (-2/17 : ℝ))
    (a38 : -(h 0) < (-5/37 : ℝ))
    (a39 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a42 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a31 + (1/3 : ℝ) * a35 + (1/6 : ℝ) * a38 + (1/6 : ℝ) * a39 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3533 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a35 : -(h 4) < (-2/17 : ℝ))
    (a39 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a41 : -(h 0) < (-6/43 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order1 + (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/3 : ℝ) * a31 + (1/3 : ℝ) * a35 + (1/6 : ℝ) * a39 + (1/6 : ℝ) * a41 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3532 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a37 : ((2 : ℝ) * (delta)) ≤ (7/33 : ℝ))
    (a40 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a37 + (1 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3531 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a34 : h 3 ≤ (5/42 : ℝ))
    (a35 : -(h 4) < (-2/17 : ℝ))
    (a37 : ((2 : ℝ) * (delta)) ≤ (7/33 : ℝ))
    (a38 : -(h 0) < (-5/37 : ℝ))
    (a39 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3532 h delta _ctx _hno a37 f0
  by_cases p1 : h 0 ≤ (6/43 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/43 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3533 h delta _ctx _hno a31 a35 a39 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3534 h delta _ctx _hno a31 a35 a38 a39 f2
  by_cases p3 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3535 h delta _ctx _hno a34 f3
  by_cases p4 : h 5 ≤ (5/46 : ℝ)
  swap
  · have f4 : -(h 5) < (-5/46 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3536 h delta _ctx _hno a31 a35 a38 a39 f4
  apply _hno 20
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (6/43 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 5 ≤ (5/46 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_3530 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a34 : h 3 ≤ (5/42 : ℝ))
    (a35 : -(h 4) < (-2/17 : ℝ))
    (a37 : ((2 : ℝ) * (delta)) ≤ (7/33 : ℝ))
    (a38 : -(h 0) < (-5/37 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3531 h delta _ctx _hno a31 a34 a35 a37 a38 f0
  by_cases p1 : h 0 ≤ (1/7 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3537 h delta _ctx _hno a13 a31 a35 f1
  by_cases p2 : h 2 ≤ (5/38 : ℝ)
  swap
  · have f2 : -(h 2) < (-5/38 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3538 h delta _ctx _hno a35 f2
  by_cases p3 : h 4 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 4) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3539 h delta _ctx _hno a34 f3
  by_cases p4 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f4 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3540 h delta _ctx _hno a13 a31 a34 a35 a38 p0 f4
  apply _hno 24
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (5/38 : ℝ)) ∧ (h 4 ≤ (1/8 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_3529 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a35 : -(h 4) < (-2/17 : ℝ))
    (a37 : ((-2 : ℝ) * (delta)) < (-7/33 : ℝ))
    (a48 : -(h 5) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/19 : ℝ) * _ctx.order1 + (4/19 : ℝ) * _ctx.order3 + (1/19 : ℝ) * _ctx.fail2 + (8/19 : ℝ) * a31 + (4/19 : ℝ) * a35 + (2/19 : ℝ) * a37 + (4/19 : ℝ) * a48 + (4/19 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3528 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a34 : h 3 ≤ (5/42 : ℝ))
    (a47 : -(h 4) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * _ctx.order3 + (1 : ℝ) * a34 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3527 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a34 : h 3 ≤ (5/42 : ℝ))
    (a46 : -(h 3) < (-4/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3526 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a35 : -(h 4) < (-2/17 : ℝ))
    (a37 : ((-2 : ℝ) * (delta)) < (-7/33 : ℝ))
    (a42 : -(h 5) < (-5/46 : ℝ))
    (a45 : -(h 1) < (-6/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/19 : ℝ) * _ctx.order3 + (1/19 : ℝ) * _ctx.fail2 + (4/19 : ℝ) * a31 + (4/19 : ℝ) * a35 + (2/19 : ℝ) * a37 + (4/19 : ℝ) * a42 + (4/19 : ℝ) * a45 + (4/19 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3525 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a39 : h 0 ≤ (6/43 : ℝ))
    (a44 : -(h 0) < (-6/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a39 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3524 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a32 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3523 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a32 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a34 : h 3 ≤ (5/42 : ℝ))
    (a35 : -(h 4) < (-2/17 : ℝ))
    (a37 : ((-2 : ℝ) * (delta)) < (-7/33 : ℝ))
    (a39 : h 0 ≤ (6/43 : ℝ))
    (a42 : -(h 5) < (-5/46 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3524 h delta _ctx _hno a32 f0
  by_cases p1 : h 0 ≤ (6/41 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/41 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3525 h delta _ctx _hno a39 f1
  by_cases p2 : h 1 ≤ (6/47 : ℝ)
  swap
  · have f2 : -(h 1) < (-6/47 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3526 h delta _ctx _hno a31 a35 a37 a42 f2
  by_cases p3 : h 3 ≤ (4/33 : ℝ)
  swap
  · have f3 : -(h 3) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3527 h delta _ctx _hno a34 f3
  by_cases p4 : h 4 ≤ (3/25 : ℝ)
  swap
  · have f4 : -(h 4) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3528 h delta _ctx _hno a34 f4
  by_cases p5 : h 5 ≤ (2/17 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_3529 h delta _ctx _hno a31 a35 a37 f5
  apply _hno 145
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (6/41 : ℝ)) ∧ (h 1 ≤ (6/47 : ℝ)) ∧ (h 3 ≤ (4/33 : ℝ)) ∧ (h 4 ≤ (3/25 : ℝ)) ∧ (h 5 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_3522 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a34 : h 3 ≤ (5/42 : ℝ))
    (a41 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3521 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a35 : -(h 4) < (-2/17 : ℝ))
    (a37 : ((-2 : ℝ) * (delta)) < (-7/33 : ℝ))
    (a40 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/17 : ℝ) * _ctx.order3 + (4/17 : ℝ) * _ctx.min + (1/17 : ℝ) * _ctx.fail2 + (4/17 : ℝ) * a31 + (4/17 : ℝ) * a35 + (4/17 : ℝ) * a37 + (4/17 : ℝ) * a40 + (4/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3520 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a35 : -(h 4) < (-2/17 : ℝ))
    (a37 : ((-2 : ℝ) * (delta)) < (-7/33 : ℝ))
    (a39 : -(h 0) < (-6/43 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order1 + (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/3 : ℝ) * a31 + (1/3 : ℝ) * a35 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a39 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3519 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a38 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a32 + (1 : ℝ) * a38
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3518 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a32 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a34 : h 3 ≤ (5/42 : ℝ))
    (a35 : -(h 4) < (-2/17 : ℝ))
    (a37 : ((-2 : ℝ) * (delta)) < (-7/33 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3519 h delta _ctx _hno a32 f0
  by_cases p1 : h 0 ≤ (6/43 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/43 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3520 h delta _ctx _hno a31 a35 a37 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3521 h delta _ctx _hno a31 a35 a37 f2
  by_cases p3 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3522 h delta _ctx _hno a34 f3
  by_cases p4 : h 5 ≤ (5/46 : ℝ)
  swap
  · have f4 : -(h 5) < (-5/46 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3523 h delta _ctx _hno a31 a32 a34 a35 a37 p1 f4
  apply _hno 20
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (6/43 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 5 ≤ (5/46 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_3517 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a32 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a34 : h 3 ≤ (5/42 : ℝ))
    (a35 : -(h 4) < (-2/17 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/33 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/33 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3518 h delta _ctx _hno a31 a32 a34 a35 f0
  by_cases p1 : h 0 ≤ (5/37 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/37 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3530 h delta _ctx _hno a13 a31 a34 a35 p0 f1
  by_cases p2 : h 2 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 2) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3552 h delta _ctx _hno a35 f2
  by_cases p3 : h 5 ≤ (4/37 : ℝ)
  swap
  · have f3 : -(h 5) < (-4/37 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3553 h delta _ctx _hno a13 a31 a34 a35 p0 p1 f3
  apply _hno 23
  change (((2 : ℝ) * (delta)) ≤ (7/33 : ℝ)) ∧ (h 0 ≤ (5/37 : ℝ)) ∧ (h 2 ≤ (2/15 : ℝ)) ∧ (h 5 ≤ (4/37 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_3516 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a32 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a34 : h 3 ≤ (5/42 : ℝ))
    (a35 : -(h 4) < (-2/17 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3517 h delta _ctx _hno a13 a31 a32 a34 a35
  by_cases p1 : h 0 ≤ (5/36 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/36 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3571 h delta _ctx _hno a13 a31 a34 a35 p0 f1
  by_cases p2 : h 1 ≤ (9/65 : ℝ)
  swap
  · have f2 : -(h 1) < (-9/65 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3577 h delta _ctx _hno a31 a35 f2
  by_cases p3 : h 2 ≤ (3/22 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3578 h delta _ctx _hno a35 f3
  by_cases p4 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3579 h delta _ctx _hno a34 f4
  by_cases p5 : h 4 ≤ (5/41 : ℝ)
  swap
  · have f5 : -(h 4) < (-5/41 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_3580 h delta _ctx _hno a34 f5
  apply _hno 22
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (5/36 : ℝ)) ∧ (h 1 ≤ (9/65 : ℝ)) ∧ (h 2 ≤ (3/22 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (5/41 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_3515 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a39 : -(h 5) < (-2/19 : ℝ))
    (a40 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ))
    (a45 : -(h 4) < (-5/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/9 : ℝ) * _ctx.order3 + (1/27 : ℝ) * _ctx.fail3 + (2/27 : ℝ) * a13 + (2/9 : ℝ) * a31 + (2/9 : ℝ) * a39 + (4/27 : ℝ) * a40 + (4/9 : ℝ) * a45 + (2/9 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3514 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a39 : -(h 5) < (-2/19 : ℝ))
    (a40 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ))
    (a44 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/43 : ℝ) * _ctx.fail2 + (4/43 : ℝ) * a13 + (12/43 : ℝ) * a31 + (12/43 : ℝ) * a39 + (6/43 : ℝ) * a40 + (12/43 : ℝ) * a44 + (12/43 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3513 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a34 : -(h 3) < (-5/42 : ℝ))
    (a43 : -(h 2) < (-3/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/13 : ℝ) * _ctx.order1 + (4/13 : ℝ) * _ctx.min + (8/13 : ℝ) * _ctx.lower + (1/13 : ℝ) * _ctx.fail2 + (4/13 : ℝ) * a34 + (8/13 : ℝ) * a43 + (4/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3512 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 3) < (-5/42 : ℝ))
    (a42 : -(h 1) < (-9/65 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/13 : ℝ) * _ctx.min + (8/13 : ℝ) * _ctx.lower + (1/13 : ℝ) * _ctx.fail2 + (4/13 : ℝ) * a31 + (4/13 : ℝ) * a34 + (4/13 : ℝ) * a42 + (4/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3511 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 3) < (-5/42 : ℝ))
    (a40 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ))
    (a46 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/43 : ℝ) * _ctx.fail2 + (4/43 : ℝ) * a13 + (12/43 : ℝ) * a31 + (12/43 : ℝ) * a34 + (6/43 : ℝ) * a40 + (12/43 : ℝ) * a46 + (12/43 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3510 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 3) < (-5/42 : ℝ))
    (a40 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ))
    (a41 : -(h 0) < (-5/36 : ℝ))
    (a45 : -(h 4) < (-4/35 : ℝ))
    (a50 : -(h 5) < (-5/46 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/16 : ℝ) * a13 + (3/16 : ℝ) * a31 + (3/16 : ℝ) * a34 + (3/32 : ℝ) * a40 + (3/16 : ℝ) * a41 + (3/16 : ℝ) * a45 + (3/16 : ℝ) * a50 + (3/16 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3509 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a39 : -(h 5) < (-2/19 : ℝ))
    (a40 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ))
    (a41 : -(h 0) < (-5/36 : ℝ))
    (a45 : -(h 4) < (-4/35 : ℝ))
    (a49 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/16 : ℝ) * _ctx.order2 + (1/16 : ℝ) * a13 + (3/16 : ℝ) * a39 + (3/32 : ℝ) * a40 + (3/16 : ℝ) * a41 + (3/16 : ℝ) * a45 + (3/8 : ℝ) * a49 + (3/16 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3508 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 3) < (-5/42 : ℝ))
    (a41 : -(h 0) < (-5/36 : ℝ))
    (a45 : -(h 4) < (-4/35 : ℝ))
    (a48 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a31 + (1/5 : ℝ) * a34 + (1/5 : ℝ) * a41 + (1/5 : ℝ) * a45 + (1/5 : ℝ) * a48 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

end RealPinwheel.WeakSevenBandData
