import Pinwheel.WeakSevenBandData.CoverChunks.Upper001

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem upper_node_4147 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : h 0 ≤ (4/23 : ℝ))
    (a42 : ((-2 : ℝ) * (h 0)) + ((-5 : ℝ) * (h 5)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * _ctx.order1 + (2 : ℝ) * _ctx.order2 + (3 : ℝ) * _ctx.order3 + (4 : ℝ) * _ctx.order4 + (1 : ℝ) * _ctx.lower + (1 : ℝ) * a29 + (1 : ℝ) * a42 + (1 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4146 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : h 0 ≤ (4/23 : ℝ))
    (a31 : h 4 ≤ (9/80 : ℝ))
    (a41 : ((-2 : ℝ) * (h 0)) + ((-5 : ℝ) * (h 4)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * a29 + (5 : ℝ) * a31 + (1 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4145 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : h 0 ≤ (4/23 : ℝ))
    (a40 : ((-2 : ℝ) * (h 0)) + ((-5 : ℝ) * (h 3)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (5/3 : ℝ) * _ctx.order1 + (10/3 : ℝ) * _ctx.order2 + (5/3 : ℝ) * _ctx.order4 + (10/3 : ℝ) * _ctx.min + (5 : ℝ) * _ctx.lower + (1/3 : ℝ) * a29 + (1 : ℝ) * a40 + (5/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4144 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : h 0 ≤ (4/23 : ℝ))
    (a34 : ((5 : ℝ) * (h 2)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a39 : ((-2 : ℝ) * (h 0)) + ((-5 : ℝ) * (h 2)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4 : ℝ) * _ctx.lower + (2 : ℝ) * a29 + (1 : ℝ) * a34 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4143 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : h 0 ≤ (4/23 : ℝ))
    (a33 : ((5 : ℝ) * (h 1)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a38 : ((-2 : ℝ) * (h 0)) + ((-5 : ℝ) * (h 1)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4 : ℝ) * _ctx.lower + (2 : ℝ) * a29 + (1 : ℝ) * a33 + (1 : ℝ) * a38
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4142 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 5) < (-1/9 : ℝ))
    (a34 : ((5 : ℝ) * (h 2)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a37 : ((-5 : ℝ) * (h 5)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (10/17 : ℝ) * _ctx.order1 + (10/17 : ℝ) * _ctx.order3 + (20/17 : ℝ) * _ctx.order4 + (5/17 : ℝ) * _ctx.fail1 + (15/34 : ℝ) * a32 + (2/17 : ℝ) * a34 + (9/34 : ℝ) * a37 + (10/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4141 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a35 : ((5 : ℝ) * (h 3)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a36 : ((-5 : ℝ) * (h 4)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (5 : ℝ) * _ctx.order3 + (1 : ℝ) * a35 + (1 : ℝ) * a36
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4140 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a34 : ((5 : ℝ) * (h 2)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a35 : ((-5 : ℝ) * (h 3)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (5 : ℝ) * _ctx.order2 + (1 : ℝ) * a34 + (1 : ℝ) * a35
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4139 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : ((5 : ℝ) * (h 1)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a34 : ((-5 : ℝ) * (h 2)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (5 : ℝ) * _ctx.order1 + (1 : ℝ) * a33 + (1 : ℝ) * a34
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4138 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : h 4 ≤ (9/80 : ℝ))
    (a37 : -(h 4) < (-13/112 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a37
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4137 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a36 : -(h 1) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * a13 + (1/2 : ℝ) * a27 + (1/2 : ℝ) * a36
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4136 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : h 4 ≤ (9/80 : ℝ))
    (a43 : -(h 4) < (-8/67 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4135 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a32 : -(h 5) < (-1/9 : ℝ))
    (a35 : -(h 0) < (-3/19 : ℝ))
    (a42 : -(h 3) < (-11/92 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order1 + (4/13 : ℝ) * _ctx.order2 + (2/13 : ℝ) * _ctx.order4 + (1/13 : ℝ) * a27 + (4/13 : ℝ) * a32 + (2/13 : ℝ) * a35 + (6/13 : ℝ) * a42 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4134 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a32 : -(h 5) < (-1/9 : ℝ))
    (a35 : -(h 0) < (-3/19 : ℝ))
    (a41 : -(h 1) < (-3/25 : ℝ))
    (a45 : -(h 3) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/16 : ℝ) * _ctx.order4 + (1/32 : ℝ) * _ctx.fail1 + (3/32 : ℝ) * a27 + (3/8 : ℝ) * a32 + (1/8 : ℝ) * a35 + (3/16 : ℝ) * a41 + (3/16 : ℝ) * a45 + (3/16 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4133 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a44 : -(h 1) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * a13 + (1/2 : ℝ) * a27 + (1/2 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4132 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a32 : -(h 5) < (-1/9 : ℝ))
    (a41 : -(h 1) < (-3/25 : ℝ))
    (a43 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/16 : ℝ) * _ctx.order3 + (3/8 : ℝ) * _ctx.order4 + (1/32 : ℝ) * _ctx.fail1 + (3/32 : ℝ) * a27 + (9/16 : ℝ) * a32 + (3/16 : ℝ) * a41 + (1/8 : ℝ) * a43 + (3/16 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4131 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a41 : -(h 1) < (-3/25 : ℝ))
    (a42 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * a13 + (1/2 : ℝ) * a41 + (1/2 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4130 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a32 : -(h 5) < (-1/9 : ℝ))
    (a35 : -(h 0) < (-3/19 : ℝ))
    (a41 : -(h 1) < (-3/25 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4131 h delta _ctx _hno a13 a41 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4132 h delta _ctx _hno a27 a32 a41 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4133 h delta _ctx _hno a13 a27 f2
  by_cases p3 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f3 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_4134 h delta _ctx _hno a27 a32 a35 a41 f3
  apply _hno 84
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_4129 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a32 : -(h 5) < (-1/9 : ℝ))
    (a38 : -(h 1) < (-5/42 : ℝ))
    (a40 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/16 : ℝ) * _ctx.order3 + (3/8 : ℝ) * _ctx.order4 + (1/32 : ℝ) * _ctx.fail1 + (3/32 : ℝ) * a27 + (9/16 : ℝ) * a32 + (3/16 : ℝ) * a38 + (1/8 : ℝ) * a40 + (3/16 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4128 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a38 : -(h 1) < (-5/42 : ℝ))
    (a39 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * a13 + (1/2 : ℝ) * a38 + (1/2 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4127 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a31 : h 4 ≤ (9/80 : ℝ))
    (a32 : -(h 5) < (-1/9 : ℝ))
    (a35 : -(h 0) < (-3/19 : ℝ))
    (a38 : -(h 1) < (-5/42 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4128 h delta _ctx _hno a13 a38 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4129 h delta _ctx _hno a27 a32 a38 f1
  by_cases p2 : h 1 ≤ (3/25 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4130 h delta _ctx _hno a13 a27 a32 a35 f2
  by_cases p3 : h 3 ≤ (11/92 : ℝ)
  swap
  · have f3 : -(h 3) < (-11/92 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_4135 h delta _ctx _hno a27 a32 a35 f3
  by_cases p4 : h 4 ≤ (8/67 : ℝ)
  swap
  · have f4 : -(h 4) < (-8/67 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_4136 h delta _ctx _hno a31 f4
  apply _hno 60
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (11/92 : ℝ)) ∧ (h 4 ≤ (8/67 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_4126 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a32 : -(h 5) < (-1/9 : ℝ))
    (a37 : -(h 0) < (-1/6 : ℝ))
    (a43 : -(h 1) < (-7/60 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/16 : ℝ) * _ctx.order3 + (3/8 : ℝ) * _ctx.order4 + (1/32 : ℝ) * _ctx.fail1 + (3/32 : ℝ) * a27 + (9/16 : ℝ) * a32 + (1/8 : ℝ) * a37 + (3/16 : ℝ) * a43 + (3/16 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4125 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : h 0 ≤ (4/23 : ℝ))
    (a42 : -(h 0) < (-2/11 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4124 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a28 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-3/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a28 + (1 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4123 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a28 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ))
    (a29 : h 0 ≤ (4/23 : ℝ))
    (a32 : -(h 5) < (-1/9 : ℝ))
    (a37 : -(h 0) < (-1/6 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/13 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4124 h delta _ctx _hno a28 f0
  by_cases p1 : h 0 ≤ (2/11 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/11 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4125 h delta _ctx _hno a29 f1
  by_cases p2 : h 1 ≤ (7/60 : ℝ)
  swap
  · have f2 : -(h 1) < (-7/60 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4126 h delta _ctx _hno a27 a32 a37 f2
  apply _hno 153
  change (((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)) ∧ (h 0 ≤ (2/11 : ℝ)) ∧ (h 1 ≤ (7/60 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem upper_node_4122 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : h 0 ≤ (4/23 : ℝ))
    (a39 : -(h 0) < (-5/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4121 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a28 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ))
    (a38 : ((-2 : ℝ) * (delta)) < (-3/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a28 + (1 : ℝ) * a38
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4120 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a28 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ))
    (a29 : h 0 ≤ (4/23 : ℝ))
    (a32 : -(h 5) < (-1/9 : ℝ))
    (a37 : -(h 0) < (-1/6 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/13 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4121 h delta _ctx _hno a28 f0
  by_cases p1 : h 0 ≤ (5/26 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/26 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4122 h delta _ctx _hno a29 f1
  by_cases p2 : h 1 ≤ (3/26 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4123 h delta _ctx _hno a27 a28 a29 a32 a37
  apply _hno 1
  change (((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)) ∧ (h 0 ≤ (5/26 : ℝ)) ∧ (h 1 ≤ (3/26 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem upper_node_4119 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a28 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ))
    (a36 : ((-2 : ℝ) * (delta)) < (-3/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a28 + (1 : ℝ) * a36
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4118 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a28 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ))
    (a29 : h 0 ≤ (4/23 : ℝ))
    (a31 : h 4 ≤ (9/80 : ℝ))
    (a32 : -(h 5) < (-1/9 : ℝ))
    (a35 : -(h 0) < (-3/19 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/13 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4119 h delta _ctx _hno a28 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4120 h delta _ctx _hno a27 a28 a29 a32 f1
  by_cases p2 : h 1 ≤ (5/42 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/42 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4127 h delta _ctx _hno a13 a27 a31 a32 a35 f2
  apply _hno 34
  change (((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (5/42 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem upper_node_4117 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : ((3 : ℝ) * (h 5)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a32 : -(h 5) < (-1/9 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * a15 + (1/2 : ℝ) * a32 + (1/2 : ℝ) * a34
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4116 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a15 : ((3 : ℝ) * (h 5)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a28 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ))
    (a29 : h 0 ≤ (4/23 : ℝ))
    (a31 : h 4 ≤ (9/80 : ℝ))
    (a32 : -(h 5) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4117 h delta _ctx _hno a15 a32 f0
  by_cases p1 : h 0 ≤ (3/19 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/19 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4118 h delta _ctx _hno a13 a27 a28 a29 a31 a32 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4137 h delta _ctx _hno a13 a27 f2
  by_cases p3 : h 4 ≤ (13/112 : ℝ)
  swap
  · have f3 : -(h 4) < (-13/112 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_4138 h delta _ctx _hno a31 f3
  apply _hno 4
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (13/112 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_4115 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a15 : ((3 : ℝ) * (h 5)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a28 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ))
    (a29 : h 0 ≤ (4/23 : ℝ))
    (a31 : h 4 ≤ (9/80 : ℝ))
    (a32 : -(h 5) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((5 : ℝ) * (h 1)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ)
  swap
  · have f0 : ((-5 : ℝ) * (h 1)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4116 h delta _ctx _hno a13 a15 a27 a28 a29 a31 a32
  by_cases p1 : ((5 : ℝ) * (h 2)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ)
  swap
  · have f1 : ((-5 : ℝ) * (h 2)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4139 h delta _ctx _hno p0 f1
  by_cases p2 : ((5 : ℝ) * (h 3)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ)
  swap
  · have f2 : ((-5 : ℝ) * (h 3)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4140 h delta _ctx _hno p1 f2
  by_cases p3 : ((5 : ℝ) * (h 4)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ)
  swap
  · have f3 : ((-5 : ℝ) * (h 4)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_4141 h delta _ctx _hno p2 f3
  by_cases p4 : ((5 : ℝ) * (h 5)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ)
  swap
  · have f4 : ((-5 : ℝ) * (h 5)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_4142 h delta _ctx _hno a32 p1 f4
  by_cases p5 : ((2 : ℝ) * (h 0)) + ((5 : ℝ) * (h 1)) ≤ (1 : ℝ)
  swap
  · have f5 : ((-2 : ℝ) * (h 0)) + ((-5 : ℝ) * (h 1)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_4143 h delta _ctx _hno a29 p0 f5
  by_cases p6 : ((2 : ℝ) * (h 0)) + ((5 : ℝ) * (h 2)) ≤ (1 : ℝ)
  swap
  · have f6 : ((-2 : ℝ) * (h 0)) + ((-5 : ℝ) * (h 2)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact upper_node_4144 h delta _ctx _hno a29 p1 f6
  by_cases p7 : ((2 : ℝ) * (h 0)) + ((5 : ℝ) * (h 3)) ≤ (1 : ℝ)
  swap
  · have f7 : ((-2 : ℝ) * (h 0)) + ((-5 : ℝ) * (h 3)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p7
      linarith only [hp]
    exact upper_node_4145 h delta _ctx _hno a29 f7
  by_cases p8 : ((2 : ℝ) * (h 0)) + ((5 : ℝ) * (h 4)) ≤ (1 : ℝ)
  swap
  · have f8 : ((-2 : ℝ) * (h 0)) + ((-5 : ℝ) * (h 4)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p8
      linarith only [hp]
    exact upper_node_4146 h delta _ctx _hno a29 a31 f8
  by_cases p9 : ((2 : ℝ) * (h 0)) + ((5 : ℝ) * (h 5)) ≤ (1 : ℝ)
  swap
  · have f9 : ((-2 : ℝ) * (h 0)) + ((-5 : ℝ) * (h 5)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p9
      linarith only [hp]
    exact upper_node_4147 h delta _ctx _hno a29 f9
  apply _hno 152
  change (((5 : ℝ) * (h 1)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ)) ∧ (((5 : ℝ) * (h 2)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ)) ∧ (((5 : ℝ) * (h 3)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ)) ∧ (((5 : ℝ) * (h 4)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ)) ∧ (((5 : ℝ) * (h 5)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ)) ∧ (((2 : ℝ) * (h 0)) + ((5 : ℝ) * (h 1)) ≤ (1 : ℝ)) ∧ (((2 : ℝ) * (h 0)) + ((5 : ℝ) * (h 2)) ≤ (1 : ℝ)) ∧ (((2 : ℝ) * (h 0)) + ((5 : ℝ) * (h 3)) ≤ (1 : ℝ)) ∧ (((2 : ℝ) * (h 0)) + ((5 : ℝ) * (h 4)) ≤ (1 : ℝ)) ∧ (((2 : ℝ) * (h 0)) + ((5 : ℝ) * (h 5)) ≤ (1 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9⟩

theorem upper_node_4114 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a34 : -(h 1) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * a13 + (1/2 : ℝ) * a27 + (1/2 : ℝ) * a34
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4113 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a33 : -(h 0) < (-2/13 : ℝ))
    (a37 : -(h 4) < (-13/112 : ℝ))
    (a40 : -(h 1) < (-5/42 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order2 + (1/3 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a33 + (1/2 : ℝ) * a37 + (1/6 : ℝ) * a40 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4112 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a35 : h 0 ≤ (3/19 : ℝ))
    (a39 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a35 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4111 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a38 : ((-2 : ℝ) * (delta)) < (-3/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a32 + (1 : ℝ) * a38
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4110 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a32 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a33 : -(h 0) < (-2/13 : ℝ))
    (a35 : h 0 ≤ (3/19 : ℝ))
    (a37 : -(h 4) < (-13/112 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/13 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4111 h delta _ctx _hno a32 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4112 h delta _ctx _hno a35 f1
  by_cases p2 : h 1 ≤ (5/42 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/42 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4113 h delta _ctx _hno a27 a33 a37 f2
  apply _hno 34
  change (((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (5/42 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem upper_node_4109 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a36 : -(h 1) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * a13 + (1/2 : ℝ) * a27 + (1/2 : ℝ) * a36
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4108 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a31 : -(h 4) < (-9/80 : ℝ))
    (a35 : -(h 0) < (-3/19 : ℝ))
    (a38 : -(h 1) < (-5/42 : ℝ))
    (a43 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/16 : ℝ) * _ctx.order3 + (1/32 : ℝ) * _ctx.fail1 + (3/32 : ℝ) * a27 + (3/8 : ℝ) * a31 + (1/8 : ℝ) * a35 + (3/16 : ℝ) * a38 + (3/16 : ℝ) * a43 + (3/16 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4107 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a35 : -(h 0) < (-3/19 : ℝ))
    (a47 : -(h 4) < (-8/67 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order1 + (1/3 : ℝ) * _ctx.order2 + (1/2 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a35 + (2/3 : ℝ) * a47 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4106 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a35 : -(h 0) < (-3/19 : ℝ))
    (a42 : -(h 4) < (-5/44 : ℝ))
    (a46 : -(h 3) < (-11/92 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order1 + (1/3 : ℝ) * _ctx.order2 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a42 + (1/2 : ℝ) * a46 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4105 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a35 : -(h 0) < (-3/19 : ℝ))
    (a42 : -(h 4) < (-5/44 : ℝ))
    (a45 : -(h 1) < (-3/25 : ℝ))
    (a49 : -(h 3) < (-4/35 : ℝ))
    (a55 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/32 : ℝ) * _ctx.fail1 + (3/32 : ℝ) * a27 + (1/8 : ℝ) * a35 + (3/16 : ℝ) * a42 + (3/16 : ℝ) * a45 + (3/16 : ℝ) * a49 + (3/16 : ℝ) * a55 + (3/16 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4104 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a35 : -(h 0) < (-3/19 : ℝ))
    (a42 : -(h 4) < (-5/44 : ℝ))
    (a45 : -(h 1) < (-3/25 : ℝ))
    (a54 : -(h 3) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order2 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a45 + (1/3 : ℝ) * a54 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4103 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a35 : -(h 0) < (-3/19 : ℝ))
    (a42 : -(h 4) < (-5/44 : ℝ))
    (a45 : -(h 1) < (-3/25 : ℝ))
    (a49 : -(h 3) < (-4/35 : ℝ))
    (a53 : -(h 2) < (-7/60 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a49 + (1/6 : ℝ) * a53 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4102 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : h 1 ≤ (1/8 : ℝ))
    (a52 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a52
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4101 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a42 : -(h 4) < (-5/44 : ℝ))
    (a45 : -(h 1) < (-3/25 : ℝ))
    (a49 : -(h 3) < (-4/35 : ℝ))
    (a51 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order2 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a45 + (1/3 : ℝ) * a49 + (1/6 : ℝ) * a51 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4100 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a45 : -(h 1) < (-3/25 : ℝ))
    (a50 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * a13 + (1/2 : ℝ) * a45 + (1/2 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4099 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a30 : h 1 ≤ (1/8 : ℝ))
    (a35 : -(h 0) < (-3/19 : ℝ))
    (a42 : -(h 4) < (-5/44 : ℝ))
    (a45 : -(h 1) < (-3/25 : ℝ))
    (a49 : -(h 3) < (-4/35 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4100 h delta _ctx _hno a13 a45 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4101 h delta _ctx _hno a27 a42 a45 a49 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4102 h delta _ctx _hno a30 f2
  by_cases p3 : h 2 ≤ (7/60 : ℝ)
  swap
  · have f3 : -(h 2) < (-7/60 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_4103 h delta _ctx _hno a27 a35 a42 a45 a49 f3
  by_cases p4 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_4104 h delta _ctx _hno a27 a35 a42 a45 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_4105 h delta _ctx _hno a27 a35 a42 a45 a49 f5
  apply _hno 54
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (7/60 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_4098 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a48 : -(h 1) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * a13 + (1/2 : ℝ) * a27 + (1/2 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4097 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a42 : -(h 4) < (-5/44 : ℝ))
    (a45 : -(h 1) < (-3/25 : ℝ))
    (a47 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order2 + (1/3 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a27 + (1/2 : ℝ) * a42 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4096 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a45 : -(h 1) < (-3/25 : ℝ))
    (a46 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * a13 + (1/2 : ℝ) * a45 + (1/2 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4095 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a30 : h 1 ≤ (1/8 : ℝ))
    (a35 : -(h 0) < (-3/19 : ℝ))
    (a42 : -(h 4) < (-5/44 : ℝ))
    (a45 : -(h 1) < (-3/25 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4096 h delta _ctx _hno a13 a45 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4097 h delta _ctx _hno a27 a42 a45 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4098 h delta _ctx _hno a13 a27 f2
  by_cases p3 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f3 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_4099 h delta _ctx _hno a13 a27 a30 a35 a42 a45 f3
  apply _hno 84
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_4094 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a38 : -(h 1) < (-5/42 : ℝ))
    (a42 : -(h 4) < (-5/44 : ℝ))
    (a44 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order2 + (1/3 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a38 + (1/2 : ℝ) * a42 + (1/6 : ℝ) * a44 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4093 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a38 : -(h 1) < (-5/42 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * a13 + (1/2 : ℝ) * a38 + (1/2 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4092 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a30 : h 1 ≤ (1/8 : ℝ))
    (a35 : -(h 0) < (-3/19 : ℝ))
    (a38 : -(h 1) < (-5/42 : ℝ))
    (a42 : -(h 4) < (-5/44 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4093 h delta _ctx _hno a13 a38 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4094 h delta _ctx _hno a27 a38 a42 f1
  by_cases p2 : h 1 ≤ (3/25 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4095 h delta _ctx _hno a13 a27 a30 a35 a42 f2
  by_cases p3 : h 3 ≤ (11/92 : ℝ)
  swap
  · have f3 : -(h 3) < (-11/92 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_4106 h delta _ctx _hno a27 a35 a42 f3
  by_cases p4 : h 4 ≤ (8/67 : ℝ)
  swap
  · have f4 : -(h 4) < (-8/67 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_4107 h delta _ctx _hno a27 a35 f4
  apply _hno 60
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (11/92 : ℝ)) ∧ (h 4 ≤ (8/67 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_4091 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a41 : -(h 1) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * a13 + (1/2 : ℝ) * a27 + (1/2 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4090 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a31 : -(h 4) < (-9/80 : ℝ))
    (a38 : -(h 1) < (-5/42 : ℝ))
    (a40 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order2 + (1/3 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a27 + (1/2 : ℝ) * a31 + (1/6 : ℝ) * a38 + (1/6 : ℝ) * a40 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4089 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a39 : ((-2 : ℝ) * (delta)) < (-5/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a32 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4088 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a30 : h 1 ≤ (1/8 : ℝ))
    (a31 : -(h 4) < (-9/80 : ℝ))
    (a32 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a35 : -(h 0) < (-3/19 : ℝ))
    (a38 : -(h 1) < (-5/42 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/22 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/22 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4089 h delta _ctx _hno a32 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4090 h delta _ctx _hno a27 a31 a38 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4091 h delta _ctx _hno a13 a27 f2
  by_cases p3 : h 4 ≤ (5/44 : ℝ)
  swap
  · have f3 : -(h 4) < (-5/44 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_4092 h delta _ctx _hno a13 a27 a30 a35 a38 f3
  by_cases p4 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_4108 h delta _ctx _hno a27 a31 a35 a38 f4
  apply _hno 58
  change (((2 : ℝ) * (delta)) ≤ (5/22 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (5/44 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_4087 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : h 0 ≤ (4/23 : ℝ))
    (a47 : ((-2 : ℝ) * (h 0)) + ((-5 : ℝ) * (h 5)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * _ctx.order1 + (2 : ℝ) * _ctx.order2 + (3 : ℝ) * _ctx.order3 + (4 : ℝ) * _ctx.order4 + (1 : ℝ) * _ctx.lower + (1 : ℝ) * a29 + (1 : ℝ) * a47 + (1 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4086 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : h 0 ≤ (4/23 : ℝ))
    (a46 : ((-2 : ℝ) * (h 0)) + ((-5 : ℝ) * (h 4)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (5/4 : ℝ) * _ctx.order1 + (5/2 : ℝ) * _ctx.order2 + (15/4 : ℝ) * _ctx.order3 + (5/4 : ℝ) * _ctx.min + (5/2 : ℝ) * _ctx.lower + (3/4 : ℝ) * a29 + (1 : ℝ) * a46 + (5/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4085 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : h 0 ≤ (4/23 : ℝ))
    (a45 : ((-2 : ℝ) * (h 0)) + ((-5 : ℝ) * (h 3)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (5/3 : ℝ) * _ctx.order1 + (10/3 : ℝ) * _ctx.order2 + (5/3 : ℝ) * _ctx.order4 + (10/3 : ℝ) * _ctx.min + (5 : ℝ) * _ctx.lower + (1/3 : ℝ) * a29 + (1 : ℝ) * a45 + (5/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4084 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : h 0 ≤ (4/23 : ℝ))
    (a39 : ((5 : ℝ) * (h 2)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a44 : ((-2 : ℝ) * (h 0)) + ((-5 : ℝ) * (h 2)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4 : ℝ) * _ctx.lower + (2 : ℝ) * a29 + (1 : ℝ) * a39 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4083 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : h 0 ≤ (4/23 : ℝ))
    (a38 : ((5 : ℝ) * (h 1)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a43 : ((-2 : ℝ) * (h 0)) + ((-5 : ℝ) * (h 1)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4 : ℝ) * _ctx.lower + (2 : ℝ) * a29 + (1 : ℝ) * a38 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4082 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a37 : -(h 0) < (-1/6 : ℝ))
    (a42 : ((-5 : ℝ) * (h 5)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/2 : ℝ) * _ctx.order1 + (1 : ℝ) * _ctx.order2 + (3/2 : ℝ) * _ctx.order3 + (2 : ℝ) * _ctx.order4 + (3/4 : ℝ) * a32 + (1/2 : ℝ) * a37 + (1/2 : ℝ) * a42 + (1/2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4081 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a37 : -(h 0) < (-1/6 : ℝ))
    (a41 : ((-5 : ℝ) * (h 4)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (5/9 : ℝ) * _ctx.order1 + (10/9 : ℝ) * _ctx.order2 + (5/3 : ℝ) * _ctx.order3 + (5/9 : ℝ) * _ctx.min + (1/3 : ℝ) * a32 + (5/9 : ℝ) * a37 + (4/9 : ℝ) * a41 + (5/9 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4080 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : -(h 4) < (-9/80 : ℝ))
    (a32 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a37 : -(h 0) < (-1/6 : ℝ))
    (a40 : ((-5 : ℝ) * (h 3)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (5/13 : ℝ) * _ctx.order1 + (10/13 : ℝ) * _ctx.order2 + (5/13 : ℝ) * _ctx.min + (5/13 : ℝ) * a31 + (1/13 : ℝ) * a32 + (5/13 : ℝ) * a37 + (3/13 : ℝ) * a40 + (5/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4079 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a31 : -(h 4) < (-9/80 : ℝ))
    (a37 : -(h 0) < (-1/6 : ℝ))
    (a39 : ((-5 : ℝ) * (h 2)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (5/18 : ℝ) * _ctx.order1 + (5/18 : ℝ) * _ctx.order3 + (5/18 : ℝ) * _ctx.min + (1/18 : ℝ) * a27 + (5/9 : ℝ) * a31 + (5/18 : ℝ) * a37 + (1/9 : ℝ) * a39 + (5/18 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4078 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a31 : -(h 4) < (-9/80 : ℝ))
    (a37 : -(h 0) < (-1/6 : ℝ))
    (a38 : ((-5 : ℝ) * (h 1)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ))
    (a46 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (10/53 : ℝ) * _ctx.order2 + (20/53 : ℝ) * _ctx.order3 + (1/53 : ℝ) * a27 + (30/53 : ℝ) * a31 + (10/53 : ℝ) * a37 + (2/53 : ℝ) * a38 + (10/53 : ℝ) * a46 + (10/53 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4077 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a31 : -(h 4) < (-9/80 : ℝ))
    (a37 : -(h 0) < (-1/6 : ℝ))
    (a41 : -(h 1) < (-3/26 : ℝ))
    (a45 : -(h 2) < (-5/44 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a27 + (1/3 : ℝ) * a31 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a41 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4076 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : h 1 ≤ (1/8 : ℝ))
    (a44 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4075 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : h 0 ≤ (4/23 : ℝ))
    (a43 : -(h 0) < (-3/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4074 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a42 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a32 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4073 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a29 : h 0 ≤ (4/23 : ℝ))
    (a30 : h 1 ≤ (1/8 : ℝ))
    (a31 : -(h 4) < (-9/80 : ℝ))
    (a32 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a37 : -(h 0) < (-1/6 : ℝ))
    (a38 : ((-5 : ℝ) * (h 1)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ))
    (a41 : -(h 1) < (-3/26 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4074 h delta _ctx _hno a32 f0
  by_cases p1 : h 0 ≤ (3/17 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/17 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4075 h delta _ctx _hno a29 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4076 h delta _ctx _hno a30 f2
  by_cases p3 : h 2 ≤ (5/44 : ℝ)
  swap
  · have f3 : -(h 2) < (-5/44 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_4077 h delta _ctx _hno a27 a31 a37 a41 f3
  by_cases p4 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_4078 h delta _ctx _hno a27 a31 a37 a38 f4
  apply _hno 76
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/17 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (5/44 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_4072 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : h 0 ≤ (4/23 : ℝ))
    (a40 : -(h 0) < (-5/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4071 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a39 : ((-2 : ℝ) * (delta)) < (-3/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a32 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4070 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a29 : h 0 ≤ (4/23 : ℝ))
    (a30 : h 1 ≤ (1/8 : ℝ))
    (a31 : -(h 4) < (-9/80 : ℝ))
    (a32 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a37 : -(h 0) < (-1/6 : ℝ))
    (a38 : ((-5 : ℝ) * (h 1)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/13 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4071 h delta _ctx _hno a32 f0
  by_cases p1 : h 0 ≤ (5/26 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/26 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4072 h delta _ctx _hno a29 f1
  by_cases p2 : h 1 ≤ (3/26 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4073 h delta _ctx _hno a27 a29 a30 a31 a32 a37 a38 f2
  apply _hno 1
  change (((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)) ∧ (h 0 ≤ (5/26 : ℝ)) ∧ (h 1 ≤ (3/26 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem upper_node_4069 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a29 : h 0 ≤ (4/23 : ℝ))
    (a30 : h 1 ≤ (1/8 : ℝ))
    (a31 : -(h 4) < (-9/80 : ℝ))
    (a32 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a37 : -(h 0) < (-1/6 : ℝ))
    : False := by
  by_cases p0 : ((5 : ℝ) * (h 1)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ)
  swap
  · have f0 : ((-5 : ℝ) * (h 1)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4070 h delta _ctx _hno a27 a29 a30 a31 a32 a37 f0
  by_cases p1 : ((5 : ℝ) * (h 2)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ)
  swap
  · have f1 : ((-5 : ℝ) * (h 2)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4079 h delta _ctx _hno a27 a31 a37 f1
  by_cases p2 : ((5 : ℝ) * (h 3)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ)
  swap
  · have f2 : ((-5 : ℝ) * (h 3)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4080 h delta _ctx _hno a31 a32 a37 f2
  by_cases p3 : ((5 : ℝ) * (h 4)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ)
  swap
  · have f3 : ((-5 : ℝ) * (h 4)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_4081 h delta _ctx _hno a32 a37 f3
  by_cases p4 : ((5 : ℝ) * (h 5)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ)
  swap
  · have f4 : ((-5 : ℝ) * (h 5)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_4082 h delta _ctx _hno a32 a37 f4
  by_cases p5 : ((2 : ℝ) * (h 0)) + ((5 : ℝ) * (h 1)) ≤ (1 : ℝ)
  swap
  · have f5 : ((-2 : ℝ) * (h 0)) + ((-5 : ℝ) * (h 1)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_4083 h delta _ctx _hno a29 p0 f5
  by_cases p6 : ((2 : ℝ) * (h 0)) + ((5 : ℝ) * (h 2)) ≤ (1 : ℝ)
  swap
  · have f6 : ((-2 : ℝ) * (h 0)) + ((-5 : ℝ) * (h 2)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact upper_node_4084 h delta _ctx _hno a29 p1 f6
  by_cases p7 : ((2 : ℝ) * (h 0)) + ((5 : ℝ) * (h 3)) ≤ (1 : ℝ)
  swap
  · have f7 : ((-2 : ℝ) * (h 0)) + ((-5 : ℝ) * (h 3)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p7
      linarith only [hp]
    exact upper_node_4085 h delta _ctx _hno a29 f7
  by_cases p8 : ((2 : ℝ) * (h 0)) + ((5 : ℝ) * (h 4)) ≤ (1 : ℝ)
  swap
  · have f8 : ((-2 : ℝ) * (h 0)) + ((-5 : ℝ) * (h 4)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p8
      linarith only [hp]
    exact upper_node_4086 h delta _ctx _hno a29 f8
  by_cases p9 : ((2 : ℝ) * (h 0)) + ((5 : ℝ) * (h 5)) ≤ (1 : ℝ)
  swap
  · have f9 : ((-2 : ℝ) * (h 0)) + ((-5 : ℝ) * (h 5)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p9
      linarith only [hp]
    exact upper_node_4087 h delta _ctx _hno a29 f9
  apply _hno 152
  change (((5 : ℝ) * (h 1)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ)) ∧ (((5 : ℝ) * (h 2)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ)) ∧ (((5 : ℝ) * (h 3)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ)) ∧ (((5 : ℝ) * (h 4)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ)) ∧ (((5 : ℝ) * (h 5)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ)) ∧ (((2 : ℝ) * (h 0)) + ((5 : ℝ) * (h 1)) ≤ (1 : ℝ)) ∧ (((2 : ℝ) * (h 0)) + ((5 : ℝ) * (h 2)) ≤ (1 : ℝ)) ∧ (((2 : ℝ) * (h 0)) + ((5 : ℝ) * (h 3)) ≤ (1 : ℝ)) ∧ (((2 : ℝ) * (h 0)) + ((5 : ℝ) * (h 4)) ≤ (1 : ℝ)) ∧ (((2 : ℝ) * (h 0)) + ((5 : ℝ) * (h 5)) ≤ (1 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9⟩

theorem upper_node_4068 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a36 : ((-2 : ℝ) * (delta)) < (-3/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a32 + (1 : ℝ) * a36
  exact (lt_irrefl (0 : ℝ)) hbad

end RealPinwheel.WeakSevenBandData
