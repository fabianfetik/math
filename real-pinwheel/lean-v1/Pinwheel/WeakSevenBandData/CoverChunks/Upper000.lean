import Pinwheel.WeakSevenBandData.UpperInputs

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem upper_node_4307 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((3 : ℝ) * (h 2)) + ((6 : ℝ) * (h 4)) ≤ (1 : ℝ))
    (a24 : ((-6 : ℝ) * (h 4)) + ((-3 : ℝ) * (h 5)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3 : ℝ) * _ctx.order2 + (3 : ℝ) * _ctx.order3 + (3 : ℝ) * _ctx.order4 + (1 : ℝ) * a23 + (1 : ℝ) * a24
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4306 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((3 : ℝ) * (h 2)) + ((6 : ℝ) * (h 3)) ≤ (1 : ℝ))
    (a23 : ((-3 : ℝ) * (h 2)) + ((-6 : ℝ) * (h 4)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6 : ℝ) * _ctx.order3 + (1 : ℝ) * a20 + (1 : ℝ) * a23
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4305 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (h 3)) ≤ (1 : ℝ))
    (a22 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 4)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6 : ℝ) * _ctx.order3 + (1 : ℝ) * a19 + (1 : ℝ) * a22
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4304 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((3 : ℝ) * (h 2)) + ((6 : ℝ) * (h 3)) ≤ (1 : ℝ))
    (a21 : ((-6 : ℝ) * (h 3)) + ((-3 : ℝ) * (h 5)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3 : ℝ) * _ctx.order2 + (3 : ℝ) * _ctx.order3 + (3 : ℝ) * _ctx.order4 + (1 : ℝ) * a20 + (1 : ℝ) * a21
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4303 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (h 3)) ≤ (1 : ℝ))
    (a20 : ((-3 : ℝ) * (h 2)) + ((-6 : ℝ) * (h 3)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3 : ℝ) * _ctx.order1 + (1 : ℝ) * a19 + (1 : ℝ) * a20
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4302 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((3 : ℝ) * (h 2)) + ((6 : ℝ) * (h 4)) ≤ (1 : ℝ))
    (a31 : ((-3 : ℝ) * (h 3)) + ((-6 : ℝ) * (h 5)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3 : ℝ) * _ctx.order2 + (6 : ℝ) * _ctx.order4 + (1 : ℝ) * a27 + (1 : ℝ) * a31
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4301 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((3 : ℝ) * (h 2)) + ((6 : ℝ) * (h 4)) ≤ (1 : ℝ))
    (a30 : ((-3 : ℝ) * (h 2)) + ((-6 : ℝ) * (h 5)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6 : ℝ) * _ctx.order4 + (1 : ℝ) * a27 + (1 : ℝ) * a30
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4300 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a26 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (h 4)) ≤ (1 : ℝ))
    (a29 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 5)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6 : ℝ) * _ctx.order4 + (1 : ℝ) * a26 + (1 : ℝ) * a29
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4299 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((3 : ℝ) * (h 2)) + ((6 : ℝ) * (h 4)) ≤ (1 : ℝ))
    (a28 : ((-3 : ℝ) * (h 3)) + ((-6 : ℝ) * (h 4)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3 : ℝ) * _ctx.order2 + (1 : ℝ) * a27 + (1 : ℝ) * a28
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4298 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a26 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (h 4)) ≤ (1 : ℝ))
    (a27 : ((-3 : ℝ) * (h 2)) + ((-6 : ℝ) * (h 4)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3 : ℝ) * _ctx.order1 + (1 : ℝ) * a26 + (1 : ℝ) * a27
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4297 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a29 : -(h 1) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.lower + (1/3 : ℝ) * a13 + (1 : ℝ) * a29
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4296 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a35 : h 0 ≤ (1/6 : ℝ))
    (a48 : ((-2 : ℝ) * (h 0)) + ((-5 : ℝ) * (h 5)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * _ctx.order1 + (2 : ℝ) * _ctx.order2 + (3 : ℝ) * _ctx.order3 + (4 : ℝ) * _ctx.order4 + (1 : ℝ) * _ctx.lower + (1 : ℝ) * a35 + (1 : ℝ) * a48 + (1 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4295 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a35 : h 0 ≤ (1/6 : ℝ))
    (a47 : ((-2 : ℝ) * (h 0)) + ((-5 : ℝ) * (h 4)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (5/4 : ℝ) * _ctx.order1 + (5/2 : ℝ) * _ctx.order2 + (15/4 : ℝ) * _ctx.order3 + (5/4 : ℝ) * _ctx.min + (5/2 : ℝ) * _ctx.lower + (3/4 : ℝ) * a35 + (1 : ℝ) * a47 + (5/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4294 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a35 : h 0 ≤ (1/6 : ℝ))
    (a41 : ((5 : ℝ) * (h 3)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a46 : ((-2 : ℝ) * (h 0)) + ((-5 : ℝ) * (h 3)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4 : ℝ) * _ctx.lower + (2 : ℝ) * a35 + (1 : ℝ) * a41 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4293 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a35 : h 0 ≤ (1/6 : ℝ))
    (a40 : ((5 : ℝ) * (h 2)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a45 : ((-2 : ℝ) * (h 0)) + ((-5 : ℝ) * (h 2)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4 : ℝ) * _ctx.lower + (2 : ℝ) * a35 + (1 : ℝ) * a40 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4292 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a35 : h 0 ≤ (1/6 : ℝ))
    (a39 : ((5 : ℝ) * (h 1)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a44 : ((-2 : ℝ) * (h 0)) + ((-5 : ℝ) * (h 1)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4 : ℝ) * _ctx.lower + (2 : ℝ) * a35 + (1 : ℝ) * a39 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4291 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a28 : -(h 0) < (-4/25 : ℝ))
    (a43 : ((-5 : ℝ) * (h 5)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/2 : ℝ) * _ctx.order1 + (1 : ℝ) * _ctx.order2 + (3/2 : ℝ) * _ctx.order3 + (2 : ℝ) * _ctx.order4 + (3/4 : ℝ) * a27 + (1/2 : ℝ) * a28 + (1/2 : ℝ) * a43 + (1/2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4290 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a41 : ((5 : ℝ) * (h 3)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a42 : ((-5 : ℝ) * (h 4)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (5 : ℝ) * _ctx.order3 + (1 : ℝ) * a41 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4289 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a40 : ((5 : ℝ) * (h 2)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a41 : ((-5 : ℝ) * (h 3)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (5 : ℝ) * _ctx.order2 + (1 : ℝ) * a40 + (1 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4288 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a39 : ((5 : ℝ) * (h 1)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a40 : ((-5 : ℝ) * (h 2)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (5 : ℝ) * _ctx.order1 + (1 : ℝ) * a39 + (1 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4287 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a28 : -(h 0) < (-4/25 : ℝ))
    (a38 : -(h 4) < (-1/9 : ℝ))
    (a46 : -(h 3) < (-4/35 : ℝ))
    (a51 : -(h 5) < (-1/9 : ℝ))
    (a54 : -(h 1) < (-5/42 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order2 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a28 + (1/6 : ℝ) * a38 + (1/3 : ℝ) * a46 + (1/6 : ℝ) * a51 + (1/6 : ℝ) * a54 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4286 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a38 : -(h 4) < (-1/9 : ℝ))
    (a42 : -(h 1) < (-2/17 : ℝ))
    (a46 : -(h 3) < (-4/35 : ℝ))
    (a51 : -(h 5) < (-1/9 : ℝ))
    (a53 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order2 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a38 + (1/6 : ℝ) * a42 + (1/3 : ℝ) * a46 + (1/6 : ℝ) * a51 + (1/6 : ℝ) * a53 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4285 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a52 : ((-2 : ℝ) * (delta)) < (-3/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a52
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4284 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a28 : -(h 0) < (-4/25 : ℝ))
    (a38 : -(h 4) < (-1/9 : ℝ))
    (a42 : -(h 1) < (-2/17 : ℝ))
    (a46 : -(h 3) < (-4/35 : ℝ))
    (a51 : -(h 5) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/13 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4285 h delta _ctx _hno a27 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4286 h delta _ctx _hno a38 a42 a46 a51 f1
  by_cases p2 : h 1 ≤ (5/42 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/42 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4287 h delta _ctx _hno a28 a38 a46 a51 f2
  apply _hno 34
  change (((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (5/42 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem upper_node_4283 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a28 : -(h 0) < (-4/25 : ℝ))
    (a58 : -(h 4) < (-8/67 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order1 + (2/5 : ℝ) * _ctx.order2 + (3/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a28 + (4/5 : ℝ) * a58 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4282 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a28 : -(h 0) < (-4/25 : ℝ))
    (a50 : -(h 4) < (-5/44 : ℝ))
    (a57 : -(h 3) < (-11/92 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order1 + (2/5 : ℝ) * _ctx.order2 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a28 + (1/5 : ℝ) * a50 + (3/5 : ℝ) * a57 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4281 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a28 : -(h 0) < (-4/25 : ℝ))
    (a46 : -(h 3) < (-4/35 : ℝ))
    (a50 : -(h 4) < (-5/44 : ℝ))
    (a56 : -(h 1) < (-3/25 : ℝ))
    (a62 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order2 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a28 + (1/3 : ℝ) * a46 + (1/6 : ℝ) * a50 + (1/6 : ℝ) * a56 + (1/6 : ℝ) * a62 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4280 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a28 : -(h 0) < (-4/25 : ℝ))
    (a50 : -(h 4) < (-5/44 : ℝ))
    (a56 : -(h 1) < (-3/25 : ℝ))
    (a61 : -(h 3) < (-3/26 : ℝ))
    (a66 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order2 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a28 + (1/6 : ℝ) * a50 + (1/6 : ℝ) * a56 + (1/3 : ℝ) * a61 + (1/6 : ℝ) * a66 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4279 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a28 : -(h 0) < (-4/25 : ℝ))
    (a50 : -(h 4) < (-5/44 : ℝ))
    (a56 : -(h 1) < (-3/25 : ℝ))
    (a61 : -(h 3) < (-3/26 : ℝ))
    (a65 : -(h 2) < (-7/60 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a28 + (1/5 : ℝ) * a50 + (1/5 : ℝ) * a56 + (1/5 : ℝ) * a61 + (1/5 : ℝ) * a65 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4278 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a28 : -(h 0) < (-4/25 : ℝ))
    (a50 : -(h 4) < (-5/44 : ℝ))
    (a61 : -(h 3) < (-3/26 : ℝ))
    (a64 : -(h 1) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order2 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a28 + (1/5 : ℝ) * a50 + (2/5 : ℝ) * a61 + (1/5 : ℝ) * a64 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4277 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a50 : -(h 4) < (-5/44 : ℝ))
    (a56 : -(h 1) < (-3/25 : ℝ))
    (a61 : -(h 3) < (-3/26 : ℝ))
    (a63 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order2 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a50 + (1/5 : ℝ) * a56 + (2/5 : ℝ) * a61 + (1/5 : ℝ) * a63 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4276 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a62 : ((-2 : ℝ) * (delta)) < (-3/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a62
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4275 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a28 : -(h 0) < (-4/25 : ℝ))
    (a50 : -(h 4) < (-5/44 : ℝ))
    (a56 : -(h 1) < (-3/25 : ℝ))
    (a61 : -(h 3) < (-3/26 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/13 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4276 h delta _ctx _hno a27 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4277 h delta _ctx _hno a50 a56 a61 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4278 h delta _ctx _hno a28 a50 a61 f2
  by_cases p3 : h 2 ≤ (7/60 : ℝ)
  swap
  · have f3 : -(h 2) < (-7/60 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_4279 h delta _ctx _hno a28 a50 a56 a61 f3
  by_cases p4 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_4280 h delta _ctx _hno a28 a50 a56 a61 f4
  apply _hno 47
  change (((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 2 ≤ (7/60 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_4274 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a28 : -(h 0) < (-4/25 : ℝ))
    (a46 : -(h 3) < (-4/35 : ℝ))
    (a50 : -(h 4) < (-5/44 : ℝ))
    (a56 : -(h 1) < (-3/25 : ℝ))
    (a60 : -(h 2) < (-7/60 : ℝ))
    (a67 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a28 + (1/6 : ℝ) * a46 + (1/6 : ℝ) * a50 + (1/6 : ℝ) * a56 + (1/6 : ℝ) * a60 + (1/6 : ℝ) * a67 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4273 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a28 : -(h 0) < (-4/25 : ℝ))
    (a46 : -(h 3) < (-4/35 : ℝ))
    (a56 : -(h 1) < (-3/25 : ℝ))
    (a60 : -(h 2) < (-7/60 : ℝ))
    (a66 : -(h 4) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a28 + (1/5 : ℝ) * a46 + (1/5 : ℝ) * a56 + (1/5 : ℝ) * a60 + (1/5 : ℝ) * a66 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4272 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a28 : -(h 0) < (-4/25 : ℝ))
    (a50 : -(h 4) < (-5/44 : ℝ))
    (a56 : -(h 1) < (-3/25 : ℝ))
    (a60 : -(h 2) < (-7/60 : ℝ))
    (a65 : -(h 3) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a28 + (1/5 : ℝ) * a50 + (1/5 : ℝ) * a56 + (1/5 : ℝ) * a60 + (1/5 : ℝ) * a65 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4271 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a28 : -(h 0) < (-4/25 : ℝ))
    (a46 : -(h 3) < (-4/35 : ℝ))
    (a50 : -(h 4) < (-5/44 : ℝ))
    (a56 : -(h 1) < (-3/25 : ℝ))
    (a64 : -(h 2) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a28 + (1/5 : ℝ) * a46 + (1/5 : ℝ) * a50 + (1/5 : ℝ) * a56 + (1/5 : ℝ) * a64 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4270 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a45 : h 1 ≤ (1/8 : ℝ))
    (a63 : -(h 1) < (-4/31 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a45 + (1 : ℝ) * a63
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4269 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a35 : h 0 ≤ (1/6 : ℝ))
    (a62 : -(h 0) < (-4/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a35 + (1 : ℝ) * a62
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4268 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a28 : -(h 0) < (-4/25 : ℝ))
    (a46 : -(h 3) < (-4/35 : ℝ))
    (a50 : -(h 4) < (-5/44 : ℝ))
    (a56 : -(h 1) < (-3/25 : ℝ))
    (a60 : -(h 2) < (-7/60 : ℝ))
    (a61 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a28 + (1/6 : ℝ) * a46 + (1/6 : ℝ) * a50 + (1/6 : ℝ) * a56 + (1/6 : ℝ) * a60 + (1/6 : ℝ) * a61 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4267 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a28 : -(h 0) < (-4/25 : ℝ))
    (a35 : h 0 ≤ (1/6 : ℝ))
    (a45 : h 1 ≤ (1/8 : ℝ))
    (a46 : -(h 3) < (-4/35 : ℝ))
    (a50 : -(h 4) < (-5/44 : ℝ))
    (a56 : -(h 1) < (-3/25 : ℝ))
    (a60 : -(h 2) < (-7/60 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4268 h delta _ctx _hno a28 a46 a50 a56 a60 f0
  by_cases p1 : h 0 ≤ (4/23 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/23 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4269 h delta _ctx _hno a35 f1
  by_cases p2 : h 1 ≤ (4/31 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/31 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4270 h delta _ctx _hno a45 f2
  by_cases p3 : h 2 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_4271 h delta _ctx _hno a28 a46 a50 a56 f3
  by_cases p4 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_4272 h delta _ctx _hno a28 a50 a56 a60 f4
  by_cases p5 : h 4 ≤ (4/35 : ℝ)
  swap
  · have f5 : -(h 4) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_4273 h delta _ctx _hno a28 a46 a56 a60 f5
  by_cases p6 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f6 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact upper_node_4274 h delta _ctx _hno a28 a46 a50 a56 a60 f6
  apply _hno 80
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (4/23 : ℝ)) ∧ (h 1 ≤ (4/31 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 4 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem upper_node_4266 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a45 : h 1 ≤ (1/8 : ℝ))
    (a59 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a45 + (1 : ℝ) * a59
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4265 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a46 : -(h 3) < (-4/35 : ℝ))
    (a50 : -(h 4) < (-5/44 : ℝ))
    (a56 : -(h 1) < (-3/25 : ℝ))
    (a58 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order2 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (2/5 : ℝ) * a46 + (1/5 : ℝ) * a50 + (1/5 : ℝ) * a56 + (1/5 : ℝ) * a58 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4264 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a57 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a57
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4263 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a28 : -(h 0) < (-4/25 : ℝ))
    (a35 : h 0 ≤ (1/6 : ℝ))
    (a45 : h 1 ≤ (1/8 : ℝ))
    (a46 : -(h 3) < (-4/35 : ℝ))
    (a50 : -(h 4) < (-5/44 : ℝ))
    (a56 : -(h 1) < (-3/25 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4264 h delta _ctx _hno a27 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4265 h delta _ctx _hno a46 a50 a56 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4266 h delta _ctx _hno a45 f2
  by_cases p3 : h 2 ≤ (7/60 : ℝ)
  swap
  · have f3 : -(h 2) < (-7/60 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_4267 h delta _ctx _hno a28 a35 a45 a46 a50 a56 f3
  by_cases p4 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_4275 h delta _ctx _hno a27 a28 a50 a56 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_4281 h delta _ctx _hno a28 a46 a50 a56 f5
  apply _hno 54
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (7/60 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_4262 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a46 : -(h 3) < (-4/35 : ℝ))
    (a50 : -(h 4) < (-5/44 : ℝ))
    (a53 : -(h 1) < (-5/42 : ℝ))
    (a55 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order2 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (2/5 : ℝ) * a46 + (1/5 : ℝ) * a50 + (1/5 : ℝ) * a53 + (1/5 : ℝ) * a55 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4261 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a54 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a54
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4260 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a28 : -(h 0) < (-4/25 : ℝ))
    (a35 : h 0 ≤ (1/6 : ℝ))
    (a45 : h 1 ≤ (1/8 : ℝ))
    (a46 : -(h 3) < (-4/35 : ℝ))
    (a50 : -(h 4) < (-5/44 : ℝ))
    (a53 : -(h 1) < (-5/42 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4261 h delta _ctx _hno a27 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4262 h delta _ctx _hno a46 a50 a53 f1
  by_cases p2 : h 1 ≤ (3/25 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4263 h delta _ctx _hno a27 a28 a35 a45 a46 a50 f2
  by_cases p3 : h 3 ≤ (11/92 : ℝ)
  swap
  · have f3 : -(h 3) < (-11/92 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_4282 h delta _ctx _hno a28 a50 f3
  by_cases p4 : h 4 ≤ (8/67 : ℝ)
  swap
  · have f4 : -(h 4) < (-8/67 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_4283 h delta _ctx _hno a28 f4
  apply _hno 60
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (11/92 : ℝ)) ∧ (h 4 ≤ (8/67 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_4259 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a42 : -(h 1) < (-2/17 : ℝ))
    (a46 : -(h 3) < (-4/35 : ℝ))
    (a50 : -(h 4) < (-5/44 : ℝ))
    (a52 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order2 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a42 + (2/5 : ℝ) * a46 + (1/5 : ℝ) * a50 + (1/5 : ℝ) * a52 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4258 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a51 : ((-2 : ℝ) * (delta)) < (-3/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a51
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4257 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a28 : -(h 0) < (-4/25 : ℝ))
    (a35 : h 0 ≤ (1/6 : ℝ))
    (a42 : -(h 1) < (-2/17 : ℝ))
    (a45 : h 1 ≤ (1/8 : ℝ))
    (a46 : -(h 3) < (-4/35 : ℝ))
    (a50 : -(h 4) < (-5/44 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/13 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4258 h delta _ctx _hno a27 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4259 h delta _ctx _hno a42 a46 a50 f1
  by_cases p2 : h 1 ≤ (5/42 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/42 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4260 h delta _ctx _hno a27 a28 a35 a45 a46 a50 f2
  apply _hno 34
  change (((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (5/42 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem upper_node_4256 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a45 : h 1 ≤ (1/8 : ℝ))
    (a49 : -(h 1) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a45 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4255 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a35 : h 0 ≤ (1/6 : ℝ))
    (a48 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a35 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4254 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a47 : ((-2 : ℝ) * (delta)) < (-5/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4253 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a28 : -(h 0) < (-4/25 : ℝ))
    (a35 : h 0 ≤ (1/6 : ℝ))
    (a38 : -(h 4) < (-1/9 : ℝ))
    (a42 : -(h 1) < (-2/17 : ℝ))
    (a45 : h 1 ≤ (1/8 : ℝ))
    (a46 : -(h 3) < (-4/35 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/22 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/22 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4254 h delta _ctx _hno a27 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4255 h delta _ctx _hno a35 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4256 h delta _ctx _hno a45 f2
  by_cases p3 : h 4 ≤ (5/44 : ℝ)
  swap
  · have f3 : -(h 4) < (-5/44 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_4257 h delta _ctx _hno a27 a28 a35 a42 a45 a46 f3
  by_cases p4 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_4284 h delta _ctx _hno a27 a28 a38 a42 a46 f4
  apply _hno 58
  change (((2 : ℝ) * (delta)) ≤ (5/22 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (5/44 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_4252 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a45 : -(h 1) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.lower + (1/3 : ℝ) * a13 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4251 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a35 : h 0 ≤ (1/6 : ℝ))
    (a44 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a35 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4250 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4249 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a27 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a28 : -(h 0) < (-4/25 : ℝ))
    (a35 : h 0 ≤ (1/6 : ℝ))
    (a38 : -(h 4) < (-1/9 : ℝ))
    (a42 : -(h 1) < (-2/17 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4250 h delta _ctx _hno a27 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4251 h delta _ctx _hno a35 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4252 h delta _ctx _hno a13 f2
  by_cases p3 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f3 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_4253 h delta _ctx _hno a27 a28 a35 a38 a42 p2 f3
  apply _hno 84
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_4248 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a35 : h 0 ≤ (1/6 : ℝ))
    (a41 : -(h 0) < (-4/21 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a35 + (1 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4247 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a40 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4246 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a27 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a28 : -(h 0) < (-4/25 : ℝ))
    (a35 : h 0 ≤ (1/6 : ℝ))
    (a38 : -(h 4) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4247 h delta _ctx _hno a27 f0
  by_cases p1 : h 0 ≤ (4/21 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/21 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4248 h delta _ctx _hno a35 f1
  by_cases p2 : h 1 ≤ (2/17 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4249 h delta _ctx _hno a13 a27 a28 a35 a38 f2
  apply _hno 155
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (4/21 : ℝ)) ∧ (h 1 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem upper_node_4245 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a27 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a28 : -(h 0) < (-4/25 : ℝ))
    (a35 : h 0 ≤ (1/6 : ℝ))
    (a38 : -(h 4) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((5 : ℝ) * (h 1)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ)
  swap
  · have f0 : ((-5 : ℝ) * (h 1)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4246 h delta _ctx _hno a13 a27 a28 a35 a38
  by_cases p1 : ((5 : ℝ) * (h 2)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ)
  swap
  · have f1 : ((-5 : ℝ) * (h 2)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4288 h delta _ctx _hno p0 f1
  by_cases p2 : ((5 : ℝ) * (h 3)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ)
  swap
  · have f2 : ((-5 : ℝ) * (h 3)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4289 h delta _ctx _hno p1 f2
  by_cases p3 : ((5 : ℝ) * (h 4)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ)
  swap
  · have f3 : ((-5 : ℝ) * (h 4)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_4290 h delta _ctx _hno p2 f3
  by_cases p4 : ((5 : ℝ) * (h 5)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ)
  swap
  · have f4 : ((-5 : ℝ) * (h 5)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_4291 h delta _ctx _hno a27 a28 f4
  by_cases p5 : ((2 : ℝ) * (h 0)) + ((5 : ℝ) * (h 1)) ≤ (1 : ℝ)
  swap
  · have f5 : ((-2 : ℝ) * (h 0)) + ((-5 : ℝ) * (h 1)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_4292 h delta _ctx _hno a35 p0 f5
  by_cases p6 : ((2 : ℝ) * (h 0)) + ((5 : ℝ) * (h 2)) ≤ (1 : ℝ)
  swap
  · have f6 : ((-2 : ℝ) * (h 0)) + ((-5 : ℝ) * (h 2)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact upper_node_4293 h delta _ctx _hno a35 p1 f6
  by_cases p7 : ((2 : ℝ) * (h 0)) + ((5 : ℝ) * (h 3)) ≤ (1 : ℝ)
  swap
  · have f7 : ((-2 : ℝ) * (h 0)) + ((-5 : ℝ) * (h 3)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p7
      linarith only [hp]
    exact upper_node_4294 h delta _ctx _hno a35 p2 f7
  by_cases p8 : ((2 : ℝ) * (h 0)) + ((5 : ℝ) * (h 4)) ≤ (1 : ℝ)
  swap
  · have f8 : ((-2 : ℝ) * (h 0)) + ((-5 : ℝ) * (h 4)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p8
      linarith only [hp]
    exact upper_node_4295 h delta _ctx _hno a35 f8
  by_cases p9 : ((2 : ℝ) * (h 0)) + ((5 : ℝ) * (h 5)) ≤ (1 : ℝ)
  swap
  · have f9 : ((-2 : ℝ) * (h 0)) + ((-5 : ℝ) * (h 5)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p9
      linarith only [hp]
    exact upper_node_4296 h delta _ctx _hno a35 f9
  apply _hno 152
  change (((5 : ℝ) * (h 1)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ)) ∧ (((5 : ℝ) * (h 2)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ)) ∧ (((5 : ℝ) * (h 3)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ)) ∧ (((5 : ℝ) * (h 4)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ)) ∧ (((5 : ℝ) * (h 5)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ)) ∧ (((2 : ℝ) * (h 0)) + ((5 : ℝ) * (h 1)) ≤ (1 : ℝ)) ∧ (((2 : ℝ) * (h 0)) + ((5 : ℝ) * (h 2)) ≤ (1 : ℝ)) ∧ (((2 : ℝ) * (h 0)) + ((5 : ℝ) * (h 3)) ≤ (1 : ℝ)) ∧ (((2 : ℝ) * (h 0)) + ((5 : ℝ) * (h 4)) ≤ (1 : ℝ)) ∧ (((2 : ℝ) * (h 0)) + ((5 : ℝ) * (h 5)) ≤ (1 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9⟩

theorem upper_node_4244 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a26 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 4)) < (-1 : ℝ))
    (a28 : -(h 0) < (-4/25 : ℝ))
    (a33 : -(h 3) < (-1/9 : ℝ))
    (a37 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/22 : ℝ) * _ctx.order1 + (3/11 : ℝ) * _ctx.min + (6/11 : ℝ) * _ctx.lower + (1/22 : ℝ) * a26 + (3/11 : ℝ) * a28 + (3/11 : ℝ) * a33 + (9/22 : ℝ) * a37 + (3/11 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4243 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a36 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.lower + (1/3 : ℝ) * a13 + (1 : ℝ) * a36
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4242 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : h 0 ≤ (8/45 : ℝ))
    (a45 : ((-2 : ℝ) * (h 0)) + ((-5 : ℝ) * (h 5)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * _ctx.order1 + (2 : ℝ) * _ctx.order2 + (3 : ℝ) * _ctx.order3 + (4 : ℝ) * _ctx.order4 + (1 : ℝ) * _ctx.lower + (1 : ℝ) * a30 + (1 : ℝ) * a45 + (1 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4241 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : h 0 ≤ (8/45 : ℝ))
    (a44 : ((-2 : ℝ) * (h 0)) + ((-5 : ℝ) * (h 4)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (5/4 : ℝ) * _ctx.order1 + (5/2 : ℝ) * _ctx.order2 + (15/4 : ℝ) * _ctx.order3 + (5/4 : ℝ) * _ctx.min + (5/2 : ℝ) * _ctx.lower + (3/4 : ℝ) * a30 + (1 : ℝ) * a44 + (5/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4240 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : h 0 ≤ (8/45 : ℝ))
    (a43 : ((-2 : ℝ) * (h 0)) + ((-5 : ℝ) * (h 3)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (5/3 : ℝ) * _ctx.order1 + (10/3 : ℝ) * _ctx.order2 + (5/3 : ℝ) * _ctx.order4 + (10/3 : ℝ) * _ctx.min + (5 : ℝ) * _ctx.lower + (1/3 : ℝ) * a30 + (1 : ℝ) * a43 + (5/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4239 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : h 0 ≤ (8/45 : ℝ))
    (a37 : ((5 : ℝ) * (h 2)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a42 : ((-2 : ℝ) * (h 0)) + ((-5 : ℝ) * (h 2)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4 : ℝ) * _ctx.lower + (2 : ℝ) * a30 + (1 : ℝ) * a37 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4238 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : h 0 ≤ (8/45 : ℝ))
    (a36 : ((5 : ℝ) * (h 1)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a41 : ((-2 : ℝ) * (h 0)) + ((-5 : ℝ) * (h 1)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4 : ℝ) * _ctx.lower + (2 : ℝ) * a30 + (1 : ℝ) * a36 + (1 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4237 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a35 : -(h 0) < (-1/6 : ℝ))
    (a40 : ((-5 : ℝ) * (h 5)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/2 : ℝ) * _ctx.order1 + (1 : ℝ) * _ctx.order2 + (3/2 : ℝ) * _ctx.order3 + (2 : ℝ) * _ctx.order4 + (3/4 : ℝ) * a27 + (1/2 : ℝ) * a35 + (1/2 : ℝ) * a40 + (1/2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4236 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a35 : -(h 0) < (-1/6 : ℝ))
    (a39 : ((-5 : ℝ) * (h 4)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (5/9 : ℝ) * _ctx.order1 + (10/9 : ℝ) * _ctx.order2 + (5/3 : ℝ) * _ctx.order3 + (5/9 : ℝ) * _ctx.min + (1/3 : ℝ) * a27 + (5/9 : ℝ) * a35 + (4/9 : ℝ) * a39 + (5/9 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4235 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a26 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 4)) < (-1 : ℝ))
    (a35 : -(h 0) < (-1/6 : ℝ))
    (a38 : ((-5 : ℝ) * (h 3)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/10 : ℝ) * _ctx.order1 + (9/10 : ℝ) * _ctx.order2 + (3/5 : ℝ) * _ctx.min + (1/10 : ℝ) * a26 + (3/5 : ℝ) * a35 + (3/10 : ℝ) * a38 + (3/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4234 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a36 : ((5 : ℝ) * (h 1)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a37 : ((-5 : ℝ) * (h 2)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (5 : ℝ) * _ctx.order1 + (1 : ℝ) * a36 + (1 : ℝ) * a37
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4233 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a35 : -(h 0) < (-1/6 : ℝ))
    (a36 : ((-5 : ℝ) * (h 1)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ))
    (a49 : -(h 5) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (5/26 : ℝ) * _ctx.order2 + (5/13 : ℝ) * _ctx.order3 + (15/26 : ℝ) * _ctx.order4 + (1/26 : ℝ) * _ctx.lower + (5/26 : ℝ) * a35 + (1/26 : ℝ) * a36 + (10/13 : ℝ) * a49 + (5/26 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4232 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : -(h 3) < (-1/9 : ℝ))
    (a35 : -(h 0) < (-1/6 : ℝ))
    (a41 : -(h 5) < (-1/9 : ℝ))
    (a44 : -(h 1) < (-2/17 : ℝ))
    (a48 : -(h 2) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order4 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a35 + (1/3 : ℝ) * a41 + (1/6 : ℝ) * a44 + (1/6 : ℝ) * a48 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4231 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : -(h 3) < (-1/9 : ℝ))
    (a35 : -(h 0) < (-1/6 : ℝ))
    (a41 : -(h 5) < (-1/9 : ℝ))
    (a47 : -(h 1) < (-5/42 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.order4 + (6/29 : ℝ) * _ctx.lower + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a33 + (4/29 : ℝ) * a35 + (12/29 : ℝ) * a41 + (6/29 : ℝ) * a47 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4230 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : -(h 3) < (-1/9 : ℝ))
    (a41 : -(h 5) < (-1/9 : ℝ))
    (a44 : -(h 1) < (-2/17 : ℝ))
    (a46 : -(h 0) < (-5/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order2 + (1/6 : ℝ) * _ctx.order4 + (1/6 : ℝ) * _ctx.lower + (1/3 : ℝ) * a33 + (1/3 : ℝ) * a41 + (1/6 : ℝ) * a44 + (1/6 : ℝ) * a46 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4229 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a45 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4228 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a33 : -(h 3) < (-1/9 : ℝ))
    (a35 : -(h 0) < (-1/6 : ℝ))
    (a36 : ((-5 : ℝ) * (h 1)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ))
    (a41 : -(h 5) < (-1/9 : ℝ))
    (a44 : -(h 1) < (-2/17 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4229 h delta _ctx _hno a27 f0
  by_cases p1 : h 0 ≤ (5/29 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/29 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4230 h delta _ctx _hno a33 a41 a44 f1
  by_cases p2 : h 1 ≤ (5/42 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/42 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4231 h delta _ctx _hno a33 a35 a41 f2
  by_cases p3 : h 2 ≤ (3/26 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_4232 h delta _ctx _hno a33 a35 a41 a44 f3
  by_cases p4 : h 5 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 5) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_4233 h delta _ctx _hno a35 a36 f4
  apply _hno 156
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (5/29 : ℝ)) ∧ (h 1 ≤ (5/42 : ℝ)) ∧ (h 2 ≤ (3/26 : ℝ)) ∧ (h 5 ≤ (4/35 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

end RealPinwheel.WeakSevenBandData
