import Pinwheel.WeakSevenBandData.CoverChunks.Upper049

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem upper_node_307 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : -(h 0) < (-8/45 : ℝ))
    (a31 : -(h 2) < (-5/44 : ℝ))
    (a34 : -(h 1) < (-11/87 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order3 + (2/3 : ℝ) * _ctx.order4 + (1 : ℝ) * _ctx.min + (4/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * a20 + (1/3 : ℝ) * a31 + (1/3 : ℝ) * a34 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_306 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a31 : -(h 2) < (-5/44 : ℝ))
    (a33 : -(h 0) < (-2/11 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/7 : ℝ) * _ctx.order3 + (6/7 : ℝ) * _ctx.order4 + (9/7 : ℝ) * _ctx.min + (6/7 : ℝ) * _ctx.lower + (1/7 : ℝ) * a13 + (3/7 : ℝ) * a31 + (3/7 : ℝ) * a33 + (3/7 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_305 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a20 : -(h 0) < (-8/45 : ℝ))
    (a31 : -(h 2) < (-5/44 : ℝ))
    (a32 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/10 : ℝ) * _ctx.order3 + (3/5 : ℝ) * _ctx.order4 + (9/10 : ℝ) * _ctx.min + (1/10 : ℝ) * a13 + (3/10 : ℝ) * a20 + (3/10 : ℝ) * a31 + (3/10 : ℝ) * a32 + (3/10 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_304 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a20 : -(h 0) < (-8/45 : ℝ))
    (a31 : -(h 2) < (-5/44 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_305 h delta _ctx _hno a13 a20 a31 f0
  by_cases p1 : h 0 ≤ (2/11 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/11 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_306 h delta _ctx _hno a13 a31 f1
  by_cases p2 : h 1 ≤ (11/87 : ℝ)
  swap
  · have f2 : -(h 1) < (-11/87 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_307 h delta _ctx _hno a20 a31 f2
  by_cases p3 : h 2 ≤ (3/26 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_308 h delta _ctx _hno a13 a20 f3
  by_cases p4 : h 3 ≤ (2/19 : ℝ)
  swap
  · have f4 : -(h 3) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_309 h delta _ctx _hno a13 a20 a31 f4
  apply _hno 65
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (2/11 : ℝ)) ∧ (h 1 ≤ (11/87 : ℝ)) ∧ (h 2 ≤ (3/26 : ℝ)) ∧ (h 3 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_303 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : -(h 0) < (-8/45 : ℝ))
    (a27 : -(h 2) < (-1/9 : ℝ))
    (a30 : -(h 1) < (-6/47 : ℝ))
    (a35 : -(h 3) < (-6/55 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.order4 + (1/2 : ℝ) * _ctx.min + (3/4 : ℝ) * _ctx.lower + (1/4 : ℝ) * a20 + (1/4 : ℝ) * a27 + (1/4 : ℝ) * a30 + (1/4 : ℝ) * a35 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_302 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : -(h 0) < (-8/45 : ℝ))
    (a30 : -(h 1) < (-6/47 : ℝ))
    (a34 : -(h 2) < (-6/53 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order3 + (2/3 : ℝ) * _ctx.order4 + (1 : ℝ) * _ctx.min + (4/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * a20 + (1/3 : ℝ) * a30 + (1/3 : ℝ) * a34 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_301 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : -(h 0) < (-8/45 : ℝ))
    (a27 : -(h 2) < (-1/9 : ℝ))
    (a33 : -(h 1) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order3 + (2/3 : ℝ) * _ctx.order4 + (1 : ℝ) * _ctx.min + (4/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * a20 + (1/3 : ℝ) * a27 + (1/3 : ℝ) * a33 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_300 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : h 0 ≤ (2/11 : ℝ))
    (a32 : -(h 0) < (-7/36 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a32
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_299 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : -(h 0) < (-8/45 : ℝ))
    (a27 : -(h 2) < (-1/9 : ℝ))
    (a30 : -(h 1) < (-6/47 : ℝ))
    (a31 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (2/5 : ℝ) * _ctx.order4 + (3/5 : ℝ) * _ctx.min + (1/5 : ℝ) * a20 + (1/5 : ℝ) * a27 + (1/5 : ℝ) * a30 + (2/5 : ℝ) * a31 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_298 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : -(h 0) < (-8/45 : ℝ))
    (a27 : -(h 2) < (-1/9 : ℝ))
    (a29 : h 0 ≤ (2/11 : ℝ))
    (a30 : -(h 1) < (-6/47 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_299 h delta _ctx _hno a20 a27 a30 f0
  by_cases p1 : h 0 ≤ (7/36 : ℝ)
  swap
  · have f1 : -(h 0) < (-7/36 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_300 h delta _ctx _hno a29 f1
  by_cases p2 : h 1 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_301 h delta _ctx _hno a20 a27 f2
  by_cases p3 : h 2 ≤ (6/53 : ℝ)
  swap
  · have f3 : -(h 2) < (-6/53 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_302 h delta _ctx _hno a20 a30 f3
  by_cases p4 : h 3 ≤ (6/55 : ℝ)
  swap
  · have f4 : -(h 3) < (-6/55 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_303 h delta _ctx _hno a20 a27 a30 f4
  apply _hno 64
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (7/36 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 2 ≤ (6/53 : ℝ)) ∧ (h 3 ≤ (6/55 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_297 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a27 : -(h 2) < (-1/9 : ℝ))
    (a29 : -(h 0) < (-2/11 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/7 : ℝ) * _ctx.order3 + (6/7 : ℝ) * _ctx.order4 + (9/7 : ℝ) * _ctx.min + (6/7 : ℝ) * _ctx.lower + (1/7 : ℝ) * a13 + (3/7 : ℝ) * a27 + (3/7 : ℝ) * a29 + (3/7 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_296 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a19 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a20 : -(h 0) < (-8/45 : ℝ))
    (a23 : -(h 1) + ((-8 : ℝ) * (h 2)) < (-1 : ℝ))
    (a34 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (12/53 : ℝ) * _ctx.order3 + (24/53 : ℝ) * _ctx.order4 + (7/106 : ℝ) * a13 + (9/106 : ℝ) * a19 + (12/53 : ℝ) * a20 + (3/106 : ℝ) * a23 + (36/53 : ℝ) * a34 + (12/53 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_295 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a20 : -(h 0) < (-8/45 : ℝ))
    (a33 : -(h 4) < (-5/44 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/13 : ℝ) * _ctx.order2 + (6/13 : ℝ) * _ctx.order3 + (3/13 : ℝ) * _ctx.min + (1/13 : ℝ) * a13 + (3/13 : ℝ) * a20 + (9/13 : ℝ) * a33 + (3/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_294 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a20 : -(h 0) < (-8/45 : ℝ))
    (a28 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a32 : -(h 2) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/10 : ℝ) * _ctx.order3 + (3/5 : ℝ) * _ctx.order4 + (9/10 : ℝ) * _ctx.min + (1/10 : ℝ) * a13 + (3/10 : ℝ) * a20 + (3/10 : ℝ) * a28 + (3/10 : ℝ) * a32 + (3/10 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_293 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : -(h 0) < (-8/45 : ℝ))
    (a27 : -(h 2) < (-1/9 : ℝ))
    (a28 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a31 : -(h 1) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (2/5 : ℝ) * _ctx.order4 + (3/5 : ℝ) * _ctx.min + (1/5 : ℝ) * a20 + (1/5 : ℝ) * a27 + (2/5 : ℝ) * a28 + (1/5 : ℝ) * a31 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_292 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a27 : -(h 2) < (-1/9 : ℝ))
    (a28 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a30 : -(h 0) < (-2/11 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/10 : ℝ) * _ctx.order3 + (3/5 : ℝ) * _ctx.order4 + (9/10 : ℝ) * _ctx.min + (1/10 : ℝ) * a13 + (3/10 : ℝ) * a27 + (3/10 : ℝ) * a28 + (3/10 : ℝ) * a30 + (3/10 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_291 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a29 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a19 + (1 : ℝ) * a29
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_290 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a19 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a20 : -(h 0) < (-8/45 : ℝ))
    (a23 : -(h 1) + ((-8 : ℝ) * (h 2)) < (-1 : ℝ))
    (a27 : -(h 2) < (-1/9 : ℝ))
    (a28 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_291 h delta _ctx _hno a19 f0
  by_cases p1 : h 0 ≤ (2/11 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/11 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_292 h delta _ctx _hno a13 a27 a28 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_293 h delta _ctx _hno a20 a27 a28 f2
  by_cases p3 : h 2 ≤ (4/35 : ℝ)
  swap
  · have f3 : -(h 2) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_294 h delta _ctx _hno a13 a20 a28 f3
  by_cases p4 : h 4 ≤ (5/44 : ℝ)
  swap
  · have f4 : -(h 4) < (-5/44 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_295 h delta _ctx _hno a13 a20 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_296 h delta _ctx _hno a13 a19 a20 a23 f5
  apply _hno 63
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (2/11 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 2 ≤ (4/35 : ℝ)) ∧ (h 4 ≤ (5/44 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_289 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a19 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a20 : -(h 0) < (-8/45 : ℝ))
    (a23 : -(h 1) + ((-8 : ℝ) * (h 2)) < (-1 : ℝ))
    (a27 : -(h 2) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_290 h delta _ctx _hno a13 a19 a20 a23 a27 f0
  by_cases p1 : h 0 ≤ (2/11 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/11 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_297 h delta _ctx _hno a13 a27 f1
  by_cases p2 : h 1 ≤ (6/47 : ℝ)
  swap
  · have f2 : -(h 1) < (-6/47 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_298 h delta _ctx _hno a20 a27 p1 f2
  by_cases p3 : h 2 ≤ (5/44 : ℝ)
  swap
  · have f3 : -(h 2) < (-5/44 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_304 h delta _ctx _hno a13 a20 f3
  by_cases p4 : h 3 ≤ (3/28 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_310 h delta _ctx _hno a13 a20 a27 f4
  apply _hno 62
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (2/11 : ℝ)) ∧ (h 1 ≤ (6/47 : ℝ)) ∧ (h 2 ≤ (5/44 : ℝ)) ∧ (h 3 ≤ (3/28 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_288 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : -(h 0) < (-8/45 : ℝ))
    (a26 : -(h 1) < (-5/36 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/11 : ℝ) * _ctx.order3 + (12/11 : ℝ) * _ctx.order4 + (18/11 : ℝ) * _ctx.min + (24/11 : ℝ) * _ctx.lower + (1/11 : ℝ) * _ctx.fail1 + (4/11 : ℝ) * a20 + (6/11 : ℝ) * a26 + (6/11 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_287 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a23 : -(h 1) + ((-8 : ℝ) * (h 2)) < (-1 : ℝ))
    (a25 : -(h 0) < (-3/16 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (12/17 : ℝ) * _ctx.order3 + (24/17 : ℝ) * _ctx.order4 + (36/17 : ℝ) * _ctx.min + (27/17 : ℝ) * _ctx.lower + (7/34 : ℝ) * a13 + (3/34 : ℝ) * a23 + (12/17 : ℝ) * a25 + (12/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_286 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a24 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a19 + (1 : ℝ) * a24
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_285 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a19 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a20 : -(h 0) < (-8/45 : ℝ))
    (a23 : -(h 1) + ((-8 : ℝ) * (h 2)) < (-1 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_286 h delta _ctx _hno a19 f0
  by_cases p1 : h 0 ≤ (3/16 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/16 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_287 h delta _ctx _hno a13 a23 f1
  by_cases p2 : h 1 ≤ (5/36 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/36 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_288 h delta _ctx _hno a20 f2
  by_cases p3 : h 2 ≤ (1/9 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_289 h delta _ctx _hno a13 a19 a20 a23 f3
  apply _hno 61
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (3/16 : ℝ)) ∧ (h 1 ≤ (5/36 : ℝ)) ∧ (h 2 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_284 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a22 : ((-4 : ℝ) * (h 0)) + -(h 1) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (9/8 : ℝ) * _ctx.order2 + (9/4 : ℝ) * _ctx.order3 + (27/8 : ℝ) * _ctx.order4 + (9/2 : ℝ) * _ctx.min + (21/8 : ℝ) * _ctx.markR + (1/16 : ℝ) * a13 + (15/16 : ℝ) * a22 + (9/8 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_283 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a20 : -(h 0) < (-8/45 : ℝ))
    (a21 : -(h 1) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/11 : ℝ) * _ctx.order3 + (12/11 : ℝ) * _ctx.order4 + (18/11 : ℝ) * _ctx.min + (1/11 : ℝ) * _ctx.fail1 + (12/11 : ℝ) * a19 + (4/11 : ℝ) * a20 + (6/11 : ℝ) * a21 + (6/11 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_282 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a19 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a20 : -(h 0) < (-8/45 : ℝ))
    : False := by
  by_cases p0 : h 1 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ)
  swap
  · have f0 : -(h 1) + ((-8 : ℝ) * (delta)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_283 h delta _ctx _hno a19 a20 f0
  by_cases p1 : ((4 : ℝ) * (h 0)) + h 1 ≤ (1 : ℝ)
  swap
  · have f1 : ((-4 : ℝ) * (h 0)) + -(h 1) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_284 h delta _ctx _hno a13 f1
  by_cases p2 : h 1 + ((8 : ℝ) * (h 2)) ≤ (1 : ℝ)
  swap
  · have f2 : -(h 1) + ((-8 : ℝ) * (h 2)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_285 h delta _ctx _hno a13 a19 a20 f2
  by_cases p3 : h 1 + ((8 : ℝ) * (h 3)) ≤ (1 : ℝ)
  swap
  · have f3 : -(h 1) + ((-8 : ℝ) * (h 3)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_311 h delta _ctx _hno a13 a20 f3
  by_cases p4 : h 1 + ((8 : ℝ) * (h 4)) ≤ (1 : ℝ)
  swap
  · have f4 : -(h 1) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_312 h delta _ctx _hno a13 a20 f4
  by_cases p5 : h 1 + ((8 : ℝ) * (h 5)) ≤ (1 : ℝ)
  swap
  · have f5 : -(h 1) + ((-8 : ℝ) * (h 5)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_313 h delta _ctx _hno a13 a20 f5
  apply _hno 50
  change (h 1 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ)) ∧ (((4 : ℝ) * (h 0)) + h 1 ≤ (1 : ℝ)) ∧ (h 1 + ((8 : ℝ) * (h 2)) ≤ (1 : ℝ)) ∧ (h 1 + ((8 : ℝ) * (h 3)) ≤ (1 : ℝ)) ∧ (h 1 + ((8 : ℝ) * (h 4)) ≤ (1 : ℝ)) ∧ (h 1 + ((8 : ℝ) * (h 5)) ≤ (1 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_281 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : h 4 ≤ (9/80 : ℝ))
    (a32 : -(h 4) < (-13/112 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a32
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_280 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) < (-2/13 : ℝ))
    (a19 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 5) < (-1/9 : ℝ))
    (a31 : -(h 1) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/16 : ℝ) * _ctx.order4 + (1/32 : ℝ) * _ctx.fail1 + (1/8 : ℝ) * a18 + (3/32 : ℝ) * a19 + (3/16 : ℝ) * a23 + (3/8 : ℝ) * a28 + (3/16 : ℝ) * a31 + (3/16 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_279 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : h 4 ≤ (9/80 : ℝ))
    (a42 : -(h 4) < (-8/67 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_278 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a28 : -(h 5) < (-1/9 : ℝ))
    (a30 : -(h 0) < (-3/19 : ℝ))
    (a41 : -(h 3) < (-11/92 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/34 : ℝ) * _ctx.order1 + (9/34 : ℝ) * _ctx.order2 + (3/17 : ℝ) * _ctx.order4 + (1/34 : ℝ) * a13 + (6/17 : ℝ) * a28 + (3/17 : ℝ) * a30 + (15/34 : ℝ) * a41 + (3/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_277 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 5) < (-1/9 : ℝ))
    (a30 : -(h 0) < (-3/19 : ℝ))
    (a37 : -(h 2) < (-3/26 : ℝ))
    (a40 : -(h 1) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order4 + (1/13 : ℝ) * a19 + (2/13 : ℝ) * a23 + (4/13 : ℝ) * a28 + (2/13 : ℝ) * a30 + (2/13 : ℝ) * a37 + (2/13 : ℝ) * a40 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_276 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 5) < (-1/9 : ℝ))
    (a33 : -(h 1) < (-5/42 : ℝ))
    (a37 : -(h 2) < (-3/26 : ℝ))
    (a39 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/17 : ℝ) * _ctx.order4 + (1/34 : ℝ) * a13 + (3/17 : ℝ) * a23 + (6/17 : ℝ) * a28 + (3/34 : ℝ) * a33 + (3/17 : ℝ) * a37 + (3/17 : ℝ) * a39 + (3/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_275 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a38 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a38
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_274 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a17 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a19 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a27 : h 4 ≤ (9/80 : ℝ))
    (a28 : -(h 5) < (-1/9 : ℝ))
    (a30 : -(h 0) < (-3/19 : ℝ))
    (a33 : -(h 1) < (-5/42 : ℝ))
    (a37 : -(h 2) < (-3/26 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_275 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_276 h delta _ctx _hno a13 a23 a28 a33 a37 f1
  by_cases p2 : h 1 ≤ (3/25 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_277 h delta _ctx _hno a19 a23 a28 a30 a37 f2
  by_cases p3 : h 3 ≤ (11/92 : ℝ)
  swap
  · have f3 : -(h 3) < (-11/92 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_278 h delta _ctx _hno a13 a28 a30 f3
  by_cases p4 : h 4 ≤ (8/67 : ℝ)
  swap
  · have f4 : -(h 4) < (-8/67 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_279 h delta _ctx _hno a27 f4
  apply _hno 60
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (11/92 : ℝ)) ∧ (h 4 ≤ (8/67 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_273 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 5) < (-1/9 : ℝ))
    (a30 : -(h 0) < (-3/19 : ℝ))
    (a36 : -(h 1) < (-4/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/16 : ℝ) * _ctx.order4 + (1/32 : ℝ) * _ctx.fail1 + (3/32 : ℝ) * a19 + (3/16 : ℝ) * a23 + (3/8 : ℝ) * a28 + (1/8 : ℝ) * a30 + (3/16 : ℝ) * a36 + (3/16 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_272 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 5) < (-1/9 : ℝ))
    (a33 : -(h 1) < (-5/42 : ℝ))
    (a35 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/9 : ℝ) * _ctx.order4 + (1/27 : ℝ) * _ctx.fail1 + (1/27 : ℝ) * a13 + (2/9 : ℝ) * a23 + (4/9 : ℝ) * a28 + (1/9 : ℝ) * a33 + (4/27 : ℝ) * a35 + (2/9 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_271 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-3/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a34
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_270 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a17 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a19 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a27 : h 4 ≤ (9/80 : ℝ))
    (a28 : -(h 5) < (-1/9 : ℝ))
    (a30 : -(h 0) < (-3/19 : ℝ))
    (a33 : -(h 1) < (-5/42 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/13 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_271 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_272 h delta _ctx _hno a13 a23 a28 a33 f1
  by_cases p2 : h 1 ≤ (4/33 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_273 h delta _ctx _hno a19 a23 a28 a30 f2
  by_cases p3 : h 2 ≤ (3/26 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_274 h delta _ctx _hno a13 a17 a19 a23 a27 a28 a30 a33 f3
  apply _hno 59
  change (((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (4/33 : ℝ)) ∧ (h 2 ≤ (3/26 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_269 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a17 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 5) < (-1/9 : ℝ))
    (a32 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/25 : ℝ) * _ctx.order4 + (1/25 : ℝ) * _ctx.fail1 + (2/25 : ℝ) * a13 + (3/25 : ℝ) * a17 + (6/25 : ℝ) * a23 + (12/25 : ℝ) * a28 + (4/25 : ℝ) * a32 + (6/25 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_268 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a31 : ((-2 : ℝ) * (delta)) < (-3/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a31
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_267 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a17 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a19 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a27 : h 4 ≤ (9/80 : ℝ))
    (a28 : -(h 5) < (-1/9 : ℝ))
    (a30 : -(h 0) < (-3/19 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/13 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_268 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_269 h delta _ctx _hno a13 a17 a23 a28 f1
  by_cases p2 : h 1 ≤ (5/42 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/42 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_270 h delta _ctx _hno a13 a17 a19 a23 a27 a28 a30 f2
  apply _hno 34
  change (((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (5/42 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem upper_node_266 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a29 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a29
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_265 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a17 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a18 : -(h 0) < (-2/13 : ℝ))
    (a19 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a27 : h 4 ≤ (9/80 : ℝ))
    (a28 : -(h 5) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_266 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (3/19 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/19 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_267 h delta _ctx _hno a13 a17 a19 a23 a27 a28 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_280 h delta _ctx _hno a18 a19 a23 a28 f2
  by_cases p3 : h 4 ≤ (13/112 : ℝ)
  swap
  · have f3 : -(h 4) < (-13/112 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_281 h delta _ctx _hno a27 f3
  apply _hno 4
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (13/112 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_264 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a18 : -(h 0) < (-2/13 : ℝ))
    (a31 : -(h 4) < (-13/112 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/13 : ℝ) * _ctx.order2 + (6/13 : ℝ) * _ctx.order3 + (3/13 : ℝ) * _ctx.min + (1/13 : ℝ) * a13 + (3/13 : ℝ) * a18 + (9/13 : ℝ) * a31 + (3/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_263 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) < (-2/13 : ℝ))
    (a19 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a27 : -(h 4) < (-9/80 : ℝ))
    (a30 : -(h 1) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.order3 + (6/29 : ℝ) * _ctx.min + (1/29 : ℝ) * _ctx.fail1 + (4/29 : ℝ) * a18 + (6/29 : ℝ) * a19 + (12/29 : ℝ) * a27 + (6/29 : ℝ) * a30 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_262 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a27 : -(h 4) < (-9/80 : ℝ))
    (a29 : -(h 0) < (-3/19 : ℝ))
    (a32 : -(h 1) < (-5/42 : ℝ))
    (a38 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/9 : ℝ) * _ctx.order3 + (1/27 : ℝ) * _ctx.fail1 + (1/27 : ℝ) * a13 + (4/9 : ℝ) * a27 + (4/27 : ℝ) * a29 + (1/9 : ℝ) * a32 + (2/9 : ℝ) * a38 + (2/9 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_261 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a27 : -(h 4) < (-9/80 : ℝ))
    (a29 : -(h 0) < (-3/19 : ℝ))
    (a37 : -(h 3) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/13 : ℝ) * _ctx.order2 + (3/13 : ℝ) * _ctx.min + (1/13 : ℝ) * a13 + (3/13 : ℝ) * a27 + (3/13 : ℝ) * a29 + (6/13 : ℝ) * a37 + (3/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_260 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a27 : -(h 4) < (-9/80 : ℝ))
    (a29 : -(h 0) < (-3/19 : ℝ))
    (a32 : -(h 1) < (-5/42 : ℝ))
    (a36 : -(h 2) < (-7/60 : ℝ))
    (a41 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/17 : ℝ) * _ctx.order3 + (1/34 : ℝ) * a13 + (6/17 : ℝ) * a27 + (3/17 : ℝ) * a29 + (3/34 : ℝ) * a32 + (3/17 : ℝ) * a36 + (3/17 : ℝ) * a41 + (3/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_259 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a29 : -(h 0) < (-3/19 : ℝ))
    (a36 : -(h 2) < (-7/60 : ℝ))
    (a40 : -(h 4) < (-5/44 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/13 : ℝ) * _ctx.order3 + (3/13 : ℝ) * _ctx.min + (1/13 : ℝ) * a13 + (3/13 : ℝ) * a29 + (3/13 : ℝ) * a36 + (6/13 : ℝ) * a40 + (3/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_258 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a27 : -(h 4) < (-9/80 : ℝ))
    (a29 : -(h 0) < (-3/19 : ℝ))
    (a36 : -(h 2) < (-7/60 : ℝ))
    (a39 : -(h 1) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a19 + (1/3 : ℝ) * a27 + (1/6 : ℝ) * a29 + (1/6 : ℝ) * a36 + (1/6 : ℝ) * a39 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_257 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a27 : -(h 4) < (-9/80 : ℝ))
    (a36 : -(h 2) < (-7/60 : ℝ))
    (a38 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/13 : ℝ) * _ctx.order3 + (3/13 : ℝ) * _ctx.min + (1/13 : ℝ) * a13 + (6/13 : ℝ) * a27 + (3/13 : ℝ) * a36 + (3/13 : ℝ) * a38 + (3/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_256 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a37 : ((-2 : ℝ) * (delta)) < (-5/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a37
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_255 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a17 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a19 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a27 : -(h 4) < (-9/80 : ℝ))
    (a29 : -(h 0) < (-3/19 : ℝ))
    (a32 : -(h 1) < (-5/42 : ℝ))
    (a36 : -(h 2) < (-7/60 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/22 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/22 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_256 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_257 h delta _ctx _hno a13 a27 a36 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_258 h delta _ctx _hno a19 a27 a29 a36 f2
  by_cases p3 : h 4 ≤ (5/44 : ℝ)
  swap
  · have f3 : -(h 4) < (-5/44 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_259 h delta _ctx _hno a13 a29 a36 f3
  by_cases p4 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_260 h delta _ctx _hno a13 a27 a29 a32 a36 f4
  apply _hno 58
  change (((2 : ℝ) * (delta)) ≤ (5/22 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (5/44 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_254 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a26 : h 1 ≤ (1/8 : ℝ))
    (a35 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a26 + (1 : ℝ) * a35
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_253 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a27 : -(h 4) < (-9/80 : ℝ))
    (a34 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/13 : ℝ) * _ctx.order2 + (6/13 : ℝ) * _ctx.order3 + (3/13 : ℝ) * _ctx.min + (1/13 : ℝ) * a13 + (9/13 : ℝ) * a27 + (3/13 : ℝ) * a34 + (3/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_252 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a33 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a33
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_251 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a17 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a19 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a26 : h 1 ≤ (1/8 : ℝ))
    (a27 : -(h 4) < (-9/80 : ℝ))
    (a29 : -(h 0) < (-3/19 : ℝ))
    (a32 : -(h 1) < (-5/42 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_252 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_253 h delta _ctx _hno a13 a27 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_254 h delta _ctx _hno a26 f2
  by_cases p3 : h 2 ≤ (7/60 : ℝ)
  swap
  · have f3 : -(h 2) < (-7/60 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_255 h delta _ctx _hno a13 a17 a19 a27 a29 a32 f3
  by_cases p4 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_261 h delta _ctx _hno a13 a27 a29 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_262 h delta _ctx _hno a13 a27 a29 a32 f5
  apply _hno 54
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (7/60 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_250 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a27 : -(h 4) < (-9/80 : ℝ))
    (a31 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/13 : ℝ) * _ctx.order2 + (6/13 : ℝ) * _ctx.order3 + (3/13 : ℝ) * _ctx.min + (1/13 : ℝ) * a13 + (9/13 : ℝ) * a27 + (3/13 : ℝ) * a31 + (3/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_249 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a30 : ((-2 : ℝ) * (delta)) < (-3/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a30
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_248 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a17 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a19 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a26 : h 1 ≤ (1/8 : ℝ))
    (a27 : -(h 4) < (-9/80 : ℝ))
    (a29 : -(h 0) < (-3/19 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/13 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_249 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_250 h delta _ctx _hno a13 a27 f1
  by_cases p2 : h 1 ≤ (5/42 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/42 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_251 h delta _ctx _hno a13 a17 a19 a26 a27 a29 f2
  apply _hno 34
  change (((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (5/42 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem upper_node_247 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a28 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a28
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_246 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a17 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a18 : -(h 0) < (-2/13 : ℝ))
    (a19 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a26 : h 1 ≤ (1/8 : ℝ))
    (a27 : -(h 4) < (-9/80 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_247 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (3/19 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/19 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_248 h delta _ctx _hno a13 a17 a19 a26 a27 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_263 h delta _ctx _hno a18 a19 a27 f2
  by_cases p3 : h 4 ≤ (13/112 : ℝ)
  swap
  · have f3 : -(h 4) < (-13/112 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_264 h delta _ctx _hno a13 a18 f3
  apply _hno 4
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (13/112 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_245 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) < (-2/13 : ℝ))
    (a19 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a26 : -(h 1) < (-1/8 : ℝ))
    (a36 : -(h 4) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.order3 + (6/29 : ℝ) * _ctx.min + (1/29 : ℝ) * _ctx.fail1 + (4/29 : ℝ) * a18 + (6/29 : ℝ) * a19 + (6/29 : ℝ) * a26 + (12/29 : ℝ) * a36 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_244 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : h 2 ≤ (7/60 : ℝ))
    (a35 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a35
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_243 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) < (-2/13 : ℝ))
    (a19 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a31 : -(h 4) < (-1/9 : ℝ))
    (a34 : -(h 1) < (-9/70 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.min + (1/29 : ℝ) * _ctx.fail1 + (4/29 : ℝ) * a18 + (6/29 : ℝ) * a19 + (6/29 : ℝ) * a23 + (6/29 : ℝ) * a31 + (6/29 : ℝ) * a34 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_242 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a26 : -(h 1) < (-1/8 : ℝ))
    (a31 : -(h 4) < (-1/9 : ℝ))
    (a33 : -(h 0) < (-7/45 : ℝ))
    (a39 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/32 : ℝ) * _ctx.fail1 + (3/32 : ℝ) * a19 + (3/16 : ℝ) * a23 + (3/16 : ℝ) * a26 + (3/16 : ℝ) * a31 + (1/8 : ℝ) * a33 + (3/16 : ℝ) * a39 + (3/16 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_241 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a26 : -(h 1) < (-1/8 : ℝ))
    (a31 : -(h 4) < (-1/9 : ℝ))
    (a33 : -(h 0) < (-7/45 : ℝ))
    (a38 : -(h 3) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.min + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a19 + (6/29 : ℝ) * a26 + (6/29 : ℝ) * a31 + (4/29 : ℝ) * a33 + (6/29 : ℝ) * a38 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_240 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a26 : -(h 1) < (-1/8 : ℝ))
    (a31 : -(h 4) < (-1/9 : ℝ))
    (a33 : -(h 0) < (-7/45 : ℝ))
    (a37 : -(h 2) < (-7/60 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a19 + (1/6 : ℝ) * a23 + (1/6 : ℝ) * a26 + (1/6 : ℝ) * a31 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_239 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a31 : -(h 4) < (-1/9 : ℝ))
    (a33 : -(h 0) < (-7/45 : ℝ))
    (a36 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.min + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a19 + (6/29 : ℝ) * a23 + (6/29 : ℝ) * a31 + (4/29 : ℝ) * a33 + (6/29 : ℝ) * a36 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_238 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a28 : h 0 ≤ (4/25 : ℝ))
    (a35 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a28 + (1 : ℝ) * a35
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_237 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a34
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_236 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a19 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a26 : -(h 1) < (-1/8 : ℝ))
    (a28 : h 0 ≤ (4/25 : ℝ))
    (a31 : -(h 4) < (-1/9 : ℝ))
    (a33 : -(h 0) < (-7/45 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_237 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_238 h delta _ctx _hno a28 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_239 h delta _ctx _hno a19 a23 a31 a33 f2
  by_cases p3 : h 2 ≤ (7/60 : ℝ)
  swap
  · have f3 : -(h 2) < (-7/60 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_240 h delta _ctx _hno a19 a23 a26 a31 a33 f3
  by_cases p4 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_241 h delta _ctx _hno a19 a26 a31 a33 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_242 h delta _ctx _hno a19 a23 a26 a31 a33 f5
  apply _hno 54
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (7/60 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_235 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a32 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a32
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_234 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a18 : -(h 0) < (-2/13 : ℝ))
    (a19 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a26 : -(h 1) < (-1/8 : ℝ))
    (a28 : h 0 ≤ (4/25 : ℝ))
    (a30 : h 2 ≤ (7/60 : ℝ))
    (a31 : -(h 4) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_235 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (7/45 : ℝ)
  swap
  · have f1 : -(h 0) < (-7/45 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_236 h delta _ctx _hno a17 a19 a23 a26 a28 a31 f1
  by_cases p2 : h 1 ≤ (9/70 : ℝ)
  swap
  · have f2 : -(h 1) < (-9/70 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_243 h delta _ctx _hno a18 a19 a23 a31 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_244 h delta _ctx _hno a30 f3
  by_cases p4 : h 4 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 4) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_245 h delta _ctx _hno a18 a19 a26 f4
  apply _hno 55
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (7/45 : ℝ)) ∧ (h 1 ≤ (9/70 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (4/35 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_233 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) < (-2/13 : ℝ))
    (a19 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a26 : -(h 1) < (-1/8 : ℝ))
    (a30 : -(h 2) < (-7/60 : ℝ))
    (a35 : -(h 4) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a18 + (1/6 : ℝ) * a19 + (1/6 : ℝ) * a26 + (1/6 : ℝ) * a30 + (1/3 : ℝ) * a35 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_232 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) < (-2/13 : ℝ))
    (a19 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a34 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/11 : ℝ) * _ctx.order1 + (2/11 : ℝ) * _ctx.order4 + (4/11 : ℝ) * _ctx.min + (2/11 : ℝ) * a18 + (3/11 : ℝ) * a19 + (2/11 : ℝ) * a23 + (4/11 : ℝ) * a34 + (2/11 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_231 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) < (-2/13 : ℝ))
    (a19 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a30 : -(h 2) < (-7/60 : ℝ))
    (a33 : -(h 1) < (-9/70 : ℝ))
    (a38 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a18 + (1/6 : ℝ) * a19 + (1/6 : ℝ) * a23 + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a38 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_230 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) < (-2/13 : ℝ))
    (a19 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a33 : -(h 1) < (-9/70 : ℝ))
    (a37 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/11 : ℝ) * _ctx.order4 + (4/11 : ℝ) * _ctx.min + (2/11 : ℝ) * a18 + (3/11 : ℝ) * a19 + (2/11 : ℝ) * a23 + (2/11 : ℝ) * a33 + (2/11 : ℝ) * a37 + (2/11 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_229 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) < (-2/13 : ℝ))
    (a19 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a30 : -(h 2) < (-7/60 : ℝ))
    (a36 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/11 : ℝ) * _ctx.order4 + (4/11 : ℝ) * _ctx.min + (2/11 : ℝ) * a18 + (3/11 : ℝ) * a19 + (2/11 : ℝ) * a23 + (2/11 : ℝ) * a30 + (2/11 : ℝ) * a36 + (2/11 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_228 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : h 0 ≤ (7/45 : ℝ))
    (a35 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a32 + (1 : ℝ) * a35
  exact (lt_irrefl (0 : ℝ)) hbad

end RealPinwheel.WeakSevenBandData
