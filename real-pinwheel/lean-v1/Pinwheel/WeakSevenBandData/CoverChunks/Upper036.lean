import Pinwheel.WeakSevenBandData.CoverChunks.Upper035

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem upper_node_1427 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a32 : -(h 1) < (-2/15 : ℝ))
    (a36 : -(h 2) < (-2/17 : ℝ))
    (a38 : -(h 0) < (-2/13 : ℝ))
    (a39 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ))
    (a40 : h 0 ≤ (5/32 : ℝ))
    (a43 : -(h 3) < (-9/79 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1428 h delta _ctx _hno a39 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1429 h delta _ctx _hno a40 f1
  by_cases p2 : h 1 ≤ (3/22 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1430 h delta _ctx _hno a18 a36 a38 a43 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1431 h delta _ctx _hno a18 a32 a38 a43 f3
  by_cases p4 : h 3 ≤ (7/57 : ℝ)
  swap
  · have f4 : -(h 3) < (-7/57 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1432 h delta _ctx _hno a18 a32 a38 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1433 h delta _ctx _hno a32 a36 a38 a43 f5
  apply _hno 110
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (7/57 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_1426 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a32 : -(h 1) < (-2/15 : ℝ))
    (a38 : -(h 0) < (-2/13 : ℝ))
    (a42 : -(h 2) < (-5/38 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.min + (1/2 : ℝ) * _ctx.lower + (1/32 : ℝ) * a18 + (1/4 : ℝ) * a24 + (1/4 : ℝ) * a32 + (7/32 : ℝ) * a38 + (1/4 : ℝ) * a42 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1425 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a36 : -(h 2) < (-2/17 : ℝ))
    (a38 : -(h 0) < (-2/13 : ℝ))
    (a41 : -(h 1) < (-3/22 : ℝ))
    (a47 : -(h 4) < (-3/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a24 + (1/5 : ℝ) * a36 + (1/5 : ℝ) * a38 + (1/5 : ℝ) * a41 + (1/5 : ℝ) * a47 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1424 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a36 : -(h 2) < (-2/17 : ℝ))
    (a38 : -(h 0) < (-2/13 : ℝ))
    (a41 : -(h 1) < (-3/22 : ℝ))
    (a46 : -(h 3) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.min + (1/2 : ℝ) * _ctx.lower + (1/32 : ℝ) * a18 + (1/4 : ℝ) * a36 + (7/32 : ℝ) * a38 + (1/4 : ℝ) * a41 + (1/4 : ℝ) * a46 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1423 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a38 : -(h 0) < (-2/13 : ℝ))
    (a41 : -(h 1) < (-3/22 : ℝ))
    (a45 : -(h 2) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.min + (1/2 : ℝ) * _ctx.lower + (1/32 : ℝ) * a18 + (1/4 : ℝ) * a24 + (7/32 : ℝ) * a38 + (1/4 : ℝ) * a41 + (1/4 : ℝ) * a45 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1422 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : h 1 ≤ (5/36 : ℝ))
    (a44 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a23 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1421 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a40 : h 0 ≤ (5/32 : ℝ))
    (a43 : -(h 0) < (-3/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a40 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1420 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a39 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ))
    (a42 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a39 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1419 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a23 : h 1 ≤ (5/36 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a36 : -(h 2) < (-2/17 : ℝ))
    (a38 : -(h 0) < (-2/13 : ℝ))
    (a39 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ))
    (a40 : h 0 ≤ (5/32 : ℝ))
    (a41 : -(h 1) < (-3/22 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1420 h delta _ctx _hno a39 f0
  by_cases p1 : h 0 ≤ (3/19 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/19 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1421 h delta _ctx _hno a40 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1422 h delta _ctx _hno a23 f2
  by_cases p3 : h 2 ≤ (3/25 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1423 h delta _ctx _hno a18 a24 a38 a41 f3
  by_cases p4 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1424 h delta _ctx _hno a18 a36 a38 a41 f4
  by_cases p5 : h 4 ≤ (3/28 : ℝ)
  swap
  · have f5 : -(h 4) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1425 h delta _ctx _hno a24 a36 a38 a41 f5
  apply _hno 107
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 4 ≤ (3/28 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_1418 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a32 : -(h 1) < (-2/15 : ℝ))
    (a36 : -(h 2) < (-2/17 : ℝ))
    (a40 : -(h 0) < (-5/32 : ℝ))
    (a46 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a24 + (1/5 : ℝ) * a32 + (1/5 : ℝ) * a36 + (1/5 : ℝ) * a40 + (1/5 : ℝ) * a46 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1417 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a32 : -(h 1) < (-2/15 : ℝ))
    (a40 : -(h 0) < (-5/32 : ℝ))
    (a45 : -(h 3) < (-7/57 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.order2 + (1/4 : ℝ) * _ctx.min + (1/2 : ℝ) * _ctx.lower + (1/32 : ℝ) * a18 + (1/4 : ℝ) * a32 + (7/32 : ℝ) * a40 + (1/2 : ℝ) * a45 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1416 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a32 : -(h 1) < (-2/15 : ℝ))
    (a40 : -(h 0) < (-5/32 : ℝ))
    (a44 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.min + (1/2 : ℝ) * _ctx.lower + (1/32 : ℝ) * a18 + (1/4 : ℝ) * a24 + (1/4 : ℝ) * a32 + (7/32 : ℝ) * a40 + (1/4 : ℝ) * a44 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1415 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a36 : -(h 2) < (-2/17 : ℝ))
    (a40 : -(h 0) < (-5/32 : ℝ))
    (a43 : -(h 1) < (-3/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.min + (1/2 : ℝ) * _ctx.lower + (1/32 : ℝ) * a18 + (1/4 : ℝ) * a24 + (1/4 : ℝ) * a36 + (7/32 : ℝ) * a40 + (1/4 : ℝ) * a43 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1414 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a26 : h 0 ≤ (4/25 : ℝ))
    (a42 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a26 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1413 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a39 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a39 + (1 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1412 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a26 : h 0 ≤ (4/25 : ℝ))
    (a32 : -(h 1) < (-2/15 : ℝ))
    (a36 : -(h 2) < (-2/17 : ℝ))
    (a39 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ))
    (a40 : -(h 0) < (-5/32 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1413 h delta _ctx _hno a39 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1414 h delta _ctx _hno a26 f1
  by_cases p2 : h 1 ≤ (3/22 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1415 h delta _ctx _hno a18 a24 a36 a40 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1416 h delta _ctx _hno a18 a24 a32 a40 f3
  by_cases p4 : h 3 ≤ (7/57 : ℝ)
  swap
  · have f4 : -(h 3) < (-7/57 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1417 h delta _ctx _hno a18 a32 a40 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1418 h delta _ctx _hno a24 a32 a36 a40 f5
  apply _hno 110
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (7/57 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_1411 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a45 : h 4 ≤ (3/28 : ℝ))
    (a52 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a45 + (1 : ℝ) * a52
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1410 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a44 : h 3 ≤ (4/35 : ℝ))
    (a51 : -(h 3) < (-7/57 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a44 + (1 : ℝ) * a51
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1409 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a32 : -(h 1) < (-2/15 : ℝ))
    (a38 : -(h 0) < (-2/13 : ℝ))
    (a46 : -(h 5) < (-2/19 : ℝ))
    (a50 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.lower + (1/40 : ℝ) * a18 + (1/5 : ℝ) * a24 + (1/5 : ℝ) * a32 + (7/40 : ℝ) * a38 + (1/5 : ℝ) * a46 + (1/5 : ℝ) * a50 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1408 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a42 : h 1 ≤ (5/37 : ℝ))
    (a49 : -(h 1) < (-3/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a42 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1407 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a41 : h 0 ≤ (3/19 : ℝ))
    (a48 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a41 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1406 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a47 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1405 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a32 : -(h 1) < (-2/15 : ℝ))
    (a33 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a38 : -(h 0) < (-2/13 : ℝ))
    (a41 : h 0 ≤ (3/19 : ℝ))
    (a42 : h 1 ≤ (5/37 : ℝ))
    (a44 : h 3 ≤ (4/35 : ℝ))
    (a45 : h 4 ≤ (3/28 : ℝ))
    (a46 : -(h 5) < (-2/19 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1406 h delta _ctx _hno a33 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1407 h delta _ctx _hno a41 f1
  by_cases p2 : h 1 ≤ (3/22 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1408 h delta _ctx _hno a42 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1409 h delta _ctx _hno a18 a24 a32 a38 a46 f3
  by_cases p4 : h 3 ≤ (7/57 : ℝ)
  swap
  · have f4 : -(h 3) < (-7/57 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1410 h delta _ctx _hno a44 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1411 h delta _ctx _hno a45 f5
  apply _hno 110
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (7/57 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_1404 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 1) < (-2/15 : ℝ))
    (a36 : -(h 2) < (-2/17 : ℝ))
    (a38 : -(h 0) < (-2/13 : ℝ))
    (a51 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a32 + (1/5 : ℝ) * a36 + (1/5 : ℝ) * a38 + (2/5 : ℝ) * a51 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1403 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 1) < (-2/15 : ℝ))
    (a36 : -(h 2) < (-2/17 : ℝ))
    (a38 : -(h 0) < (-2/13 : ℝ))
    (a45 : -(h 4) < (-3/28 : ℝ))
    (a50 : -(h 3) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a32 + (1/5 : ℝ) * a36 + (1/5 : ℝ) * a38 + (1/5 : ℝ) * a45 + (1/5 : ℝ) * a50 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1402 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 1) < (-2/15 : ℝ))
    (a38 : -(h 0) < (-2/13 : ℝ))
    (a49 : -(h 2) < (-5/42 : ℝ))
    (a55 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a32 + (1/5 : ℝ) * a38 + (1/5 : ℝ) * a49 + (2/5 : ℝ) * a55 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1401 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a44 : h 3 ≤ (4/35 : ℝ))
    (a54 : -(h 3) < (-7/57 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a44 + (1 : ℝ) * a54
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1400 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a32 : -(h 1) < (-2/15 : ℝ))
    (a38 : -(h 0) < (-2/13 : ℝ))
    (a45 : -(h 4) < (-3/28 : ℝ))
    (a53 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a24 + (1/5 : ℝ) * a32 + (1/5 : ℝ) * a38 + (1/5 : ℝ) * a45 + (1/5 : ℝ) * a53 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1399 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a42 : h 1 ≤ (5/37 : ℝ))
    (a52 : -(h 1) < (-3/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a42 + (1 : ℝ) * a52
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1398 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a47 : h 0 ≤ (7/45 : ℝ))
    (a51 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a47 + (1 : ℝ) * a51
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1397 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a50 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1396 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a32 : -(h 1) < (-2/15 : ℝ))
    (a33 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a38 : -(h 0) < (-2/13 : ℝ))
    (a42 : h 1 ≤ (5/37 : ℝ))
    (a44 : h 3 ≤ (4/35 : ℝ))
    (a45 : -(h 4) < (-3/28 : ℝ))
    (a47 : h 0 ≤ (7/45 : ℝ))
    (a49 : -(h 2) < (-5/42 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1397 h delta _ctx _hno a33 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1398 h delta _ctx _hno a47 f1
  by_cases p2 : h 1 ≤ (3/22 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1399 h delta _ctx _hno a42 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1400 h delta _ctx _hno a24 a32 a38 a45 f3
  by_cases p4 : h 3 ≤ (7/57 : ℝ)
  swap
  · have f4 : -(h 3) < (-7/57 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1401 h delta _ctx _hno a44 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1402 h delta _ctx _hno a32 a38 a49 f5
  apply _hno 110
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (7/57 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_1395 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a42 : h 1 ≤ (5/37 : ℝ))
    (a48 : -(h 1) < (-5/36 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a42 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1394 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 1) < (-2/15 : ℝ))
    (a36 : -(h 2) < (-2/17 : ℝ))
    (a47 : -(h 0) < (-7/45 : ℝ))
    (a53 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a32 + (1/5 : ℝ) * a36 + (1/5 : ℝ) * a47 + (2/5 : ℝ) * a53 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1393 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 1) < (-2/15 : ℝ))
    (a36 : -(h 2) < (-2/17 : ℝ))
    (a45 : -(h 4) < (-3/28 : ℝ))
    (a47 : -(h 0) < (-7/45 : ℝ))
    (a52 : -(h 3) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a32 + (1/5 : ℝ) * a36 + (1/5 : ℝ) * a45 + (1/5 : ℝ) * a47 + (1/5 : ℝ) * a52 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1392 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a32 : -(h 1) < (-2/15 : ℝ))
    (a45 : -(h 4) < (-3/28 : ℝ))
    (a47 : -(h 0) < (-7/45 : ℝ))
    (a51 : -(h 2) < (-5/42 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a24 + (1/5 : ℝ) * a32 + (1/5 : ℝ) * a45 + (1/5 : ℝ) * a47 + (1/5 : ℝ) * a51 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1391 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a42 : h 1 ≤ (5/37 : ℝ))
    (a50 : -(h 1) < (-3/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a42 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1390 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a32 : -(h 1) < (-2/15 : ℝ))
    (a36 : -(h 2) < (-2/17 : ℝ))
    (a45 : -(h 4) < (-3/28 : ℝ))
    (a49 : -(h 0) < (-3/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a24 + (1/5 : ℝ) * a32 + (1/5 : ℝ) * a36 + (1/5 : ℝ) * a45 + (1/5 : ℝ) * a49 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1389 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a32 : -(h 1) < (-2/15 : ℝ))
    (a36 : -(h 2) < (-2/17 : ℝ))
    (a45 : -(h 4) < (-3/28 : ℝ))
    (a47 : -(h 0) < (-7/45 : ℝ))
    (a48 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a24 + (1/6 : ℝ) * a32 + (1/6 : ℝ) * a36 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * a48 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1388 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a32 : -(h 1) < (-2/15 : ℝ))
    (a36 : -(h 2) < (-2/17 : ℝ))
    (a42 : h 1 ≤ (5/37 : ℝ))
    (a45 : -(h 4) < (-3/28 : ℝ))
    (a47 : -(h 0) < (-7/45 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1389 h delta _ctx _hno a24 a32 a36 a45 a47 f0
  by_cases p1 : h 0 ≤ (3/19 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/19 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1390 h delta _ctx _hno a24 a32 a36 a45 f1
  by_cases p2 : h 1 ≤ (3/22 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1391 h delta _ctx _hno a42 f2
  by_cases p3 : h 2 ≤ (5/42 : ℝ)
  swap
  · have f3 : -(h 2) < (-5/42 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1392 h delta _ctx _hno a24 a32 a45 a47 f3
  by_cases p4 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1393 h delta _ctx _hno a32 a36 a45 a47 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1394 h delta _ctx _hno a32 a36 a47 f5
  apply _hno 109
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 2 ≤ (5/42 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_1387 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a32 : -(h 1) < (-2/15 : ℝ))
    (a36 : -(h 2) < (-2/17 : ℝ))
    (a38 : -(h 0) < (-2/13 : ℝ))
    (a45 : -(h 4) < (-3/28 : ℝ))
    (a46 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a24 + (1/6 : ℝ) * a32 + (1/6 : ℝ) * a36 + (1/6 : ℝ) * a38 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a46 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1386 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a32 : -(h 1) < (-2/15 : ℝ))
    (a33 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a36 : -(h 2) < (-2/17 : ℝ))
    (a38 : -(h 0) < (-2/13 : ℝ))
    (a42 : h 1 ≤ (5/37 : ℝ))
    (a44 : h 3 ≤ (4/35 : ℝ))
    (a45 : -(h 4) < (-3/28 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1387 h delta _ctx _hno a24 a32 a36 a38 a45 f0
  by_cases p1 : h 0 ≤ (7/45 : ℝ)
  swap
  · have f1 : -(h 0) < (-7/45 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1388 h delta _ctx _hno a24 a32 a36 a42 a45 f1
  by_cases p2 : h 1 ≤ (5/36 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/36 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1395 h delta _ctx _hno a42 f2
  by_cases p3 : h 2 ≤ (5/42 : ℝ)
  swap
  · have f3 : -(h 2) < (-5/42 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1396 h delta _ctx _hno a24 a32 a33 a38 a42 a44 a45 p1 f3
  by_cases p4 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1403 h delta _ctx _hno a32 a36 a38 a45 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1404 h delta _ctx _hno a32 a36 a38 f5
  apply _hno 108
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (7/45 : ℝ)) ∧ (h 1 ≤ (5/36 : ℝ)) ∧ (h 2 ≤ (5/42 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_1385 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 1) < (-2/15 : ℝ))
    (a36 : -(h 2) < (-2/17 : ℝ))
    (a38 : -(h 0) < (-2/13 : ℝ))
    (a44 : -(h 3) < (-4/35 : ℝ))
    (a50 : -(h 4) < (-3/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a32 + (1/5 : ℝ) * a36 + (1/5 : ℝ) * a38 + (1/5 : ℝ) * a44 + (1/5 : ℝ) * a50 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1384 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a32 : -(h 1) < (-2/15 : ℝ))
    (a36 : -(h 2) < (-2/17 : ℝ))
    (a38 : -(h 0) < (-2/13 : ℝ))
    (a49 : -(h 3) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.min + (1/2 : ℝ) * _ctx.lower + (1/32 : ℝ) * a18 + (1/4 : ℝ) * a32 + (1/4 : ℝ) * a36 + (7/32 : ℝ) * a38 + (1/4 : ℝ) * a49 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1383 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a32 : -(h 1) < (-2/15 : ℝ))
    (a38 : -(h 0) < (-2/13 : ℝ))
    (a44 : -(h 3) < (-4/35 : ℝ))
    (a48 : -(h 2) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.min + (1/2 : ℝ) * _ctx.lower + (1/32 : ℝ) * a18 + (1/4 : ℝ) * a32 + (7/32 : ℝ) * a38 + (1/4 : ℝ) * a44 + (1/4 : ℝ) * a48 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1382 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a42 : h 1 ≤ (5/37 : ℝ))
    (a47 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a42 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1381 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a32 : -(h 1) < (-2/15 : ℝ))
    (a36 : -(h 2) < (-2/17 : ℝ))
    (a44 : -(h 3) < (-4/35 : ℝ))
    (a46 : -(h 0) < (-3/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.min + (1/2 : ℝ) * _ctx.lower + (1/32 : ℝ) * a18 + (1/4 : ℝ) * a32 + (1/4 : ℝ) * a36 + (1/4 : ℝ) * a44 + (7/32 : ℝ) * a46 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1380 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a45 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1379 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a32 : -(h 1) < (-2/15 : ℝ))
    (a33 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a36 : -(h 2) < (-2/17 : ℝ))
    (a38 : -(h 0) < (-2/13 : ℝ))
    (a42 : h 1 ≤ (5/37 : ℝ))
    (a44 : -(h 3) < (-4/35 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1380 h delta _ctx _hno a33 f0
  by_cases p1 : h 0 ≤ (3/19 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/19 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1381 h delta _ctx _hno a18 a32 a36 a44 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1382 h delta _ctx _hno a42 f2
  by_cases p3 : h 2 ≤ (3/25 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1383 h delta _ctx _hno a18 a32 a38 a44 f3
  by_cases p4 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1384 h delta _ctx _hno a18 a32 a36 a38 f4
  by_cases p5 : h 4 ≤ (3/28 : ℝ)
  swap
  · have f5 : -(h 4) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1385 h delta _ctx _hno a32 a36 a38 a44 f5
  apply _hno 107
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 4 ≤ (3/28 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_1378 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a32 : -(h 1) < (-2/15 : ℝ))
    (a38 : -(h 0) < (-2/13 : ℝ))
    (a43 : -(h 2) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.min + (1/2 : ℝ) * _ctx.lower + (1/32 : ℝ) * a18 + (1/4 : ℝ) * a24 + (1/4 : ℝ) * a32 + (7/32 : ℝ) * a38 + (1/4 : ℝ) * a43 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1377 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a36 : -(h 2) < (-2/17 : ℝ))
    (a38 : -(h 0) < (-2/13 : ℝ))
    (a42 : -(h 1) < (-5/37 : ℝ))
    (a54 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a36 + (1/5 : ℝ) * a38 + (1/5 : ℝ) * a42 + (2/5 : ℝ) * a54 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1376 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a36 : -(h 2) < (-2/17 : ℝ))
    (a38 : -(h 0) < (-2/13 : ℝ))
    (a42 : -(h 1) < (-5/37 : ℝ))
    (a48 : -(h 4) < (-3/28 : ℝ))
    (a53 : -(h 3) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a36 + (1/5 : ℝ) * a38 + (1/5 : ℝ) * a42 + (1/5 : ℝ) * a48 + (1/5 : ℝ) * a53 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1375 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a38 : -(h 0) < (-2/13 : ℝ))
    (a42 : -(h 1) < (-5/37 : ℝ))
    (a48 : -(h 4) < (-3/28 : ℝ))
    (a52 : -(h 2) < (-5/42 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a24 + (1/5 : ℝ) * a38 + (1/5 : ℝ) * a42 + (1/5 : ℝ) * a48 + (1/5 : ℝ) * a52 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1374 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a36 : -(h 2) < (-2/17 : ℝ))
    (a38 : -(h 0) < (-2/13 : ℝ))
    (a48 : -(h 4) < (-3/28 : ℝ))
    (a51 : -(h 1) < (-5/36 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a24 + (1/5 : ℝ) * a36 + (1/5 : ℝ) * a38 + (1/5 : ℝ) * a48 + (1/5 : ℝ) * a51 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1373 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a36 : -(h 2) < (-2/17 : ℝ))
    (a42 : -(h 1) < (-5/37 : ℝ))
    (a48 : -(h 4) < (-3/28 : ℝ))
    (a50 : -(h 0) < (-7/45 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a24 + (1/5 : ℝ) * a36 + (1/5 : ℝ) * a42 + (1/5 : ℝ) * a48 + (1/5 : ℝ) * a50 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1372 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a36 : -(h 2) < (-2/17 : ℝ))
    (a38 : -(h 0) < (-2/13 : ℝ))
    (a42 : -(h 1) < (-5/37 : ℝ))
    (a48 : -(h 4) < (-3/28 : ℝ))
    (a49 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a24 + (1/6 : ℝ) * a36 + (1/6 : ℝ) * a38 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a48 + (1/6 : ℝ) * a49 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1371 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a36 : -(h 2) < (-2/17 : ℝ))
    (a38 : -(h 0) < (-2/13 : ℝ))
    (a42 : -(h 1) < (-5/37 : ℝ))
    (a48 : -(h 4) < (-3/28 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1372 h delta _ctx _hno a24 a36 a38 a42 a48 f0
  by_cases p1 : h 0 ≤ (7/45 : ℝ)
  swap
  · have f1 : -(h 0) < (-7/45 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1373 h delta _ctx _hno a24 a36 a42 a48 f1
  by_cases p2 : h 1 ≤ (5/36 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/36 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1374 h delta _ctx _hno a24 a36 a38 a48 f2
  by_cases p3 : h 2 ≤ (5/42 : ℝ)
  swap
  · have f3 : -(h 2) < (-5/42 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1375 h delta _ctx _hno a24 a38 a42 a48 f3
  by_cases p4 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1376 h delta _ctx _hno a36 a38 a42 a48 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1377 h delta _ctx _hno a36 a38 a42 f5
  apply _hno 108
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (7/45 : ℝ)) ∧ (h 1 ≤ (5/36 : ℝ)) ∧ (h 2 ≤ (5/42 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_1370 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a36 : -(h 2) < (-2/17 : ℝ))
    (a38 : -(h 0) < (-2/13 : ℝ))
    (a42 : -(h 1) < (-5/37 : ℝ))
    (a47 : -(h 3) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.min + (1/2 : ℝ) * _ctx.lower + (1/32 : ℝ) * a18 + (1/4 : ℝ) * a36 + (7/32 : ℝ) * a38 + (1/4 : ℝ) * a42 + (1/4 : ℝ) * a47 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1369 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a38 : -(h 0) < (-2/13 : ℝ))
    (a42 : -(h 1) < (-5/37 : ℝ))
    (a46 : -(h 2) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.min + (1/2 : ℝ) * _ctx.lower + (1/32 : ℝ) * a18 + (1/4 : ℝ) * a24 + (7/32 : ℝ) * a38 + (1/4 : ℝ) * a42 + (1/4 : ℝ) * a46 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1368 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : h 1 ≤ (5/36 : ℝ))
    (a45 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a23 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1367 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a36 : -(h 2) < (-2/17 : ℝ))
    (a42 : -(h 1) < (-5/37 : ℝ))
    (a44 : -(h 0) < (-3/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.min + (1/2 : ℝ) * _ctx.lower + (1/32 : ℝ) * a18 + (1/4 : ℝ) * a24 + (1/4 : ℝ) * a36 + (1/4 : ℝ) * a42 + (7/32 : ℝ) * a44 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1366 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1365 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a23 : h 1 ≤ (5/36 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a33 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a36 : -(h 2) < (-2/17 : ℝ))
    (a38 : -(h 0) < (-2/13 : ℝ))
    (a42 : -(h 1) < (-5/37 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1366 h delta _ctx _hno a33 f0
  by_cases p1 : h 0 ≤ (3/19 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/19 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1367 h delta _ctx _hno a18 a24 a36 a42 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1368 h delta _ctx _hno a23 f2
  by_cases p3 : h 2 ≤ (3/25 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1369 h delta _ctx _hno a18 a24 a38 a42 f3
  by_cases p4 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1370 h delta _ctx _hno a18 a36 a38 a42 f4
  by_cases p5 : h 4 ≤ (3/28 : ℝ)
  swap
  · have f5 : -(h 4) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1371 h delta _ctx _hno a24 a36 a38 a42 f5
  apply _hno 107
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 4 ≤ (3/28 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_1364 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a32 : -(h 1) < (-2/15 : ℝ))
    (a36 : -(h 2) < (-2/17 : ℝ))
    (a41 : -(h 0) < (-3/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.min + (1/2 : ℝ) * _ctx.lower + (1/32 : ℝ) * a18 + (1/4 : ℝ) * a24 + (1/4 : ℝ) * a32 + (1/4 : ℝ) * a36 + (7/32 : ℝ) * a41 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1363 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a40 : ((-2 : ℝ) * (delta)) < (-7/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1362 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a23 : h 1 ≤ (5/36 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a32 : -(h 1) < (-2/15 : ℝ))
    (a33 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a36 : -(h 2) < (-2/17 : ℝ))
    (a38 : -(h 0) < (-2/13 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/33 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/33 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1363 h delta _ctx _hno a33 f0
  by_cases p1 : h 0 ≤ (3/19 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/19 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1364 h delta _ctx _hno a18 a24 a32 a36 f1
  by_cases p2 : h 1 ≤ (5/37 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/37 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1365 h delta _ctx _hno a18 a23 a24 a33 a36 a38 f2
  by_cases p3 : h 2 ≤ (2/15 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1378 h delta _ctx _hno a18 a24 a32 a38 f3
  by_cases p4 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1379 h delta _ctx _hno a18 a32 a33 a36 a38 p2 f4
  by_cases p5 : h 4 ≤ (3/28 : ℝ)
  swap
  · have f5 : -(h 4) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1386 h delta _ctx _hno a24 a32 a33 a36 a38 p2 p4 f5
  by_cases p6 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f6 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact upper_node_1405 h delta _ctx _hno a18 a24 a32 a33 a38 p1 p2 p4 p5 f6
  apply _hno 15
  change (((2 : ℝ) * (delta)) ≤ (7/33 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (5/37 : ℝ)) ∧ (h 2 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 4 ≤ (3/28 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem upper_node_1361 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a23 : h 1 ≤ (5/36 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a26 : h 0 ≤ (4/25 : ℝ))
    (a32 : -(h 1) < (-2/15 : ℝ))
    (a33 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a36 : -(h 2) < (-2/17 : ℝ))
    (a38 : -(h 0) < (-2/13 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1362 h delta _ctx _hno a18 a23 a24 a32 a33 a36 a38
  by_cases p1 : h 0 ≤ (5/32 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/32 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1412 h delta _ctx _hno a18 a24 a26 a32 a36 p0 f1
  by_cases p2 : h 1 ≤ (3/22 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1419 h delta _ctx _hno a18 a23 a24 a36 a38 p0 p1 f2
  by_cases p3 : h 2 ≤ (5/38 : ℝ)
  swap
  · have f3 : -(h 2) < (-5/38 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1426 h delta _ctx _hno a18 a24 a32 a38 f3
  by_cases p4 : h 3 ≤ (9/79 : ℝ)
  swap
  · have f4 : -(h 3) < (-9/79 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1427 h delta _ctx _hno a18 a32 a36 a38 p0 p1 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1434 h delta _ctx _hno a24 a32 a36 a38 f5
  apply _hno 16
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (5/32 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 2 ≤ (5/38 : ℝ)) ∧ (h 3 ≤ (9/79 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_1360 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a37 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a37
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1359 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a23 : h 1 ≤ (5/36 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a26 : h 0 ≤ (4/25 : ℝ))
    (a29 : -(h 0) < (-5/33 : ℝ))
    (a32 : -(h 1) < (-2/15 : ℝ))
    (a33 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a36 : -(h 2) < (-2/17 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1360 h delta _ctx _hno a33 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1361 h delta _ctx _hno a18 a23 a24 a26 a32 a33 a36 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1435 h delta _ctx _hno a23 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1436 h delta _ctx _hno a18 a24 a29 a32 f3
  by_cases p4 : h 4 ≤ (6/55 : ℝ)
  swap
  · have f4 : -(h 4) < (-6/55 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1437 h delta _ctx _hno a20 a24 a29 a32 a33 a36 p1 p3 f4
  by_cases p5 : h 5 ≤ (3/28 : ℝ)
  swap
  · have f5 : -(h 5) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1450 h delta _ctx _hno a18 a20 a24 a29 a32 a33 a36 p1 p4 f5
  apply _hno 88
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (6/55 : ℝ)) ∧ (h 5 ≤ (3/28 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_1358 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : h 1 ≤ (5/36 : ℝ))
    (a35 : -(h 1) < (-5/31 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a23 + (1 : ℝ) * a35
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1357 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a26 : h 0 ≤ (4/25 : ℝ))
    (a34 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a26 + (1 : ℝ) * a34
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1356 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a38 : h 4 ≤ (6/55 : ℝ))
    (a45 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a38 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1355 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : -(h 0) < (-5/33 : ℝ))
    (a32 : -(h 1) < (-2/15 : ℝ))
    (a33 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a39 : -(h 5) < (-3/28 : ℝ))
    (a44 : -(h 3) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/16 : ℝ) * _ctx.order4 + (1/32 : ℝ) * _ctx.fail1 + (1/8 : ℝ) * a29 + (3/16 : ℝ) * a32 + (3/32 : ℝ) * a33 + (3/8 : ℝ) * a39 + (3/16 : ℝ) * a44 + (3/16 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1354 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a38 : h 4 ≤ (6/55 : ℝ))
    (a49 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a38 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1353 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a38 : h 4 ≤ (6/55 : ℝ))
    (a54 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a38 + (1 : ℝ) * a54
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1352 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : -(h 0) < (-5/33 : ℝ))
    (a32 : -(h 1) < (-2/15 : ℝ))
    (a33 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a39 : -(h 5) < (-3/28 : ℝ))
    (a43 : -(h 2) < (-5/43 : ℝ))
    (a53 : -(h 3) < (-6/53 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order4 + (2/13 : ℝ) * a29 + (2/13 : ℝ) * a32 + (1/13 : ℝ) * a33 + (4/13 : ℝ) * a39 + (2/13 : ℝ) * a43 + (2/13 : ℝ) * a53 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1351 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : -(h 0) < (-5/33 : ℝ))
    (a32 : -(h 1) < (-2/15 : ℝ))
    (a33 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a39 : -(h 5) < (-3/28 : ℝ))
    (a48 : -(h 3) < (-9/80 : ℝ))
    (a52 : -(h 2) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order4 + (2/13 : ℝ) * a29 + (2/13 : ℝ) * a32 + (1/13 : ℝ) * a33 + (4/13 : ℝ) * a39 + (2/13 : ℝ) * a48 + (2/13 : ℝ) * a52 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1350 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : h 1 ≤ (5/36 : ℝ))
    (a51 : -(h 1) < (-15/107 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a23 + (1 : ℝ) * a51
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1349 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 1) < (-2/15 : ℝ))
    (a33 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a39 : -(h 5) < (-3/28 : ℝ))
    (a43 : -(h 2) < (-5/43 : ℝ))
    (a48 : -(h 3) < (-9/80 : ℝ))
    (a50 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order4 + (2/13 : ℝ) * a32 + (1/13 : ℝ) * a33 + (4/13 : ℝ) * a39 + (2/13 : ℝ) * a43 + (2/13 : ℝ) * a48 + (2/13 : ℝ) * a50 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1348 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a49 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a25 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

end RealPinwheel.WeakSevenBandData
