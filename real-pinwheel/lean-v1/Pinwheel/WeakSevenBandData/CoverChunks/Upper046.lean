import Pinwheel.WeakSevenBandData.CoverChunks.Upper045

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem upper_node_627 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a16 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a31 : -(h 1) < (-5/37 : ℝ))
    (a36 : -(h 3) < (-7/57 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (47/163 : ℝ) * _ctx.order2 + (47/163 : ℝ) * _ctx.order4 + (89/163 : ℝ) * _ctx.min + (17/163 : ℝ) * a14 + (5/163 : ℝ) * a16 + (47/163 : ℝ) * a31 + (94/163 : ℝ) * a36 + (47/163 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_626 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a16 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a31 : -(h 1) < (-5/37 : ℝ))
    (a35 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (47/163 : ℝ) * _ctx.order4 + (89/163 : ℝ) * _ctx.min + (17/163 : ℝ) * a14 + (5/163 : ℝ) * a16 + (47/163 : ℝ) * a23 + (47/163 : ℝ) * a31 + (47/163 : ℝ) * a35 + (47/163 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_625 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a22 : h 1 ≤ (5/36 : ℝ))
    (a34 : -(h 1) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a22 + (1 : ℝ) * a34
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_624 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a31 : -(h 1) < (-5/37 : ℝ))
    (a37 : h 2 ≤ (5/43 : ℝ))
    (a39 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (8/29 : ℝ) * _ctx.min + (3/29 : ℝ) * _ctx.fail1 + (2/29 : ℝ) * a14 + (8/29 : ℝ) * a23 + (8/29 : ℝ) * a31 + (10/29 : ℝ) * a37 + (8/29 : ℝ) * a39 + (8/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_623 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a31 : -(h 1) < (-5/37 : ℝ))
    (a37 : h 2 ≤ (5/43 : ℝ))
    (a38 : -(h 3) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (16/43 : ℝ) * _ctx.order4 + (32/43 : ℝ) * _ctx.min + (5/43 : ℝ) * _ctx.fail1 + (6/43 : ℝ) * a14 + (16/43 : ℝ) * a31 + (14/43 : ℝ) * a37 + (16/43 : ℝ) * a38 + (16/43 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_622 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a31 : -(h 1) < (-5/37 : ℝ))
    (a33 : -(h 0) < (-5/33 : ℝ))
    (a43 : -(h 5) < (-3/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.order4 + (1/29 : ℝ) * _ctx.fail1 + (3/116 : ℝ) * a14 + (6/29 : ℝ) * a23 + (6/29 : ℝ) * a31 + (13/116 : ℝ) * a33 + (12/29 : ℝ) * a43 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_621 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a31 : -(h 1) < (-5/37 : ℝ))
    (a33 : -(h 0) < (-5/33 : ℝ))
    (a42 : -(h 4) < (-6/55 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.min + (1/23 : ℝ) * _ctx.fail1 + (3/46 : ℝ) * a14 + (6/23 : ℝ) * a23 + (6/23 : ℝ) * a31 + (5/46 : ℝ) * a33 + (6/23 : ℝ) * a42 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_620 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a31 : -(h 1) < (-5/37 : ℝ))
    (a33 : -(h 0) < (-5/33 : ℝ))
    (a41 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.order4 + (1/2 : ℝ) * _ctx.min + (3/32 : ℝ) * a14 + (1/4 : ℝ) * a23 + (1/4 : ℝ) * a31 + (5/32 : ℝ) * a33 + (1/4 : ℝ) * a41 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_619 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a22 : h 1 ≤ (5/36 : ℝ))
    (a40 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a22 + (1 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_618 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a31 : -(h 1) < (-5/37 : ℝ))
    (a37 : -(h 2) < (-5/43 : ℝ))
    (a39 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.order4 + (1/2 : ℝ) * _ctx.min + (3/32 : ℝ) * a14 + (1/4 : ℝ) * a23 + (1/4 : ℝ) * a31 + (1/4 : ℝ) * a37 + (5/32 : ℝ) * a39 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_617 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a38 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a38
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_616 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a22 : h 1 ≤ (5/36 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a29 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a31 : -(h 1) < (-5/37 : ℝ))
    (a33 : -(h 0) < (-5/33 : ℝ))
    (a37 : -(h 2) < (-5/43 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_617 h delta _ctx _hno a29 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_618 h delta _ctx _hno a14 a23 a31 a37 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_619 h delta _ctx _hno a22 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_620 h delta _ctx _hno a14 a23 a31 a33 f3
  by_cases p4 : h 4 ≤ (6/55 : ℝ)
  swap
  · have f4 : -(h 4) < (-6/55 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_621 h delta _ctx _hno a14 a23 a31 a33 f4
  by_cases p5 : h 5 ≤ (3/28 : ℝ)
  swap
  · have f5 : -(h 5) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_622 h delta _ctx _hno a14 a23 a31 a33 f5
  apply _hno 88
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (6/55 : ℝ)) ∧ (h 5 ≤ (3/28 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_615 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a33 : -(h 0) < (-5/33 : ℝ))
    (a36 : -(h 1) < (-6/43 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/17 : ℝ) * _ctx.order4 + (12/17 : ℝ) * _ctx.min + (1/17 : ℝ) * _ctx.fail1 + (9/68 : ℝ) * a14 + (6/17 : ℝ) * a23 + (7/68 : ℝ) * a33 + (6/17 : ℝ) * a36 + (6/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_614 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : h 0 ≤ (2/13 : ℝ))
    (a35 : -(h 0) < (-4/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a18 + (1 : ℝ) * a35
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_613 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-10/43 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a34
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_612 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a18 : h 0 ≤ (2/13 : ℝ))
    (a22 : h 1 ≤ (5/36 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a29 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a31 : -(h 1) < (-5/37 : ℝ))
    (a33 : -(h 0) < (-5/33 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (10/43 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-10/43 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_613 h delta _ctx _hno a29 f0
  by_cases p1 : h 0 ≤ (4/25 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/25 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_614 h delta _ctx _hno a18 f1
  by_cases p2 : h 1 ≤ (6/43 : ℝ)
  swap
  · have f2 : -(h 1) < (-6/43 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_615 h delta _ctx _hno a14 a23 a33 f2
  by_cases p3 : h 2 ≤ (5/43 : ℝ)
  swap
  · have f3 : -(h 2) < (-5/43 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_616 h delta _ctx _hno a14 a22 a23 a29 a31 a33 f3
  by_cases p4 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_623 h delta _ctx _hno a14 a31 p3 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_624 h delta _ctx _hno a14 a23 a31 p3 f5
  apply _hno 74
  change (((2 : ℝ) * (delta)) ≤ (10/43 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (6/43 : ℝ)) ∧ (h 2 ≤ (5/43 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_611 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a32 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a32
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_610 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a16 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a18 : h 0 ≤ (2/13 : ℝ))
    (a22 : h 1 ≤ (5/36 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a25 : -(h 0) < (-3/20 : ℝ))
    (a29 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a31 : -(h 1) < (-5/37 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_611 h delta _ctx _hno a29 f0
  by_cases p1 : h 0 ≤ (5/33 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/33 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_612 h delta _ctx _hno a14 a18 a22 a23 a29 a31 f1
  by_cases p2 : h 1 ≤ (3/20 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_625 h delta _ctx _hno a22 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_626 h delta _ctx _hno a14 a16 a23 a31 f3
  by_cases p4 : h 3 ≤ (7/57 : ℝ)
  swap
  · have f4 : -(h 3) < (-7/57 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_627 h delta _ctx _hno a14 a16 a31 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_628 h delta _ctx _hno a14 a23 a25 a31 f5
  apply _hno 87
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (5/33 : ℝ)) ∧ (h 1 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (7/57 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_609 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : h 0 ≤ (2/13 : ℝ))
    (a30 : -(h 0) < (-3/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a18 + (1 : ℝ) * a30
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_608 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a25 : -(h 0) < (-3/20 : ℝ))
    (a28 : -(h 1) < (-2/15 : ℝ))
    (a29 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a35 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.min + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a23 + (4/29 : ℝ) * a25 + (6/29 : ℝ) * a28 + (6/29 : ℝ) * a29 + (6/29 : ℝ) * a35 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_607 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a16 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a28 : -(h 1) < (-2/15 : ℝ))
    (a34 : -(h 3) < (-7/57 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (47/163 : ℝ) * _ctx.order2 + (47/163 : ℝ) * _ctx.order4 + (89/163 : ℝ) * _ctx.min + (17/163 : ℝ) * a14 + (5/163 : ℝ) * a16 + (47/163 : ℝ) * a28 + (94/163 : ℝ) * a34 + (47/163 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_606 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a16 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 1) < (-2/15 : ℝ))
    (a29 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a33 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (12/55 : ℝ) * _ctx.order4 + (2/5 : ℝ) * _ctx.min + (2/55 : ℝ) * a16 + (12/55 : ℝ) * a23 + (12/55 : ℝ) * a28 + (17/55 : ℝ) * a29 + (12/55 : ℝ) * a33 + (12/55 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_605 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a22 : h 1 ≤ (5/36 : ℝ))
    (a32 : -(h 1) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a22 + (1 : ℝ) * a32
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_604 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 1) < (-2/15 : ℝ))
    (a29 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a31 : -(h 0) < (-5/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/13 : ℝ) * _ctx.order4 + (6/13 : ℝ) * _ctx.min + (1/26 : ℝ) * _ctx.fail1 + (3/13 : ℝ) * a23 + (3/13 : ℝ) * a28 + (9/26 : ℝ) * a29 + (2/13 : ℝ) * a31 + (3/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_603 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a30 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a30
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_602 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a16 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a17 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a22 : h 1 ≤ (5/36 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a25 : -(h 0) < (-3/20 : ℝ))
    (a28 : -(h 1) < (-2/15 : ℝ))
    (a29 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_603 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (5/33 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/33 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_604 h delta _ctx _hno a23 a28 a29 f1
  by_cases p2 : h 1 ≤ (3/20 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_605 h delta _ctx _hno a22 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_606 h delta _ctx _hno a16 a23 a28 a29 f3
  by_cases p4 : h 3 ≤ (7/57 : ℝ)
  swap
  · have f4 : -(h 3) < (-7/57 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_607 h delta _ctx _hno a14 a16 a28 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_608 h delta _ctx _hno a23 a25 a28 a29 f5
  apply _hno 87
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (5/33 : ℝ)) ∧ (h 1 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (7/57 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_601 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a16 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a17 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a18 : h 0 ≤ (2/13 : ℝ))
    (a22 : h 1 ≤ (5/36 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a25 : -(h 0) < (-3/20 : ℝ))
    (a28 : -(h 1) < (-2/15 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_602 h delta _ctx _hno a14 a16 a17 a22 a23 a25 a28 f0
  by_cases p1 : h 0 ≤ (3/19 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/19 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_609 h delta _ctx _hno a18 f1
  by_cases p2 : h 1 ≤ (5/37 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/37 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_610 h delta _ctx _hno a14 a16 a18 a22 a23 a25 p0 f2
  by_cases p3 : h 2 ≤ (3/25 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_629 h delta _ctx _hno a14 a16 a23 a25 a28 p0 p2 f3
  by_cases p4 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_636 h delta _ctx _hno a14 a16 a25 a28 p0 p2 p3 f4
  by_cases p5 : h 4 ≤ (3/28 : ℝ)
  swap
  · have f5 : -(h 4) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_643 h delta _ctx _hno a14 a18 a23 a25 a28 p0 p2 p3 p4
  apply _hno 75
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (5/37 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 4 ≤ (3/28 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_600 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : h 0 ≤ (2/13 : ℝ))
    (a27 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a18 + (1 : ℝ) * a27
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_599 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a26 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a26
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_598 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a16 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a17 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a18 : h 0 ≤ (2/13 : ℝ))
    (a19 : -(h 1) < (-1/8 : ℝ))
    (a22 : h 1 ≤ (5/36 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a25 : -(h 0) < (-3/20 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_599 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_600 h delta _ctx _hno a18 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_601 h delta _ctx _hno a14 a16 a17 a18 a22 a23 a25 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_668 h delta _ctx _hno a14 a16 a17 a18 a19 a23 a25 f3
  by_cases p4 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_679 h delta _ctx _hno a14 a17 a18 a19 a23 a25 f4
  apply _hno 57
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_597 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a24 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a24
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_596 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a16 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a17 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a18 : h 0 ≤ (2/13 : ℝ))
    (a19 : -(h 1) < (-1/8 : ℝ))
    (a22 : h 1 ≤ (5/36 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_597 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_598 h delta _ctx _hno a14 a16 a17 a18 a19 a22 a23 f1
  by_cases p2 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_695 h delta _ctx _hno a14 a16 a17 a19 a23 p1 f2
  by_cases p3 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f3 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_706 h delta _ctx _hno a14 a16 a17 a19 a23 p1 f3
  apply _hno 8
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_595 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a16 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a22 : -(h 1) < (-5/36 : ℝ))
    (a31 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (94/327 : ℝ) * _ctx.order3 + (262/981 : ℝ) * _ctx.min + (47/981 : ℝ) * _ctx.fail1 + (68/981 : ℝ) * a14 + (20/981 : ℝ) * a16 + (94/327 : ℝ) * a22 + (188/327 : ℝ) * a31 + (94/327 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_594 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a16 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a22 : -(h 1) < (-5/36 : ℝ))
    (a30 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (47/121 : ℝ) * _ctx.order3 + (94/121 : ℝ) * _ctx.order4 + (137/121 : ℝ) * _ctx.min + (23/121 : ℝ) * a14 + (4/121 : ℝ) * a16 + (47/121 : ℝ) * a22 + (47/121 : ℝ) * a30 + (47/121 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_593 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a22 : -(h 1) < (-5/36 : ℝ))
    (a29 : -(h 0) < (-3/20 : ℝ))
    (a35 : -(h 4) < (-5/46 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.order3 + (6/23 : ℝ) * _ctx.min + (1/23 : ℝ) * _ctx.fail1 + (3/46 : ℝ) * a14 + (6/23 : ℝ) * a22 + (5/46 : ℝ) * a29 + (12/23 : ℝ) * a35 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_592 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a22 : -(h 1) < (-5/36 : ℝ))
    (a29 : -(h 0) < (-3/20 : ℝ))
    (a34 : -(h 3) < (-6/55 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/17 : ℝ) * _ctx.order4 + (12/17 : ℝ) * _ctx.min + (1/17 : ℝ) * _ctx.fail1 + (9/68 : ℝ) * a14 + (6/17 : ℝ) * a22 + (7/68 : ℝ) * a29 + (6/17 : ℝ) * a34 + (6/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_591 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a16 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a33 : -(h 2) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (47/121 : ℝ) * _ctx.order1 + (47/121 : ℝ) * _ctx.order3 + (94/121 : ℝ) * _ctx.order4 + (137/121 : ℝ) * _ctx.min + (23/121 : ℝ) * a14 + (4/121 : ℝ) * a16 + (94/121 : ℝ) * a33 + (47/121 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_590 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a16 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a32 : -(h 1) < (-8/55 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (94/159 : ℝ) * _ctx.order3 + (188/159 : ℝ) * _ctx.order4 + (838/477 : ℝ) * _ctx.min + (47/477 : ℝ) * _ctx.fail1 + (140/477 : ℝ) * a14 + (8/477 : ℝ) * a16 + (94/159 : ℝ) * a32 + (94/159 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_589 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : h 0 ≤ (2/13 : ℝ))
    (a31 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a18 + (1 : ℝ) * a31
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_588 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a30 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a23 + (1 : ℝ) * a30
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_587 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a16 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a18 : h 0 ≤ (2/13 : ℝ))
    (a22 : -(h 1) < (-5/36 : ℝ))
    (a23 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a29 : -(h 0) < (-3/20 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_588 h delta _ctx _hno a23 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_589 h delta _ctx _hno a18 f1
  by_cases p2 : h 1 ≤ (8/55 : ℝ)
  swap
  · have f2 : -(h 1) < (-8/55 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_590 h delta _ctx _hno a14 a16 f2
  by_cases p3 : h 2 ≤ (1/7 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_591 h delta _ctx _hno a14 a16 f3
  by_cases p4 : h 3 ≤ (6/55 : ℝ)
  swap
  · have f4 : -(h 3) < (-6/55 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_592 h delta _ctx _hno a14 a22 a29 f4
  by_cases p5 : h 4 ≤ (5/46 : ℝ)
  swap
  · have f5 : -(h 4) < (-5/46 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_593 h delta _ctx _hno a14 a22 a29 f5
  apply _hno 12
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (8/55 : ℝ)) ∧ (h 2 ≤ (1/7 : ℝ)) ∧ (h 3 ≤ (6/55 : ℝ)) ∧ (h 4 ≤ (5/46 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_586 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a28 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a23 + (1 : ℝ) * a28
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_585 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a16 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a18 : h 0 ≤ (2/13 : ℝ))
    (a22 : -(h 1) < (-5/36 : ℝ))
    (a23 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_586 h delta _ctx _hno a23 f0
  by_cases p1 : h 0 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_587 h delta _ctx _hno a14 a16 a18 a22 a23 f1
  by_cases p2 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_594 h delta _ctx _hno a14 a16 a22 f2
  by_cases p3 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f3 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_595 h delta _ctx _hno a14 a16 a22 f3
  apply _hno 8
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_584 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a16 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a26 : -(h 2) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (47/121 : ℝ) * _ctx.order1 + (47/121 : ℝ) * _ctx.order3 + (94/121 : ℝ) * _ctx.order4 + (137/121 : ℝ) * _ctx.min + (23/121 : ℝ) * a14 + (4/121 : ℝ) * a16 + (94/121 : ℝ) * a26 + (47/121 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_583 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a25 : -(h 1) < (-7/44 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/11 : ℝ) * _ctx.order0 + (6/11 : ℝ) * _ctx.order3 + (12/11 : ℝ) * _ctx.order4 + (18/11 : ℝ) * _ctx.min + (1/11 : ℝ) * _ctx.fail1 + (3/11 : ℝ) * a14 + (7/11 : ℝ) * a25 + (6/11 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_582 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : h 0 ≤ (2/13 : ℝ))
    (a24 : -(h 0) < (-4/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a18 + (1 : ℝ) * a24
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_581 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a16 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a22 : -(h 1) < (-5/36 : ℝ))
    (a23 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (9/29 : ℝ) * _ctx.order3 + (18/29 : ℝ) * _ctx.order4 + (26/29 : ℝ) * _ctx.min + (3/58 : ℝ) * _ctx.fail1 + (1/29 : ℝ) * a16 + (9/29 : ℝ) * a22 + (35/58 : ℝ) * a23 + (9/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_580 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a16 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a18 : h 0 ≤ (2/13 : ℝ))
    (a22 : -(h 1) < (-5/36 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_581 h delta _ctx _hno a16 a22 f0
  by_cases p1 : h 0 ≤ (4/25 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/25 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_582 h delta _ctx _hno a18 f1
  by_cases p2 : h 1 ≤ (7/44 : ℝ)
  swap
  · have f2 : -(h 1) < (-7/44 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_583 h delta _ctx _hno a14 f2
  by_cases p3 : h 2 ≤ (1/7 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_584 h delta _ctx _hno a14 a16 f3
  by_cases p4 : h 3 ≤ (3/28 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_585 h delta _ctx _hno a14 a16 a18 a22 p0
  apply _hno 10
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (7/44 : ℝ)) ∧ (h 2 ≤ (1/7 : ℝ)) ∧ (h 3 ≤ (3/28 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_579 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : h 0 ≤ (2/13 : ℝ))
    (a21 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a18 + (1 : ℝ) * a21
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_578 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a20 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a20
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_577 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a16 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a17 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a18 : h 0 ≤ (2/13 : ℝ))
    (a19 : -(h 1) < (-1/8 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_578 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_579 h delta _ctx _hno a18 f1
  by_cases p2 : h 1 ≤ (5/36 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/36 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_580 h delta _ctx _hno a14 a16 a18 f2
  by_cases p3 : h 3 ≤ (1/9 : ℝ)
  swap
  · have f3 : -(h 3) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_596 h delta _ctx _hno a14 a16 a17 a18 a19 p2 f3
  apply _hno 0
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (5/36 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_576 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a18 : -(h 0) < (-2/13 : ℝ))
    (a32 : -(h 4) < (-13/112 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/13 : ℝ) * _ctx.order2 + (6/13 : ℝ) * _ctx.order3 + (3/13 : ℝ) * _ctx.min + (1/13 : ℝ) * a13 + (3/13 : ℝ) * a18 + (9/13 : ℝ) * a32 + (3/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_575 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a18 : -(h 0) < (-2/13 : ℝ))
    (a31 : -(h 1) < (-1/8 : ℝ))
    (a36 : -(h 4) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.order3 + (6/23 : ℝ) * _ctx.min + (1/23 : ℝ) * _ctx.fail1 + (3/46 : ℝ) * a14 + (5/46 : ℝ) * a18 + (6/23 : ℝ) * a31 + (12/23 : ℝ) * a36 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_574 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a18 : -(h 0) < (-2/13 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a35 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order1 + (1/5 : ℝ) * _ctx.min + (1/20 : ℝ) * a14 + (3/20 : ℝ) * a18 + (1/5 : ℝ) * a23 + (1/5 : ℝ) * a28 + (2/5 : ℝ) * a35 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_573 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a18 : -(h 0) < (-2/13 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a34 : -(h 1) < (-9/70 : ℝ))
    (a40 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/29 : ℝ) * _ctx.fail1 + (3/116 : ℝ) * a14 + (13/116 : ℝ) * a18 + (6/29 : ℝ) * a23 + (6/29 : ℝ) * a28 + (6/29 : ℝ) * a34 + (6/29 : ℝ) * a40 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_572 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a18 : -(h 0) < (-2/13 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a34 : -(h 1) < (-9/70 : ℝ))
    (a39 : -(h 3) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.min + (1/23 : ℝ) * _ctx.fail1 + (3/46 : ℝ) * a14 + (5/46 : ℝ) * a18 + (6/23 : ℝ) * a28 + (6/23 : ℝ) * a34 + (6/23 : ℝ) * a39 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_571 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a18 : -(h 0) < (-2/13 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a34 : -(h 1) < (-9/70 : ℝ))
    (a38 : -(h 2) < (-7/60 : ℝ))
    (a44 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/48 : ℝ) * a14 + (7/48 : ℝ) * a18 + (1/6 : ℝ) * a23 + (1/6 : ℝ) * a28 + (1/6 : ℝ) * a34 + (1/6 : ℝ) * a38 + (1/6 : ℝ) * a44 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_570 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a18 : -(h 0) < (-2/13 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a34 : -(h 1) < (-9/70 : ℝ))
    (a38 : -(h 2) < (-7/60 : ℝ))
    (a43 : -(h 3) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (1/20 : ℝ) * a14 + (3/20 : ℝ) * a18 + (1/5 : ℝ) * a28 + (1/5 : ℝ) * a34 + (1/5 : ℝ) * a38 + (1/5 : ℝ) * a43 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_569 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a18 : -(h 0) < (-2/13 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a34 : -(h 1) < (-9/70 : ℝ))
    (a42 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (1/20 : ℝ) * a14 + (3/20 : ℝ) * a18 + (1/5 : ℝ) * a23 + (1/5 : ℝ) * a28 + (1/5 : ℝ) * a34 + (1/5 : ℝ) * a42 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_568 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a18 : -(h 0) < (-2/13 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a38 : -(h 2) < (-7/60 : ℝ))
    (a41 : -(h 1) < (-4/31 : ℝ))
    (a47 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/48 : ℝ) * a14 + (7/48 : ℝ) * a18 + (1/6 : ℝ) * a23 + (1/6 : ℝ) * a28 + (1/6 : ℝ) * a38 + (1/6 : ℝ) * a41 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_567 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a18 : -(h 0) < (-2/13 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a38 : -(h 2) < (-7/60 : ℝ))
    (a41 : -(h 1) < (-4/31 : ℝ))
    (a46 : -(h 3) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (1/20 : ℝ) * a14 + (3/20 : ℝ) * a18 + (1/5 : ℝ) * a28 + (1/5 : ℝ) * a38 + (1/5 : ℝ) * a41 + (1/5 : ℝ) * a46 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_566 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a18 : -(h 0) < (-2/13 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a41 : -(h 1) < (-4/31 : ℝ))
    (a45 : -(h 2) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (1/20 : ℝ) * a14 + (3/20 : ℝ) * a18 + (1/5 : ℝ) * a23 + (1/5 : ℝ) * a28 + (1/5 : ℝ) * a41 + (1/5 : ℝ) * a45 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_565 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a18 : -(h 0) < (-2/13 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a38 : -(h 2) < (-7/60 : ℝ))
    (a44 : -(h 1) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (1/20 : ℝ) * a14 + (3/20 : ℝ) * a18 + (1/5 : ℝ) * a23 + (1/5 : ℝ) * a28 + (1/5 : ℝ) * a38 + (1/5 : ℝ) * a44 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_564 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : h 0 ≤ (7/45 : ℝ))
    (a43 : -(h 0) < (-5/32 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_563 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a42 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a19 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_562 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a18 : -(h 0) < (-2/13 : ℝ))
    (a19 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a33 : h 0 ≤ (7/45 : ℝ))
    (a38 : -(h 2) < (-7/60 : ℝ))
    (a41 : -(h 1) < (-4/31 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_563 h delta _ctx _hno a19 f0
  by_cases p1 : h 0 ≤ (5/32 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/32 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_564 h delta _ctx _hno a33 f1
  by_cases p2 : h 1 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_565 h delta _ctx _hno a14 a18 a23 a28 a38 f2
  by_cases p3 : h 2 ≤ (3/25 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_566 h delta _ctx _hno a14 a18 a23 a28 a41 f3
  by_cases p4 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_567 h delta _ctx _hno a14 a18 a28 a38 a41 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_568 h delta _ctx _hno a14 a18 a23 a28 a38 a41 f5
  apply _hno 86
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (5/32 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_561 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : h 0 ≤ (7/45 : ℝ))
    (a40 : -(h 0) < (-3/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_560 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) < (-2/13 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a34 : -(h 1) < (-9/70 : ℝ))
    (a38 : -(h 2) < (-7/60 : ℝ))
    (a39 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a18 + (1/6 : ℝ) * a23 + (1/6 : ℝ) * a28 + (1/6 : ℝ) * a34 + (1/6 : ℝ) * a38 + (1/6 : ℝ) * a39 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_559 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a18 : -(h 0) < (-2/13 : ℝ))
    (a19 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a33 : h 0 ≤ (7/45 : ℝ))
    (a34 : -(h 1) < (-9/70 : ℝ))
    (a38 : -(h 2) < (-7/60 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_560 h delta _ctx _hno a18 a23 a28 a34 a38 f0
  by_cases p1 : h 0 ≤ (3/19 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/19 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_561 h delta _ctx _hno a33 f1
  by_cases p2 : h 1 ≤ (4/31 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/31 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_562 h delta _ctx _hno a14 a18 a19 a23 a28 a33 a38 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_569 h delta _ctx _hno a14 a18 a23 a28 a34 f3
  by_cases p4 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_570 h delta _ctx _hno a14 a18 a28 a34 a38 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_571 h delta _ctx _hno a14 a18 a23 a28 a34 a38 f5
  apply _hno 85
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (4/31 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_558 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a21 : h 1 ≤ (5/38 : ℝ))
    (a37 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a21 + (1 : ℝ) * a37
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_557 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : h 0 ≤ (7/45 : ℝ))
    (a36 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a36
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_556 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a35 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a19 + (1 : ℝ) * a35
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_555 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a18 : -(h 0) < (-2/13 : ℝ))
    (a19 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a21 : h 1 ≤ (5/38 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a33 : h 0 ≤ (7/45 : ℝ))
    (a34 : -(h 1) < (-9/70 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_556 h delta _ctx _hno a19 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_557 h delta _ctx _hno a33 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_558 h delta _ctx _hno a21 f2
  by_cases p3 : h 2 ≤ (7/60 : ℝ)
  swap
  · have f3 : -(h 2) < (-7/60 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_559 h delta _ctx _hno a14 a18 a19 a23 a28 a33 a34 f3
  by_cases p4 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_572 h delta _ctx _hno a14 a18 a28 a34 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_573 h delta _ctx _hno a14 a18 a23 a28 a34 f5
  apply _hno 54
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (7/60 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_554 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a31 : -(h 1) < (-1/8 : ℝ))
    (a33 : -(h 0) < (-7/45 : ℝ))
    (a39 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/29 : ℝ) * _ctx.fail1 + (3/116 : ℝ) * a14 + (6/29 : ℝ) * a23 + (6/29 : ℝ) * a28 + (6/29 : ℝ) * a31 + (13/116 : ℝ) * a33 + (6/29 : ℝ) * a39 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_553 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a31 : -(h 1) < (-1/8 : ℝ))
    (a33 : -(h 0) < (-7/45 : ℝ))
    (a38 : -(h 3) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order2 + (1/5 : ℝ) * _ctx.min + (1/20 : ℝ) * a14 + (1/5 : ℝ) * a28 + (1/5 : ℝ) * a31 + (3/20 : ℝ) * a33 + (2/5 : ℝ) * a38 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_552 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a31 : -(h 1) < (-1/8 : ℝ))
    (a33 : -(h 0) < (-7/45 : ℝ))
    (a37 : -(h 2) < (-7/60 : ℝ))
    (a44 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/3 : ℝ) * _ctx.order4 + (1/48 : ℝ) * a14 + (1/6 : ℝ) * a31 + (7/48 : ℝ) * a33 + (1/6 : ℝ) * a37 + (1/2 : ℝ) * a44 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_551 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a31 : -(h 1) < (-1/8 : ℝ))
    (a33 : -(h 0) < (-7/45 : ℝ))
    (a37 : -(h 2) < (-7/60 : ℝ))
    (a43 : -(h 4) < (-6/53 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (1/20 : ℝ) * a14 + (1/5 : ℝ) * a31 + (3/20 : ℝ) * a33 + (1/5 : ℝ) * a37 + (2/5 : ℝ) * a43 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_550 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a31 : -(h 1) < (-1/8 : ℝ))
    (a33 : -(h 0) < (-7/45 : ℝ))
    (a37 : -(h 2) < (-7/60 : ℝ))
    (a42 : -(h 3) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (1/20 : ℝ) * a14 + (1/5 : ℝ) * a28 + (1/5 : ℝ) * a31 + (3/20 : ℝ) * a33 + (1/5 : ℝ) * a37 + (1/5 : ℝ) * a42 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_549 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a31 : -(h 1) < (-1/8 : ℝ))
    (a33 : -(h 0) < (-7/45 : ℝ))
    (a41 : -(h 2) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (1/20 : ℝ) * a14 + (1/5 : ℝ) * a23 + (1/5 : ℝ) * a28 + (1/5 : ℝ) * a31 + (3/20 : ℝ) * a33 + (1/5 : ℝ) * a41 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_548 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a33 : -(h 0) < (-7/45 : ℝ))
    (a37 : -(h 2) < (-7/60 : ℝ))
    (a40 : -(h 1) < (-9/71 : ℝ))
    (a46 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/48 : ℝ) * a14 + (1/6 : ℝ) * a23 + (1/6 : ℝ) * a28 + (7/48 : ℝ) * a33 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a40 + (1/6 : ℝ) * a46 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

end RealPinwheel.WeakSevenBandData
