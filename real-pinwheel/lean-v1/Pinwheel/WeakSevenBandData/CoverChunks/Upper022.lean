import Pinwheel.WeakSevenBandData.CoverChunks.Upper021

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem upper_node_2547 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a36 : -(h 1) < (-3/22 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    (a45 : -(h 0) < (-8/55 : ℝ))
    (a53 : -(h 2) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (8/33 : ℝ) * _ctx.lower + (7/264 : ℝ) * a23 + (1/33 : ℝ) * a28 + (8/33 : ℝ) * a36 + (19/88 : ℝ) * a42 + (8/33 : ℝ) * a45 + (8/33 : ℝ) * a53 + (8/33 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2546 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a45 : -(h 0) < (-8/55 : ℝ))
    (a52 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (171/397 : ℝ) * _ctx.min + (363/397 : ℝ) * _ctx.lower + (32/397 : ℝ) * _ctx.fail1 + (21/397 : ℝ) * a23 + (24/397 : ℝ) * a28 + (128/397 : ℝ) * a45 + (192/397 : ℝ) * a52 + (192/397 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2545 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a36 : -(h 1) < (-3/22 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    (a49 : -(h 4) < (-1/9 : ℝ))
    (a51 : -(h 0) < (-5/34 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.lower + (1/23 : ℝ) * _ctx.fail1 + (3/92 : ℝ) * a23 + (6/23 : ℝ) * a36 + (21/92 : ℝ) * a42 + (6/23 : ℝ) * a49 + (4/23 : ℝ) * a51 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2544 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a37 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a50 : ((-2 : ℝ) * (delta)) < (-16/71 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a37 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2543 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a36 : -(h 1) < (-3/22 : ℝ))
    (a37 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    (a45 : -(h 0) < (-8/55 : ℝ))
    (a49 : -(h 4) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (16/71 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-16/71 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2544 h delta _ctx _hno a37 f0
  by_cases p1 : h 0 ≤ (5/34 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/34 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2545 h delta _ctx _hno a23 a36 a42 a49 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2546 h delta _ctx _hno a23 a28 a45 f2
  by_cases p3 : h 2 ≤ (3/25 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2547 h delta _ctx _hno a23 a28 a36 a42 a45 f3
  by_cases p4 : h 3 ≤ (5/44 : ℝ)
  swap
  · have f4 : -(h 3) < (-5/44 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2548 h delta _ctx _hno a36 a42 a45 a49 f4
  apply _hno 40
  change (((2 : ℝ) * (delta)) ≤ (16/71 : ℝ)) ∧ (h 0 ≤ (5/34 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (5/44 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_2542 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a36 : -(h 1) < (-3/22 : ℝ))
    (a45 : -(h 0) < (-8/55 : ℝ))
    (a48 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (19/69 : ℝ) * _ctx.min + (121/207 : ℝ) * _ctx.lower + (7/207 : ℝ) * a23 + (8/207 : ℝ) * a28 + (64/207 : ℝ) * a36 + (64/207 : ℝ) * a45 + (64/207 : ℝ) * a48 + (64/207 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2541 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a36 : -(h 1) < (-3/22 : ℝ))
    (a47 : -(h 0) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (24/1097 : ℝ) * _ctx.lower + (4/1097 : ℝ) * _ctx.fail1 + (24/1097 : ℝ) * a23 + (171/1097 : ℝ) * a25 + (3/1097 : ℝ) * a28 + (24/1097 : ℝ) * a36 + (1042/1097 : ℝ) * a47 + (24/1097 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2540 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a37 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a46 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a37 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2539 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a36 : -(h 1) < (-3/22 : ℝ))
    (a37 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    (a45 : -(h 0) < (-8/55 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2540 h delta _ctx _hno a37 f0
  by_cases p1 : h 0 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2541 h delta _ctx _hno a23 a25 a28 a36 f1
  by_cases p2 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2542 h delta _ctx _hno a23 a28 a36 a45 f2
  by_cases p3 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f3 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2543 h delta _ctx _hno a23 a28 a36 a37 a42 a45 f3
  apply _hno 8
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_2538 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a37 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a44 : ((-2 : ℝ) * (delta)) < (-7/31 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a37 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2537 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a36 : -(h 1) < (-3/22 : ℝ))
    (a37 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/31 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/31 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2538 h delta _ctx _hno a37 f0
  by_cases p1 : h 0 ≤ (8/55 : ℝ)
  swap
  · have f1 : -(h 0) < (-8/55 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2539 h delta _ctx _hno a23 a25 a28 a36 a37 a42 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2549 h delta _ctx _hno a23 a28 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2550 h delta _ctx _hno a23 a28 a30 a36 a42 f3
  by_cases p4 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2551 h delta _ctx _hno a28 a30 a36 a37 a42 p1 f4
  by_cases p5 : h 5 ≤ (6/53 : ℝ)
  swap
  · have f5 : -(h 5) < (-6/53 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_2562 h delta _ctx _hno a30 a36 f5
  apply _hno 39
  change (((2 : ℝ) * (delta)) ≤ (7/31 : ℝ)) ∧ (h 0 ≤ (8/55 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (6/53 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_2536 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a36 : -(h 1) < (-3/22 : ℝ))
    (a37 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a40 : h 2 ≤ (1/8 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2537 h delta _ctx _hno a23 a25 a28 a30 a36 a37 a42
  by_cases p1 : h 0 ≤ (25/173 : ℝ)
  swap
  · have f1 : -(h 0) < (-25/173 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2563 h delta _ctx _hno a23 a25 a28 a36 a42 p0 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2579 h delta _ctx _hno a23 a28 f2
  by_cases p3 : h 2 ≤ (3/22 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2580 h delta _ctx _hno a40 f3
  by_cases p4 : h 3 ≤ (7/61 : ℝ)
  swap
  · have f4 : -(h 3) < (-7/61 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2581 h delta _ctx _hno a28 a30 a36 a42 p0 p1 f4
  by_cases p5 : h 4 ≤ (5/44 : ℝ)
  swap
  · have f5 : -(h 4) < (-5/44 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_2586 h delta _ctx _hno a30 a36 a42 f5
  by_cases p6 : h 5 ≤ (6/53 : ℝ)
  swap
  · have f6 : -(h 5) < (-6/53 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact upper_node_2587 h delta _ctx _hno a30 a36 f6
  apply _hno 27
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (25/173 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (3/22 : ℝ)) ∧ (h 3 ≤ (7/61 : ℝ)) ∧ (h 4 ≤ (5/44 : ℝ)) ∧ (h 5 ≤ (6/53 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem upper_node_2535 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a36 : -(h 1) < (-3/22 : ℝ))
    (a41 : -(h 4) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.order3 + (6/23 : ℝ) * _ctx.min + (12/23 : ℝ) * _ctx.lower + (1/23 : ℝ) * _ctx.fail1 + (4/23 : ℝ) * a30 + (6/23 : ℝ) * a36 + (12/23 : ℝ) * a41 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2534 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a36 : -(h 1) < (-3/22 : ℝ))
    (a40 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (19/69 : ℝ) * _ctx.min + (121/207 : ℝ) * _ctx.lower + (7/207 : ℝ) * a23 + (8/207 : ℝ) * a28 + (64/207 : ℝ) * a30 + (64/207 : ℝ) * a36 + (64/207 : ℝ) * a40 + (64/207 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2533 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a39 : -(h 1) < (-6/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (128/397 : ℝ) * _ctx.order0 + (171/397 : ℝ) * _ctx.min + (363/397 : ℝ) * _ctx.lower + (32/397 : ℝ) * _ctx.fail1 + (21/397 : ℝ) * a23 + (24/397 : ℝ) * a28 + (320/397 : ℝ) * a39 + (192/397 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2532 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a36 : -(h 1) < (-3/22 : ℝ))
    (a38 : -(h 0) < (-4/27 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (24/1097 : ℝ) * _ctx.lower + (4/1097 : ℝ) * _ctx.fail1 + (24/1097 : ℝ) * a23 + (171/1097 : ℝ) * a25 + (3/1097 : ℝ) * a28 + (24/1097 : ℝ) * a36 + (1042/1097 : ℝ) * a38 + (24/1097 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2531 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a36 : -(h 1) < (-3/22 : ℝ))
    (a37 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a47 : -(h 5) < (-6/53 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/16 : ℝ) * _ctx.order3 + (3/8 : ℝ) * _ctx.order4 + (1/32 : ℝ) * _ctx.fail1 + (1/8 : ℝ) * a30 + (3/16 : ℝ) * a36 + (3/32 : ℝ) * a37 + (9/16 : ℝ) * a47 + (3/16 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2530 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a36 : -(h 1) < (-3/22 : ℝ))
    (a37 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a41 : -(h 4) < (-1/9 : ℝ))
    (a46 : -(h 3) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.min + (1/29 : ℝ) * _ctx.fail1 + (4/29 : ℝ) * a30 + (6/29 : ℝ) * a36 + (6/29 : ℝ) * a37 + (6/29 : ℝ) * a41 + (6/29 : ℝ) * a46 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2529 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a36 : -(h 1) < (-3/22 : ℝ))
    (a37 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a45 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (114/535 : ℝ) * _ctx.min + (14/535 : ℝ) * a23 + (16/535 : ℝ) * a28 + (128/535 : ℝ) * a30 + (128/535 : ℝ) * a36 + (121/535 : ℝ) * a37 + (128/535 : ℝ) * a45 + (128/535 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2528 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a37 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a44 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (342/1157 : ℝ) * _ctx.min + (64/1157 : ℝ) * _ctx.fail1 + (42/1157 : ℝ) * a23 + (48/1157 : ℝ) * a28 + (256/1157 : ℝ) * a30 + (363/1157 : ℝ) * a37 + (384/1157 : ℝ) * a44 + (384/1157 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2527 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a36 : -(h 1) < (-3/22 : ℝ))
    (a37 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a41 : -(h 4) < (-1/9 : ℝ))
    (a43 : -(h 0) < (-8/55 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (42/187 : ℝ) * _ctx.min + (8/187 : ℝ) * _ctx.fail1 + (6/187 : ℝ) * a23 + (48/187 : ℝ) * a36 + (45/187 : ℝ) * a37 + (48/187 : ℝ) * a41 + (32/187 : ℝ) * a43 + (48/187 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2526 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a42 : ((-2 : ℝ) * (delta)) < (-7/31 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * a14 + (1/5 : ℝ) * a30 + (4/5 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2525 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a36 : -(h 1) < (-3/22 : ℝ))
    (a37 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a41 : -(h 4) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/31 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/31 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2526 h delta _ctx _hno a14 a30 f0
  by_cases p1 : h 0 ≤ (8/55 : ℝ)
  swap
  · have f1 : -(h 0) < (-8/55 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2527 h delta _ctx _hno a23 a36 a37 a41 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2528 h delta _ctx _hno a23 a28 a30 a37 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2529 h delta _ctx _hno a23 a28 a30 a36 a37 f3
  by_cases p4 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2530 h delta _ctx _hno a30 a36 a37 a41 f4
  by_cases p5 : h 5 ≤ (6/53 : ℝ)
  swap
  · have f5 : -(h 5) < (-6/53 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_2531 h delta _ctx _hno a30 a36 a37 f5
  apply _hno 39
  change (((2 : ℝ) * (delta)) ≤ (7/31 : ℝ)) ∧ (h 0 ≤ (8/55 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (6/53 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_2524 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a36 : -(h 1) < (-3/22 : ℝ))
    (a37 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a40 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (114/535 : ℝ) * _ctx.min + (14/535 : ℝ) * a23 + (16/535 : ℝ) * a28 + (128/535 : ℝ) * a30 + (128/535 : ℝ) * a36 + (121/535 : ℝ) * a37 + (128/535 : ℝ) * a40 + (128/535 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2523 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a36 : -(h 1) < (-3/22 : ℝ))
    (a37 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a39 : -(h 0) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/1109 : ℝ) * _ctx.fail1 + (24/1109 : ℝ) * a23 + (171/1109 : ℝ) * a25 + (3/1109 : ℝ) * a28 + (24/1109 : ℝ) * a36 + (12/1109 : ℝ) * a37 + (1042/1109 : ℝ) * a39 + (24/1109 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2522 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a38 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * a14 + (1/5 : ℝ) * a30 + (4/5 : ℝ) * a38
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2521 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a36 : -(h 1) < (-3/22 : ℝ))
    (a37 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2522 h delta _ctx _hno a14 a30 f0
  by_cases p1 : h 0 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2523 h delta _ctx _hno a23 a25 a28 a36 a37 f1
  by_cases p2 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2524 h delta _ctx _hno a23 a28 a30 a36 a37 f2
  by_cases p3 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f3 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2525 h delta _ctx _hno a14 a23 a28 a30 a36 a37 f3
  apply _hno 8
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_2520 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a36 : -(h 1) < (-3/22 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2521 h delta _ctx _hno a14 a23 a25 a28 a30 a36 f0
  by_cases p1 : h 0 ≤ (4/27 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/27 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2532 h delta _ctx _hno a23 a25 a28 a36 f1
  by_cases p2 : h 1 ≤ (6/41 : ℝ)
  swap
  · have f2 : -(h 1) < (-6/41 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2533 h delta _ctx _hno a23 a28 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2534 h delta _ctx _hno a23 a28 a30 a36 f3
  by_cases p4 : h 4 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 4) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2535 h delta _ctx _hno a30 a36 f4
  by_cases p5 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_2536 h delta _ctx _hno a23 a25 a28 a30 a36 p0 p3 f5
  apply _hno 9
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (4/27 : ℝ)) ∧ (h 1 ≤ (6/41 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_2519 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a35 : -(h 0) < (-11/73 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/55 : ℝ) * a20 + (1/55 : ℝ) * a23 + (8/55 : ℝ) * a25 + (54/55 : ℝ) * a35
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2518 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * a14 + (1/5 : ℝ) * a30 + (4/5 : ℝ) * a34
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2517 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a20 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a33 : -(h 1) < (-9/70 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2518 h delta _ctx _hno a14 a30 f0
  by_cases p1 : h 0 ≤ (11/73 : ℝ)
  swap
  · have f1 : -(h 0) < (-11/73 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2519 h delta _ctx _hno a20 a23 a25 f1
  by_cases p2 : h 1 ≤ (3/22 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2520 h delta _ctx _hno a14 a23 a25 a28 a30 f2
  by_cases p3 : h 2 ≤ (5/41 : ℝ)
  swap
  · have f3 : -(h 2) < (-5/41 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2588 h delta _ctx _hno a14 a20 a23 a25 a28 a30 a33 p2 f3
  by_cases p4 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2788 h delta _ctx _hno a14 a20 a23 a25 a28 a30 a33 p2 p3 f4
  by_cases p5 : h 4 ≤ (5/44 : ℝ)
  swap
  · have f5 : -(h 4) < (-5/44 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_3058 h delta _ctx _hno a14 a20 a23 a25 a30 a33 p2 p3 p4 f5
  by_cases p6 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f6 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact upper_node_3088 h delta _ctx _hno a14 a20 a23 a25 a28 a30 a33 p2 p3 p4 p5 f6
  apply _hno 122
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (11/73 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 2 ≤ (5/41 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 4 ≤ (5/44 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem upper_node_2516 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a32 : -(h 0) < (-7/45 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/55 : ℝ) * a20 + (1/55 : ℝ) * a23 + (8/55 : ℝ) * a25 + (54/55 : ℝ) * a32
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2515 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a31 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * a14 + (1/5 : ℝ) * a30 + (4/5 : ℝ) * a31
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2514 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a20 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2515 h delta _ctx _hno a14 a30 f0
  by_cases p1 : h 0 ≤ (7/45 : ℝ)
  swap
  · have f1 : -(h 0) < (-7/45 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2516 h delta _ctx _hno a20 a23 a25 f1
  by_cases p2 : h 1 ≤ (9/70 : ℝ)
  swap
  · have f2 : -(h 1) < (-9/70 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2517 h delta _ctx _hno a14 a20 a23 a25 a28 a30 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3159 h delta _ctx _hno a13 a14 a20 a23 a25 a28 a30 p2 f3
  by_cases p4 : h 4 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 4) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3205 h delta _ctx _hno a13 a14 a20 a23 a25 a28 a30 p2 p3 f4
  apply _hno 55
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (7/45 : ℝ)) ∧ (h 1 ≤ (9/70 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (4/35 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_2513 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a29 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/24 : ℝ) * _ctx.fail3 + (1/4 : ℝ) * a14 + (23/24 : ℝ) * a29
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2512 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a20 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2513 h delta _ctx _hno a14 f0
  by_cases p1 : h 0 ≤ (1/7 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2514 h delta _ctx _hno a13 a14 a20 a23 a25 a28 f1
  by_cases p2 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3395 h delta _ctx _hno a13 a14 a23 p1 f2
  by_cases p3 : h 4 ≤ (4/35 : ℝ)
  swap
  · have f3 : -(h 4) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3581 h delta _ctx _hno a13 a14 p1 p2 f3
  apply _hno 97
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (4/35 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_2511 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a27 : ((-6 : ℝ) * (h 2)) + -(h 3) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (16/9 : ℝ) * _ctx.order0 + (32/9 : ℝ) * _ctx.order1 + (16/9 : ℝ) * _ctx.order4 + (31/9 : ℝ) * _ctx.min + (47/9 : ℝ) * _ctx.lower + (1/9 : ℝ) * a23 + (8/9 : ℝ) * a27 + (16/9 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2510 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : h 0 + ((6 : ℝ) * (h 1)) ≤ (1 : ℝ))
    (a26 : ((-6 : ℝ) * (h 1)) + -(h 3) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (17/14 : ℝ) * _ctx.order0 + (1/2 : ℝ) * _ctx.order2 + (1/2 : ℝ) * _ctx.order4 + (1 : ℝ) * _ctx.min + (3/2 : ℝ) * _ctx.lower + (5/7 : ℝ) * a15 + (1 : ℝ) * a26 + (1/2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2509 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a35 : -(h 5) < (-2/19 : ℝ))
    (a38 : -(h 1) < (-1/8 : ℝ))
    (a48 : -(h 4) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (16/69 : ℝ) * _ctx.order3 + (1/23 : ℝ) * _ctx.fail1 + (1/23 : ℝ) * a13 + (2/69 : ℝ) * a25 + (6/23 : ℝ) * a35 + (3/23 : ℝ) * a38 + (34/69 : ℝ) * a48 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2508 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a38 : -(h 1) < (-1/8 : ℝ))
    (a43 : -(h 4) < (-4/35 : ℝ))
    (a47 : -(h 2) < (-3/25 : ℝ))
    (a52 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (5/28 : ℝ) * _ctx.order3 + (1/28 : ℝ) * a13 + (1/28 : ℝ) * a25 + (3/28 : ℝ) * a38 + (11/28 : ℝ) * a43 + (3/14 : ℝ) * a47 + (3/14 : ℝ) * a52 + (3/14 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2507 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a38 : -(h 1) < (-1/8 : ℝ))
    (a43 : -(h 4) < (-4/35 : ℝ))
    (a47 : -(h 2) < (-3/25 : ℝ))
    (a51 : -(h 3) < (-3/26 : ℝ))
    (a57 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/28 : ℝ) * a13 + (1/28 : ℝ) * a25 + (3/28 : ℝ) * a38 + (3/14 : ℝ) * a43 + (3/14 : ℝ) * a47 + (5/28 : ℝ) * a51 + (3/14 : ℝ) * a57 + (3/14 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2506 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a35 : -(h 5) < (-2/19 : ℝ))
    (a38 : -(h 1) < (-1/8 : ℝ))
    (a47 : -(h 2) < (-3/25 : ℝ))
    (a56 : -(h 4) < (-5/43 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (5/28 : ℝ) * _ctx.order3 + (1/28 : ℝ) * a13 + (1/28 : ℝ) * a25 + (3/14 : ℝ) * a35 + (3/28 : ℝ) * a38 + (3/14 : ℝ) * a47 + (11/28 : ℝ) * a56 + (3/14 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2505 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a35 : -(h 5) < (-2/19 : ℝ))
    (a38 : -(h 1) < (-1/8 : ℝ))
    (a43 : -(h 4) < (-4/35 : ℝ))
    (a47 : -(h 2) < (-3/25 : ℝ))
    (a55 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/28 : ℝ) * a13 + (1/28 : ℝ) * a25 + (3/14 : ℝ) * a35 + (3/28 : ℝ) * a38 + (3/14 : ℝ) * a43 + (3/14 : ℝ) * a47 + (5/28 : ℝ) * a55 + (3/14 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2504 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a35 : -(h 5) < (-2/19 : ℝ))
    (a43 : -(h 4) < (-4/35 : ℝ))
    (a47 : -(h 2) < (-3/25 : ℝ))
    (a51 : -(h 3) < (-3/26 : ℝ))
    (a54 : -(h 1) < (-6/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.lower + (1/30 : ℝ) * a25 + (1/5 : ℝ) * a35 + (1/5 : ℝ) * a43 + (1/5 : ℝ) * a47 + (1/6 : ℝ) * a51 + (1/5 : ℝ) * a54 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2503 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : h 0 ≤ (4/27 : ℝ))
    (a53 : -(h 0) < (-10/67 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a53
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2502 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a52 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a52
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2501 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a30 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a31 : h 0 ≤ (4/27 : ℝ))
    (a35 : -(h 5) < (-2/19 : ℝ))
    (a38 : -(h 1) < (-1/8 : ℝ))
    (a43 : -(h 4) < (-4/35 : ℝ))
    (a47 : -(h 2) < (-3/25 : ℝ))
    (a51 : -(h 3) < (-3/26 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2502 h delta _ctx _hno a30 f0
  by_cases p1 : h 0 ≤ (10/67 : ℝ)
  swap
  · have f1 : -(h 0) < (-10/67 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2503 h delta _ctx _hno a31 f1
  by_cases p2 : h 1 ≤ (6/47 : ℝ)
  swap
  · have f2 : -(h 1) < (-6/47 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2504 h delta _ctx _hno a25 a35 a43 a47 a51 f2
  by_cases p3 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2505 h delta _ctx _hno a13 a25 a35 a38 a43 a47 f3
  by_cases p4 : h 4 ≤ (5/43 : ℝ)
  swap
  · have f4 : -(h 4) < (-5/43 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2506 h delta _ctx _hno a13 a25 a35 a38 a47 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_2507 h delta _ctx _hno a13 a25 a38 a43 a47 a51 f5
  apply _hno 130
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (10/67 : ℝ)) ∧ (h 1 ≤ (6/47 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (5/43 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_2500 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a46 : h 1 ≤ (5/39 : ℝ))
    (a50 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a46 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2499 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : h 0 ≤ (4/27 : ℝ))
    (a49 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2498 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a48 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2497 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a30 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a31 : h 0 ≤ (4/27 : ℝ))
    (a35 : -(h 5) < (-2/19 : ℝ))
    (a38 : -(h 1) < (-1/8 : ℝ))
    (a43 : -(h 4) < (-4/35 : ℝ))
    (a46 : h 1 ≤ (5/39 : ℝ))
    (a47 : -(h 2) < (-3/25 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2498 h delta _ctx _hno a30 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2499 h delta _ctx _hno a31 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2500 h delta _ctx _hno a46 f2
  by_cases p3 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f3 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2501 h delta _ctx _hno a13 a25 a30 a31 a35 a38 a43 a47 f3
  by_cases p4 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2508 h delta _ctx _hno a13 a25 a38 a43 a47 f4
  apply _hno 19
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_2496 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a43 : -(h 4) < (-4/35 : ℝ))
    (a46 : -(h 1) < (-5/39 : ℝ))
    (a51 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (16/75 : ℝ) * _ctx.order3 + (6/25 : ℝ) * _ctx.lower + (1/25 : ℝ) * _ctx.fail1 + (2/75 : ℝ) * a25 + (34/75 : ℝ) * a43 + (6/25 : ℝ) * a46 + (6/25 : ℝ) * a51 + (6/25 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2495 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a43 : -(h 4) < (-4/35 : ℝ))
    (a46 : -(h 1) < (-5/39 : ℝ))
    (a50 : -(h 3) < (-3/26 : ℝ))
    (a55 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/25 : ℝ) * _ctx.lower + (1/25 : ℝ) * _ctx.fail1 + (2/75 : ℝ) * a25 + (6/25 : ℝ) * a43 + (6/25 : ℝ) * a46 + (16/75 : ℝ) * a50 + (6/25 : ℝ) * a55 + (6/25 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2494 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a35 : -(h 5) < (-2/19 : ℝ))
    (a46 : -(h 1) < (-5/39 : ℝ))
    (a54 : -(h 2) < (-2/17 : ℝ))
    (a60 : -(h 4) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.lower + (1/30 : ℝ) * a25 + (1/5 : ℝ) * a35 + (1/5 : ℝ) * a46 + (1/5 : ℝ) * a54 + (11/30 : ℝ) * a60 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2493 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a35 : -(h 5) < (-2/19 : ℝ))
    (a43 : -(h 4) < (-4/35 : ℝ))
    (a46 : -(h 1) < (-5/39 : ℝ))
    (a59 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/25 : ℝ) * _ctx.lower + (1/25 : ℝ) * _ctx.fail1 + (2/75 : ℝ) * a25 + (6/25 : ℝ) * a35 + (6/25 : ℝ) * a43 + (6/25 : ℝ) * a46 + (16/75 : ℝ) * a59 + (6/25 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2492 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a35 : -(h 5) < (-2/19 : ℝ))
    (a43 : -(h 4) < (-4/35 : ℝ))
    (a46 : -(h 1) < (-5/39 : ℝ))
    (a50 : -(h 3) < (-3/26 : ℝ))
    (a58 : -(h 2) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.lower + (1/30 : ℝ) * a25 + (1/5 : ℝ) * a35 + (1/5 : ℝ) * a43 + (1/5 : ℝ) * a46 + (1/6 : ℝ) * a50 + (1/5 : ℝ) * a58 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2491 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a41 : h 1 ≤ (9/70 : ℝ))
    (a57 : -(h 1) < (-4/31 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a41 + (1 : ℝ) * a57
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2490 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : h 0 ≤ (4/27 : ℝ))
    (a56 : -(h 0) < (-3/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a56
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2489 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a55 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a55
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2488 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a30 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a31 : h 0 ≤ (4/27 : ℝ))
    (a35 : -(h 5) < (-2/19 : ℝ))
    (a41 : h 1 ≤ (9/70 : ℝ))
    (a43 : -(h 4) < (-4/35 : ℝ))
    (a46 : -(h 1) < (-5/39 : ℝ))
    (a50 : -(h 3) < (-3/26 : ℝ))
    (a54 : -(h 2) < (-2/17 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2489 h delta _ctx _hno a30 f0
  by_cases p1 : h 0 ≤ (3/19 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/19 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2490 h delta _ctx _hno a31 f1
  by_cases p2 : h 1 ≤ (4/31 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/31 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2491 h delta _ctx _hno a41 f2
  by_cases p3 : h 2 ≤ (3/25 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2492 h delta _ctx _hno a25 a35 a43 a46 a50 f3
  by_cases p4 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2493 h delta _ctx _hno a25 a35 a43 a46 f4
  by_cases p5 : h 4 ≤ (3/26 : ℝ)
  swap
  · have f5 : -(h 4) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_2494 h delta _ctx _hno a25 a35 a46 a54 f5
  apply _hno 113
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (4/31 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (3/26 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_2487 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a41 : h 1 ≤ (9/70 : ℝ))
    (a53 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a41 + (1 : ℝ) * a53
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2486 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : h 0 ≤ (4/27 : ℝ))
    (a52 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a52
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2485 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a51 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a51
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2484 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a30 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a31 : h 0 ≤ (4/27 : ℝ))
    (a35 : -(h 5) < (-2/19 : ℝ))
    (a41 : h 1 ≤ (9/70 : ℝ))
    (a43 : -(h 4) < (-4/35 : ℝ))
    (a46 : -(h 1) < (-5/39 : ℝ))
    (a50 : -(h 3) < (-3/26 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2485 h delta _ctx _hno a30 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2486 h delta _ctx _hno a31 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2487 h delta _ctx _hno a41 f2
  by_cases p3 : h 2 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2488 h delta _ctx _hno a25 a30 a31 a35 a41 a43 a46 a50 f3
  by_cases p4 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2495 h delta _ctx _hno a25 a43 a46 a50 f4
  apply _hno 118
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_2483 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a41 : h 1 ≤ (9/70 : ℝ))
    (a49 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a41 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2482 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : h 0 ≤ (4/27 : ℝ))
    (a48 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2481 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a47 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2480 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a30 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a31 : h 0 ≤ (4/27 : ℝ))
    (a35 : -(h 5) < (-2/19 : ℝ))
    (a41 : h 1 ≤ (9/70 : ℝ))
    (a43 : -(h 4) < (-4/35 : ℝ))
    (a46 : -(h 1) < (-5/39 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2481 h delta _ctx _hno a30 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2482 h delta _ctx _hno a31 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2483 h delta _ctx _hno a41 f2
  by_cases p3 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f3 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2484 h delta _ctx _hno a25 a30 a31 a35 a41 a43 a46 f3
  by_cases p4 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2496 h delta _ctx _hno a25 a43 a46 f4
  apply _hno 19
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_2479 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : h 0 ≤ (4/27 : ℝ))
    (a45 : -(h 0) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2478 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a44 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2477 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a30 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a31 : h 0 ≤ (4/27 : ℝ))
    (a35 : -(h 5) < (-2/19 : ℝ))
    (a38 : -(h 1) < (-1/8 : ℝ))
    (a41 : h 1 ≤ (9/70 : ℝ))
    (a43 : -(h 4) < (-4/35 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2478 h delta _ctx _hno a30 f0
  by_cases p1 : h 0 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2479 h delta _ctx _hno a31 f1
  by_cases p2 : h 1 ≤ (5/39 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/39 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2480 h delta _ctx _hno a25 a30 a31 a35 a41 a43 f2
  by_cases p3 : h 2 ≤ (3/25 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2497 h delta _ctx _hno a13 a25 a30 a31 a35 a38 a43 p2 f3
  by_cases p4 : h 4 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 4) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2509 h delta _ctx _hno a13 a25 a35 a38 f4
  apply _hno 135
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 1 ≤ (5/39 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_2476 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a28 : h 2 ≤ (1/8 : ℝ))
    (a42 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a28 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2475 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a41 : -(h 1) < (-9/70 : ℝ))
    (a46 : -(h 5) < (-1/9 : ℝ))
    (a52 : -(h 4) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (16/75 : ℝ) * _ctx.order3 + (6/25 : ℝ) * _ctx.lower + (1/25 : ℝ) * _ctx.fail1 + (2/75 : ℝ) * a25 + (6/25 : ℝ) * a41 + (6/25 : ℝ) * a46 + (34/75 : ℝ) * a52 + (6/25 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2474 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a45 : h 3 ≤ (3/26 : ℝ))
    (a51 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a45 + (1 : ℝ) * a51
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2473 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a29 : -(h 4) < (-1/9 : ℝ))
    (a41 : -(h 1) < (-9/70 : ℝ))
    (a46 : -(h 5) < (-1/9 : ℝ))
    (a50 : -(h 2) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/25 : ℝ) * _ctx.lower + (1/40 : ℝ) * a23 + (1/25 : ℝ) * a25 + (6/25 : ℝ) * a29 + (6/25 : ℝ) * a41 + (43/200 : ℝ) * a46 + (6/25 : ℝ) * a50 + (6/25 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2472 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a46 : -(h 5) < (-1/9 : ℝ))
    (a49 : -(h 1) < (-4/31 : ℝ))
    (a55 : -(h 4) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (16/75 : ℝ) * _ctx.order3 + (6/25 : ℝ) * _ctx.lower + (1/25 : ℝ) * _ctx.fail1 + (2/75 : ℝ) * a25 + (6/25 : ℝ) * a46 + (6/25 : ℝ) * a49 + (34/75 : ℝ) * a55 + (6/25 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2471 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a45 : h 3 ≤ (3/26 : ℝ))
    (a54 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a45 + (1 : ℝ) * a54
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2470 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a29 : -(h 4) < (-1/9 : ℝ))
    (a46 : -(h 5) < (-1/9 : ℝ))
    (a49 : -(h 1) < (-4/31 : ℝ))
    (a53 : -(h 2) < (-12/101 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/25 : ℝ) * _ctx.lower + (1/40 : ℝ) * a23 + (1/25 : ℝ) * a25 + (6/25 : ℝ) * a29 + (43/200 : ℝ) * a46 + (6/25 : ℝ) * a49 + (6/25 : ℝ) * a53 + (6/25 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2469 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a29 : -(h 4) < (-1/9 : ℝ))
    (a46 : -(h 5) < (-1/9 : ℝ))
    (a52 : -(h 1) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (18/59 : ℝ) * _ctx.lower + (3/59 : ℝ) * _ctx.fail1 + (2/59 : ℝ) * a23 + (2/59 : ℝ) * a25 + (18/59 : ℝ) * a29 + (16/59 : ℝ) * a46 + (18/59 : ℝ) * a52 + (18/59 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2468 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : h 0 ≤ (4/27 : ℝ))
    (a51 : -(h 0) < (-3/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a51
  exact (lt_irrefl (0 : ℝ)) hbad

end RealPinwheel.WeakSevenBandData
