import Pinwheel.WeakSevenBandData.CoverChunks.Upper039

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem upper_node_1107 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 0) + ((-6 : ℝ) * (h 1)) < (-1 : ℝ))
    (a31 : -(h 3) < (-1/9 : ℝ))
    (a33 : -(h 0) < (-5/33 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/10 : ℝ) * _ctx.order4 + (3/5 : ℝ) * _ctx.min + (1/20 : ℝ) * _ctx.fail1 + (1/20 : ℝ) * a15 + (3/10 : ℝ) * a31 + (3/20 : ℝ) * a33 + (9/20 : ℝ) * a34 + (3/10 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1106 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 0) + ((-6 : ℝ) * (h 1)) < (-1 : ℝ))
    (a17 : h 0 ≤ (4/25 : ℝ))
    (a29 : h 1 ≤ (1/7 : ℝ))
    (a31 : -(h 3) < (-1/9 : ℝ))
    (a33 : -(h 0) < (-5/33 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1107 h delta _ctx _hno a15 a31 a33 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1108 h delta _ctx _hno a17 f1
  by_cases p2 : h 1 ≤ (5/31 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/31 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1109 h delta _ctx _hno a29 f2
  by_cases p3 : h 2 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1110 h delta _ctx _hno a15 a31 a33 f3
  by_cases p4 : h 4 ≤ (3/28 : ℝ)
  swap
  · have f4 : -(h 4) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1111 h delta _ctx _hno a15 a31 a33 f4
  by_cases p5 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1112 h delta _ctx _hno a15 a31 a33 f5
  apply _hno 103
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (5/31 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (3/28 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_1105 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a15 : -(h 0) + ((-6 : ℝ) * (h 1)) < (-1 : ℝ))
    (a22 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a24 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a32 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/443 : ℝ) * _ctx.order4 + (1/443 : ℝ) * _ctx.fail1 + (105/443 : ℝ) * a14 + (1/443 : ℝ) * a15 + (6/443 : ℝ) * a22 + (12/443 : ℝ) * a24 + (423/443 : ℝ) * a32 + (6/443 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1104 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a15 : -(h 0) + ((-6 : ℝ) * (h 1)) < (-1 : ℝ))
    (a17 : h 0 ≤ (4/25 : ℝ))
    (a22 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a24 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a29 : h 1 ≤ (1/7 : ℝ))
    (a31 : -(h 3) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1105 h delta _ctx _hno a14 a15 a22 a24 f0
  by_cases p1 : h 0 ≤ (5/33 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/33 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1106 h delta _ctx _hno a15 a17 a29 a31 f1
  by_cases p2 : h 1 ≤ (3/20 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1113 h delta _ctx _hno a29 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1114 h delta _ctx _hno a15 a24 a31 f3
  by_cases p4 : h 3 ≤ (7/57 : ℝ)
  swap
  · have f4 : -(h 3) < (-7/57 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1115 h delta _ctx _hno a15 a24 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1116 h delta _ctx _hno a15 a24 a31 f5
  apply _hno 87
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (5/33 : ℝ)) ∧ (h 1 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (7/57 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_1103 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 0) + ((-6 : ℝ) * (h 1)) < (-1 : ℝ))
    (a20 : -(h 3) < (-3/28 : ℝ))
    (a24 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a30 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (36/83 : ℝ) * _ctx.order4 + (67/83 : ℝ) * _ctx.min + (103/83 : ℝ) * _ctx.lower + (6/83 : ℝ) * a15 + (36/83 : ℝ) * a20 + (5/83 : ℝ) * a24 + (36/83 : ℝ) * a30 + (36/83 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1102 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 0) + ((-6 : ℝ) * (h 1)) < (-1 : ℝ))
    (a24 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a35 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (12/29 : ℝ) * _ctx.order3 + (11/29 : ℝ) * _ctx.min + (23/29 : ℝ) * _ctx.lower + (2/29 : ℝ) * _ctx.fail1 + (2/29 : ℝ) * a15 + (1/29 : ℝ) * a24 + (24/29 : ℝ) * a35 + (12/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1101 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 0) + ((-6 : ℝ) * (h 1)) < (-1 : ℝ))
    (a24 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a34 : -(h 3) < (-7/57 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (12/17 : ℝ) * _ctx.order4 + (23/17 : ℝ) * _ctx.min + (35/17 : ℝ) * _ctx.lower + (2/17 : ℝ) * _ctx.fail1 + (2/17 : ℝ) * a15 + (1/17 : ℝ) * a24 + (12/17 : ℝ) * a34 + (12/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1100 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : -(h 3) < (-3/28 : ℝ))
    (a24 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a29 : -(h 1) < (-1/7 : ℝ))
    (a33 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/19 : ℝ) * _ctx.order4 + (11/19 : ℝ) * _ctx.min + (17/19 : ℝ) * _ctx.lower + (6/19 : ℝ) * a20 + (1/19 : ℝ) * a24 + (6/19 : ℝ) * a29 + (6/19 : ℝ) * a33 + (6/19 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1099 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : -(h 3) < (-3/28 : ℝ))
    (a24 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a32 : -(h 1) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (18/41 : ℝ) * _ctx.order4 + (34/41 : ℝ) * _ctx.min + (52/41 : ℝ) * _ctx.lower + (3/41 : ℝ) * _ctx.fail1 + (18/41 : ℝ) * a20 + (2/41 : ℝ) * a24 + (18/41 : ℝ) * a32 + (18/41 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1098 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : -(h 1) < (-1/7 : ℝ))
    (a31 : -(h 0) < (-5/33 : ℝ))
    (a37 : -(h 4) < (-5/46 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.order3 + (6/23 : ℝ) * _ctx.min + (12/23 : ℝ) * _ctx.lower + (1/23 : ℝ) * _ctx.fail1 + (6/23 : ℝ) * a29 + (4/23 : ℝ) * a31 + (12/23 : ℝ) * a37 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1097 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : -(h 1) < (-1/7 : ℝ))
    (a31 : -(h 0) < (-5/33 : ℝ))
    (a36 : -(h 3) < (-6/55 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.order4 + (6/29 : ℝ) * _ctx.lower + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a29 + (4/29 : ℝ) * a31 + (6/29 : ℝ) * a36 + (12/29 : ℝ) * a42 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1096 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : -(h 1) < (-1/7 : ℝ))
    (a31 : -(h 0) < (-5/33 : ℝ))
    (a36 : -(h 3) < (-6/55 : ℝ))
    (a41 : -(h 4) < (-3/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.min + (12/23 : ℝ) * _ctx.lower + (1/23 : ℝ) * _ctx.fail1 + (6/23 : ℝ) * a29 + (4/23 : ℝ) * a31 + (6/23 : ℝ) * a36 + (6/23 : ℝ) * a41 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1095 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : -(h 1) < (-1/7 : ℝ))
    (a31 : -(h 0) < (-5/33 : ℝ))
    (a36 : -(h 3) < (-6/55 : ℝ))
    (a40 : -(h 2) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.order4 + (1/2 : ℝ) * _ctx.min + (3/4 : ℝ) * _ctx.lower + (1/4 : ℝ) * a29 + (1/4 : ℝ) * a31 + (1/4 : ℝ) * a36 + (1/4 : ℝ) * a40 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1094 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a34 : h 1 ≤ (8/55 : ℝ))
    (a39 : -(h 1) < (-5/31 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1093 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : h 0 ≤ (2/13 : ℝ))
    (a38 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a38
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1092 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : -(h 1) < (-1/7 : ℝ))
    (a31 : -(h 0) < (-5/33 : ℝ))
    (a36 : -(h 3) < (-6/55 : ℝ))
    (a37 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/13 : ℝ) * _ctx.order4 + (6/13 : ℝ) * _ctx.min + (1/26 : ℝ) * _ctx.fail1 + (3/13 : ℝ) * a29 + (2/13 : ℝ) * a31 + (3/13 : ℝ) * a36 + (9/26 : ℝ) * a37 + (3/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1091 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : -(h 1) < (-1/7 : ℝ))
    (a31 : -(h 0) < (-5/33 : ℝ))
    (a33 : h 0 ≤ (2/13 : ℝ))
    (a34 : h 1 ≤ (8/55 : ℝ))
    (a36 : -(h 3) < (-6/55 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1092 h delta _ctx _hno a29 a31 a36 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1093 h delta _ctx _hno a33 f1
  by_cases p2 : h 1 ≤ (5/31 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/31 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1094 h delta _ctx _hno a34 f2
  by_cases p3 : h 2 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1095 h delta _ctx _hno a29 a31 a36 f3
  by_cases p4 : h 4 ≤ (3/28 : ℝ)
  swap
  · have f4 : -(h 4) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1096 h delta _ctx _hno a29 a31 a36 f4
  by_cases p5 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1097 h delta _ctx _hno a29 a31 a36 f5
  apply _hno 103
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (5/31 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (3/28 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_1090 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 0) + ((-6 : ℝ) * (h 1)) < (-1 : ℝ))
    (a22 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a35 : -(h 2) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (31/47 : ℝ) * _ctx.order3 + (67/47 : ℝ) * _ctx.order4 + (103/47 : ℝ) * _ctx.min + (139/47 : ℝ) * _ctx.lower + (6/47 : ℝ) * a15 + (5/47 : ℝ) * a22 + (36/47 : ℝ) * a35 + (36/47 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1089 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : -(h 3) < (-3/28 : ℝ))
    (a31 : -(h 0) < (-5/33 : ℝ))
    (a34 : -(h 1) < (-8/55 : ℝ))
    (a40 : -(h 5) < (-2/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.order4 + (6/29 : ℝ) * _ctx.lower + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a20 + (4/29 : ℝ) * a31 + (6/29 : ℝ) * a34 + (12/29 : ℝ) * a40 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1088 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : -(h 3) < (-3/28 : ℝ))
    (a31 : -(h 0) < (-5/33 : ℝ))
    (a34 : -(h 1) < (-8/55 : ℝ))
    (a39 : -(h 4) < (-3/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.min + (12/23 : ℝ) * _ctx.lower + (1/23 : ℝ) * _ctx.fail1 + (6/23 : ℝ) * a20 + (4/23 : ℝ) * a31 + (6/23 : ℝ) * a34 + (6/23 : ℝ) * a39 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1087 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : -(h 3) < (-3/28 : ℝ))
    (a31 : -(h 0) < (-5/33 : ℝ))
    (a34 : -(h 1) < (-8/55 : ℝ))
    (a38 : -(h 2) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.order4 + (1/2 : ℝ) * _ctx.min + (3/4 : ℝ) * _ctx.lower + (1/4 : ℝ) * a20 + (1/4 : ℝ) * a31 + (1/4 : ℝ) * a34 + (1/4 : ℝ) * a38 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1086 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a37 : -(h 1) < (-5/31 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/11 : ℝ) * _ctx.order0 + (6/11 : ℝ) * _ctx.order3 + (12/11 : ℝ) * _ctx.order4 + (18/11 : ℝ) * _ctx.min + (24/11 : ℝ) * _ctx.lower + (1/11 : ℝ) * _ctx.fail1 + (10/11 : ℝ) * a37 + (6/11 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1085 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : h 0 ≤ (2/13 : ℝ))
    (a36 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a36
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1084 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : -(h 3) < (-3/28 : ℝ))
    (a31 : -(h 0) < (-5/33 : ℝ))
    (a34 : -(h 1) < (-8/55 : ℝ))
    (a35 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/13 : ℝ) * _ctx.order4 + (6/13 : ℝ) * _ctx.min + (1/26 : ℝ) * _ctx.fail1 + (3/13 : ℝ) * a20 + (2/13 : ℝ) * a31 + (3/13 : ℝ) * a34 + (9/26 : ℝ) * a35 + (3/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1083 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : -(h 3) < (-3/28 : ℝ))
    (a31 : -(h 0) < (-5/33 : ℝ))
    (a33 : h 0 ≤ (2/13 : ℝ))
    (a34 : -(h 1) < (-8/55 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1084 h delta _ctx _hno a20 a31 a34 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1085 h delta _ctx _hno a33 f1
  by_cases p2 : h 1 ≤ (5/31 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/31 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1086 h delta _ctx _hno f2
  by_cases p3 : h 2 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1087 h delta _ctx _hno a20 a31 a34 f3
  by_cases p4 : h 4 ≤ (3/28 : ℝ)
  swap
  · have f4 : -(h 4) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1088 h delta _ctx _hno a20 a31 a34 f4
  by_cases p5 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1089 h delta _ctx _hno a20 a31 a34 f5
  apply _hno 103
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (5/31 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (3/28 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_1082 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : -(h 1) < (-1/7 : ℝ))
    (a33 : -(h 0) < (-2/13 : ℝ))
    (a39 : -(h 4) < (-5/46 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.order3 + (6/23 : ℝ) * _ctx.min + (12/23 : ℝ) * _ctx.lower + (1/23 : ℝ) * _ctx.fail1 + (6/23 : ℝ) * a29 + (4/23 : ℝ) * a33 + (12/23 : ℝ) * a39 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1081 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : -(h 1) < (-1/7 : ℝ))
    (a33 : -(h 0) < (-2/13 : ℝ))
    (a38 : -(h 3) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/17 : ℝ) * _ctx.order4 + (12/17 : ℝ) * _ctx.min + (18/17 : ℝ) * _ctx.lower + (1/17 : ℝ) * _ctx.fail1 + (6/17 : ℝ) * a29 + (4/17 : ℝ) * a33 + (6/17 : ℝ) * a38 + (6/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1080 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 0) + ((-6 : ℝ) * (h 1)) < (-1 : ℝ))
    (a20 : -(h 3) < (-3/28 : ℝ))
    (a33 : -(h 0) < (-2/13 : ℝ))
    (a37 : -(h 2) < (-6/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order4 + (2/3 : ℝ) * _ctx.min + (1 : ℝ) * _ctx.lower + (1/18 : ℝ) * a15 + (1/3 : ℝ) * a20 + (5/18 : ℝ) * a33 + (1/3 : ℝ) * a37 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1079 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a36 : -(h 1) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/11 : ℝ) * _ctx.order0 + (6/11 : ℝ) * _ctx.order3 + (12/11 : ℝ) * _ctx.order4 + (18/11 : ℝ) * _ctx.min + (24/11 : ℝ) * _ctx.lower + (1/11 : ℝ) * _ctx.fail1 + (10/11 : ℝ) * a36 + (6/11 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1078 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : -(h 3) < (-3/28 : ℝ))
    (a29 : -(h 1) < (-1/7 : ℝ))
    (a35 : -(h 0) < (-4/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/17 : ℝ) * _ctx.order4 + (12/17 : ℝ) * _ctx.min + (18/17 : ℝ) * _ctx.lower + (1/17 : ℝ) * _ctx.fail1 + (6/17 : ℝ) * a20 + (6/17 : ℝ) * a29 + (4/17 : ℝ) * a35 + (6/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1077 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : -(h 3) < (-3/28 : ℝ))
    (a29 : -(h 1) < (-1/7 : ℝ))
    (a33 : -(h 0) < (-2/13 : ℝ))
    (a40 : -(h 5) < (-2/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.order4 + (6/29 : ℝ) * _ctx.lower + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a20 + (6/29 : ℝ) * a29 + (4/29 : ℝ) * a33 + (12/29 : ℝ) * a40 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1076 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : -(h 3) < (-3/28 : ℝ))
    (a29 : -(h 1) < (-1/7 : ℝ))
    (a33 : -(h 0) < (-2/13 : ℝ))
    (a39 : -(h 4) < (-3/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.min + (12/23 : ℝ) * _ctx.lower + (1/23 : ℝ) * _ctx.fail1 + (6/23 : ℝ) * a20 + (6/23 : ℝ) * a29 + (4/23 : ℝ) * a33 + (6/23 : ℝ) * a39 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1075 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : -(h 3) < (-3/28 : ℝ))
    (a29 : -(h 1) < (-1/7 : ℝ))
    (a33 : -(h 0) < (-2/13 : ℝ))
    (a38 : -(h 2) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.order4 + (1/2 : ℝ) * _ctx.min + (3/4 : ℝ) * _ctx.lower + (1/4 : ℝ) * a20 + (1/4 : ℝ) * a29 + (1/4 : ℝ) * a33 + (1/4 : ℝ) * a38 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1074 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a37 : -(h 1) < (-5/31 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/11 : ℝ) * _ctx.order0 + (6/11 : ℝ) * _ctx.order3 + (12/11 : ℝ) * _ctx.order4 + (18/11 : ℝ) * _ctx.min + (24/11 : ℝ) * _ctx.lower + (1/11 : ℝ) * _ctx.fail1 + (10/11 : ℝ) * a37 + (6/11 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1073 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : h 0 ≤ (4/25 : ℝ))
    (a36 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a36
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1072 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : -(h 3) < (-3/28 : ℝ))
    (a29 : -(h 1) < (-1/7 : ℝ))
    (a33 : -(h 0) < (-2/13 : ℝ))
    (a35 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/13 : ℝ) * _ctx.order4 + (6/13 : ℝ) * _ctx.min + (1/26 : ℝ) * _ctx.fail1 + (3/13 : ℝ) * a20 + (3/13 : ℝ) * a29 + (2/13 : ℝ) * a33 + (9/26 : ℝ) * a35 + (3/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1071 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : h 0 ≤ (4/25 : ℝ))
    (a20 : -(h 3) < (-3/28 : ℝ))
    (a29 : -(h 1) < (-1/7 : ℝ))
    (a33 : -(h 0) < (-2/13 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1072 h delta _ctx _hno a20 a29 a33 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1073 h delta _ctx _hno a17 f1
  by_cases p2 : h 1 ≤ (5/31 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/31 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1074 h delta _ctx _hno f2
  by_cases p3 : h 2 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1075 h delta _ctx _hno a20 a29 a33 f3
  by_cases p4 : h 4 ≤ (3/28 : ℝ)
  swap
  · have f4 : -(h 4) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1076 h delta _ctx _hno a20 a29 a33 f4
  by_cases p5 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1077 h delta _ctx _hno a20 a29 a33 f5
  apply _hno 103
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (5/31 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (3/28 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_1070 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 0) + ((-6 : ℝ) * (h 1)) < (-1 : ℝ))
    (a17 : h 0 ≤ (4/25 : ℝ))
    (a20 : -(h 3) < (-3/28 : ℝ))
    (a29 : -(h 1) < (-1/7 : ℝ))
    (a33 : -(h 0) < (-2/13 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1071 h delta _ctx _hno a17 a20 a29 a33
  by_cases p1 : h 0 ≤ (4/25 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/25 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1078 h delta _ctx _hno a20 a29 f1
  by_cases p2 : h 1 ≤ (2/13 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1079 h delta _ctx _hno f2
  by_cases p3 : h 2 ≤ (6/47 : ℝ)
  swap
  · have f3 : -(h 2) < (-6/47 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1080 h delta _ctx _hno a15 a20 a33 f3
  by_cases p4 : h 3 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1081 h delta _ctx _hno a29 a33 f4
  by_cases p5 : h 4 ≤ (5/46 : ℝ)
  swap
  · have f5 : -(h 4) < (-5/46 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1082 h delta _ctx _hno a29 a33 f5
  apply _hno 11
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (6/47 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ)) ∧ (h 4 ≤ (5/46 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_1069 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a15 : -(h 0) + ((-6 : ℝ) * (h 1)) < (-1 : ℝ))
    (a24 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a32 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/443 : ℝ) * _ctx.order3 + (12/443 : ℝ) * _ctx.order4 + (1/443 : ℝ) * _ctx.fail1 + (105/443 : ℝ) * a14 + (1/443 : ℝ) * a15 + (18/443 : ℝ) * a24 + (423/443 : ℝ) * a32 + (6/443 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1068 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a15 : -(h 0) + ((-6 : ℝ) * (h 1)) < (-1 : ℝ))
    (a17 : h 0 ≤ (4/25 : ℝ))
    (a20 : -(h 3) < (-3/28 : ℝ))
    (a22 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a24 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a29 : -(h 1) < (-1/7 : ℝ))
    (a31 : -(h 0) < (-5/33 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1069 h delta _ctx _hno a14 a15 a24 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1070 h delta _ctx _hno a15 a17 a20 a29 f1
  by_cases p2 : h 1 ≤ (8/55 : ℝ)
  swap
  · have f2 : -(h 1) < (-8/55 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1083 h delta _ctx _hno a20 a31 p1 f2
  by_cases p3 : h 2 ≤ (1/7 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1090 h delta _ctx _hno a15 a22 f3
  by_cases p4 : h 3 ≤ (6/55 : ℝ)
  swap
  · have f4 : -(h 3) < (-6/55 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1091 h delta _ctx _hno a29 a31 p1 p2 f4
  by_cases p5 : h 4 ≤ (5/46 : ℝ)
  swap
  · have f5 : -(h 4) < (-5/46 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1098 h delta _ctx _hno a29 a31 f5
  apply _hno 12
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (8/55 : ℝ)) ∧ (h 2 ≤ (1/7 : ℝ)) ∧ (h 3 ≤ (6/55 : ℝ)) ∧ (h 4 ≤ (5/46 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_1067 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a15 : -(h 0) + ((-6 : ℝ) * (h 1)) < (-1 : ℝ))
    (a22 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a24 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a30 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/443 : ℝ) * _ctx.order4 + (1/443 : ℝ) * _ctx.fail1 + (105/443 : ℝ) * a14 + (1/443 : ℝ) * a15 + (6/443 : ℝ) * a22 + (12/443 : ℝ) * a24 + (423/443 : ℝ) * a30 + (6/443 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1066 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a15 : -(h 0) + ((-6 : ℝ) * (h 1)) < (-1 : ℝ))
    (a17 : h 0 ≤ (4/25 : ℝ))
    (a20 : -(h 3) < (-3/28 : ℝ))
    (a22 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a24 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a29 : -(h 1) < (-1/7 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1067 h delta _ctx _hno a14 a15 a22 a24 f0
  by_cases p1 : h 0 ≤ (5/33 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/33 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1068 h delta _ctx _hno a14 a15 a17 a20 a22 a24 a29 f1
  by_cases p2 : h 1 ≤ (3/20 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1099 h delta _ctx _hno a20 a24 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1100 h delta _ctx _hno a20 a24 a29 f3
  by_cases p4 : h 3 ≤ (7/57 : ℝ)
  swap
  · have f4 : -(h 3) < (-7/57 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1101 h delta _ctx _hno a15 a24 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1102 h delta _ctx _hno a15 a24 f5
  apply _hno 87
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (5/33 : ℝ)) ∧ (h 1 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (7/57 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_1065 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : h 0 ≤ (4/25 : ℝ))
    (a28 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a28
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1064 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a15 : -(h 0) + ((-6 : ℝ) * (h 1)) < (-1 : ℝ))
    (a22 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a24 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-11/50 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/443 : ℝ) * _ctx.order4 + (1/443 : ℝ) * _ctx.fail1 + (105/443 : ℝ) * a14 + (1/443 : ℝ) * a15 + (6/443 : ℝ) * a22 + (12/443 : ℝ) * a24 + (423/443 : ℝ) * a27 + (6/443 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1063 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a15 : -(h 0) + ((-6 : ℝ) * (h 1)) < (-1 : ℝ))
    (a17 : h 0 ≤ (4/25 : ℝ))
    (a20 : -(h 3) < (-3/28 : ℝ))
    (a22 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a24 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (11/50 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-11/50 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1064 h delta _ctx _hno a14 a15 a22 a24 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1065 h delta _ctx _hno a17 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1066 h delta _ctx _hno a14 a15 a17 a20 a22 a24 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1103 h delta _ctx _hno a15 a20 a24 f3
  by_cases p4 : h 3 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1104 h delta _ctx _hno a14 a15 a17 a22 a24 p2 f4
  apply _hno 72
  change (((2 : ℝ) * (delta)) ≤ (11/50 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_1062 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a15 : -(h 0) + ((-6 : ℝ) * (h 1)) < (-1 : ℝ))
    (a22 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a24 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a25 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/443 : ℝ) * _ctx.order4 + (1/443 : ℝ) * _ctx.fail1 + (105/443 : ℝ) * a14 + (1/443 : ℝ) * a15 + (6/443 : ℝ) * a22 + (12/443 : ℝ) * a24 + (423/443 : ℝ) * a25 + (6/443 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1061 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a15 : -(h 0) + ((-6 : ℝ) * (h 1)) < (-1 : ℝ))
    (a17 : h 0 ≤ (4/25 : ℝ))
    (a20 : -(h 3) < (-3/28 : ℝ))
    (a22 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a24 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1062 h delta _ctx _hno a14 a15 a22 a24 f0
  by_cases p1 : h 0 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1063 h delta _ctx _hno a14 a15 a17 a20 a22 a24
  by_cases p2 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1117 h delta _ctx _hno a15 a20 a24 f2
  by_cases p3 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f3 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1118 h delta _ctx _hno a15 a24 f3
  apply _hno 8
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_1060 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 0) + ((-6 : ℝ) * (h 1)) < (-1 : ℝ))
    (a16 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a22 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a23 : -(h 5) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (11/40 : ℝ) * _ctx.order3 + (23/40 : ℝ) * _ctx.order4 + (1/20 : ℝ) * _ctx.fail1 + (1/20 : ℝ) * a15 + (67/20 : ℝ) * a16 + (1/40 : ℝ) * a22 + (7/8 : ℝ) * a23 + (3/10 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1059 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a15 : -(h 0) + ((-6 : ℝ) * (h 1)) < (-1 : ℝ))
    (a16 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a17 : h 0 ≤ (4/25 : ℝ))
    (a20 : -(h 3) < (-3/28 : ℝ))
    (a22 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    : False := by
  by_cases p0 : h 5 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ)
  swap
  · have f0 : -(h 5) + ((-8 : ℝ) * (delta)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1060 h delta _ctx _hno a15 a16 a22 f0
  by_cases p1 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ)
  swap
  · have f1 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1061 h delta _ctx _hno a14 a15 a17 a20 a22 f1
  by_cases p2 : ((6 : ℝ) * (h 1)) + h 5 ≤ (1 : ℝ)
  swap
  · have f2 : ((-6 : ℝ) * (h 1)) + -(h 5) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1119 h delta _ctx _hno a20 f2
  by_cases p3 : ((6 : ℝ) * (h 2)) + h 5 ≤ (1 : ℝ)
  swap
  · have f3 : ((-6 : ℝ) * (h 2)) + -(h 5) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1120 h delta _ctx _hno a22 f3
  by_cases p4 : ((8 : ℝ) * (h 3)) + h 5 ≤ (1 : ℝ)
  swap
  · have f4 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1121 h delta _ctx _hno a15 a22 p1 f4
  by_cases p5 : ((8 : ℝ) * (h 4)) + h 5 ≤ (1 : ℝ)
  swap
  · have f5 : ((-8 : ℝ) * (h 4)) + -(h 5) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1126 h delta _ctx _hno a15 a22 f5
  apply _hno 32
  change (h 5 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ)) ∧ (((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ)) ∧ (((6 : ℝ) * (h 1)) + h 5 ≤ (1 : ℝ)) ∧ (((6 : ℝ) * (h 2)) + h 5 ≤ (1 : ℝ)) ∧ (((8 : ℝ) * (h 3)) + h 5 ≤ (1 : ℝ)) ∧ (((8 : ℝ) * (h 4)) + h 5 ≤ (1 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_1058 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 0) + ((-6 : ℝ) * (h 1)) < (-1 : ℝ))
    (a16 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a21 : -(h 3) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (5/16 : ℝ) * _ctx.order0 + (7/16 : ℝ) * _ctx.order2 + (7/16 : ℝ) * _ctx.order4 + (7/8 : ℝ) * _ctx.min + (1/8 : ℝ) * a15 + (91/32 : ℝ) * a16 + (7/8 : ℝ) * a21 + (7/16 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1057 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a15 : -(h 0) + ((-6 : ℝ) * (h 1)) < (-1 : ℝ))
    (a16 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a17 : h 0 ≤ (4/25 : ℝ))
    (a20 : -(h 3) < (-3/28 : ℝ))
    : False := by
  by_cases p0 : h 3 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ)
  swap
  · have f0 : -(h 3) + ((-8 : ℝ) * (delta)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1058 h delta _ctx _hno a15 a16 f0
  by_cases p1 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ)
  swap
  · have f1 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1059 h delta _ctx _hno a14 a15 a16 a17 a20 f1
  by_cases p2 : ((6 : ℝ) * (h 1)) + h 3 ≤ (1 : ℝ)
  swap
  · have f2 : ((-6 : ℝ) * (h 1)) + -(h 3) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1127 h delta _ctx _hno a20 f2
  by_cases p3 : ((6 : ℝ) * (h 2)) + h 3 ≤ (1 : ℝ)
  swap
  · have f3 : ((-6 : ℝ) * (h 2)) + -(h 3) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1128 h delta _ctx _hno f3
  by_cases p4 : h 3 + ((8 : ℝ) * (h 4)) ≤ (1 : ℝ)
  swap
  · have f4 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1129 h delta _ctx _hno a15 f4
  by_cases p5 : h 3 + ((8 : ℝ) * (h 5)) ≤ (1 : ℝ)
  swap
  · have f5 : -(h 3) + ((-8 : ℝ) * (h 5)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1130 h delta _ctx _hno a15 f5
  apply _hno 90
  change (h 3 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ)) ∧ (((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ)) ∧ (((6 : ℝ) * (h 1)) + h 3 ≤ (1 : ℝ)) ∧ (((6 : ℝ) * (h 2)) + h 3 ≤ (1 : ℝ)) ∧ (h 3 + ((8 : ℝ) * (h 4)) ≤ (1 : ℝ)) ∧ (h 3 + ((8 : ℝ) * (h 5)) ≤ (1 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_1056 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 0) + ((-6 : ℝ) * (h 1)) < (-1 : ℝ))
    (a19 : -(h 2) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (8/11 : ℝ) * _ctx.order3 + (28/33 : ℝ) * _ctx.order4 + (52/33 : ℝ) * _ctx.min + (76/33 : ℝ) * _ctx.lower + (5/33 : ℝ) * _ctx.fail2 + (4/33 : ℝ) * a15 + (8/11 : ℝ) * a19 + (8/11 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1055 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 1) < (-7/44 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/11 : ℝ) * _ctx.order0 + (6/11 : ℝ) * _ctx.order3 + (12/11 : ℝ) * _ctx.order4 + (18/11 : ℝ) * _ctx.min + (24/11 : ℝ) * _ctx.lower + (1/11 : ℝ) * _ctx.fail1 + (10/11 : ℝ) * a18 + (6/11 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1054 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 0) + ((-6 : ℝ) * (h 1)) < (-1 : ℝ))
    (a17 : -(h 0) < (-4/25 : ℝ))
    (a22 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/17 : ℝ) * _ctx.order3 + (6/17 : ℝ) * _ctx.min + (12/17 : ℝ) * _ctx.lower + (1/17 : ℝ) * _ctx.fail1 + (1/17 : ℝ) * a15 + (3/17 : ℝ) * a17 + (12/17 : ℝ) * a22 + (6/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1053 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 0) + ((-6 : ℝ) * (h 1)) < (-1 : ℝ))
    (a17 : -(h 0) < (-4/25 : ℝ))
    (a26 : -(h 3) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/11 : ℝ) * _ctx.order4 + (12/11 : ℝ) * _ctx.min + (18/11 : ℝ) * _ctx.lower + (1/11 : ℝ) * _ctx.fail1 + (1/11 : ℝ) * a15 + (3/11 : ℝ) * a17 + (6/11 : ℝ) * a26 + (6/11 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1052 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 0) + ((-6 : ℝ) * (h 1)) < (-1 : ℝ))
    (a17 : -(h 0) < (-4/25 : ℝ))
    (a25 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/2 : ℝ) * _ctx.order3 + (1 : ℝ) * _ctx.order4 + (3/2 : ℝ) * _ctx.min + (2 : ℝ) * _ctx.lower + (1/12 : ℝ) * a15 + (5/12 : ℝ) * a17 + (1/2 : ℝ) * a25 + (1/2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1051 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : -(h 0) < (-4/25 : ℝ))
    (a21 : -(h 2) < (-4/35 : ℝ))
    (a24 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order3 + (2/3 : ℝ) * _ctx.order4 + (1 : ℝ) * _ctx.min + (4/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * a17 + (1/3 : ℝ) * a21 + (1/3 : ℝ) * a24 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1050 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 0) + ((-6 : ℝ) * (h 1)) < (-1 : ℝ))
    (a21 : -(h 2) < (-4/35 : ℝ))
    (a23 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/2 : ℝ) * _ctx.order3 + (1 : ℝ) * _ctx.order4 + (3/2 : ℝ) * _ctx.min + (2 : ℝ) * _ctx.lower + (1/12 : ℝ) * a15 + (1/2 : ℝ) * a21 + (5/12 : ℝ) * a23 + (1/2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1049 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a17 : -(h 0) < (-4/25 : ℝ))
    (a22 : ((-2 : ℝ) * (delta)) < (-11/50 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * a14 + (1/5 : ℝ) * a17 + (4/5 : ℝ) * a22
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1048 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a15 : -(h 0) + ((-6 : ℝ) * (h 1)) < (-1 : ℝ))
    (a17 : -(h 0) < (-4/25 : ℝ))
    (a21 : -(h 2) < (-4/35 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (11/50 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-11/50 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1049 h delta _ctx _hno a14 a17 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1050 h delta _ctx _hno a15 a21 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1051 h delta _ctx _hno a17 a21 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1052 h delta _ctx _hno a15 a17 f3
  by_cases p4 : h 3 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1053 h delta _ctx _hno a15 a17 f4
  apply _hno 72
  change (((2 : ℝ) * (delta)) ≤ (11/50 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_1047 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : -(h 0) < (-4/25 : ℝ))
    (a20 : -(h 1) < (-1/7 : ℝ))
    (a25 : -(h 3) < (-3/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/17 : ℝ) * _ctx.order4 + (12/17 : ℝ) * _ctx.min + (18/17 : ℝ) * _ctx.lower + (1/17 : ℝ) * _ctx.fail1 + (4/17 : ℝ) * a17 + (6/17 : ℝ) * a20 + (6/17 : ℝ) * a25 + (6/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1046 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : -(h 0) < (-4/25 : ℝ))
    (a20 : -(h 1) < (-1/7 : ℝ))
    (a24 : -(h 2) < (-13/113 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order3 + (2/3 : ℝ) * _ctx.order4 + (1 : ℝ) * _ctx.min + (4/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * a17 + (1/3 : ℝ) * a20 + (1/3 : ℝ) * a24 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1045 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : -(h 0) < (-4/25 : ℝ))
    (a23 : -(h 1) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/11 : ℝ) * _ctx.order3 + (12/11 : ℝ) * _ctx.order4 + (18/11 : ℝ) * _ctx.min + (24/11 : ℝ) * _ctx.lower + (1/11 : ℝ) * _ctx.fail1 + (4/11 : ℝ) * a17 + (6/11 : ℝ) * a23 + (6/11 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1044 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : -(h 1) < (-1/7 : ℝ))
    (a22 : -(h 0) < (-6/37 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/11 : ℝ) * _ctx.order3 + (12/11 : ℝ) * _ctx.order4 + (18/11 : ℝ) * _ctx.min + (24/11 : ℝ) * _ctx.lower + (1/11 : ℝ) * _ctx.fail1 + (6/11 : ℝ) * a20 + (4/11 : ℝ) * a22 + (6/11 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1043 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a17 : -(h 0) < (-4/25 : ℝ))
    (a21 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * a14 + (1/5 : ℝ) * a17 + (4/5 : ℝ) * a21
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1042 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a17 : -(h 0) < (-4/25 : ℝ))
    (a20 : -(h 1) < (-1/7 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1043 h delta _ctx _hno a14 a17 f0
  by_cases p1 : h 0 ≤ (6/37 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/37 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1044 h delta _ctx _hno a20 f1
  by_cases p2 : h 1 ≤ (2/13 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1045 h delta _ctx _hno a17 f2
  by_cases p3 : h 2 ≤ (13/113 : ℝ)
  swap
  · have f3 : -(h 2) < (-13/113 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1046 h delta _ctx _hno a17 a20 f3
  by_cases p4 : h 3 ≤ (3/28 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1047 h delta _ctx _hno a17 a20 f4
  apply _hno 102
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (6/37 : ℝ)) ∧ (h 1 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (13/113 : ℝ)) ∧ (h 3 ≤ (3/28 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_1041 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a19 : -(h 0) < (-6/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (8 : ℝ) * _ctx.lower + (1 : ℝ) * a14 + (1 : ℝ) * a19
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1040 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a17 : -(h 0) < (-4/25 : ℝ))
    (a18 : ((-2 : ℝ) * (delta)) < (-8/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * a14 + (1/5 : ℝ) * a17 + (4/5 : ℝ) * a18
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1039 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a15 : -(h 0) + ((-6 : ℝ) * (h 1)) < (-1 : ℝ))
    (a17 : -(h 0) < (-4/25 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (8/35 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-8/35 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1040 h delta _ctx _hno a14 a17 f0
  by_cases p1 : h 0 ≤ (6/35 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/35 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1041 h delta _ctx _hno a14 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1042 h delta _ctx _hno a14 a17 f2
  by_cases p3 : h 2 ≤ (4/35 : ℝ)
  swap
  · have f3 : -(h 2) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1048 h delta _ctx _hno a14 a15 a17 f3
  by_cases p4 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1054 h delta _ctx _hno a15 a17 f4
  apply _hno 51
  change (((2 : ℝ) * (delta)) ≤ (8/35 : ℝ)) ∧ (h 0 ≤ (6/35 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (4/35 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_1038 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a15 : -(h 0) + ((-6 : ℝ) * (h 1)) < (-1 : ℝ))
    (a16 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/47 : ℝ) * _ctx.order3 + (6/47 : ℝ) * _ctx.min + (1/47 : ℝ) * _ctx.fail1 + (3/47 : ℝ) * _ctx.fail2 + (9/47 : ℝ) * a14 + (1/47 : ℝ) * a15 + (42/47 : ℝ) * a16 + (6/47 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1037 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a15 : -(h 0) + ((-6 : ℝ) * (h 1)) < (-1 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1038 h delta _ctx _hno a14 a15 f0
  by_cases p1 : h 0 ≤ (4/25 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/25 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1039 h delta _ctx _hno a14 a15 f1
  by_cases p2 : h 1 ≤ (7/44 : ℝ)
  swap
  · have f2 : -(h 1) < (-7/44 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1055 h delta _ctx _hno f2
  by_cases p3 : h 2 ≤ (1/7 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1056 h delta _ctx _hno a15 f3
  by_cases p4 : h 3 ≤ (3/28 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1057 h delta _ctx _hno a14 a15 p0 p1 f4
  apply _hno 10
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (7/44 : ℝ)) ∧ (h 2 ≤ (1/7 : ℝ)) ∧ (h 3 ≤ (3/28 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_1036 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : ((8 : ℝ) * (h 3)) + h 5 ≤ (1 : ℝ))
    (a20 : ((-8 : ℝ) * (h 4)) + -(h 5) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (8 : ℝ) * _ctx.order3 + (1 : ℝ) * a19 + (1 : ℝ) * a20
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1035 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a24 : h 3 + ((8 : ℝ) * (h 4)) ≤ (1 : ℝ))
    (a25 : -(h 3) + ((-8 : ℝ) * (h 5)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (8 : ℝ) * _ctx.order4 + (1 : ℝ) * a24 + (1 : ℝ) * a25
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1034 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a34 : h 2 ≤ (1/8 : ℝ))
    (a39 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1033 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a31 : -(h 3) < (-4/35 : ℝ))
    (a37 : h 0 ≤ (11/80 : ℝ))
    (a38 : -(h 1) < (-7/51 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/8 : ℝ) * _ctx.min + (1/16 : ℝ) * _ctx.fail1 + (3/32 : ℝ) * _ctx.fail2 + (3/32 : ℝ) * a14 + (3/8 : ℝ) * a31 + (7/32 : ℝ) * a37 + (3/8 : ℝ) * a38 + (3/8 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1032 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a46 : -(h 3) < (-2/17 : ℝ))
    (a52 : -(h 4) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.min + (1/23 : ℝ) * _ctx.fail1 + (3/46 : ℝ) * a14 + (6/23 : ℝ) * a27 + (5/46 : ℝ) * a37 + (6/23 : ℝ) * a46 + (6/23 : ℝ) * a52 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1031 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a51 : -(h 3) < (-5/42 : ℝ))
    (a57 : -(h 5) < (-7/64 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/29 : ℝ) * _ctx.fail1 + (3/116 : ℝ) * a14 + (6/29 : ℝ) * a27 + (13/116 : ℝ) * a37 + (6/29 : ℝ) * a42 + (6/29 : ℝ) * a51 + (6/29 : ℝ) * a57 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1030 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a56 : -(h 4) < (-4/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.order3 + (6/23 : ℝ) * _ctx.min + (1/23 : ℝ) * _ctx.fail1 + (3/46 : ℝ) * a14 + (6/23 : ℝ) * a27 + (5/46 : ℝ) * a37 + (12/23 : ℝ) * a56 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1029 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a50 : h 2 ≤ (4/33 : ℝ))
    (a55 : -(h 3) < (-5/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * _ctx.order2 + (1 : ℝ) * a50 + (1 : ℝ) * a55
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1028 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a50 : h 2 ≤ (4/33 : ℝ))
    (a54 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a50 + (1 : ℝ) * a54
  exact (lt_irrefl (0 : ℝ)) hbad

end RealPinwheel.WeakSevenBandData
