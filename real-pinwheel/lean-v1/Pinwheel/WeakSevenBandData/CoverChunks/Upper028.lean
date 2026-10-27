import Pinwheel.WeakSevenBandData.CoverChunks.Upper027

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem upper_node_2067 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a33 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a20 + (1 : ℝ) * a33
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2066 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a32 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/145 : ℝ) * _ctx.order1 + (4/145 : ℝ) * _ctx.order2 + (2/145 : ℝ) * _ctx.order4 + (4/145 : ℝ) * _ctx.min + (34/145 : ℝ) * a14 + (6/145 : ℝ) * a25 + (139/145 : ℝ) * a32 + (2/145 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2065 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a20 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a28 : -(h 2) < (-1/8 : ℝ))
    (a31 : -(h 1) < (-7/54 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2066 h delta _ctx _hno a14 a25 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2067 h delta _ctx _hno a20 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2068 h delta _ctx _hno a18 a20 a23 a25 a28 f2
  by_cases p3 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f3 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2075 h delta _ctx _hno a18 a20 a25 a28 a31 f3
  by_cases p4 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2088 h delta _ctx _hno a23 a25 a28 a31 f4
  apply _hno 19
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_2064 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a30 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a20 + (1 : ℝ) * a30
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2063 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a28 : -(h 2) < (-1/8 : ℝ))
    (a29 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/49 : ℝ) * _ctx.order1 + (2/49 : ℝ) * _ctx.order4 + (4/49 : ℝ) * _ctx.min + (10/49 : ℝ) * a14 + (2/49 : ℝ) * a25 + (4/49 : ℝ) * a28 + (43/49 : ℝ) * a29 + (2/49 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2062 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a20 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a28 : -(h 2) < (-1/8 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2063 h delta _ctx _hno a14 a25 a28 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2064 h delta _ctx _hno a20 f1
  by_cases p2 : h 1 ≤ (7/54 : ℝ)
  swap
  · have f2 : -(h 1) < (-7/54 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2065 h delta _ctx _hno a14 a18 a20 a23 a25 a28 f2
  by_cases p3 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2089 h delta _ctx _hno a13 a18 a25 a28 f3
  by_cases p4 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2090 h delta _ctx _hno a13 a14 a20 a23 a25 a28 p2 f4
  apply _hno 14
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (7/54 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_2061 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a27 : -(h 0) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a20 + (1 : ℝ) * a27
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2060 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a26 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/145 : ℝ) * _ctx.order1 + (4/145 : ℝ) * _ctx.order2 + (2/145 : ℝ) * _ctx.order4 + (4/145 : ℝ) * _ctx.min + (34/145 : ℝ) * a14 + (6/145 : ℝ) * a25 + (139/145 : ℝ) * a26 + (2/145 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2059 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a15 : h 0 + ((6 : ℝ) * (h 1)) ≤ (1 : ℝ))
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a20 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2060 h delta _ctx _hno a14 a25 f0
  by_cases p1 : h 0 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2061 h delta _ctx _hno a20 f1
  by_cases p2 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2062 h delta _ctx _hno a13 a14 a18 a20 a23 a25 f2
  by_cases p3 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f3 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2102 h delta _ctx _hno a13 a14 a15 a20 a23 a25 p2 f3
  apply _hno 8
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_2058 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (92/147 : ℝ) * _ctx.order1 + (92/147 : ℝ) * _ctx.min + (92/441 : ℝ) * _ctx.fail1 + (23/147 : ℝ) * _ctx.fail2 + (4/441 : ℝ) * _ctx.fail3 + (208/441 : ℝ) * a14 + (92/147 : ℝ) * a24 + (92/147 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2057 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a15 : h 0 + ((6 : ℝ) * (h 1)) ≤ (1 : ℝ))
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a20 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    : False := by
  by_cases p0 : h 3 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ)
  swap
  · have f0 : -(h 3) + ((-8 : ℝ) * (delta)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2058 h delta _ctx _hno a14 f0
  by_cases p1 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ)
  swap
  · have f1 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2059 h delta _ctx _hno a13 a14 a15 a18 a20 a23 f1
  by_cases p2 : ((6 : ℝ) * (h 1)) + h 3 ≤ (1 : ℝ)
  swap
  · have f2 : ((-6 : ℝ) * (h 1)) + -(h 3) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2510 h delta _ctx _hno a15 f2
  by_cases p3 : ((6 : ℝ) * (h 2)) + h 3 ≤ (1 : ℝ)
  swap
  · have f3 : ((-6 : ℝ) * (h 2)) + -(h 3) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2511 h delta _ctx _hno a23 f3
  by_cases p4 : h 3 + ((8 : ℝ) * (h 4)) ≤ (1 : ℝ)
  swap
  · have f4 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2512 h delta _ctx _hno a13 a14 a20 a23 p1 f4
  by_cases p5 : h 3 + ((8 : ℝ) * (h 5)) ≤ (1 : ℝ)
  swap
  · have f5 : -(h 3) + ((-8 : ℝ) * (h 5)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_3990 h delta _ctx _hno p4 f5
  apply _hno 90
  change (h 3 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ)) ∧ (((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ)) ∧ (((6 : ℝ) * (h 1)) + h 3 ≤ (1 : ℝ)) ∧ (((6 : ℝ) * (h 2)) + h 3 ≤ (1 : ℝ)) ∧ (h 3 + ((8 : ℝ) * (h 4)) ≤ (1 : ℝ)) ∧ (h 3 + ((8 : ℝ) * (h 5)) ≤ (1 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_2056 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a22 : ((-6 : ℝ) * (h 2)) + -(h 5) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.order0 + (4 : ℝ) * _ctx.order1 + (2 : ℝ) * _ctx.order3 + (4 : ℝ) * _ctx.order4 + (5 : ℝ) * _ctx.min + (7 : ℝ) * _ctx.lower + (1 : ℝ) * a22 + (2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2055 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : h 0 + ((6 : ℝ) * (h 1)) ≤ (1 : ℝ))
    (a21 : ((-6 : ℝ) * (h 1)) + -(h 5) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (18/19 : ℝ) * _ctx.order0 + (6/19 : ℝ) * _ctx.order3 + (12/19 : ℝ) * _ctx.order4 + (6/19 : ℝ) * _ctx.lower + (1/19 : ℝ) * _ctx.fail1 + (14/19 : ℝ) * a15 + (18/19 : ℝ) * a21 + (6/19 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2054 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a38 : -(h 5) < (-1/9 : ℝ))
    (a43 : -(h 4) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.order3 + (1/23 : ℝ) * _ctx.fail1 + (1/23 : ℝ) * a13 + (2/69 : ℝ) * a20 + (3/23 : ℝ) * a27 + (16/69 : ℝ) * a38 + (12/23 : ℝ) * a43 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2053 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a38 : -(h 5) < (-1/9 : ℝ))
    (a42 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/28 : ℝ) * _ctx.order1 + (1/28 : ℝ) * a13 + (1/28 : ℝ) * a20 + (3/14 : ℝ) * a24 + (3/14 : ℝ) * a33 + (5/28 : ℝ) * a38 + (9/28 : ℝ) * a42 + (3/14 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2052 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a38 : -(h 5) < (-1/9 : ℝ))
    (a41 : -(h 1) < (-9/70 : ℝ))
    (a47 : -(h 4) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/25 : ℝ) * _ctx.order3 + (6/25 : ℝ) * _ctx.lower + (1/25 : ℝ) * _ctx.fail1 + (2/75 : ℝ) * a20 + (16/75 : ℝ) * a38 + (6/25 : ℝ) * a41 + (12/25 : ℝ) * a47 + (6/25 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2051 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a37 : h 3 ≤ (3/26 : ℝ))
    (a46 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a37 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2050 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a38 : -(h 5) < (-1/9 : ℝ))
    (a41 : -(h 1) < (-9/70 : ℝ))
    (a45 : -(h 2) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.lower + (1/30 : ℝ) * a20 + (1/5 : ℝ) * a24 + (1/5 : ℝ) * a33 + (1/6 : ℝ) * a38 + (1/5 : ℝ) * a41 + (1/5 : ℝ) * a45 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2049 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a38 : -(h 5) < (-1/9 : ℝ))
    (a44 : -(h 1) < (-4/31 : ℝ))
    (a50 : -(h 4) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/25 : ℝ) * _ctx.order3 + (6/25 : ℝ) * _ctx.lower + (1/25 : ℝ) * _ctx.fail1 + (2/75 : ℝ) * a20 + (16/75 : ℝ) * a38 + (6/25 : ℝ) * a44 + (12/25 : ℝ) * a50 + (6/25 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2048 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a37 : h 3 ≤ (3/26 : ℝ))
    (a49 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a37 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2047 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a38 : -(h 5) < (-1/9 : ℝ))
    (a44 : -(h 1) < (-4/31 : ℝ))
    (a48 : -(h 2) < (-12/101 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.lower + (1/30 : ℝ) * a20 + (2/5 : ℝ) * a33 + (1/6 : ℝ) * a38 + (1/5 : ℝ) * a44 + (1/5 : ℝ) * a48 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2046 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a38 : -(h 5) < (-1/9 : ℝ))
    (a47 : -(h 1) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/25 : ℝ) * _ctx.order3 + (6/25 : ℝ) * _ctx.lower + (1/25 : ℝ) * _ctx.fail1 + (2/75 : ℝ) * a20 + (12/25 : ℝ) * a33 + (16/75 : ℝ) * a38 + (6/25 : ℝ) * a47 + (6/25 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2045 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : h 0 ≤ (5/33 : ℝ))
    (a46 : -(h 0) < (-3/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2044 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a38 : -(h 5) < (-1/9 : ℝ))
    (a44 : -(h 1) < (-4/31 : ℝ))
    (a45 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a50 : -(h 3) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/28 : ℝ) * _ctx.fail1 + (1/42 : ℝ) * a20 + (3/14 : ℝ) * a33 + (4/21 : ℝ) * a38 + (3/14 : ℝ) * a44 + (3/28 : ℝ) * a45 + (3/14 : ℝ) * a50 + (3/14 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2043 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a38 : -(h 5) < (-1/9 : ℝ))
    (a44 : -(h 1) < (-4/31 : ℝ))
    (a45 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a49 : -(h 2) < (-6/49 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/11 : ℝ) * _ctx.order3 + (1/33 : ℝ) * a20 + (4/11 : ℝ) * a33 + (5/33 : ℝ) * a38 + (2/11 : ℝ) * a44 + (1/11 : ℝ) * a45 + (2/11 : ℝ) * a49 + (2/11 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2042 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a38 : -(h 5) < (-1/9 : ℝ))
    (a45 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a48 : -(h 1) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/14 : ℝ) * _ctx.order3 + (1/28 : ℝ) * _ctx.fail1 + (1/42 : ℝ) * a20 + (3/7 : ℝ) * a33 + (4/21 : ℝ) * a38 + (3/28 : ℝ) * a45 + (3/14 : ℝ) * a48 + (3/14 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2041 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a38 : -(h 5) < (-1/9 : ℝ))
    (a44 : -(h 1) < (-4/31 : ℝ))
    (a45 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a47 : -(h 0) < (-7/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/32 : ℝ) * _ctx.fail1 + (3/16 : ℝ) * a24 + (3/16 : ℝ) * a33 + (3/16 : ℝ) * a38 + (3/16 : ℝ) * a44 + (3/32 : ℝ) * a45 + (1/8 : ℝ) * a47 + (3/16 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2040 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a46 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a25 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2039 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a25 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a38 : -(h 5) < (-1/9 : ℝ))
    (a44 : -(h 1) < (-4/31 : ℝ))
    (a45 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2040 h delta _ctx _hno a25 f0
  by_cases p1 : h 0 ≤ (7/47 : ℝ)
  swap
  · have f1 : -(h 0) < (-7/47 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2041 h delta _ctx _hno a24 a33 a38 a44 a45 f1
  by_cases p2 : h 1 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2042 h delta _ctx _hno a20 a33 a38 a45 f2
  by_cases p3 : h 2 ≤ (6/49 : ℝ)
  swap
  · have f3 : -(h 2) < (-6/49 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2043 h delta _ctx _hno a20 a33 a38 a44 a45 f3
  by_cases p4 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2044 h delta _ctx _hno a20 a33 a38 a44 a45 f4
  apply _hno 95
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (7/47 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 2 ≤ (6/49 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_2038 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a25 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a29 : h 0 ≤ (5/33 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a37 : h 3 ≤ (3/26 : ℝ))
    (a38 : -(h 5) < (-1/9 : ℝ))
    (a44 : -(h 1) < (-4/31 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2039 h delta _ctx _hno a20 a24 a25 a33 a38 a44 f0
  by_cases p1 : h 0 ≤ (3/19 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/19 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2045 h delta _ctx _hno a29 f1
  by_cases p2 : h 1 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2046 h delta _ctx _hno a20 a33 a38 f2
  by_cases p3 : h 2 ≤ (12/101 : ℝ)
  swap
  · have f3 : -(h 2) < (-12/101 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2047 h delta _ctx _hno a20 a33 a38 a44 f3
  by_cases p4 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2048 h delta _ctx _hno a37 f4
  by_cases p5 : h 4 ≤ (3/26 : ℝ)
  swap
  · have f5 : -(h 4) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_2049 h delta _ctx _hno a20 a38 a44 f5
  apply _hno 117
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 2 ≤ (12/101 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (3/26 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_2037 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : h 0 ≤ (5/33 : ℝ))
    (a43 : -(h 0) < (-3/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2036 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a42 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a25 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2035 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a25 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a29 : h 0 ≤ (5/33 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a37 : h 3 ≤ (3/26 : ℝ))
    (a38 : -(h 5) < (-1/9 : ℝ))
    (a41 : -(h 1) < (-9/70 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2036 h delta _ctx _hno a25 f0
  by_cases p1 : h 0 ≤ (3/19 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/19 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2037 h delta _ctx _hno a29 f1
  by_cases p2 : h 1 ≤ (4/31 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/31 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2038 h delta _ctx _hno a20 a24 a25 a29 a33 a37 a38 f2
  by_cases p3 : h 2 ≤ (3/25 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2050 h delta _ctx _hno a20 a24 a33 a38 a41 f3
  by_cases p4 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2051 h delta _ctx _hno a37 f4
  by_cases p5 : h 4 ≤ (3/26 : ℝ)
  swap
  · have f5 : -(h 4) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_2052 h delta _ctx _hno a20 a38 a41 f5
  apply _hno 113
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (4/31 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (3/26 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_2034 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : h 0 ≤ (5/33 : ℝ))
    (a40 : -(h 0) < (-7/45 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2033 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a39 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a25 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2032 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a25 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a29 : h 0 ≤ (5/33 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a37 : h 3 ≤ (3/26 : ℝ))
    (a38 : -(h 5) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2033 h delta _ctx _hno a25 f0
  by_cases p1 : h 0 ≤ (7/45 : ℝ)
  swap
  · have f1 : -(h 0) < (-7/45 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2034 h delta _ctx _hno a29 f1
  by_cases p2 : h 1 ≤ (9/70 : ℝ)
  swap
  · have f2 : -(h 1) < (-9/70 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2035 h delta _ctx _hno a20 a24 a25 a29 a33 a37 a38 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2053 h delta _ctx _hno a13 a20 a24 a33 a38 f3
  by_cases p4 : h 4 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 4) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2054 h delta _ctx _hno a13 a20 a27 a38 f4
  apply _hno 55
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (7/45 : ℝ)) ∧ (h 1 ≤ (9/70 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (4/35 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_2031 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a37 : -(h 3) < (-3/26 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a47 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/23 : ℝ) * _ctx.fail1 + (1/23 : ℝ) * a13 + (2/69 : ℝ) * a20 + (3/23 : ℝ) * a27 + (6/23 : ℝ) * a37 + (6/23 : ℝ) * a42 + (16/69 : ℝ) * a47 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2030 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a52 : -(h 4) < (-3/26 : ℝ))
    (a58 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.order3 + (1/23 : ℝ) * _ctx.fail1 + (1/23 : ℝ) * a13 + (2/69 : ℝ) * a20 + (3/23 : ℝ) * a27 + (12/23 : ℝ) * a52 + (16/69 : ℝ) * a58 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2029 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a52 : -(h 4) < (-3/26 : ℝ))
    (a57 : -(h 3) < (-5/43 : ℝ))
    (a63 : -(h 5) < (-5/44 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/23 : ℝ) * _ctx.fail1 + (1/23 : ℝ) * a13 + (2/69 : ℝ) * a20 + (3/23 : ℝ) * a27 + (6/23 : ℝ) * a52 + (6/23 : ℝ) * a57 + (16/69 : ℝ) * a63 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2028 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a51 : h 3 ≤ (2/17 : ℝ))
    (a62 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a51 + (1 : ℝ) * a62
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2027 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a56 : h 2 ≤ (9/76 : ℝ))
    (a61 : -(h 2) < (-5/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a56 + (1 : ℝ) * a61
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2026 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a52 : -(h 4) < (-3/26 : ℝ))
    (a57 : -(h 3) < (-5/43 : ℝ))
    (a60 : -(h 1) < (-12/95 : ℝ))
    (a66 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/25 : ℝ) * _ctx.lower + (1/25 : ℝ) * _ctx.fail1 + (2/75 : ℝ) * a20 + (6/25 : ℝ) * a52 + (6/25 : ℝ) * a57 + (6/25 : ℝ) * a60 + (16/75 : ℝ) * a66 + (6/25 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2025 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a60 : -(h 1) < (-12/95 : ℝ))
    (a65 : -(h 4) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (18/59 : ℝ) * _ctx.order3 + (16/59 : ℝ) * _ctx.min + (34/59 : ℝ) * _ctx.lower + (3/59 : ℝ) * _ctx.fail1 + (2/59 : ℝ) * a20 + (18/59 : ℝ) * a60 + (36/59 : ℝ) * a65 + (18/59 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2024 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a56 : h 2 ≤ (9/76 : ℝ))
    (a64 : -(h 2) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a56 + (1 : ℝ) * a64
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2023 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a46 : -(h 2) < (-2/17 : ℝ))
    (a52 : -(h 4) < (-3/26 : ℝ))
    (a57 : -(h 3) < (-5/43 : ℝ))
    (a63 : -(h 1) < (-10/79 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (11/25 : ℝ) * _ctx.lower + (1/25 : ℝ) * a20 + (6/25 : ℝ) * a46 + (6/25 : ℝ) * a52 + (6/25 : ℝ) * a57 + (6/25 : ℝ) * a63 + (6/25 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2022 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : h 0 ≤ (5/33 : ℝ))
    (a62 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a62
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2021 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a53 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a61 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a53 + (1 : ℝ) * a61
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2020 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a29 : h 0 ≤ (5/33 : ℝ))
    (a46 : -(h 2) < (-2/17 : ℝ))
    (a52 : -(h 4) < (-3/26 : ℝ))
    (a53 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a56 : h 2 ≤ (9/76 : ℝ))
    (a57 : -(h 3) < (-5/43 : ℝ))
    (a60 : -(h 1) < (-12/95 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2021 h delta _ctx _hno a53 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2022 h delta _ctx _hno a29 f1
  by_cases p2 : h 1 ≤ (10/79 : ℝ)
  swap
  · have f2 : -(h 1) < (-10/79 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2023 h delta _ctx _hno a20 a46 a52 a57 f2
  by_cases p3 : h 2 ≤ (3/25 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2024 h delta _ctx _hno a56 f3
  by_cases p4 : h 4 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 4) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2025 h delta _ctx _hno a20 a60 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_2026 h delta _ctx _hno a20 a52 a57 a60 f5
  apply _hno 128
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (10/79 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_2019 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : h 0 ≤ (5/33 : ℝ))
    (a59 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a59
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2018 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a46 : -(h 2) < (-2/17 : ℝ))
    (a52 : -(h 4) < (-3/26 : ℝ))
    (a57 : -(h 3) < (-5/43 : ℝ))
    (a58 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (10/61 : ℝ) * _ctx.min + (2/61 : ℝ) * a20 + (12/61 : ℝ) * a27 + (12/61 : ℝ) * a46 + (12/61 : ℝ) * a52 + (12/61 : ℝ) * a57 + (11/61 : ℝ) * a58 + (12/61 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2017 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a29 : h 0 ≤ (5/33 : ℝ))
    (a46 : -(h 2) < (-2/17 : ℝ))
    (a51 : h 3 ≤ (2/17 : ℝ))
    (a52 : -(h 4) < (-3/26 : ℝ))
    (a53 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a56 : h 2 ≤ (9/76 : ℝ))
    (a57 : -(h 3) < (-5/43 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2018 h delta _ctx _hno a20 a27 a46 a52 a57 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2019 h delta _ctx _hno a29 f1
  by_cases p2 : h 1 ≤ (12/95 : ℝ)
  swap
  · have f2 : -(h 1) < (-12/95 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2020 h delta _ctx _hno a20 a29 a46 a52 a53 a56 a57 f2
  by_cases p3 : h 2 ≤ (5/41 : ℝ)
  swap
  · have f3 : -(h 2) < (-5/41 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2027 h delta _ctx _hno a56 f3
  by_cases p4 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2028 h delta _ctx _hno a51 f4
  by_cases p5 : h 5 ≤ (5/44 : ℝ)
  swap
  · have f5 : -(h 5) < (-5/44 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_2029 h delta _ctx _hno a13 a20 a27 a52 a57 f5
  apply _hno 127
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (12/95 : ℝ)) ∧ (h 2 ≤ (5/41 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (5/44 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_2016 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a52 : -(h 4) < (-3/26 : ℝ))
    (a62 : -(h 5) < (-5/44 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.order3 + (1/23 : ℝ) * _ctx.fail1 + (1/23 : ℝ) * a13 + (2/69 : ℝ) * a20 + (3/23 : ℝ) * a27 + (12/23 : ℝ) * a52 + (16/69 : ℝ) * a62 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2015 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a52 : -(h 4) < (-3/26 : ℝ))
    (a56 : -(h 2) < (-9/76 : ℝ))
    (a61 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (15/64 : ℝ) * _ctx.min + (11/128 : ℝ) * a13 + (3/64 : ℝ) * a20 + (3/128 : ℝ) * a27 + (9/32 : ℝ) * a52 + (9/32 : ℝ) * a56 + (9/32 : ℝ) * a61 + (9/32 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2014 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a50 : h 2 ≤ (3/25 : ℝ))
    (a60 : -(h 2) < (-5/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a50 + (1 : ℝ) * a60
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2013 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a52 : -(h 4) < (-3/26 : ℝ))
    (a56 : -(h 2) < (-9/76 : ℝ))
    (a59 : -(h 1) < (-12/95 : ℝ))
    (a65 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.lower + (1/30 : ℝ) * a20 + (2/5 : ℝ) * a52 + (1/5 : ℝ) * a56 + (1/5 : ℝ) * a59 + (1/6 : ℝ) * a65 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2012 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a56 : -(h 2) < (-9/76 : ℝ))
    (a59 : -(h 1) < (-12/95 : ℝ))
    (a64 : -(h 4) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/25 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (11/25 : ℝ) * _ctx.lower + (1/25 : ℝ) * a20 + (6/25 : ℝ) * a56 + (6/25 : ℝ) * a59 + (12/25 : ℝ) * a64 + (6/25 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2011 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a37 : -(h 3) < (-3/26 : ℝ))
    (a52 : -(h 4) < (-3/26 : ℝ))
    (a59 : -(h 1) < (-12/95 : ℝ))
    (a63 : -(h 2) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (11/25 : ℝ) * _ctx.lower + (1/25 : ℝ) * a20 + (6/25 : ℝ) * a37 + (6/25 : ℝ) * a52 + (6/25 : ℝ) * a59 + (6/25 : ℝ) * a63 + (6/25 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2010 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a37 : -(h 3) < (-3/26 : ℝ))
    (a52 : -(h 4) < (-3/26 : ℝ))
    (a56 : -(h 2) < (-9/76 : ℝ))
    (a62 : -(h 1) < (-10/79 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (11/25 : ℝ) * _ctx.lower + (1/25 : ℝ) * a20 + (6/25 : ℝ) * a37 + (6/25 : ℝ) * a52 + (6/25 : ℝ) * a56 + (6/25 : ℝ) * a62 + (6/25 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2009 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : h 0 ≤ (5/33 : ℝ))
    (a61 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a61
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2008 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a53 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a60 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a53 + (1 : ℝ) * a60
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2007 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a29 : h 0 ≤ (5/33 : ℝ))
    (a37 : -(h 3) < (-3/26 : ℝ))
    (a52 : -(h 4) < (-3/26 : ℝ))
    (a53 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a56 : -(h 2) < (-9/76 : ℝ))
    (a59 : -(h 1) < (-12/95 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2008 h delta _ctx _hno a53 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2009 h delta _ctx _hno a29 f1
  by_cases p2 : h 1 ≤ (10/79 : ℝ)
  swap
  · have f2 : -(h 1) < (-10/79 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2010 h delta _ctx _hno a20 a37 a52 a56 f2
  by_cases p3 : h 2 ≤ (3/25 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2011 h delta _ctx _hno a20 a37 a52 a59 f3
  by_cases p4 : h 4 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 4) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2012 h delta _ctx _hno a20 a56 a59 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_2013 h delta _ctx _hno a20 a52 a56 a59 f5
  apply _hno 128
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (10/79 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_2006 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : h 0 ≤ (5/33 : ℝ))
    (a58 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a58
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2005 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a52 : -(h 4) < (-3/26 : ℝ))
    (a56 : -(h 2) < (-9/76 : ℝ))
    (a57 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (12/61 : ℝ) * _ctx.order3 + (10/61 : ℝ) * _ctx.min + (2/61 : ℝ) * a20 + (12/61 : ℝ) * a27 + (24/61 : ℝ) * a52 + (12/61 : ℝ) * a56 + (11/61 : ℝ) * a57 + (12/61 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2004 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a29 : h 0 ≤ (5/33 : ℝ))
    (a37 : -(h 3) < (-3/26 : ℝ))
    (a50 : h 2 ≤ (3/25 : ℝ))
    (a52 : -(h 4) < (-3/26 : ℝ))
    (a53 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a56 : -(h 2) < (-9/76 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2005 h delta _ctx _hno a20 a27 a52 a56 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2006 h delta _ctx _hno a29 f1
  by_cases p2 : h 1 ≤ (12/95 : ℝ)
  swap
  · have f2 : -(h 1) < (-12/95 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2007 h delta _ctx _hno a20 a29 a37 a52 a53 a56 f2
  by_cases p3 : h 2 ≤ (5/41 : ℝ)
  swap
  · have f3 : -(h 2) < (-5/41 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2014 h delta _ctx _hno a50 f3
  by_cases p4 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2015 h delta _ctx _hno a13 a20 a27 a52 a56 f4
  by_cases p5 : h 5 ≤ (5/44 : ℝ)
  swap
  · have f5 : -(h 5) < (-5/44 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_2016 h delta _ctx _hno a13 a20 a27 a52 f5
  apply _hno 127
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (12/95 : ℝ)) ∧ (h 2 ≤ (5/41 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (5/44 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_2003 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a40 : h 1 ≤ (9/70 : ℝ))
    (a55 : -(h 1) < (-3/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a40 + (1 : ℝ) * a55
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2002 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : h 0 ≤ (5/33 : ℝ))
    (a54 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a54
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2001 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a52 : -(h 4) < (-3/26 : ℝ))
    (a53 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a59 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/14 : ℝ) * _ctx.order3 + (1/28 : ℝ) * _ctx.fail1 + (1/42 : ℝ) * a20 + (3/14 : ℝ) * a27 + (3/7 : ℝ) * a52 + (3/28 : ℝ) * a53 + (4/21 : ℝ) * a59 + (3/14 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2000 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a53 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a58 : -(h 4) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (9/38 : ℝ) * _ctx.order3 + (4/19 : ℝ) * _ctx.min + (3/76 : ℝ) * _ctx.fail1 + (1/38 : ℝ) * a20 + (9/38 : ℝ) * a27 + (17/76 : ℝ) * a53 + (9/19 : ℝ) * a58 + (9/38 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1999 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a52 : -(h 4) < (-3/26 : ℝ))
    (a53 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a57 : -(h 2) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (12/61 : ℝ) * _ctx.order3 + (10/61 : ℝ) * _ctx.min + (2/61 : ℝ) * a20 + (12/61 : ℝ) * a27 + (24/61 : ℝ) * a52 + (11/61 : ℝ) * a53 + (12/61 : ℝ) * a57 + (12/61 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1998 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a46 : -(h 2) < (-2/17 : ℝ))
    (a52 : -(h 4) < (-3/26 : ℝ))
    (a53 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a56 : -(h 1) < (-10/79 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (12/61 : ℝ) * _ctx.order3 + (10/61 : ℝ) * _ctx.min + (2/61 : ℝ) * a20 + (12/61 : ℝ) * a46 + (24/61 : ℝ) * a52 + (11/61 : ℝ) * a53 + (12/61 : ℝ) * a56 + (12/61 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1997 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : h 0 ≤ (5/33 : ℝ))
    (a55 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a55
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1996 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a54 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a25 + (1 : ℝ) * a54
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1995 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a25 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a29 : h 0 ≤ (5/33 : ℝ))
    (a46 : -(h 2) < (-2/17 : ℝ))
    (a52 : -(h 4) < (-3/26 : ℝ))
    (a53 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1996 h delta _ctx _hno a25 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1997 h delta _ctx _hno a29 f1
  by_cases p2 : h 1 ≤ (10/79 : ℝ)
  swap
  · have f2 : -(h 1) < (-10/79 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1998 h delta _ctx _hno a20 a46 a52 a53 f2
  by_cases p3 : h 2 ≤ (3/25 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1999 h delta _ctx _hno a20 a27 a52 a53 f3
  by_cases p4 : h 4 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 4) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2000 h delta _ctx _hno a20 a27 a53 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_2001 h delta _ctx _hno a20 a27 a52 a53 f5
  apply _hno 128
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (10/79 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_1994 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a25 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a29 : h 0 ≤ (5/33 : ℝ))
    (a37 : -(h 3) < (-3/26 : ℝ))
    (a40 : h 1 ≤ (9/70 : ℝ))
    (a46 : -(h 2) < (-2/17 : ℝ))
    (a50 : h 2 ≤ (3/25 : ℝ))
    (a51 : h 3 ≤ (2/17 : ℝ))
    (a52 : -(h 4) < (-3/26 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1995 h delta _ctx _hno a20 a25 a27 a29 a46 a52 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2002 h delta _ctx _hno a29 f1
  by_cases p2 : h 1 ≤ (3/22 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2003 h delta _ctx _hno a40 f2
  by_cases p3 : h 2 ≤ (9/76 : ℝ)
  swap
  · have f3 : -(h 2) < (-9/76 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2004 h delta _ctx _hno a13 a20 a27 a29 a37 a50 a52 p0 f3
  by_cases p4 : h 3 ≤ (5/43 : ℝ)
  swap
  · have f4 : -(h 3) < (-5/43 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2017 h delta _ctx _hno a13 a20 a27 a29 a46 a51 a52 p0 p3 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_2030 h delta _ctx _hno a13 a20 a27 a52 f5
  apply _hno 121
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 2 ≤ (9/76 : ℝ)) ∧ (h 3 ≤ (5/43 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_1993 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a51 : -(h 3) < (-2/17 : ℝ))
    (a57 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/23 : ℝ) * _ctx.fail1 + (1/23 : ℝ) * a13 + (2/69 : ℝ) * a20 + (3/23 : ℝ) * a27 + (6/23 : ℝ) * a42 + (6/23 : ℝ) * a51 + (16/69 : ℝ) * a57 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1992 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a46 : -(h 2) < (-2/17 : ℝ))
    (a56 : -(h 4) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (9/32 : ℝ) * _ctx.order3 + (15/64 : ℝ) * _ctx.min + (11/128 : ℝ) * a13 + (3/64 : ℝ) * a20 + (3/128 : ℝ) * a27 + (9/32 : ℝ) * a46 + (9/16 : ℝ) * a56 + (9/32 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1991 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a51 : -(h 3) < (-2/17 : ℝ))
    (a55 : -(h 2) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (15/64 : ℝ) * _ctx.min + (11/128 : ℝ) * a13 + (3/64 : ℝ) * a20 + (3/128 : ℝ) * a27 + (9/32 : ℝ) * a42 + (9/32 : ℝ) * a51 + (9/32 : ℝ) * a55 + (9/32 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1990 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a46 : -(h 2) < (-2/17 : ℝ))
    (a51 : -(h 3) < (-2/17 : ℝ))
    (a54 : -(h 1) < (-10/79 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (11/25 : ℝ) * _ctx.lower + (1/25 : ℝ) * a20 + (6/25 : ℝ) * a42 + (6/25 : ℝ) * a46 + (6/25 : ℝ) * a51 + (6/25 : ℝ) * a54 + (6/25 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1989 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : h 0 ≤ (5/33 : ℝ))
    (a53 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a53
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1988 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a52 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a25 + (1 : ℝ) * a52
  exact (lt_irrefl (0 : ℝ)) hbad

end RealPinwheel.WeakSevenBandData
