import Pinwheel.WeakSevenBandData.CoverChunks.Upper033

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem upper_node_1587 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a34 : -(h 4) < (-1/9 : ℝ))
    (a40 : -(h 2) < (-7/60 : ℝ))
    (a45 : -(h 0) < (-3/19 : ℝ))
    (a48 : -(h 1) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a24 + (1/5 : ℝ) * a34 + (1/5 : ℝ) * a40 + (1/5 : ℝ) * a45 + (1/5 : ℝ) * a48 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1586 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a26 : h 0 ≤ (4/25 : ℝ))
    (a47 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a26 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1585 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a34 : -(h 4) < (-1/9 : ℝ))
    (a40 : -(h 2) < (-7/60 : ℝ))
    (a43 : -(h 1) < (-6/47 : ℝ))
    (a45 : -(h 0) < (-3/19 : ℝ))
    (a53 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.lower + (1/3 : ℝ) * a34 + (1/6 : ℝ) * a40 + (1/6 : ℝ) * a43 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a53 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1584 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a40 : -(h 2) < (-7/60 : ℝ))
    (a43 : -(h 1) < (-6/47 : ℝ))
    (a45 : -(h 0) < (-3/19 : ℝ))
    (a52 : -(h 4) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a40 + (1/5 : ℝ) * a43 + (1/5 : ℝ) * a45 + (2/5 : ℝ) * a52 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1583 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a34 : -(h 4) < (-1/9 : ℝ))
    (a40 : -(h 2) < (-7/60 : ℝ))
    (a43 : -(h 1) < (-6/47 : ℝ))
    (a45 : -(h 0) < (-3/19 : ℝ))
    (a51 : -(h 3) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a34 + (1/5 : ℝ) * a40 + (1/5 : ℝ) * a43 + (1/5 : ℝ) * a45 + (1/5 : ℝ) * a51 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1582 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a34 : -(h 4) < (-1/9 : ℝ))
    (a43 : -(h 1) < (-6/47 : ℝ))
    (a45 : -(h 0) < (-3/19 : ℝ))
    (a50 : -(h 2) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a24 + (1/5 : ℝ) * a34 + (1/5 : ℝ) * a43 + (1/5 : ℝ) * a45 + (1/5 : ℝ) * a50 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1581 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a34 : -(h 4) < (-1/9 : ℝ))
    (a40 : -(h 2) < (-7/60 : ℝ))
    (a45 : -(h 0) < (-3/19 : ℝ))
    (a49 : -(h 1) < (-4/31 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a24 + (1/5 : ℝ) * a34 + (1/5 : ℝ) * a40 + (1/5 : ℝ) * a45 + (1/5 : ℝ) * a49 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1580 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a26 : h 0 ≤ (4/25 : ℝ))
    (a48 : -(h 0) < (-4/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a26 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1579 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a34 : -(h 4) < (-1/9 : ℝ))
    (a40 : -(h 2) < (-7/60 : ℝ))
    (a43 : -(h 1) < (-6/47 : ℝ))
    (a45 : -(h 0) < (-3/19 : ℝ))
    (a47 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a24 + (1/6 : ℝ) * a34 + (1/6 : ℝ) * a40 + (1/6 : ℝ) * a43 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1578 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a26 : h 0 ≤ (4/25 : ℝ))
    (a34 : -(h 4) < (-1/9 : ℝ))
    (a40 : -(h 2) < (-7/60 : ℝ))
    (a43 : -(h 1) < (-6/47 : ℝ))
    (a45 : -(h 0) < (-3/19 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1579 h delta _ctx _hno a24 a34 a40 a43 a45 f0
  by_cases p1 : h 0 ≤ (4/23 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/23 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1580 h delta _ctx _hno a26 f1
  by_cases p2 : h 1 ≤ (4/31 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/31 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1581 h delta _ctx _hno a24 a34 a40 a45 f2
  by_cases p3 : h 2 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1582 h delta _ctx _hno a24 a34 a43 a45 f3
  by_cases p4 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1583 h delta _ctx _hno a34 a40 a43 a45 f4
  by_cases p5 : h 4 ≤ (4/35 : ℝ)
  swap
  · have f5 : -(h 4) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1584 h delta _ctx _hno a40 a43 a45 f5
  by_cases p6 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f6 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact upper_node_1585 h delta _ctx _hno a34 a40 a43 a45 f6
  apply _hno 80
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (4/23 : ℝ)) ∧ (h 1 ≤ (4/31 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 4 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem upper_node_1577 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a26 : h 0 ≤ (4/25 : ℝ))
    (a34 : -(h 4) < (-1/9 : ℝ))
    (a40 : -(h 2) < (-7/60 : ℝ))
    (a43 : -(h 1) < (-6/47 : ℝ))
    (a45 : -(h 0) < (-3/19 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1578 h delta _ctx _hno a24 a26 a34 a40 a43 a45
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1586 h delta _ctx _hno a26 f1
  by_cases p2 : h 1 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1587 h delta _ctx _hno a24 a34 a40 a45 f2
  by_cases p3 : h 3 ≤ (7/62 : ℝ)
  swap
  · have f3 : -(h 3) < (-7/62 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1588 h delta _ctx _hno a34 a40 a43 a45 f3
  by_cases p4 : h 5 ≤ (4/37 : ℝ)
  swap
  · have f4 : -(h 5) < (-4/37 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1589 h delta _ctx _hno a24 a34 a40 a43 a45 f4
  apply _hno 18
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (7/62 : ℝ)) ∧ (h 5 ≤ (4/37 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_1576 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a41 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a44 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a41 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1575 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a26 : h 0 ≤ (4/25 : ℝ))
    (a34 : -(h 4) < (-1/9 : ℝ))
    (a36 : -(h 0) < (-7/45 : ℝ))
    (a40 : -(h 2) < (-7/60 : ℝ))
    (a41 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a43 : -(h 1) < (-6/47 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1576 h delta _ctx _hno a41 f0
  by_cases p1 : h 0 ≤ (3/19 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/19 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1577 h delta _ctx _hno a24 a26 a34 a40 a43 f1
  by_cases p2 : h 1 ≤ (4/31 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/31 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1590 h delta _ctx _hno a24 a34 a36 a40 a41 p1 f2
  by_cases p3 : h 2 ≤ (3/25 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1620 h delta _ctx _hno a24 a34 a36 a43 f3
  by_cases p4 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1621 h delta _ctx _hno a34 a36 a43 f4
  by_cases p5 : h 4 ≤ (3/26 : ℝ)
  swap
  · have f5 : -(h 4) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1622 h delta _ctx _hno a36 a40 a43 f5
  apply _hno 113
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (4/31 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (3/26 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_1574 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a26 : h 0 ≤ (4/25 : ℝ))
    (a42 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a26 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1573 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a34 : -(h 4) < (-1/9 : ℝ))
    (a36 : -(h 0) < (-7/45 : ℝ))
    (a40 : -(h 2) < (-7/60 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a47 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * a24 + (2/13 : ℝ) * a27 + (2/13 : ℝ) * a34 + (2/13 : ℝ) * a36 + (2/13 : ℝ) * a40 + (1/13 : ℝ) * a41 + (2/13 : ℝ) * a47 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1572 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a36 : -(h 0) < (-7/45 : ℝ))
    (a40 : -(h 2) < (-7/60 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a52 : -(h 4) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a36 + (1/6 : ℝ) * a40 + (1/6 : ℝ) * a41 + (1/3 : ℝ) * a52 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1571 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a34 : -(h 4) < (-1/9 : ℝ))
    (a36 : -(h 0) < (-7/45 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a51 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order2 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a34 + (1/6 : ℝ) * a36 + (1/6 : ℝ) * a41 + (1/3 : ℝ) * a51 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1570 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a34 : -(h 4) < (-1/9 : ℝ))
    (a36 : -(h 0) < (-7/45 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a46 : -(h 3) < (-4/35 : ℝ))
    (a50 : -(h 2) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a34 + (1/6 : ℝ) * a36 + (1/6 : ℝ) * a41 + (1/6 : ℝ) * a46 + (1/6 : ℝ) * a50 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1569 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a34 : -(h 4) < (-1/9 : ℝ))
    (a36 : -(h 0) < (-7/45 : ℝ))
    (a40 : -(h 2) < (-7/60 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a46 : -(h 3) < (-4/35 : ℝ))
    (a49 : -(h 1) < (-4/31 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a34 + (1/6 : ℝ) * a36 + (1/6 : ℝ) * a40 + (1/6 : ℝ) * a41 + (1/6 : ℝ) * a46 + (1/6 : ℝ) * a49 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1568 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a34 : -(h 4) < (-1/9 : ℝ))
    (a40 : -(h 2) < (-7/60 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a46 : -(h 3) < (-4/35 : ℝ))
    (a48 : -(h 0) < (-3/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a34 + (1/6 : ℝ) * a40 + (1/6 : ℝ) * a41 + (1/6 : ℝ) * a46 + (1/6 : ℝ) * a48 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1567 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a36 : -(h 0) < (-7/45 : ℝ))
    (a47 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * a14 + (1/5 : ℝ) * a36 + (4/5 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1566 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a34 : -(h 4) < (-1/9 : ℝ))
    (a36 : -(h 0) < (-7/45 : ℝ))
    (a40 : -(h 2) < (-7/60 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a46 : -(h 3) < (-4/35 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1567 h delta _ctx _hno a14 a36 f0
  by_cases p1 : h 0 ≤ (3/19 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/19 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1568 h delta _ctx _hno a27 a34 a40 a41 a46 f1
  by_cases p2 : h 1 ≤ (4/31 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/31 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1569 h delta _ctx _hno a34 a36 a40 a41 a46 f2
  by_cases p3 : h 2 ≤ (3/25 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1570 h delta _ctx _hno a27 a34 a36 a41 a46 f3
  by_cases p4 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1571 h delta _ctx _hno a27 a34 a36 a41 f4
  by_cases p5 : h 4 ≤ (3/26 : ℝ)
  swap
  · have f5 : -(h 4) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1572 h delta _ctx _hno a27 a36 a40 a41 f5
  apply _hno 113
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (4/31 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (3/26 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_1565 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a34 : -(h 4) < (-1/9 : ℝ))
    (a36 : -(h 0) < (-7/45 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a45 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order1 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a24 + (1/6 : ℝ) * a34 + (1/6 : ℝ) * a36 + (1/6 : ℝ) * a41 + (1/3 : ℝ) * a45 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1564 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a34 : -(h 4) < (-1/9 : ℝ))
    (a36 : -(h 0) < (-7/45 : ℝ))
    (a40 : -(h 2) < (-7/60 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a44 : -(h 1) < (-4/31 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a24 + (1/6 : ℝ) * a34 + (1/6 : ℝ) * a36 + (1/6 : ℝ) * a40 + (1/6 : ℝ) * a41 + (1/6 : ℝ) * a44 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1563 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a43 : -(h 0) < (-3/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * a14 + (4/5 : ℝ) * a41 + (1/5 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1562 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a36 : -(h 0) < (-7/45 : ℝ))
    (a42 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * a14 + (1/5 : ℝ) * a36 + (4/5 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1561 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a34 : -(h 4) < (-1/9 : ℝ))
    (a36 : -(h 0) < (-7/45 : ℝ))
    (a40 : -(h 2) < (-7/60 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1562 h delta _ctx _hno a14 a36 f0
  by_cases p1 : h 0 ≤ (3/19 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/19 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1563 h delta _ctx _hno a14 a41 f1
  by_cases p2 : h 1 ≤ (4/31 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/31 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1564 h delta _ctx _hno a24 a34 a36 a40 a41 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1565 h delta _ctx _hno a24 a34 a36 a41 f3
  by_cases p4 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1566 h delta _ctx _hno a14 a27 a34 a36 a40 a41 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1573 h delta _ctx _hno a24 a27 a34 a36 a40 a41 f5
  apply _hno 85
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (4/31 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_1560 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a26 : h 0 ≤ (4/25 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a34 : -(h 4) < (-1/9 : ℝ))
    (a36 : -(h 0) < (-7/45 : ℝ))
    (a40 : -(h 2) < (-7/60 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1561 h delta _ctx _hno a14 a24 a27 a34 a36 a40 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1574 h delta _ctx _hno a26 f1
  by_cases p2 : h 1 ≤ (6/47 : ℝ)
  swap
  · have f2 : -(h 1) < (-6/47 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1575 h delta _ctx _hno a24 a26 a34 a36 a40 p0 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1623 h delta _ctx _hno a13 a24 a34 a36 f3
  by_cases p4 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1624 h delta _ctx _hno a13 a26 a27 a34 a36 a40 p0 p2 f4
  by_cases p5 : h 5 ≤ (5/44 : ℝ)
  swap
  · have f5 : -(h 5) < (-5/44 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1638 h delta _ctx _hno a13 a27 a36 a40 f5
  apply _hno 104
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (6/47 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (5/44 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_1559 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a34 : -(h 4) < (-1/9 : ℝ))
    (a36 : -(h 0) < (-7/45 : ℝ))
    (a39 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.min + (12/23 : ℝ) * _ctx.lower + (1/23 : ℝ) * _ctx.fail1 + (6/23 : ℝ) * a24 + (6/23 : ℝ) * a34 + (4/23 : ℝ) * a36 + (6/23 : ℝ) * a39 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1558 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a26 : h 0 ≤ (4/25 : ℝ))
    (a38 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a26 + (1 : ℝ) * a38
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1557 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a37 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a25 + (1 : ℝ) * a37
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1556 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a25 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a26 : h 0 ≤ (4/25 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a34 : -(h 4) < (-1/9 : ℝ))
    (a36 : -(h 0) < (-7/45 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1557 h delta _ctx _hno a25 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1558 h delta _ctx _hno a26 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1559 h delta _ctx _hno a24 a34 a36 f2
  by_cases p3 : h 2 ≤ (7/60 : ℝ)
  swap
  · have f3 : -(h 2) < (-7/60 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1560 h delta _ctx _hno a13 a14 a24 a26 a27 a34 a36 f3
  by_cases p4 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1639 h delta _ctx _hno a13 a14 a27 a34 a36 p3 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1652 h delta _ctx _hno a13 a24 a26 a27 a34 a36 p3 f5
  apply _hno 54
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (7/60 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_1555 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a35 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a25 + (1 : ℝ) * a35
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1554 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a25 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a26 : h 0 ≤ (4/25 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a29 : -(h 0) < (-5/33 : ℝ))
    (a32 : h 1 ≤ (2/15 : ℝ))
    (a33 : h 2 ≤ (1/8 : ℝ))
    (a34 : -(h 4) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1555 h delta _ctx _hno a25 f0
  by_cases p1 : h 0 ≤ (7/45 : ℝ)
  swap
  · have f1 : -(h 0) < (-7/45 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1556 h delta _ctx _hno a13 a14 a24 a25 a26 a27 a34 f1
  by_cases p2 : h 1 ≤ (9/70 : ℝ)
  swap
  · have f2 : -(h 1) < (-9/70 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1659 h delta _ctx _hno a14 a24 a25 a29 a32 a34 p1 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1768 h delta _ctx _hno a33 f3
  by_cases p4 : h 4 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 4) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1769 h delta _ctx _hno a13 a14 a25 a27 a29 p1 p2 f4
  apply _hno 55
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (7/45 : ℝ)) ∧ (h 1 ≤ (9/70 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (4/35 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_1553 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a29 : -(h 0) < (-5/33 : ℝ))
    (a33 : -(h 2) < (-1/8 : ℝ))
    (a38 : -(h 4) < (-1/9 : ℝ))
    (a43 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/34 : ℝ) * a13 + (3/17 : ℝ) * a24 + (3/34 : ℝ) * a27 + (3/17 : ℝ) * a29 + (3/17 : ℝ) * a33 + (3/17 : ℝ) * a38 + (3/17 : ℝ) * a43 + (3/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1552 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a29 : -(h 0) < (-5/33 : ℝ))
    (a33 : -(h 2) < (-1/8 : ℝ))
    (a38 : -(h 4) < (-1/9 : ℝ))
    (a42 : -(h 3) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/13 : ℝ) * _ctx.min + (1/13 : ℝ) * a13 + (3/13 : ℝ) * a29 + (3/13 : ℝ) * a33 + (3/13 : ℝ) * a38 + (3/13 : ℝ) * a42 + (3/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1551 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a36 : h 1 ≤ (7/54 : ℝ))
    (a41 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a36 + (1 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1550 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a33 : -(h 2) < (-1/8 : ℝ))
    (a38 : -(h 4) < (-1/9 : ℝ))
    (a40 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/13 : ℝ) * _ctx.min + (1/13 : ℝ) * a13 + (3/13 : ℝ) * a24 + (3/13 : ℝ) * a33 + (3/13 : ℝ) * a38 + (3/13 : ℝ) * a40 + (3/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1549 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a39 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a25 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1548 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a25 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a29 : -(h 0) < (-5/33 : ℝ))
    (a33 : -(h 2) < (-1/8 : ℝ))
    (a36 : h 1 ≤ (7/54 : ℝ))
    (a38 : -(h 4) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1549 h delta _ctx _hno a25 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1550 h delta _ctx _hno a13 a24 a33 a38 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1551 h delta _ctx _hno a36 f2
  by_cases p3 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f3 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1552 h delta _ctx _hno a13 a29 a33 a38 f3
  by_cases p4 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1553 h delta _ctx _hno a13 a24 a27 a29 a33 a38 f4
  apply _hno 19
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_1547 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a29 : -(h 0) < (-5/33 : ℝ))
    (a33 : -(h 2) < (-1/8 : ℝ))
    (a37 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/10 : ℝ) * _ctx.min + (1/10 : ℝ) * a13 + (3/80 : ℝ) * a18 + (21/80 : ℝ) * a29 + (3/10 : ℝ) * a33 + (3/10 : ℝ) * a37 + (3/10 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1546 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a29 : -(h 0) < (-5/33 : ℝ))
    (a33 : -(h 2) < (-1/8 : ℝ))
    (a36 : -(h 1) < (-7/54 : ℝ))
    (a41 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order4 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a24 + (1/6 : ℝ) * a29 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a36 + (1/3 : ℝ) * a41 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1545 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a29 : -(h 0) < (-5/33 : ℝ))
    (a33 : -(h 2) < (-1/8 : ℝ))
    (a36 : -(h 1) < (-7/54 : ℝ))
    (a40 : -(h 3) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.min + (1/2 : ℝ) * _ctx.lower + (1/32 : ℝ) * a18 + (7/32 : ℝ) * a29 + (1/4 : ℝ) * a33 + (1/4 : ℝ) * a36 + (1/4 : ℝ) * a40 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1544 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a29 : -(h 0) < (-5/33 : ℝ))
    (a33 : -(h 2) < (-1/8 : ℝ))
    (a39 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.min + (1/2 : ℝ) * _ctx.lower + (1/32 : ℝ) * a18 + (1/4 : ℝ) * a24 + (7/32 : ℝ) * a29 + (1/4 : ℝ) * a33 + (1/4 : ℝ) * a39 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1543 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a33 : -(h 2) < (-1/8 : ℝ))
    (a36 : -(h 1) < (-7/54 : ℝ))
    (a38 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.min + (1/2 : ℝ) * _ctx.lower + (1/32 : ℝ) * a18 + (1/4 : ℝ) * a24 + (1/4 : ℝ) * a33 + (1/4 : ℝ) * a36 + (7/32 : ℝ) * a38 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1542 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a37 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a25 + (1 : ℝ) * a37
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1541 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a25 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a29 : -(h 0) < (-5/33 : ℝ))
    (a33 : -(h 2) < (-1/8 : ℝ))
    (a36 : -(h 1) < (-7/54 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1542 h delta _ctx _hno a25 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1543 h delta _ctx _hno a18 a24 a33 a36 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1544 h delta _ctx _hno a18 a24 a29 a33 f2
  by_cases p3 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f3 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1545 h delta _ctx _hno a18 a29 a33 a36 f3
  by_cases p4 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1546 h delta _ctx _hno a24 a29 a33 a36 f4
  apply _hno 19
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_1540 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a26 : h 0 ≤ (4/25 : ℝ))
    (a35 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a26 + (1 : ℝ) * a35
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1539 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a29 : -(h 0) < (-5/33 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * a14 + (1/5 : ℝ) * a29 + (4/5 : ℝ) * a34
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1538 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a25 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a26 : h 0 ≤ (4/25 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a29 : -(h 0) < (-5/33 : ℝ))
    (a33 : -(h 2) < (-1/8 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1539 h delta _ctx _hno a14 a29 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1540 h delta _ctx _hno a26 f1
  by_cases p2 : h 1 ≤ (7/54 : ℝ)
  swap
  · have f2 : -(h 1) < (-7/54 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1541 h delta _ctx _hno a18 a24 a25 a29 a33 f2
  by_cases p3 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1547 h delta _ctx _hno a13 a18 a29 a33 f3
  by_cases p4 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1548 h delta _ctx _hno a13 a24 a25 a27 a29 a33 p2 f4
  apply _hno 14
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (7/54 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_1537 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a37 : h 4 ≤ (3/28 : ℝ))
    (a44 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a37 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1536 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a36 : h 2 ≤ (2/17 : ℝ))
    (a43 : -(h 3) < (-7/57 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * _ctx.order2 + (1 : ℝ) * a36 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1535 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a36 : h 2 ≤ (2/17 : ℝ))
    (a42 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a36 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1534 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a29 : -(h 0) < (-5/33 : ℝ))
    (a41 : -(h 1) < (-3/22 : ℝ))
    (a47 : -(h 5) < (-3/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.order4 + (6/29 : ℝ) * _ctx.lower + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a24 + (4/29 : ℝ) * a29 + (6/29 : ℝ) * a41 + (12/29 : ℝ) * a47 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1533 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a37 : h 4 ≤ (3/28 : ℝ))
    (a46 : -(h 4) < (-6/55 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a37 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1532 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a36 : h 2 ≤ (2/17 : ℝ))
    (a45 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a36 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1531 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : h 1 ≤ (5/36 : ℝ))
    (a44 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a23 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1530 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a37 : h 4 ≤ (3/28 : ℝ))
    (a49 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a37 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1529 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a38 : -(h 5) < (-2/19 : ℝ))
    (a41 : -(h 1) < (-3/22 : ℝ))
    (a43 : -(h 0) < (-2/13 : ℝ))
    (a48 : -(h 3) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.lower + (1/23 : ℝ) * _ctx.fail1 + (3/92 : ℝ) * a18 + (6/23 : ℝ) * a38 + (6/23 : ℝ) * a41 + (13/92 : ℝ) * a43 + (6/23 : ℝ) * a48 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1528 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a37 : h 4 ≤ (3/28 : ℝ))
    (a53 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a37 + (1 : ℝ) * a53
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1527 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a38 : -(h 5) < (-2/19 : ℝ))
    (a41 : -(h 1) < (-3/22 : ℝ))
    (a43 : -(h 0) < (-2/13 : ℝ))
    (a47 : -(h 2) < (-5/43 : ℝ))
    (a52 : -(h 3) < (-9/80 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.lower + (1/40 : ℝ) * a18 + (1/5 : ℝ) * a38 + (1/5 : ℝ) * a41 + (7/40 : ℝ) * a43 + (1/5 : ℝ) * a47 + (1/5 : ℝ) * a52 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1526 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a38 : -(h 5) < (-2/19 : ℝ))
    (a41 : -(h 1) < (-3/22 : ℝ))
    (a43 : -(h 0) < (-2/13 : ℝ))
    (a51 : -(h 2) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.lower + (1/40 : ℝ) * a18 + (1/5 : ℝ) * a24 + (1/5 : ℝ) * a38 + (1/5 : ℝ) * a41 + (7/40 : ℝ) * a43 + (1/5 : ℝ) * a51 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1525 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : h 1 ≤ (5/36 : ℝ))
    (a50 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a23 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1524 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a38 : -(h 5) < (-2/19 : ℝ))
    (a41 : -(h 1) < (-3/22 : ℝ))
    (a47 : -(h 2) < (-5/43 : ℝ))
    (a49 : -(h 0) < (-5/32 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.lower + (1/40 : ℝ) * a18 + (1/5 : ℝ) * a24 + (1/5 : ℝ) * a38 + (1/5 : ℝ) * a41 + (1/5 : ℝ) * a47 + (7/40 : ℝ) * a49 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1523 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a48 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1522 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a23 : h 1 ≤ (5/36 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a33 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a37 : h 4 ≤ (3/28 : ℝ))
    (a38 : -(h 5) < (-2/19 : ℝ))
    (a41 : -(h 1) < (-3/22 : ℝ))
    (a43 : -(h 0) < (-2/13 : ℝ))
    (a47 : -(h 2) < (-5/43 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1523 h delta _ctx _hno a33 f0
  by_cases p1 : h 0 ≤ (5/32 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/32 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1524 h delta _ctx _hno a18 a24 a38 a41 a47 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1525 h delta _ctx _hno a23 f2
  by_cases p3 : h 2 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1526 h delta _ctx _hno a18 a24 a38 a41 a43 f3
  by_cases p4 : h 3 ≤ (9/80 : ℝ)
  swap
  · have f4 : -(h 3) < (-9/80 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1527 h delta _ctx _hno a18 a38 a41 a43 a47 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1528 h delta _ctx _hno a37 f5
  apply _hno 105
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (5/32 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 3 ≤ (9/80 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_1521 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : h 1 ≤ (5/36 : ℝ))
    (a46 : -(h 1) < (-6/43 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a23 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1520 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a38 : -(h 5) < (-2/19 : ℝ))
    (a41 : -(h 1) < (-3/22 : ℝ))
    (a45 : -(h 0) < (-4/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.lower + (1/23 : ℝ) * _ctx.fail1 + (3/92 : ℝ) * a18 + (6/23 : ℝ) * a24 + (6/23 : ℝ) * a38 + (6/23 : ℝ) * a41 + (13/92 : ℝ) * a45 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1519 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a44 : ((-2 : ℝ) * (delta)) < (-10/43 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1518 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a23 : h 1 ≤ (5/36 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a33 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a37 : h 4 ≤ (3/28 : ℝ))
    (a38 : -(h 5) < (-2/19 : ℝ))
    (a41 : -(h 1) < (-3/22 : ℝ))
    (a43 : -(h 0) < (-2/13 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (10/43 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-10/43 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1519 h delta _ctx _hno a33 f0
  by_cases p1 : h 0 ≤ (4/25 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/25 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1520 h delta _ctx _hno a18 a24 a38 a41 f1
  by_cases p2 : h 1 ≤ (6/43 : ℝ)
  swap
  · have f2 : -(h 1) < (-6/43 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1521 h delta _ctx _hno a23 f2
  by_cases p3 : h 2 ≤ (5/43 : ℝ)
  swap
  · have f3 : -(h 2) < (-5/43 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1522 h delta _ctx _hno a18 a23 a24 a33 a37 a38 a41 a43 f3
  by_cases p4 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1529 h delta _ctx _hno a18 a38 a41 a43 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1530 h delta _ctx _hno a37 f5
  apply _hno 74
  change (((2 : ℝ) * (delta)) ≤ (10/43 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (6/43 : ℝ)) ∧ (h 2 ≤ (5/43 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_1517 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a42 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1516 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a23 : h 1 ≤ (5/36 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a29 : -(h 0) < (-5/33 : ℝ))
    (a33 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a36 : h 2 ≤ (2/17 : ℝ))
    (a37 : h 4 ≤ (3/28 : ℝ))
    (a38 : -(h 5) < (-2/19 : ℝ))
    (a41 : -(h 1) < (-3/22 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1517 h delta _ctx _hno a33 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1518 h delta _ctx _hno a18 a23 a24 a33 a37 a38 a41 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1531 h delta _ctx _hno a23 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1532 h delta _ctx _hno a36 f3
  by_cases p4 : h 4 ≤ (6/55 : ℝ)
  swap
  · have f4 : -(h 4) < (-6/55 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1533 h delta _ctx _hno a37 f4
  by_cases p5 : h 5 ≤ (3/28 : ℝ)
  swap
  · have f5 : -(h 5) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1534 h delta _ctx _hno a24 a29 a41 f5
  apply _hno 88
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (6/55 : ℝ)) ∧ (h 5 ≤ (3/28 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_1515 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a26 : h 0 ≤ (4/25 : ℝ))
    (a40 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a26 + (1 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1514 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a39 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1513 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a23 : h 1 ≤ (5/36 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a26 : h 0 ≤ (4/25 : ℝ))
    (a29 : -(h 0) < (-5/33 : ℝ))
    (a33 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a36 : h 2 ≤ (2/17 : ℝ))
    (a37 : h 4 ≤ (3/28 : ℝ))
    (a38 : -(h 5) < (-2/19 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1514 h delta _ctx _hno a33 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1515 h delta _ctx _hno a26 f1
  by_cases p2 : h 1 ≤ (3/22 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1516 h delta _ctx _hno a18 a23 a24 a29 a33 a36 a37 a38 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1535 h delta _ctx _hno a36 f3
  by_cases p4 : h 3 ≤ (7/57 : ℝ)
  swap
  · have f4 : -(h 3) < (-7/57 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1536 h delta _ctx _hno a36 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1537 h delta _ctx _hno a37 f5
  apply _hno 110
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (7/57 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_1512 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : -(h 0) < (-5/33 : ℝ))
    (a32 : -(h 1) < (-2/15 : ℝ))
    (a43 : -(h 4) < (-1/9 : ℝ))
    (a55 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.order3 + (6/29 : ℝ) * _ctx.lower + (1/29 : ℝ) * _ctx.fail1 + (4/29 : ℝ) * a29 + (6/29 : ℝ) * a32 + (12/29 : ℝ) * a43 + (6/29 : ℝ) * a55 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1511 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a48 : h 3 ≤ (7/62 : ℝ))
    (a54 : -(h 3) < (-6/53 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a48 + (1 : ℝ) * a54
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1510 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a29 : -(h 0) < (-5/33 : ℝ))
    (a32 : -(h 1) < (-2/15 : ℝ))
    (a43 : -(h 4) < (-1/9 : ℝ))
    (a60 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.lower + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a24 + (4/29 : ℝ) * a29 + (6/29 : ℝ) * a32 + (6/29 : ℝ) * a43 + (6/29 : ℝ) * a60 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1509 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : -(h 0) < (-5/33 : ℝ))
    (a32 : -(h 1) < (-2/15 : ℝ))
    (a49 : -(h 5) < (-2/19 : ℝ))
    (a59 : -(h 4) < (-5/44 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.order3 + (6/29 : ℝ) * _ctx.lower + (1/29 : ℝ) * _ctx.fail1 + (4/29 : ℝ) * a29 + (6/29 : ℝ) * a32 + (6/29 : ℝ) * a49 + (12/29 : ℝ) * a59 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1508 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a48 : h 3 ≤ (7/62 : ℝ))
    (a58 : -(h 3) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a48 + (1 : ℝ) * a58
  exact (lt_irrefl (0 : ℝ)) hbad

end RealPinwheel.WeakSevenBandData
