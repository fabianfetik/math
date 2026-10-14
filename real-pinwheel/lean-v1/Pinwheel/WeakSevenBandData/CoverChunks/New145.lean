import Pinwheel.WeakSevenBandData.CoverChunks.New144

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem new_node_1514 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a28 : -(h 4) < (-3/28 : ℝ))
    (a30 : -(h 0) < (-5/33 : ℝ))
    (a33 : h 2 ≤ (2/17 : ℝ))
    (a34 : -(h 3) < (-8/73 : ℝ))
    (a35 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ))
    (a38 : -(h 1) < (-1/7 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_1517 h delta _ctx _hno a28 a30 a34 a38 f0
  by_cases p1 : h 0 ≤ (4/25 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/25 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_1518 h delta _ctx _hno a28 a34 a35 a38 f1
  by_cases p2 : h 1 ≤ (2/13 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_1519 h delta _ctx _hno a28 a34 a35 f2
  by_cases p3 : h 2 ≤ (6/47 : ℝ)
  swap
  · have f3 : -(h 2) < (-6/47 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_1520 h delta _ctx _hno a33 f3
  by_cases p4 : h 3 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_1521 h delta _ctx _hno a28 a30 a35 a38 f4
  by_cases p5 : h 4 ≤ (5/46 : ℝ)
  swap
  · have f5 : -(h 4) < (-5/46 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_1522 h delta _ctx _hno a30 a34 a35 a38 f5
  apply _hno 157
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (6/47 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ)) ∧ (h 4 ≤ (5/46 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_1513 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a18 : h 0 ≤ (4/25 : ℝ))
    (a37 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a18 + (1 : ℝ) * a37
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1512 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a36 : ((-2 : ℝ) * (delta)) < (-11/50 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a36
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1511 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a33 : h 2 ≤ (2/17 : ℝ))
    (a38 : -(h 2) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a38
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1510 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a27 : h 3 ≤ (1/9 : ℝ))
    (a28 : -(h 4) < (-3/28 : ℝ))
    (a30 : -(h 0) < (-5/33 : ℝ))
    (a33 : h 2 ≤ (2/17 : ℝ))
    (a34 : -(h 3) < (-8/73 : ℝ))
    (a35 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ))
    (a36 : h 0 ≤ (2/13 : ℝ))
    (a37 : -(h 1) < (-1/7 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_1534 h delta _ctx _hno a35 f0
  by_cases p1 : h 0 ≤ (4/25 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/25 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_1535 h delta _ctx _hno a36 f1
  by_cases p2 : h 1 ≤ (2/13 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_1536 h delta _ctx _hno a13 a28 a34 f2
  by_cases p3 : h 2 ≤ (6/47 : ℝ)
  swap
  · have f3 : -(h 2) < (-6/47 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_1537 h delta _ctx _hno a33 f3
  by_cases p4 : h 3 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_1538 h delta _ctx _hno a27 f4
  by_cases p5 : h 4 ≤ (5/46 : ℝ)
  swap
  · have f5 : -(h 4) < (-5/46 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_1539 h delta _ctx _hno a13 a30 a33 a34 a35 a37 f5
  apply _hno 157
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (6/47 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ)) ∧ (h 4 ≤ (5/46 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_1509 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a18 : h 0 ≤ (4/25 : ℝ))
    (a27 : h 3 ≤ (1/9 : ℝ))
    (a28 : -(h 4) < (-3/28 : ℝ))
    (a33 : h 2 ≤ (2/17 : ℝ))
    (a34 : -(h 3) < (-8/73 : ℝ))
    (a35 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ))
    (a36 : -(h 0) < (-2/13 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (11/50 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-11/50 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_1523 h delta _ctx _hno a35 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_1524 h delta _ctx _hno a18 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_1525 h delta _ctx _hno a13 a28 a33 a34 a35 a36 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_1526 h delta _ctx _hno a33 f3
  by_cases p4 : h 3 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_1527 h delta _ctx _hno a27 f4
  apply _hno 77
  change (((2 : ℝ) * (delta)) ≤ (11/50 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_1508 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a18 : h 0 ≤ (4/25 : ℝ))
    (a27 : h 3 ≤ (1/9 : ℝ))
    (a28 : -(h 4) < (-3/28 : ℝ))
    (a30 : -(h 0) < (-5/33 : ℝ))
    (a33 : h 2 ≤ (2/17 : ℝ))
    (a34 : -(h 3) < (-8/73 : ℝ))
    (a35 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (11/50 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-11/50 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_1512 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_1513 h delta _ctx _hno a18 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_1514 h delta _ctx _hno a28 a30 a33 a34 a35 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_1515 h delta _ctx _hno a33 f3
  by_cases p4 : h 3 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_1516 h delta _ctx _hno a27 f4
  apply _hno 77
  change (((2 : ℝ) * (delta)) ≤ (11/50 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_1507 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : h 3 ≤ (1/9 : ℝ))
    (a42 : -(h 3) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1506 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : h 2 ≤ (1/8 : ℝ))
    (a41 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a26 + (1 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1505 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a36 : h 1 ≤ (1/7 : ℝ))
    (a40 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a36 + (1 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1504 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a35 : h 0 ≤ (2/13 : ℝ))
    (a39 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a35 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1503 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ))
    (a38 : ((-2 : ℝ) * (delta)) < (-11/50 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a38
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1502 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a41 : h 3 ≤ (6/55 : ℝ))
    (a46 : -(h 3) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a41 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1501 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a30 : -(h 0) < (-5/33 : ℝ))
    (a36 : -(h 1) < (-1/7 : ℝ))
    (a42 : -(h 4) < (-5/46 : ℝ))
    (a45 : -(h 2) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a36 + (1/3 : ℝ) * a42 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1500 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a33 : -(h 2) < (-2/17 : ℝ))
    (a36 : -(h 1) < (-1/7 : ℝ))
    (a42 : -(h 4) < (-5/46 : ℝ))
    (a44 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a36 + (1/3 : ℝ) * a42 + (1/6 : ℝ) * a44 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1499 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-9/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1498 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a30 : -(h 0) < (-5/33 : ℝ))
    (a33 : -(h 2) < (-2/17 : ℝ))
    (a36 : -(h 1) < (-1/7 : ℝ))
    (a47 : -(h 4) < (-5/46 : ℝ))
    (a51 : -(h 3) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a36 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * a51 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1497 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a30 : -(h 0) < (-5/33 : ℝ))
    (a36 : -(h 1) < (-1/7 : ℝ))
    (a41 : -(h 3) < (-6/55 : ℝ))
    (a47 : -(h 4) < (-5/46 : ℝ))
    (a50 : -(h 2) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a36 + (1/6 : ℝ) * a41 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * a50 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1496 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a33 : -(h 2) < (-2/17 : ℝ))
    (a36 : -(h 1) < (-1/7 : ℝ))
    (a41 : -(h 3) < (-6/55 : ℝ))
    (a47 : -(h 4) < (-5/46 : ℝ))
    (a49 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a36 + (1/6 : ℝ) * a41 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * a49 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1495 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ))
    (a48 : ((-2 : ℝ) * (delta)) < (-9/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1494 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a30 : -(h 0) < (-5/33 : ℝ))
    (a33 : -(h 2) < (-2/17 : ℝ))
    (a34 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ))
    (a36 : -(h 1) < (-1/7 : ℝ))
    (a41 : -(h 3) < (-6/55 : ℝ))
    (a47 : -(h 4) < (-5/46 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (9/41 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-9/41 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_1495 h delta _ctx _hno a34 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_1496 h delta _ctx _hno a13 a33 a36 a41 a47 f1
  by_cases p2 : h 2 ≤ (3/25 : ℝ)
  swap
  · have f2 : -(h 2) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_1497 h delta _ctx _hno a13 a30 a36 a41 a47 f2
  by_cases p3 : h 3 ≤ (1/9 : ℝ)
  swap
  · have f3 : -(h 3) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_1498 h delta _ctx _hno a13 a30 a33 a36 a47 f3
  apply _hno 195
  change (((2 : ℝ) * (delta)) ≤ (9/41 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_1493 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a28 : -(h 4) < (-3/28 : ℝ))
    (a30 : -(h 0) < (-5/33 : ℝ))
    (a33 : -(h 2) < (-2/17 : ℝ))
    (a36 : -(h 1) < (-1/7 : ℝ))
    (a46 : -(h 3) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a28 + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a36 + (1/6 : ℝ) * a46 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1492 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : h 2 ≤ (1/8 : ℝ))
    (a45 : -(h 2) < (-6/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a26 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1491 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a39 : h 1 ≤ (8/55 : ℝ))
    (a44 : -(h 1) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a39 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1490 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a35 : h 0 ≤ (2/13 : ℝ))
    (a43 : -(h 0) < (-4/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a35 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1489 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ))
    (a42 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1488 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a30 : -(h 0) < (-5/33 : ℝ))
    (a33 : -(h 2) < (-2/17 : ℝ))
    (a39 : -(h 1) < (-8/55 : ℝ))
    (a50 : -(h 4) < (-5/46 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a39 + (1/3 : ℝ) * a50 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1487 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a28 : -(h 4) < (-3/28 : ℝ))
    (a30 : -(h 0) < (-5/33 : ℝ))
    (a33 : -(h 2) < (-2/17 : ℝ))
    (a39 : -(h 1) < (-8/55 : ℝ))
    (a49 : -(h 3) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a28 + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a39 + (1/6 : ℝ) * a49 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1486 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : h 2 ≤ (1/8 : ℝ))
    (a48 : -(h 2) < (-6/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a26 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1485 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a28 : -(h 4) < (-3/28 : ℝ))
    (a33 : -(h 2) < (-2/17 : ℝ))
    (a44 : -(h 3) < (-4/37 : ℝ))
    (a47 : -(h 1) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order0 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a28 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a44 + (1/3 : ℝ) * a47 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1484 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a35 : h 0 ≤ (2/13 : ℝ))
    (a46 : -(h 0) < (-4/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a35 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1483 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ))
    (a45 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1482 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a26 : h 2 ≤ (1/8 : ℝ))
    (a28 : -(h 4) < (-3/28 : ℝ))
    (a30 : -(h 0) < (-5/33 : ℝ))
    (a33 : -(h 2) < (-2/17 : ℝ))
    (a34 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ))
    (a35 : h 0 ≤ (2/13 : ℝ))
    (a39 : -(h 1) < (-8/55 : ℝ))
    (a44 : -(h 3) < (-4/37 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_1483 h delta _ctx _hno a34 f0
  by_cases p1 : h 0 ≤ (4/25 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/25 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_1484 h delta _ctx _hno a35 f1
  by_cases p2 : h 1 ≤ (2/13 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_1485 h delta _ctx _hno a13 a28 a33 a44 f2
  by_cases p3 : h 2 ≤ (6/47 : ℝ)
  swap
  · have f3 : -(h 2) < (-6/47 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_1486 h delta _ctx _hno a26 f3
  by_cases p4 : h 3 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_1487 h delta _ctx _hno a13 a28 a30 a33 a39 f4
  by_cases p5 : h 4 ≤ (5/46 : ℝ)
  swap
  · have f5 : -(h 4) < (-5/46 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_1488 h delta _ctx _hno a13 a30 a33 a39 f5
  apply _hno 157
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (6/47 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ)) ∧ (h 4 ≤ (5/46 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_1481 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a28 : -(h 4) < (-3/28 : ℝ))
    (a30 : -(h 0) < (-5/33 : ℝ))
    (a39 : -(h 1) < (-8/55 : ℝ))
    (a43 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/3 : ℝ) * a28 + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a39 + (1/6 : ℝ) * a43 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1480 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a35 : h 0 ≤ (2/13 : ℝ))
    (a42 : -(h 1) < (-4/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * _ctx.order0 + (1 : ℝ) * a35 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1479 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a35 : h 0 ≤ (2/13 : ℝ))
    (a41 : -(h 0) < (-6/37 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a35 + (1 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1478 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ))
    (a40 : ((-2 : ℝ) * (delta)) < (-8/37 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1477 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a30 : -(h 0) < (-5/33 : ℝ))
    (a33 : -(h 2) < (-2/17 : ℝ))
    (a34 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ))
    (a36 : -(h 1) < (-1/7 : ℝ))
    (a41 : h 3 ≤ (6/55 : ℝ))
    (a42 : -(h 4) < (-5/46 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (9/41 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-9/41 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_1499 h delta _ctx _hno a34 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_1500 h delta _ctx _hno a13 a33 a36 a42 f1
  by_cases p2 : h 2 ≤ (3/25 : ℝ)
  swap
  · have f2 : -(h 2) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_1501 h delta _ctx _hno a13 a30 a36 a42 f2
  by_cases p3 : h 3 ≤ (1/9 : ℝ)
  swap
  · have f3 : -(h 3) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_1502 h delta _ctx _hno a41 f3
  apply _hno 195
  change (((2 : ℝ) * (delta)) ≤ (9/41 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_1476 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a26 : h 2 ≤ (1/8 : ℝ))
    (a28 : -(h 4) < (-3/28 : ℝ))
    (a30 : -(h 0) < (-5/33 : ℝ))
    (a33 : -(h 2) < (-2/17 : ℝ))
    (a34 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ))
    (a35 : h 0 ≤ (2/13 : ℝ))
    (a36 : -(h 1) < (-1/7 : ℝ))
    (a39 : h 1 ≤ (8/55 : ℝ))
    (a41 : -(h 3) < (-6/55 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_1489 h delta _ctx _hno a34 f0
  by_cases p1 : h 0 ≤ (4/25 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/25 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_1490 h delta _ctx _hno a35 f1
  by_cases p2 : h 1 ≤ (2/13 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_1491 h delta _ctx _hno a39 f2
  by_cases p3 : h 2 ≤ (6/47 : ℝ)
  swap
  · have f3 : -(h 2) < (-6/47 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_1492 h delta _ctx _hno a26 f3
  by_cases p4 : h 3 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_1493 h delta _ctx _hno a13 a28 a30 a33 a36 f4
  by_cases p5 : h 4 ≤ (5/46 : ℝ)
  swap
  · have f5 : -(h 4) < (-5/46 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_1494 h delta _ctx _hno a13 a30 a33 a34 a36 a41 f5
  apply _hno 157
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (6/47 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ)) ∧ (h 4 ≤ (5/46 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_1475 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : h 2 ≤ (1/8 : ℝ))
    (a40 : -(h 2) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a26 + (1 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1474 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a26 : h 2 ≤ (1/8 : ℝ))
    (a28 : -(h 4) < (-3/28 : ℝ))
    (a30 : -(h 0) < (-5/33 : ℝ))
    (a33 : -(h 2) < (-2/17 : ℝ))
    (a34 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ))
    (a35 : h 0 ≤ (2/13 : ℝ))
    (a39 : -(h 1) < (-8/55 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (8/37 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-8/37 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_1478 h delta _ctx _hno a34 f0
  by_cases p1 : h 0 ≤ (6/37 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/37 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_1479 h delta _ctx _hno a35 f1
  by_cases p2 : h 1 ≤ (4/25 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/25 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_1480 h delta _ctx _hno a35 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_1481 h delta _ctx _hno a13 a28 a30 a39 f3
  by_cases p4 : h 3 ≤ (4/37 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/37 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_1482 h delta _ctx _hno a13 a26 a28 a30 a33 a34 a35 a39 f4
  apply _hno 26
  change (((2 : ℝ) * (delta)) ≤ (8/37 : ℝ)) ∧ (h 0 ≤ (6/37 : ℝ)) ∧ (h 1 ≤ (4/25 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (4/37 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_1473 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a35 : h 0 ≤ (2/13 : ℝ))
    (a38 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a35 + (1 : ℝ) * a38
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1472 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ))
    (a37 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a37
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1471 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a33 : -(h 2) < (-2/17 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a38 : -(h 1) < (-1/7 : ℝ))
    (a49 : -(h 4) < (-5/46 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a38 + (1/3 : ℝ) * a49 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1470 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a28 : -(h 4) < (-3/28 : ℝ))
    (a33 : -(h 2) < (-2/17 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a38 : -(h 1) < (-1/7 : ℝ))
    (a48 : -(h 3) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a28 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a38 + (1/6 : ℝ) * a48 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1469 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : h 2 ≤ (1/8 : ℝ))
    (a47 : -(h 2) < (-6/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a26 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1468 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a28 : -(h 4) < (-3/28 : ℝ))
    (a33 : -(h 2) < (-2/17 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a43 : -(h 3) < (-4/37 : ℝ))
    (a46 : -(h 1) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a28 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a43 + (1/6 : ℝ) * a46 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1467 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a28 : -(h 4) < (-3/28 : ℝ))
    (a33 : -(h 2) < (-2/17 : ℝ))
    (a38 : -(h 1) < (-1/7 : ℝ))
    (a43 : -(h 3) < (-4/37 : ℝ))
    (a45 : -(h 0) < (-4/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a28 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a38 + (1/6 : ℝ) * a43 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1466 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ))
    (a44 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1465 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a26 : h 2 ≤ (1/8 : ℝ))
    (a28 : -(h 4) < (-3/28 : ℝ))
    (a33 : -(h 2) < (-2/17 : ℝ))
    (a34 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a38 : -(h 1) < (-1/7 : ℝ))
    (a43 : -(h 3) < (-4/37 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_1466 h delta _ctx _hno a34 f0
  by_cases p1 : h 0 ≤ (4/25 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/25 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_1467 h delta _ctx _hno a13 a28 a33 a38 a43 f1
  by_cases p2 : h 1 ≤ (2/13 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_1468 h delta _ctx _hno a13 a28 a33 a35 a43 f2
  by_cases p3 : h 2 ≤ (6/47 : ℝ)
  swap
  · have f3 : -(h 2) < (-6/47 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_1469 h delta _ctx _hno a26 f3
  by_cases p4 : h 3 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_1470 h delta _ctx _hno a13 a28 a33 a35 a38 f4
  by_cases p5 : h 4 ≤ (5/46 : ℝ)
  swap
  · have f5 : -(h 4) < (-5/46 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_1471 h delta _ctx _hno a13 a33 a35 a38 f5
  apply _hno 157
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (6/47 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ)) ∧ (h 4 ≤ (5/46 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_1464 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a28 : -(h 4) < (-3/28 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a38 : -(h 1) < (-1/7 : ℝ))
    (a42 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/3 : ℝ) * a28 + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a38 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1463 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a28 : -(h 4) < (-3/28 : ℝ))
    (a41 : -(h 1) < (-4/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/23 : ℝ) * _ctx.order0 + (6/23 : ℝ) * _ctx.order3 + (6/23 : ℝ) * _ctx.min + (12/23 : ℝ) * _ctx.lower + (1/23 : ℝ) * _ctx.fail1 + (12/23 : ℝ) * a28 + (10/23 : ℝ) * a41 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1462 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a18 : h 0 ≤ (4/25 : ℝ))
    (a40 : -(h 0) < (-6/37 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a18 + (1 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1461 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ))
    (a39 : ((-2 : ℝ) * (delta)) < (-8/37 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1460 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : h 3 ≤ (1/9 : ℝ))
    (a40 : -(h 3) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1459 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a16 : -(h 1) < (-5/36 : ℝ))
    (a28 : -(h 4) < (-3/28 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a39 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a16 + (1/3 : ℝ) * a28 + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a39 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1458 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a18 : h 0 ≤ (4/25 : ℝ))
    (a26 : h 2 ≤ (1/8 : ℝ))
    (a28 : -(h 4) < (-3/28 : ℝ))
    (a33 : -(h 2) < (-2/17 : ℝ))
    (a34 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a38 : -(h 1) < (-1/7 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (8/37 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-8/37 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_1461 h delta _ctx _hno a34 f0
  by_cases p1 : h 0 ≤ (6/37 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/37 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_1462 h delta _ctx _hno a18 f1
  by_cases p2 : h 1 ≤ (4/25 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/25 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_1463 h delta _ctx _hno a28 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_1464 h delta _ctx _hno a13 a28 a35 a38 f3
  by_cases p4 : h 3 ≤ (4/37 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/37 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_1465 h delta _ctx _hno a13 a26 a28 a33 a34 a35 a38 f4
  apply _hno 26
  change (((2 : ℝ) * (delta)) ≤ (8/37 : ℝ)) ∧ (h 0 ≤ (6/37 : ℝ)) ∧ (h 1 ≤ (4/25 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (4/37 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_1457 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a18 : h 0 ≤ (4/25 : ℝ))
    (a37 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a18 + (1 : ℝ) * a37
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1456 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ))
    (a36 : ((-2 : ℝ) * (delta)) < (-11/50 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a36
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1455 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a30 : -(h 0) < (-5/33 : ℝ))
    (a33 : -(h 2) < (-2/17 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ))
    (a37 : -(h 1) < (-1/7 : ℝ))
    (a43 : -(h 4) < (-5/46 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a34 + (1/6 : ℝ) * a37 + (1/3 : ℝ) * a43 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1454 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a28 : -(h 4) < (-3/28 : ℝ))
    (a30 : -(h 0) < (-5/33 : ℝ))
    (a33 : -(h 2) < (-2/17 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ))
    (a37 : -(h 1) < (-1/7 : ℝ))
    (a42 : -(h 3) < (-6/55 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a28 + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a34 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1453 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : h 2 ≤ (1/8 : ℝ))
    (a41 : -(h 2) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a26 + (1 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1452 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a28 : -(h 4) < (-3/28 : ℝ))
    (a30 : -(h 0) < (-5/33 : ℝ))
    (a33 : -(h 2) < (-2/17 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ))
    (a40 : -(h 1) < (-8/55 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/3 : ℝ) * a28 + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a34 + (1/6 : ℝ) * a40 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1451 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a28 : -(h 4) < (-3/28 : ℝ))
    (a33 : -(h 2) < (-2/17 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ))
    (a37 : -(h 1) < (-1/7 : ℝ))
    (a39 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/3 : ℝ) * a28 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a34 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a39 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1450 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a38 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a38
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1449 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : h 3 ≤ (1/9 : ℝ))
    (a39 : -(h 3) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1448 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : -(h 1) < (-5/36 : ℝ))
    (a28 : -(h 4) < (-3/28 : ℝ))
    (a30 : -(h 0) < (-5/33 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ))
    (a38 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a16 + (1/3 : ℝ) * a28 + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a34 + (1/6 : ℝ) * a38 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1447 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : h 2 ≤ (1/8 : ℝ))
    (a28 : -(h 4) < (-3/28 : ℝ))
    (a30 : -(h 0) < (-5/33 : ℝ))
    (a33 : -(h 2) < (-2/17 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ))
    (a37 : -(h 1) < (-1/7 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_1450 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_1451 h delta _ctx _hno a28 a33 a34 a37 f1
  by_cases p2 : h 1 ≤ (8/55 : ℝ)
  swap
  · have f2 : -(h 1) < (-8/55 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_1452 h delta _ctx _hno a28 a30 a33 a34 f2
  by_cases p3 : h 2 ≤ (1/7 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_1453 h delta _ctx _hno a26 f3
  by_cases p4 : h 3 ≤ (6/55 : ℝ)
  swap
  · have f4 : -(h 3) < (-6/55 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_1454 h delta _ctx _hno a28 a30 a33 a34 a37 f4
  by_cases p5 : h 4 ≤ (5/46 : ℝ)
  swap
  · have f5 : -(h 4) < (-5/46 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_1455 h delta _ctx _hno a30 a33 a34 a37 f5
  apply _hno 82
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (8/55 : ℝ)) ∧ (h 2 ≤ (1/7 : ℝ)) ∧ (h 3 ≤ (6/55 : ℝ)) ∧ (h 4 ≤ (5/46 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_1446 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a18 : h 0 ≤ (4/25 : ℝ))
    (a36 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a18 + (1 : ℝ) * a36
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1445 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a35 : ((-2 : ℝ) * (delta)) < (-11/50 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a35
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1444 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : h 2 ≤ (1/8 : ℝ))
    (a27 : h 3 ≤ (1/9 : ℝ))
    (a34 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ))
    (a35 : h 0 ≤ (2/13 : ℝ))
    (a36 : h 1 ≤ (1/7 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (11/50 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-11/50 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_1503 h delta _ctx _hno a34 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_1504 h delta _ctx _hno a35 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_1505 h delta _ctx _hno a36 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_1506 h delta _ctx _hno a26 f3
  by_cases p4 : h 3 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_1507 h delta _ctx _hno a27 f4
  apply _hno 77
  change (((2 : ℝ) * (delta)) ≤ (11/50 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_1443 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a26 : h 2 ≤ (1/8 : ℝ))
    (a28 : -(h 4) < (-3/28 : ℝ))
    (a30 : -(h 0) < (-5/33 : ℝ))
    (a33 : -(h 2) < (-2/17 : ℝ))
    (a34 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ))
    (a35 : h 0 ≤ (2/13 : ℝ))
    (a36 : -(h 1) < (-1/7 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_1472 h delta _ctx _hno a34 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_1473 h delta _ctx _hno a35 f1
  by_cases p2 : h 1 ≤ (8/55 : ℝ)
  swap
  · have f2 : -(h 1) < (-8/55 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_1474 h delta _ctx _hno a13 a26 a28 a30 a33 a34 a35 f2
  by_cases p3 : h 2 ≤ (1/7 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_1475 h delta _ctx _hno a26 f3
  by_cases p4 : h 3 ≤ (6/55 : ℝ)
  swap
  · have f4 : -(h 3) < (-6/55 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_1476 h delta _ctx _hno a13 a26 a28 a30 a33 a34 a35 a36 p2 f4
  by_cases p5 : h 4 ≤ (5/46 : ℝ)
  swap
  · have f5 : -(h 4) < (-5/46 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_1477 h delta _ctx _hno a13 a30 a33 a34 a36 p4 f5
  apply _hno 82
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (8/55 : ℝ)) ∧ (h 2 ≤ (1/7 : ℝ)) ∧ (h 3 ≤ (6/55 : ℝ)) ∧ (h 4 ≤ (5/46 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_1442 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a16 : -(h 1) < (-5/36 : ℝ))
    (a18 : h 0 ≤ (4/25 : ℝ))
    (a26 : h 2 ≤ (1/8 : ℝ))
    (a27 : h 3 ≤ (1/9 : ℝ))
    (a28 : -(h 4) < (-3/28 : ℝ))
    (a33 : -(h 2) < (-2/17 : ℝ))
    (a34 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (11/50 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-11/50 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_1456 h delta _ctx _hno a34 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_1457 h delta _ctx _hno a18 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_1458 h delta _ctx _hno a13 a18 a26 a28 a33 a34 a35 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_1459 h delta _ctx _hno a13 a16 a28 a35 f3
  by_cases p4 : h 3 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_1460 h delta _ctx _hno a27 f4
  apply _hno 77
  change (((2 : ℝ) * (delta)) ≤ (11/50 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_1441 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : -(h 1) < (-5/36 : ℝ))
    (a18 : h 0 ≤ (4/25 : ℝ))
    (a26 : h 2 ≤ (1/8 : ℝ))
    (a27 : h 3 ≤ (1/9 : ℝ))
    (a28 : -(h 4) < (-3/28 : ℝ))
    (a30 : -(h 0) < (-5/33 : ℝ))
    (a33 : -(h 2) < (-2/17 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (11/50 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-11/50 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_1445 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_1446 h delta _ctx _hno a18 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_1447 h delta _ctx _hno a26 a28 a30 a33 a34 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_1448 h delta _ctx _hno a16 a28 a30 a34 f3
  by_cases p4 : h 3 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_1449 h delta _ctx _hno a27 f4
  apply _hno 77
  change (((2 : ℝ) * (delta)) ≤ (11/50 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_1440 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a18 : h 0 ≤ (4/25 : ℝ))
    (a27 : h 3 ≤ (1/9 : ℝ))
    (a28 : -(h 4) < (-3/28 : ℝ))
    (a30 : -(h 0) < (-5/33 : ℝ))
    (a33 : h 2 ≤ (2/17 : ℝ))
    (a34 : -(h 3) < (-8/73 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_1508 h delta _ctx _hno a18 a27 a28 a30 a33 a34 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_1509 h delta _ctx _hno a13 a18 a27 a28 a33 a34 p0 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_1510 h delta _ctx _hno a13 a27 a28 a30 a33 a34 p0 p1 f2
  by_cases p3 : h 2 ≤ (3/25 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_1511 h delta _ctx _hno a33 f3
  apply _hno 198
  change (((2 : ℝ) * (delta)) ≤ (8/39 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_1439 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a16 : -(h 1) < (-5/36 : ℝ))
    (a18 : h 0 ≤ (4/25 : ℝ))
    (a26 : h 2 ≤ (1/8 : ℝ))
    (a27 : h 3 ≤ (1/9 : ℝ))
    (a28 : -(h 4) < (-3/28 : ℝ))
    (a30 : -(h 0) < (-5/33 : ℝ))
    (a33 : -(h 2) < (-2/17 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_1441 h delta _ctx _hno a16 a18 a26 a27 a28 a30 a33 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_1442 h delta _ctx _hno a13 a16 a18 a26 a27 a28 a33 p0 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_1443 h delta _ctx _hno a13 a26 a28 a30 a33 p0 p1 f2
  by_cases p3 : h 2 ≤ (3/25 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_1444 h delta _ctx _hno a26 a27 p0 p1 p2
  apply _hno 198
  change (((2 : ℝ) * (delta)) ≤ (8/39 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_1438 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a18 : h 0 ≤ (4/25 : ℝ))
    (a32 : -(h 0) < (-7/43 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a18 + (1 : ℝ) * a32
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1437 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a31 : ((-2 : ℝ) * (delta)) < (-16/73 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a31
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1436 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : h 3 ≤ (1/9 : ℝ))
    (a34 : -(h 5) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * _ctx.order3 + (1 : ℝ) * _ctx.order4 + (1 : ℝ) * a27 + (1 : ℝ) * a34
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1435 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : h 3 ≤ (1/9 : ℝ))
    (a33 : -(h 3) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a33
  exact (lt_irrefl (0 : ℝ)) hbad

end RealPinwheel.WeakSevenBandData
