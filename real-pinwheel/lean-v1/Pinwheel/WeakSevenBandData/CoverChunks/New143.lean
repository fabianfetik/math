import Pinwheel.WeakSevenBandData.CoverChunks.New142

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem new_node_1674 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a28 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a45 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a28 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1673 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a27 : -(h 0) < (-4/25 : ℝ))
    (a28 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a30 : -(h 1) < (-4/29 : ℝ))
    (a34 : -(h 2) < (-4/35 : ℝ))
    (a44 : -(h 4) < (-2/19 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_1674 h delta _ctx _hno a28 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_1675 h delta _ctx _hno a13 a17 a30 a34 a44 f1
  by_cases p2 : h 1 ≤ (5/31 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/31 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_1676 h delta _ctx _hno a16 f2
  by_cases p3 : h 2 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_1677 h delta _ctx _hno a13 a17 a27 a30 a44 f3
  by_cases p4 : h 4 ≤ (3/28 : ℝ)
  swap
  · have f4 : -(h 4) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_1678 h delta _ctx _hno a13 a17 a27 a30 a34 f4
  by_cases p5 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_1679 h delta _ctx _hno a13 a17 a27 a30 a34 a44 f5
  apply _hno 144
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (5/31 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (3/28 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_1672 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a27 : -(h 0) < (-4/25 : ℝ))
    (a30 : -(h 1) < (-4/29 : ℝ))
    (a39 : -(h 4) < (-5/48 : ℝ))
    (a43 : -(h 3) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order2 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a39 + (1/3 : ℝ) * a43 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1671 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a27 : -(h 0) < (-4/25 : ℝ))
    (a30 : -(h 1) < (-4/29 : ℝ))
    (a39 : -(h 4) < (-5/48 : ℝ))
    (a42 : -(h 2) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a17 + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a39 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1670 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a30 : -(h 1) < (-4/29 : ℝ))
    (a34 : -(h 2) < (-4/35 : ℝ))
    (a39 : -(h 4) < (-5/48 : ℝ))
    (a41 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a17 + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a34 + (1/6 : ℝ) * a39 + (1/6 : ℝ) * a41 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1669 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a28 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a40 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a28 + (1 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1668 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a27 : -(h 0) < (-4/25 : ℝ))
    (a28 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a30 : -(h 1) < (-4/29 : ℝ))
    (a34 : -(h 2) < (-4/35 : ℝ))
    (a39 : h 4 ≤ (5/48 : ℝ))
    (a40 : -(h 5) < (-3/29 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_1680 h delta _ctx _hno a28 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_1681 h delta _ctx _hno a13 a17 a30 a34 a40 f1
  by_cases p2 : h 2 ≤ (2/17 : ℝ)
  swap
  · have f2 : -(h 2) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_1682 h delta _ctx _hno a13 a17 a27 a30 a40 f2
  by_cases p3 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f3 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_1683 h delta _ctx _hno a13 a27 a30 a40 f3
  by_cases p4 : h 4 ≤ (2/19 : ℝ)
  swap
  · have f4 : -(h 4) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_1684 h delta _ctx _hno a39 f4
  apply _hno 200
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 4 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_1667 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a27 : -(h 0) < (-4/25 : ℝ))
    (a28 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a30 : -(h 1) < (-4/29 : ℝ))
    (a34 : -(h 2) < (-4/35 : ℝ))
    (a39 : -(h 4) < (-5/48 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_1669 h delta _ctx _hno a28 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_1670 h delta _ctx _hno a13 a17 a30 a34 a39 f1
  by_cases p2 : h 2 ≤ (2/17 : ℝ)
  swap
  · have f2 : -(h 2) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_1671 h delta _ctx _hno a13 a17 a27 a30 a39 f2
  by_cases p3 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f3 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_1672 h delta _ctx _hno a13 a27 a30 a39 f3
  by_cases p4 : h 4 ≤ (2/19 : ℝ)
  swap
  · have f4 : -(h 4) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_1673 h delta _ctx _hno a13 a16 a17 a27 a28 a30 a34 f4
  apply _hno 200
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 4 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_1666 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a27 : -(h 0) < (-4/25 : ℝ))
    (a30 : -(h 1) < (-4/29 : ℝ))
    (a38 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/11 : ℝ) * _ctx.order4 + (4/11 : ℝ) * _ctx.min + (3/11 : ℝ) * a13 + (2/11 : ℝ) * a17 + (2/11 : ℝ) * a27 + (2/11 : ℝ) * a30 + (2/11 : ℝ) * a38 + (2/11 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1665 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a37 : -(h 1) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a37
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1664 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a30 : -(h 1) < (-4/29 : ℝ))
    (a34 : -(h 2) < (-4/35 : ℝ))
    (a36 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/11 : ℝ) * _ctx.order4 + (4/11 : ℝ) * _ctx.min + (3/11 : ℝ) * a13 + (2/11 : ℝ) * a17 + (2/11 : ℝ) * a30 + (2/11 : ℝ) * a34 + (2/11 : ℝ) * a36 + (2/11 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1663 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a28 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a35 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a28 + (1 : ℝ) * a35
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1662 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a27 : -(h 0) < (-4/25 : ℝ))
    (a30 : -(h 1) < (-4/29 : ℝ))
    (a35 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.order3 + (6/29 : ℝ) * _ctx.min + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a13 + (4/29 : ℝ) * a27 + (6/29 : ℝ) * a30 + (12/29 : ℝ) * a35 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1661 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a27 : -(h 0) < (-4/25 : ℝ))
    (a28 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a30 : -(h 1) < (-4/29 : ℝ))
    (a34 : -(h 2) < (-4/35 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_1663 h delta _ctx _hno a28 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_1664 h delta _ctx _hno a13 a17 a30 a34 f1
  by_cases p2 : h 1 ≤ (2/13 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_1665 h delta _ctx _hno a16 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_1666 h delta _ctx _hno a13 a17 a27 a30 f3
  by_cases p4 : h 4 ≤ (5/48 : ℝ)
  swap
  · have f4 : -(h 4) < (-5/48 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_1667 h delta _ctx _hno a13 a16 a17 a27 a28 a30 a34 f4
  by_cases p5 : h 5 ≤ (3/29 : ℝ)
  swap
  · have f5 : -(h 5) < (-3/29 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_1668 h delta _ctx _hno a13 a17 a27 a28 a30 a34 p4 f5
  apply _hno 63
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (5/48 : ℝ)) ∧ (h 5 ≤ (3/29 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_1660 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a33 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a33
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1659 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : h 0 ≤ (1/6 : ℝ))
    (a32 : -(h 0) < (-6/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a15 + (1 : ℝ) * a32
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1658 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a28 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a31 : ((-2 : ℝ) * (delta)) < (-8/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a28 + (1 : ℝ) * a31
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1657 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a27 : -(h 0) < (-4/25 : ℝ))
    (a28 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a31 : -(h 1) < (-3/22 : ℝ))
    (a35 : -(h 2) < (-4/35 : ℝ))
    (a40 : -(h 4) < (-2/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a17 + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a28 + (1/6 : ℝ) * a31 + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a40 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1656 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : -(h 0) < (-4/25 : ℝ))
    (a28 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a31 : -(h 1) < (-3/22 : ℝ))
    (a39 : -(h 3) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/11 : ℝ) * _ctx.order2 + (2/11 : ℝ) * _ctx.order4 + (4/11 : ℝ) * _ctx.min + (2/11 : ℝ) * a27 + (3/11 : ℝ) * a28 + (2/11 : ℝ) * a31 + (4/11 : ℝ) * a39 + (2/11 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1655 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a27 : -(h 0) < (-4/25 : ℝ))
    (a28 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a31 : -(h 1) < (-3/22 : ℝ))
    (a38 : -(h 2) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/11 : ℝ) * _ctx.order4 + (4/11 : ℝ) * _ctx.min + (2/11 : ℝ) * a17 + (2/11 : ℝ) * a27 + (3/11 : ℝ) * a28 + (2/11 : ℝ) * a31 + (2/11 : ℝ) * a38 + (2/11 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1654 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a28 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a31 : -(h 1) < (-3/22 : ℝ))
    (a35 : -(h 2) < (-4/35 : ℝ))
    (a37 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/11 : ℝ) * _ctx.order4 + (4/11 : ℝ) * _ctx.min + (2/11 : ℝ) * a17 + (3/11 : ℝ) * a28 + (2/11 : ℝ) * a31 + (2/11 : ℝ) * a35 + (2/11 : ℝ) * a37 + (2/11 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1653 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a36 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a36
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1652 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : -(h 0) < (-4/25 : ℝ))
    (a28 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a31 : -(h 1) < (-3/22 : ℝ))
    (a36 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.order3 + (6/29 : ℝ) * _ctx.min + (1/29 : ℝ) * _ctx.fail1 + (4/29 : ℝ) * a27 + (6/29 : ℝ) * a28 + (6/29 : ℝ) * a31 + (12/29 : ℝ) * a36 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1651 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a27 : -(h 0) < (-4/25 : ℝ))
    (a28 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a31 : -(h 1) < (-3/22 : ℝ))
    (a35 : -(h 2) < (-4/35 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_1653 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_1654 h delta _ctx _hno a17 a28 a31 a35 f1
  by_cases p2 : h 2 ≤ (2/17 : ℝ)
  swap
  · have f2 : -(h 2) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_1655 h delta _ctx _hno a17 a27 a28 a31 f2
  by_cases p3 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f3 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_1656 h delta _ctx _hno a27 a28 a31 f3
  by_cases p4 : h 4 ≤ (2/19 : ℝ)
  swap
  · have f4 : -(h 4) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_1657 h delta _ctx _hno a17 a27 a28 a31 a35 f4
  apply _hno 200
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 4 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_1650 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a34 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a34
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1649 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : h 0 ≤ (1/6 : ℝ))
    (a33 : -(h 0) < (-6/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a15 + (1 : ℝ) * a33
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1648 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a32 : ((-2 : ℝ) * (delta)) < (-8/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a32
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1647 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a27 : -(h 0) < (-4/25 : ℝ))
    (a28 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a34 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.order3 + (6/29 : ℝ) * _ctx.min + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a23 + (4/29 : ℝ) * a27 + (6/29 : ℝ) * a28 + (12/29 : ℝ) * a34 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1646 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a27 : -(h 0) < (-4/25 : ℝ))
    (a28 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a33 : -(h 3) < (-7/57 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/11 : ℝ) * _ctx.order2 + (2/11 : ℝ) * _ctx.order4 + (4/11 : ℝ) * _ctx.min + (2/11 : ℝ) * a23 + (2/11 : ℝ) * a27 + (3/11 : ℝ) * a28 + (4/11 : ℝ) * a33 + (2/11 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1645 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a27 : -(h 0) < (-4/25 : ℝ))
    (a28 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a32 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/11 : ℝ) * _ctx.order4 + (4/11 : ℝ) * _ctx.min + (2/11 : ℝ) * a17 + (2/11 : ℝ) * a23 + (2/11 : ℝ) * a27 + (3/11 : ℝ) * a28 + (2/11 : ℝ) * a32 + (2/11 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1644 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : h 0 ≤ (1/6 : ℝ))
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a27 : -(h 0) < (-4/25 : ℝ))
    (a28 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a31 : -(h 1) < (-3/22 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (8/35 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-8/35 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_1648 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (6/35 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/35 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_1649 h delta _ctx _hno a15 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_1650 h delta _ctx _hno a16 f2
  by_cases p3 : h 2 ≤ (4/35 : ℝ)
  swap
  · have f3 : -(h 2) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_1651 h delta _ctx _hno a17 a27 a28 a31 f3
  by_cases p4 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_1652 h delta _ctx _hno a27 a28 a31 f4
  apply _hno 16
  change (((2 : ℝ) * (delta)) ≤ (8/35 : ℝ)) ∧ (h 0 ≤ (6/35 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (4/35 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_1643 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : h 0 ≤ (1/6 : ℝ))
    (a30 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a15 + (1 : ℝ) * a30
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1642 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a29 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a29
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1641 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a15 : h 0 ≤ (1/6 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a27 : -(h 0) < (-4/25 : ℝ))
    (a28 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a30 : h 1 ≤ (4/29 : ℝ))
    (a31 : -(h 4) < (-3/29 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_1685 h delta _ctx _hno a28 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_1686 h delta _ctx _hno a15 f1
  by_cases p2 : h 1 ≤ (3/22 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_1687 h delta _ctx _hno a13 a15 a17 a27 a28 a30 a31 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_1688 h delta _ctx _hno a13 a17 a23 a27 a31 f3
  by_cases p4 : h 3 ≤ (7/57 : ℝ)
  swap
  · have f4 : -(h 3) < (-7/57 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_1689 h delta _ctx _hno a13 a23 a27 a31 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_1690 h delta _ctx _hno a13 a15 a17 a23 a27 a28 p2 f5
  apply _hno 121
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (7/57 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_1640 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a15 : h 0 ≤ (1/6 : ℝ))
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a27 : -(h 0) < (-4/25 : ℝ))
    (a28 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a30 : -(h 1) < (-4/29 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (8/35 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-8/35 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_1658 h delta _ctx _hno a28 f0
  by_cases p1 : h 0 ≤ (6/35 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/35 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_1659 h delta _ctx _hno a15 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_1660 h delta _ctx _hno a16 f2
  by_cases p3 : h 2 ≤ (4/35 : ℝ)
  swap
  · have f3 : -(h 2) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_1661 h delta _ctx _hno a13 a16 a17 a27 a28 a30 f3
  by_cases p4 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_1662 h delta _ctx _hno a13 a27 a30 f4
  apply _hno 16
  change (((2 : ℝ) * (delta)) ≤ (8/35 : ℝ)) ∧ (h 0 ≤ (6/35 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (4/35 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_1639 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : h 0 ≤ (1/6 : ℝ))
    (a29 : -(h 0) < (-5/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a15 + (1 : ℝ) * a29
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1638 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : h 0 ≤ (1/6 : ℝ))
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a27 : -(h 0) < (-4/25 : ℝ))
    (a28 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_1642 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_1643 h delta _ctx _hno a15 f1
  by_cases p2 : h 1 ≤ (3/22 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_1644 h delta _ctx _hno a15 a16 a17 a27 a28 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_1645 h delta _ctx _hno a17 a23 a27 a28 f3
  by_cases p4 : h 3 ≤ (7/57 : ℝ)
  swap
  · have f4 : -(h 3) < (-7/57 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_1646 h delta _ctx _hno a23 a27 a28 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_1647 h delta _ctx _hno a23 a27 a28 f5
  apply _hno 121
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (7/57 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_1637 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a25 : -(h 0) < (-5/33 : ℝ))
    (a27 : h 0 ≤ (4/25 : ℝ))
    (a29 : h 2 ≤ (1/8 : ℝ))
    (a30 : -(h 4) < (-3/28 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_1849 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_1850 h delta _ctx _hno a27 f1
  by_cases p2 : h 1 ≤ (3/22 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_1851 h delta _ctx _hno a13 a16 a17 a25 a27 a29 a30 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_1852 h delta _ctx _hno a29 f3
  by_cases p4 : h 3 ≤ (7/57 : ℝ)
  swap
  · have f4 : -(h 3) < (-7/57 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_1853 h delta _ctx _hno a13 a23 a25 a30 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_1854 h delta _ctx _hno a13 a17 a23 a25 a27 a29 p2 f5
  apply _hno 121
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (7/57 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_1636 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a25 : -(h 0) < (-5/33 : ℝ))
    (a27 : h 0 ≤ (4/25 : ℝ))
    (a29 : -(h 2) < (-1/8 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_1737 h delta _ctx _hno a16 a17 a23 a25 a29 f0
  by_cases p1 : h 0 ≤ (5/29 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/29 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_1738 h delta _ctx _hno a27 f1
  by_cases p2 : h 1 ≤ (4/29 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/29 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_1739 h delta _ctx _hno a13 a16 a17 a25 a29 p0 f2
  by_cases p3 : h 4 ≤ (3/29 : ℝ)
  swap
  · have f3 : -(h 4) < (-3/29 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_1740 h delta _ctx _hno a13 a17 a23 a25 a29 p0 p2 f3
  apply _hno 7
  change (((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)) ∧ (h 0 ≤ (5/29 : ℝ)) ∧ (h 1 ≤ (4/29 : ℝ)) ∧ (h 4 ≤ (3/29 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_1635 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a28 : -(h 1) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a28
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1634 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a15 : h 0 ≤ (1/6 : ℝ))
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a27 : -(h 0) < (-4/25 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_1638 h delta _ctx _hno a15 a16 a17 a23 a27 f0
  by_cases p1 : h 0 ≤ (5/29 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/29 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_1639 h delta _ctx _hno a15 f1
  by_cases p2 : h 1 ≤ (4/29 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/29 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_1640 h delta _ctx _hno a13 a15 a16 a17 a27 p0 f2
  by_cases p3 : h 4 ≤ (3/29 : ℝ)
  swap
  · have f3 : -(h 4) < (-3/29 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_1641 h delta _ctx _hno a13 a15 a17 a23 a27 p0 p2 f3
  apply _hno 7
  change (((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)) ∧ (h 0 ≤ (5/29 : ℝ)) ∧ (h 1 ≤ (4/29 : ℝ)) ∧ (h 4 ≤ (3/29 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_1633 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a26
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1632 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a27 : h 2 ≤ (4/33 : ℝ))
    (a29 : -(h 5) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (2/5 : ℝ) * _ctx.order4 + (1/10 : ℝ) * _ctx.fail1 + (1/10 : ℝ) * a13 + (1/5 : ℝ) * a23 + (2/5 : ℝ) * a27 + (3/5 : ℝ) * a29 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1631 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a25 : h 0 ≤ (5/33 : ℝ))
    (a27 : h 2 ≤ (4/33 : ℝ))
    (a28 : -(h 3) < (-3/25 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_2846 h delta _ctx _hno a23 a27 a28 f0
  by_cases p1 : h 0 ≤ (5/29 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/29 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_2847 h delta _ctx _hno a25 f1
  by_cases p2 : h 1 ≤ (4/29 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/29 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_2848 h delta _ctx _hno a13 a16 a27 a28 p0 f2
  by_cases p3 : h 4 ≤ (3/29 : ℝ)
  swap
  · have f3 : -(h 4) < (-3/29 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_2849 h delta _ctx _hno a13 a23 a25 a27 a28 p0 p2
  apply _hno 7
  change (((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)) ∧ (h 0 ≤ (5/29 : ℝ)) ∧ (h 1 ≤ (4/29 : ℝ)) ∧ (h 4 ≤ (3/29 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_1630 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a25 : h 0 ≤ (5/33 : ℝ))
    (a27 : -(h 2) < (-4/33 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_2255 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (4/27 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/27 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_2256 h delta _ctx _hno a13 a16 a17 a23 a25 a27 f1
  by_cases p2 : h 2 ≤ (7/54 : ℝ)
  swap
  · have f2 : -(h 2) < (-7/54 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_2257 h delta _ctx _hno a13 a16 a17 a23 p1 f2
  by_cases p3 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f3 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_2258 h delta _ctx _hno a13 a16 a23 a27 p1 p2 f3
  apply _hno 76
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (4/27 : ℝ)) ∧ (h 2 ≤ (7/54 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_1629 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a26 : -(h 1) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a26
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1628 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a15 : h 0 ≤ (1/6 : ℝ))
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a25 : -(h 0) < (-5/33 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_1633 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (4/25 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/25 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_1634 h delta _ctx _hno a13 a15 a16 a17 a23 f1
  by_cases p2 : h 1 ≤ (2/13 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_1635 h delta _ctx _hno a16 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_1636 h delta _ctx _hno a13 a16 a17 a23 a25 p1 f3
  by_cases p4 : h 4 ≤ (3/28 : ℝ)
  swap
  · have f4 : -(h 4) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_1637 h delta _ctx _hno a13 a16 a17 a23 a25 p1 p3 f4
  apply _hno 221
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (3/28 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_1627 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : ((-2 : ℝ) * (delta)) < (-7/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a24
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1626 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a15 : h 0 ≤ (1/6 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a20 : -(h 1) < (-1/8 : ℝ))
    (a23 : h 1 ≤ (2/15 : ℝ))
    (a24 : h 2 ≤ (1/8 : ℝ))
    (a25 : -(h 4) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_3486 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (1/7 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_3487 h delta _ctx _hno a13 a15 a17 a20 a23 a24 a25 f1
  by_cases p2 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_3488 h delta _ctx _hno a24 f2
  apply _hno 84
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem new_node_1625 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a15 : h 0 ≤ (1/6 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a20 : -(h 1) < (-1/8 : ℝ))
    (a23 : h 1 ≤ (2/15 : ℝ))
    (a24 : -(h 2) < (-1/8 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_2897 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (4/27 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/27 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_2898 h delta _ctx _hno a13 a15 a17 a20 a23 a24 f1
  by_cases p2 : h 2 ≤ (7/54 : ℝ)
  swap
  · have f2 : -(h 2) < (-7/54 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_2899 h delta _ctx _hno a13 a23 p1 f2
  by_cases p3 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f3 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_2900 h delta _ctx _hno a13 a20 a23 a24 p1 p2 f3
  apply _hno 76
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (4/27 : ℝ)) ∧ (h 2 ≤ (7/54 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_1624 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a15 : h 0 ≤ (1/6 : ℝ))
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a23 : -(h 1) < (-2/15 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/33 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/33 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_1627 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (5/33 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/33 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_1628 h delta _ctx _hno a13 a15 a16 a17 a23 f1
  by_cases p2 : h 1 ≤ (3/20 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_1629 h delta _ctx _hno a16 f2
  by_cases p3 : h 2 ≤ (4/33 : ℝ)
  swap
  · have f3 : -(h 2) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_1630 h delta _ctx _hno a13 a16 a17 a23 p1 f3
  by_cases p4 : h 3 ≤ (3/25 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_1631 h delta _ctx _hno a13 a16 a23 p1 p3 f4
  by_cases p5 : h 5 ≤ (2/17 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_1632 h delta _ctx _hno a13 a23 p3 f5
  apply _hno 11
  change (((2 : ℝ) * (delta)) ≤ (7/33 : ℝ)) ∧ (h 0 ≤ (5/33 : ℝ)) ∧ (h 1 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (4/33 : ℝ)) ∧ (h 3 ≤ (3/25 : ℝ)) ∧ (h 5 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_1623 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : h 0 ≤ (1/6 : ℝ))
    (a22 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a15 + (1 : ℝ) * a22
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1622 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a21 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a21
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1621 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a15 : h 0 ≤ (1/6 : ℝ))
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a20 : -(h 1) < (-1/8 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_1622 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_1623 h delta _ctx _hno a15 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_1624 h delta _ctx _hno a13 a15 a16 a17 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_1625 h delta _ctx _hno a13 a15 a17 a20 p2 f3
  by_cases p4 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_1626 h delta _ctx _hno a13 a15 a17 a20 p2 p3 f4
  apply _hno 120
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_1620 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : h 0 ≤ (1/6 : ℝ))
    (a19 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a15 + (1 : ℝ) * a19
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1619 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a18 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a18
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1618 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a16 : -(h 1) < (-5/36 : ℝ))
    (a28 : -(h 2) < (-1/8 : ℝ))
    (a31 : -(h 3) < (-5/42 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/17 : ℝ) * _ctx.min + (1/17 : ℝ) * _ctx.fail2 + (4/17 : ℝ) * a13 + (4/17 : ℝ) * a16 + (4/17 : ℝ) * a28 + (4/17 : ℝ) * a31 + (4/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1617 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : h 0 ≤ (1/7 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a30
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1616 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a29 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a29
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1615 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a27 : -(h 0) < (-1/7 : ℝ))
    (a31 : -(h 2) < (-4/33 : ℝ))
    (a34 : -(h 1) < (-1/7 : ℝ))
    (a40 : -(h 5) < (-2/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order3 + (1/13 : ℝ) * a13 + (4/13 : ℝ) * a25 + (2/13 : ℝ) * a27 + (2/13 : ℝ) * a31 + (2/13 : ℝ) * a34 + (2/13 : ℝ) * a40 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1614 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a27 : -(h 0) < (-1/7 : ℝ))
    (a34 : -(h 1) < (-1/7 : ℝ))
    (a39 : -(h 4) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.order3 + (6/29 : ℝ) * _ctx.min + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a13 + (4/29 : ℝ) * a27 + (6/29 : ℝ) * a34 + (12/29 : ℝ) * a39 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1613 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a27 : -(h 0) < (-1/7 : ℝ))
    (a34 : -(h 1) < (-1/7 : ℝ))
    (a38 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/3 : ℝ) * a25 + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a34 + (1/6 : ℝ) * a38 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1612 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a31 : -(h 2) < (-4/33 : ℝ))
    (a37 : -(h 1) < (-6/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order0 + (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/3 : ℝ) * a25 + (1/6 : ℝ) * a31 + (1/3 : ℝ) * a37 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1611 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a33 : h 0 ≤ (5/34 : ℝ))
    (a36 : -(h 0) < (-4/27 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a36
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1610 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a32 : ((2 : ℝ) * (delta)) ≤ (7/34 : ℝ))
    (a35 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a32 + (1 : ℝ) * a35
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1609 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a16 : -(h 1) < (-5/36 : ℝ))
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a31 : -(h 2) < (-4/33 : ℝ))
    (a33 : -(h 0) < (-5/34 : ℝ))
    (a39 : -(h 5) < (-2/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order3 + (1/13 : ℝ) * a13 + (2/13 : ℝ) * a16 + (4/13 : ℝ) * a25 + (2/13 : ℝ) * a31 + (2/13 : ℝ) * a33 + (2/13 : ℝ) * a39 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1608 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a16 : -(h 1) < (-5/36 : ℝ))
    (a31 : -(h 2) < (-4/33 : ℝ))
    (a33 : -(h 0) < (-5/34 : ℝ))
    (a38 : -(h 4) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a16 + (1/6 : ℝ) * a31 + (1/6 : ℝ) * a33 + (1/3 : ℝ) * a38 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1607 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a16 : -(h 1) < (-5/36 : ℝ))
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a33 : -(h 0) < (-5/34 : ℝ))
    (a37 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a16 + (1/3 : ℝ) * a25 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1606 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a31 : -(h 2) < (-4/33 : ℝ))
    (a33 : -(h 0) < (-5/34 : ℝ))
    (a36 : -(h 1) < (-6/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/3 : ℝ) * a25 + (1/6 : ℝ) * a31 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a36 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1605 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a16 : -(h 1) < (-5/36 : ℝ))
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a31 : -(h 2) < (-4/33 : ℝ))
    (a35 : -(h 0) < (-4/27 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a16 + (1/3 : ℝ) * a25 + (1/6 : ℝ) * a31 + (1/6 : ℝ) * a35 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1604 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a32 : ((2 : ℝ) * (delta)) ≤ (7/34 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a32 + (1 : ℝ) * a34
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1603 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : -(h 1) < (-5/36 : ℝ))
    (a32 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a34 : -(h 0) < (-13/90 : ℝ))
    (a40 : -(h 5) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/16 : ℝ) * _ctx.order3 + (3/8 : ℝ) * _ctx.order4 + (1/32 : ℝ) * _ctx.fail1 + (3/16 : ℝ) * a16 + (3/32 : ℝ) * a32 + (1/8 : ℝ) * a34 + (9/16 : ℝ) * a40 + (3/16 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1602 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : -(h 1) < (-5/36 : ℝ))
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a31 : -(h 2) < (-4/33 : ℝ))
    (a32 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a34 : -(h 0) < (-13/90 : ℝ))
    (a39 : -(h 3) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a16 + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a31 + (1/6 : ℝ) * a32 + (1/6 : ℝ) * a34 + (1/6 : ℝ) * a39 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1601 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : -(h 1) < (-5/36 : ℝ))
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a32 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a34 : -(h 0) < (-13/90 : ℝ))
    (a38 : -(h 2) < (-5/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a16 + (1/3 : ℝ) * a25 + (1/6 : ℝ) * a32 + (1/6 : ℝ) * a34 + (1/6 : ℝ) * a38 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1600 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a31 : -(h 2) < (-4/33 : ℝ))
    (a32 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a34 : -(h 0) < (-13/90 : ℝ))
    (a37 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/3 : ℝ) * a25 + (1/6 : ℝ) * a31 + (1/6 : ℝ) * a32 + (1/6 : ℝ) * a34 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1599 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : -(h 1) < (-5/36 : ℝ))
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a31 : -(h 2) < (-4/33 : ℝ))
    (a32 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a36 : -(h 0) < (-6/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a16 + (1/3 : ℝ) * a25 + (1/6 : ℝ) * a31 + (1/6 : ℝ) * a32 + (1/6 : ℝ) * a36 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1598 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a33 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a35 : ((-2 : ℝ) * (delta)) < (-9/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a35
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1597 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : -(h 1) < (-5/36 : ℝ))
    (a27 : -(h 0) < (-1/7 : ℝ))
    (a33 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a37 : -(h 2) < (-5/41 : ℝ))
    (a43 : -(h 5) < (-5/44 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order3 + (4/13 : ℝ) * _ctx.order4 + (2/13 : ℝ) * a16 + (2/13 : ℝ) * a27 + (1/13 : ℝ) * a33 + (2/13 : ℝ) * a37 + (6/13 : ℝ) * a43 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1596 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : -(h 1) < (-5/36 : ℝ))
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a27 : -(h 0) < (-1/7 : ℝ))
    (a33 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a37 : -(h 2) < (-5/41 : ℝ))
    (a42 : -(h 3) < (-7/61 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a16 + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1595 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : -(h 1) < (-5/36 : ℝ))
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a27 : -(h 0) < (-1/7 : ℝ))
    (a33 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a41 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a16 + (1/3 : ℝ) * a25 + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a41 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

end RealPinwheel.WeakSevenBandData
