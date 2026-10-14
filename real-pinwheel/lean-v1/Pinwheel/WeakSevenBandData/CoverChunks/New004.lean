import Pinwheel.WeakSevenBandData.CoverChunks.New003

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem new_node_12794 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a47 : h 0 ≤ (5/34 : ℝ))
    (a53 : -(h 0) < (-4/27 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a47 + (1 : ℝ) * a53
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12793 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a52 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a52
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12792 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a28 : -(h 2) < (-7/54 : ℝ))
    (a45 : -(h 1) < (-2/15 : ℝ))
    (a49 : -(h 3) < (-2/17 : ℝ))
    (a55 : -(h 5) < (-2/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/17 : ℝ) * _ctx.lower + (1/17 : ℝ) * _ctx.fail2 + (4/17 : ℝ) * a28 + (4/17 : ℝ) * a45 + (4/17 : ℝ) * a49 + (4/17 : ℝ) * a55 + (4/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12791 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a21 : -(h 0) < (-1/7 : ℝ))
    (a28 : -(h 2) < (-7/54 : ℝ))
    (a40 : h 1 ≤ (5/37 : ℝ))
    (a45 : -(h 1) < (-2/15 : ℝ))
    (a49 : -(h 3) < (-2/17 : ℝ))
    (a51 : h 0 ≤ (12/83 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_12799 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (4/27 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/27 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_12800 h delta _ctx _hno a51 f1
  by_cases p2 : h 2 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 2) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_12801 h delta _ctx _hno a17 a21 a40 a45 a49 a51 f2
  by_cases p3 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_12802 h delta _ctx _hno a28 a45 f3
  by_cases p4 : h 4 ≤ (5/46 : ℝ)
  swap
  · have f4 : -(h 4) < (-5/46 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_12803 h delta _ctx _hno a17 a21 a28 a40 a45 a49 a51 p2
  by_cases p5 : h 5 ≤ (4/37 : ℝ)
  swap
  · have f5 : -(h 5) < (-4/37 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_12804 h delta _ctx _hno a28 a45 a49 f5
  apply _hno 55
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (4/27 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (5/46 : ℝ)) ∧ (h 5 ≤ (4/37 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_12790 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a28 : -(h 2) < (-7/54 : ℝ))
    (a45 : -(h 1) < (-2/15 : ℝ))
    (a53 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/13 : ℝ) * _ctx.min + (8/13 : ℝ) * _ctx.lower + (1/13 : ℝ) * _ctx.fail2 + (4/13 : ℝ) * a28 + (4/13 : ℝ) * a45 + (4/13 : ℝ) * a53 + (4/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12789 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a41 : h 2 ≤ (2/15 : ℝ))
    (a52 : -(h 2) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a41 + (1 : ℝ) * a52
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12788 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a28 : -(h 2) < (-7/54 : ℝ))
    (a42 : -(h 4) < (-4/37 : ℝ))
    (a45 : -(h 1) < (-2/15 : ℝ))
    (a47 : h 0 ≤ (5/34 : ℝ))
    (a49 : -(h 3) < (-2/17 : ℝ))
    (a51 : -(h 0) < (-12/83 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_12793 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (4/27 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/27 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_12794 h delta _ctx _hno a47 f1
  by_cases p2 : h 2 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 2) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_12795 h delta _ctx _hno a42 a45 a49 a51 f2
  by_cases p3 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_12796 h delta _ctx _hno a28 a42 a45 a51 f3
  by_cases p4 : h 4 ≤ (5/46 : ℝ)
  swap
  · have f4 : -(h 4) < (-5/46 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_12797 h delta _ctx _hno a28 a45 a49 a51 f4
  by_cases p5 : h 5 ≤ (4/37 : ℝ)
  swap
  · have f5 : -(h 5) < (-4/37 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_12798 h delta _ctx _hno a28 a42 a45 a49 a51 f5
  apply _hno 55
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (4/27 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (5/46 : ℝ)) ∧ (h 5 ≤ (4/37 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_12787 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a50 : ((-2 : ℝ) * (delta)) < (-18/83 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12786 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a21 : -(h 0) < (-1/7 : ℝ))
    (a25 : -(h 3) < (-7/60 : ℝ))
    (a28 : -(h 2) < (-7/54 : ℝ))
    (a45 : -(h 1) < (-2/15 : ℝ))
    (a50 : -(h 5) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order4 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a21 + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a28 + (1/6 : ℝ) * a45 + (1/3 : ℝ) * a50 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12785 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a21 : -(h 0) < (-1/7 : ℝ))
    (a28 : -(h 2) < (-7/54 : ℝ))
    (a40 : h 1 ≤ (5/37 : ℝ))
    (a41 : h 2 ≤ (2/15 : ℝ))
    (a42 : -(h 4) < (-4/37 : ℝ))
    (a45 : -(h 1) < (-2/15 : ℝ))
    (a47 : h 0 ≤ (5/34 : ℝ))
    (a49 : -(h 3) < (-2/17 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (18/83 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-18/83 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_12787 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (12/83 : ℝ)
  swap
  · have f1 : -(h 0) < (-12/83 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_12788 h delta _ctx _hno a17 a28 a42 a45 a47 a49 f1
  by_cases p2 : h 2 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 2) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_12789 h delta _ctx _hno a41 f2
  by_cases p3 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_12790 h delta _ctx _hno a28 a45 f3
  by_cases p4 : h 4 ≤ (9/83 : ℝ)
  swap
  · have f4 : -(h 4) < (-9/83 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_12791 h delta _ctx _hno a17 a21 a28 a40 a45 a49 p1
  by_cases p5 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_12792 h delta _ctx _hno a28 a45 a49 f5
  apply _hno 142
  change (((2 : ℝ) * (delta)) ≤ (18/83 : ℝ)) ∧ (h 0 ≤ (12/83 : ℝ)) ∧ (h 2 ≤ (1/7 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (9/83 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_12784 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a40 : h 1 ≤ (5/37 : ℝ))
    (a48 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a40 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12783 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 3) < (-7/60 : ℝ))
    (a28 : -(h 2) < (-7/54 : ℝ))
    (a42 : -(h 4) < (-4/37 : ℝ))
    (a45 : -(h 1) < (-2/15 : ℝ))
    (a47 : -(h 0) < (-5/34 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a25 + (1/5 : ℝ) * a28 + (1/5 : ℝ) * a42 + (1/5 : ℝ) * a45 + (1/5 : ℝ) * a47 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12782 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a46 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12781 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a21 : -(h 0) < (-1/7 : ℝ))
    (a25 : -(h 3) < (-7/60 : ℝ))
    (a28 : -(h 2) < (-7/54 : ℝ))
    (a45 : h 1 ≤ (2/15 : ℝ))
    (a47 : -(h 4) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_12825 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (5/34 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/34 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_12826 h delta _ctx _hno a25 a28 a47 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_12827 h delta _ctx _hno a45 f2
  by_cases p3 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_12828 h delta _ctx _hno a17 a21 a28 a47 p1 f3
  by_cases p4 : h 5 ≤ (3/26 : ℝ)
  swap
  · have f4 : -(h 5) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_12829 h delta _ctx _hno a21 a25 a28 f4
  apply _hno 14
  change (((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)) ∧ (h 0 ≤ (5/34 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (3/26 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_12780 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a21 : -(h 0) < (-1/7 : ℝ))
    (a28 : -(h 2) < (-7/54 : ℝ))
    (a42 : -(h 4) < (-4/37 : ℝ))
    (a46 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order1 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a21 + (2/5 : ℝ) * a28 + (1/5 : ℝ) * a42 + (1/5 : ℝ) * a46 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12779 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a21 : -(h 0) < (-1/7 : ℝ))
    (a25 : -(h 3) < (-7/60 : ℝ))
    (a28 : -(h 2) < (-7/54 : ℝ))
    (a40 : h 1 ≤ (5/37 : ℝ))
    (a41 : h 2 ≤ (2/15 : ℝ))
    (a42 : -(h 4) < (-4/37 : ℝ))
    (a45 : -(h 1) < (-2/15 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_12782 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (5/34 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/34 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_12783 h delta _ctx _hno a25 a28 a42 a45 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_12784 h delta _ctx _hno a40 f2
  by_cases p3 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_12785 h delta _ctx _hno a17 a21 a28 a40 a41 a42 a45 p1 f3
  by_cases p4 : h 5 ≤ (3/26 : ℝ)
  swap
  · have f4 : -(h 5) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_12786 h delta _ctx _hno a21 a25 a28 a45 f4
  apply _hno 14
  change (((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)) ∧ (h 0 ≤ (5/34 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (3/26 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_12778 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : h 0 ≤ (4/27 : ℝ))
    (a44 : -(h 0) < (-3/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12777 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12776 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a28 : -(h 2) < (-7/54 : ℝ))
    (a40 : -(h 1) < (-5/37 : ℝ))
    (a44 : -(h 3) < (-2/17 : ℝ))
    (a59 : -(h 5) < (-2/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/17 : ℝ) * _ctx.lower + (1/17 : ℝ) * _ctx.fail2 + (4/17 : ℝ) * a28 + (4/17 : ℝ) * a40 + (4/17 : ℝ) * a44 + (4/17 : ℝ) * a59 + (4/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12775 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a21 : -(h 0) < (-1/7 : ℝ))
    (a28 : -(h 2) < (-7/54 : ℝ))
    (a40 : -(h 1) < (-5/37 : ℝ))
    (a44 : -(h 3) < (-2/17 : ℝ))
    (a58 : -(h 4) < (-9/83 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a21 + (1/5 : ℝ) * a28 + (1/5 : ℝ) * a40 + (1/5 : ℝ) * a44 + (1/5 : ℝ) * a58 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12774 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a28 : -(h 2) < (-7/54 : ℝ))
    (a40 : -(h 1) < (-5/37 : ℝ))
    (a57 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/13 : ℝ) * _ctx.min + (8/13 : ℝ) * _ctx.lower + (1/13 : ℝ) * _ctx.fail2 + (4/13 : ℝ) * a28 + (4/13 : ℝ) * a40 + (4/13 : ℝ) * a57 + (4/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12773 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a52 : h 2 ≤ (3/23 : ℝ))
    (a56 : -(h 2) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a52 + (1 : ℝ) * a56
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12772 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a28 : -(h 2) < (-7/54 : ℝ))
    (a40 : -(h 1) < (-5/37 : ℝ))
    (a44 : -(h 3) < (-2/17 : ℝ))
    (a53 : -(h 4) < (-5/47 : ℝ))
    (a55 : -(h 0) < (-12/83 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a28 + (1/5 : ℝ) * a40 + (1/5 : ℝ) * a44 + (1/5 : ℝ) * a53 + (1/5 : ℝ) * a55 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12771 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a54 : ((-2 : ℝ) * (delta)) < (-18/83 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a54
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12770 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a40 : -(h 1) < (-5/37 : ℝ))
    (a44 : -(h 3) < (-2/17 : ℝ))
    (a52 : -(h 2) < (-3/23 : ℝ))
    (a64 : -(h 5) < (-2/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/17 : ℝ) * _ctx.lower + (1/17 : ℝ) * _ctx.fail2 + (4/17 : ℝ) * a40 + (4/17 : ℝ) * a44 + (4/17 : ℝ) * a52 + (4/17 : ℝ) * a64 + (4/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12769 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a21 : -(h 0) < (-1/7 : ℝ))
    (a40 : -(h 1) < (-5/37 : ℝ))
    (a44 : -(h 3) < (-2/17 : ℝ))
    (a52 : -(h 2) < (-3/23 : ℝ))
    (a63 : -(h 4) < (-9/83 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a21 + (1/5 : ℝ) * a40 + (1/5 : ℝ) * a44 + (1/5 : ℝ) * a52 + (1/5 : ℝ) * a63 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12768 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a40 : -(h 1) < (-5/37 : ℝ))
    (a52 : -(h 2) < (-3/23 : ℝ))
    (a62 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/13 : ℝ) * _ctx.min + (8/13 : ℝ) * _ctx.lower + (1/13 : ℝ) * _ctx.fail2 + (4/13 : ℝ) * a40 + (4/13 : ℝ) * a52 + (4/13 : ℝ) * a62 + (4/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12767 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a48 : h 2 ≤ (5/38 : ℝ))
    (a61 : -(h 2) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a48 + (1 : ℝ) * a61
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12766 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a40 : -(h 1) < (-5/37 : ℝ))
    (a44 : -(h 3) < (-2/17 : ℝ))
    (a52 : -(h 2) < (-3/23 : ℝ))
    (a58 : -(h 4) < (-5/47 : ℝ))
    (a60 : -(h 0) < (-12/83 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a40 + (1/5 : ℝ) * a44 + (1/5 : ℝ) * a52 + (1/5 : ℝ) * a58 + (1/5 : ℝ) * a60 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12765 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a59 : ((-2 : ℝ) * (delta)) < (-18/83 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a59
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12764 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a40 : -(h 1) < (-5/37 : ℝ))
    (a44 : -(h 3) < (-2/17 : ℝ))
    (a52 : -(h 2) < (-3/23 : ℝ))
    (a59 : -(h 5) < (-2/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/17 : ℝ) * _ctx.lower + (1/17 : ℝ) * _ctx.fail2 + (4/17 : ℝ) * a40 + (4/17 : ℝ) * a44 + (4/17 : ℝ) * a52 + (4/17 : ℝ) * a59 + (4/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12763 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a21 : -(h 0) < (-1/7 : ℝ))
    (a40 : -(h 1) < (-5/37 : ℝ))
    (a44 : -(h 3) < (-2/17 : ℝ))
    (a48 : h 2 ≤ (5/38 : ℝ))
    (a52 : -(h 2) < (-3/23 : ℝ))
    (a58 : -(h 4) < (-5/47 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (18/83 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-18/83 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_12765 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (12/83 : ℝ)
  swap
  · have f1 : -(h 0) < (-12/83 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_12766 h delta _ctx _hno a40 a44 a52 a58 f1
  by_cases p2 : h 2 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 2) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_12767 h delta _ctx _hno a48 f2
  by_cases p3 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_12768 h delta _ctx _hno a40 a52 f3
  by_cases p4 : h 4 ≤ (9/83 : ℝ)
  swap
  · have f4 : -(h 4) < (-9/83 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_12769 h delta _ctx _hno a21 a40 a44 a52 f4
  by_cases p5 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_12770 h delta _ctx _hno a40 a44 a52 f5
  apply _hno 142
  change (((2 : ℝ) * (delta)) ≤ (18/83 : ℝ)) ∧ (h 0 ≤ (12/83 : ℝ)) ∧ (h 2 ≤ (1/7 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (9/83 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_12762 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a40 : -(h 1) < (-5/37 : ℝ))
    (a52 : -(h 2) < (-3/23 : ℝ))
    (a57 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/13 : ℝ) * _ctx.min + (8/13 : ℝ) * _ctx.lower + (1/13 : ℝ) * _ctx.fail2 + (4/13 : ℝ) * a40 + (4/13 : ℝ) * a52 + (4/13 : ℝ) * a57 + (4/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12761 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a48 : h 2 ≤ (5/38 : ℝ))
    (a56 : -(h 2) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a48 + (1 : ℝ) * a56
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12760 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : h 1 ≤ (8/59 : ℝ))
    (a55 : -(h 1) < (-5/34 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a15 + (1 : ℝ) * a55
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12759 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a42 : h 0 ≤ (5/34 : ℝ))
    (a54 : -(h 0) < (-4/27 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a42 + (1 : ℝ) * a54
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12758 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a53 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a53
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12757 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a21 : -(h 0) < (-1/7 : ℝ))
    (a28 : -(h 2) < (-7/54 : ℝ))
    (a40 : -(h 1) < (-5/37 : ℝ))
    (a44 : -(h 3) < (-2/17 : ℝ))
    (a52 : h 2 ≤ (3/23 : ℝ))
    (a53 : -(h 4) < (-5/47 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (18/83 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-18/83 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_12771 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (12/83 : ℝ)
  swap
  · have f1 : -(h 0) < (-12/83 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_12772 h delta _ctx _hno a28 a40 a44 a53 f1
  by_cases p2 : h 2 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 2) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_12773 h delta _ctx _hno a52 f2
  by_cases p3 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_12774 h delta _ctx _hno a28 a40 f3
  by_cases p4 : h 4 ≤ (9/83 : ℝ)
  swap
  · have f4 : -(h 4) < (-9/83 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_12775 h delta _ctx _hno a21 a28 a40 a44 f4
  by_cases p5 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_12776 h delta _ctx _hno a28 a40 a44 f5
  apply _hno 142
  change (((2 : ℝ) * (delta)) ≤ (18/83 : ℝ)) ∧ (h 0 ≤ (12/83 : ℝ)) ∧ (h 2 ≤ (1/7 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (9/83 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_12756 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : h 1 ≤ (8/59 : ℝ))
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a21 : -(h 0) < (-1/7 : ℝ))
    (a40 : -(h 1) < (-5/37 : ℝ))
    (a42 : h 0 ≤ (5/34 : ℝ))
    (a44 : -(h 3) < (-2/17 : ℝ))
    (a48 : h 2 ≤ (5/38 : ℝ))
    (a52 : -(h 2) < (-3/23 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_12758 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (4/27 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/27 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_12759 h delta _ctx _hno a42 f1
  by_cases p2 : h 1 ≤ (5/34 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/34 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_12760 h delta _ctx _hno a15 f2
  by_cases p3 : h 2 ≤ (1/7 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_12761 h delta _ctx _hno a48 f3
  by_cases p4 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_12762 h delta _ctx _hno a40 a52 f4
  by_cases p5 : h 4 ≤ (5/47 : ℝ)
  swap
  · have f5 : -(h 4) < (-5/47 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_12763 h delta _ctx _hno a17 a21 a40 a44 a48 a52 f5
  by_cases p6 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f6 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact new_node_12764 h delta _ctx _hno a40 a44 a52 f6
  apply _hno 57
  change (((2 : ℝ) * (delta)) ≤ (10/47 : ℝ)) ∧ (h 0 ≤ (4/27 : ℝ)) ∧ (h 1 ≤ (5/34 : ℝ)) ∧ (h 2 ≤ (1/7 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (5/47 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem new_node_12755 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a42 : h 0 ≤ (5/34 : ℝ))
    (a51 : -(h 0) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a42 + (1 : ℝ) * a51
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12754 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a50 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12753 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : h 1 ≤ (8/59 : ℝ))
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a21 : -(h 0) < (-1/7 : ℝ))
    (a28 : -(h 2) < (-7/54 : ℝ))
    (a40 : -(h 1) < (-5/37 : ℝ))
    (a42 : h 0 ≤ (5/34 : ℝ))
    (a44 : -(h 3) < (-2/17 : ℝ))
    (a48 : h 2 ≤ (5/38 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_12754 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_12755 h delta _ctx _hno a42 f1
  by_cases p2 : h 2 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 2) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_12756 h delta _ctx _hno a15 a17 a21 a40 a42 a44 a48 f2
  by_cases p3 : h 4 ≤ (5/47 : ℝ)
  swap
  · have f3 : -(h 4) < (-5/47 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_12757 h delta _ctx _hno a17 a21 a28 a40 a44 p2 f3
  apply _hno 143
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 4 ≤ (5/47 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_12752 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a40 : -(h 1) < (-5/37 : ℝ))
    (a44 : -(h 3) < (-2/17 : ℝ))
    (a48 : -(h 2) < (-5/38 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/13 : ℝ) * _ctx.min + (8/13 : ℝ) * _ctx.lower + (1/13 : ℝ) * _ctx.fail2 + (4/13 : ℝ) * a40 + (4/13 : ℝ) * a44 + (4/13 : ℝ) * a48 + (4/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12751 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : h 1 ≤ (8/59 : ℝ))
    (a47 : -(h 1) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a15 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12750 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a42 : h 0 ≤ (5/34 : ℝ))
    (a46 : -(h 0) < (-3/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a42 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12749 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a45 : ((-2 : ℝ) * (delta)) < (-1/5 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12748 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 3) < (-7/60 : ℝ))
    (a28 : -(h 2) < (-7/54 : ℝ))
    (a40 : -(h 1) < (-5/37 : ℝ))
    (a42 : -(h 0) < (-5/34 : ℝ))
    (a47 : -(h 4) < (-2/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a25 + (1/5 : ℝ) * a28 + (1/5 : ℝ) * a40 + (1/5 : ℝ) * a42 + (1/5 : ℝ) * a47 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12747 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 3) < (-7/60 : ℝ))
    (a37 : -(h 4) < (-3/29 : ℝ))
    (a40 : -(h 1) < (-5/37 : ℝ))
    (a42 : -(h 0) < (-5/34 : ℝ))
    (a46 : -(h 2) < (-5/38 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a25 + (1/5 : ℝ) * a37 + (1/5 : ℝ) * a40 + (1/5 : ℝ) * a42 + (1/5 : ℝ) * a46 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12746 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : h 1 ≤ (8/59 : ℝ))
    (a45 : -(h 1) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a15 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12745 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : h 0 ≤ (4/27 : ℝ))
    (a44 : -(h 0) < (-3/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12744 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-1/5 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12743 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a21 : -(h 0) < (-1/7 : ℝ))
    (a25 : -(h 3) < (-7/60 : ℝ))
    (a28 : -(h 2) < (-7/54 : ℝ))
    (a40 : -(h 1) < (-5/37 : ℝ))
    (a45 : -(h 5) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order4 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a21 + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a28 + (1/6 : ℝ) * a40 + (1/3 : ℝ) * a45 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12742 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : h 1 ≤ (8/59 : ℝ))
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a21 : -(h 0) < (-1/7 : ℝ))
    (a28 : -(h 2) < (-7/54 : ℝ))
    (a40 : -(h 1) < (-5/37 : ℝ))
    (a42 : h 0 ≤ (5/34 : ℝ))
    (a44 : -(h 3) < (-2/17 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-1/5 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_12749 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (3/19 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/19 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_12750 h delta _ctx _hno a42 f1
  by_cases p2 : h 1 ≤ (2/13 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_12751 h delta _ctx _hno a15 f2
  by_cases p3 : h 2 ≤ (5/38 : ℝ)
  swap
  · have f3 : -(h 2) < (-5/38 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_12752 h delta _ctx _hno a40 a44 f3
  by_cases p4 : h 4 ≤ (2/19 : ℝ)
  swap
  · have f4 : -(h 4) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_12753 h delta _ctx _hno a15 a17 a21 a28 a40 a42 a44 p3
  apply _hno 28
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (5/38 : ℝ)) ∧ (h 4 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_12741 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : h 1 ≤ (8/59 : ℝ))
    (a43 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a15 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12740 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : h 1 ≤ (8/59 : ℝ))
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a25 : -(h 3) < (-7/60 : ℝ))
    (a27 : h 0 ≤ (4/27 : ℝ))
    (a28 : -(h 2) < (-7/54 : ℝ))
    (a37 : -(h 4) < (-3/29 : ℝ))
    (a40 : -(h 1) < (-5/37 : ℝ))
    (a42 : -(h 0) < (-5/34 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-1/5 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_12744 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (3/19 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/19 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_12745 h delta _ctx _hno a27 f1
  by_cases p2 : h 1 ≤ (2/13 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_12746 h delta _ctx _hno a15 f2
  by_cases p3 : h 2 ≤ (5/38 : ℝ)
  swap
  · have f3 : -(h 2) < (-5/38 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_12747 h delta _ctx _hno a25 a37 a40 a42 f3
  by_cases p4 : h 4 ≤ (2/19 : ℝ)
  swap
  · have f4 : -(h 4) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_12748 h delta _ctx _hno a25 a28 a40 a42 f4
  apply _hno 28
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (5/38 : ℝ)) ∧ (h 4 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_12739 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12738 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a25 : -(h 3) < (-7/60 : ℝ))
    (a28 : -(h 2) < (-7/54 : ℝ))
    (a40 : h 1 ≤ (5/37 : ℝ))
    (a42 : h 4 ≤ (4/37 : ℝ))
    (a43 : -(h 5) < (-3/28 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_12840 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (5/34 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/34 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_12841 h delta _ctx _hno a25 a28 a43 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_12842 h delta _ctx _hno a40 f2
  by_cases p3 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_12843 h delta _ctx _hno a28 a43 f3
  by_cases p4 : h 5 ≤ (3/26 : ℝ)
  swap
  · have f4 : -(h 5) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_12844 h delta _ctx _hno a42 f4
  apply _hno 14
  change (((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)) ∧ (h 0 ≤ (5/34 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (3/26 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_12737 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a21 : -(h 0) < (-1/7 : ℝ))
    (a25 : -(h 3) < (-7/60 : ℝ))
    (a27 : h 0 ≤ (4/27 : ℝ))
    (a28 : -(h 2) < (-7/54 : ℝ))
    (a40 : h 1 ≤ (5/37 : ℝ))
    (a41 : h 2 ≤ (2/15 : ℝ))
    (a42 : -(h 4) < (-4/37 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_12777 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (3/19 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/19 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_12778 h delta _ctx _hno a27 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_12779 h delta _ctx _hno a17 a21 a25 a28 a40 a41 a42 f2
  by_cases p3 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_12780 h delta _ctx _hno a21 a28 a42 f3
  by_cases p4 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_12781 h delta _ctx _hno a17 a21 a25 a28 p2 f4
  apply _hno 213
  change (((2 : ℝ) * (delta)) ≤ (8/39 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_12736 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 3) < (-7/60 : ℝ))
    (a41 : -(h 2) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/13 : ℝ) * _ctx.order1 + (4/13 : ℝ) * _ctx.min + (8/13 : ℝ) * _ctx.lower + (1/13 : ℝ) * _ctx.fail2 + (4/13 : ℝ) * a25 + (8/13 : ℝ) * a41 + (4/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12735 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : h 1 ≤ (8/59 : ℝ))
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a21 : -(h 0) < (-1/7 : ℝ))
    (a25 : -(h 3) < (-7/60 : ℝ))
    (a27 : h 0 ≤ (4/27 : ℝ))
    (a28 : -(h 2) < (-7/54 : ℝ))
    (a37 : -(h 4) < (-3/29 : ℝ))
    (a40 : -(h 1) < (-5/37 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_12739 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (5/34 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/34 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_12740 h delta _ctx _hno a15 a17 a25 a27 a28 a37 a40 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_12741 h delta _ctx _hno a15 f2
  by_cases p3 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_12742 h delta _ctx _hno a15 a17 a21 a28 a40 p1 f3
  by_cases p4 : h 5 ≤ (3/26 : ℝ)
  swap
  · have f4 : -(h 5) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_12743 h delta _ctx _hno a21 a25 a28 a40 f4
  apply _hno 14
  change (((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)) ∧ (h 0 ≤ (5/34 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (3/26 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_12734 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : h 0 ≤ (4/27 : ℝ))
    (a39 : -(h 0) < (-6/37 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12733 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a38 : ((-2 : ℝ) * (delta)) < (-7/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a38
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12732 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : h 1 ≤ (8/59 : ℝ))
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a21 : -(h 0) < (-1/7 : ℝ))
    (a25 : -(h 3) < (-7/60 : ℝ))
    (a27 : h 0 ≤ (4/27 : ℝ))
    (a28 : -(h 2) < (-7/54 : ℝ))
    (a37 : -(h 4) < (-3/29 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/33 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/33 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_12733 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (6/37 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/37 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_12734 h delta _ctx _hno a27 f1
  by_cases p2 : h 1 ≤ (5/37 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/37 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_12735 h delta _ctx _hno a15 a17 a21 a25 a27 a28 a37 f2
  by_cases p3 : h 2 ≤ (2/15 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_12736 h delta _ctx _hno a25 f3
  by_cases p4 : h 4 ≤ (4/37 : ℝ)
  swap
  · have f4 : -(h 4) < (-4/37 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_12737 h delta _ctx _hno a17 a21 a25 a27 a28 p2 p3 f4
  by_cases p5 : h 5 ≤ (3/28 : ℝ)
  swap
  · have f5 : -(h 5) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_12738 h delta _ctx _hno a17 a25 a28 p2 p4 f5
  apply _hno 249
  change (((2 : ℝ) * (delta)) ≤ (7/33 : ℝ)) ∧ (h 0 ≤ (6/37 : ℝ)) ∧ (h 1 ≤ (5/37 : ℝ)) ∧ (h 2 ≤ (2/15 : ℝ)) ∧ (h 4 ≤ (4/37 : ℝ)) ∧ (h 5 ≤ (3/28 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_12731 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : h 1 ≤ (8/59 : ℝ))
    (a36 : -(h 1) < (-4/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a15 + (1 : ℝ) * a36
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12730 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : h 0 ≤ (4/27 : ℝ))
    (a35 : -(h 0) < (-5/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a35
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12729 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a34
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12728 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : h 1 ≤ (8/59 : ℝ))
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a21 : -(h 0) < (-1/7 : ℝ))
    (a25 : -(h 3) < (-7/60 : ℝ))
    (a27 : h 0 ≤ (4/27 : ℝ))
    (a28 : -(h 2) < (-7/54 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_12729 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (5/29 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/29 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_12730 h delta _ctx _hno a27 f1
  by_cases p2 : h 1 ≤ (4/29 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/29 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_12731 h delta _ctx _hno a15 f2
  by_cases p3 : h 4 ≤ (3/29 : ℝ)
  swap
  · have f3 : -(h 4) < (-3/29 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_12732 h delta _ctx _hno a15 a17 a21 a25 a27 a28 f3
  apply _hno 7
  change (((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)) ∧ (h 0 ≤ (5/29 : ℝ)) ∧ (h 1 ≤ (4/29 : ℝ)) ∧ (h 4 ≤ (3/29 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_12727 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a28 : -(h 2) < (-7/54 : ℝ))
    (a32 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/13 : ℝ) * _ctx.order1 + (4/13 : ℝ) * _ctx.min + (8/13 : ℝ) * _ctx.lower + (1/13 : ℝ) * _ctx.fail2 + (8/13 : ℝ) * a28 + (4/13 : ℝ) * a32 + (4/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12726 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : h 1 ≤ (8/59 : ℝ))
    (a31 : -(h 2) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * _ctx.order1 + (1 : ℝ) * a15 + (1 : ℝ) * a31
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12725 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : h 0 ≤ (4/27 : ℝ))
    (a30 : -(h 0) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a30
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12724 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a29 : ((-2 : ℝ) * (delta)) < (-1/5 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a29
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12723 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a37 : h 4 ≤ (4/37 : ℝ))
    (a45 : -(h 4) < (-7/62 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a37 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12722 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : -(h 2) < (-1/8 : ℝ))
    (a25 : -(h 3) < (-7/60 : ℝ))
    (a27 : -(h 0) < (-4/27 : ℝ))
    (a38 : -(h 5) < (-3/28 : ℝ))
    (a44 : -(h 1) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order4 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a19 + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a27 + (1/3 : ℝ) * a38 + (1/6 : ℝ) * a44 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12721 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : -(h 2) < (-1/8 : ℝ))
    (a25 : -(h 3) < (-7/60 : ℝ))
    (a38 : -(h 5) < (-3/28 : ℝ))
    (a41 : -(h 1) < (-5/39 : ℝ))
    (a43 : -(h 0) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order4 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a19 + (1/6 : ℝ) * a25 + (1/3 : ℝ) * a38 + (1/6 : ℝ) * a41 + (1/6 : ℝ) * a43 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12720 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a42 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12719 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a37 : h 4 ≤ (4/37 : ℝ))
    (a42 : -(h 4) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a37 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12718 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a19 : -(h 2) < (-1/8 : ℝ))
    (a25 : -(h 3) < (-7/60 : ℝ))
    (a27 : -(h 0) < (-4/27 : ℝ))
    (a37 : h 4 ≤ (4/37 : ℝ))
    (a38 : -(h 5) < (-3/28 : ℝ))
    (a41 : -(h 1) < (-5/39 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_12720 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_12721 h delta _ctx _hno a19 a25 a38 a41 f1
  by_cases p2 : h 1 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_12722 h delta _ctx _hno a19 a25 a27 a38 f2
  by_cases p3 : h 4 ≤ (7/62 : ℝ)
  swap
  · have f3 : -(h 4) < (-7/62 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_12723 h delta _ctx _hno a37 f3
  apply _hno 216
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 4 ≤ (7/62 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_12717 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a18 : h 0 ≤ (3/20 : ℝ))
    (a40 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a18 + (1 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12716 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a39 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_12715 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : -(h 2) < (-1/8 : ℝ))
    (a25 : -(h 3) < (-7/60 : ℝ))
    (a27 : -(h 0) < (-4/27 : ℝ))
    (a41 : -(h 4) < (-3/26 : ℝ))
    (a46 : -(h 5) < (-2/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order1 + (1/6 : ℝ) * _ctx.lower + (1/3 : ℝ) * a19 + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a41 + (1/6 : ℝ) * a46 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

end RealPinwheel.WeakSevenBandData
