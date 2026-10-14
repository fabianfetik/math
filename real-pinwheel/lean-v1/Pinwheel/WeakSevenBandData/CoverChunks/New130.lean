import Pinwheel.WeakSevenBandData.CoverChunks.New129

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem new_node_2714 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a29 : h 0 ≤ (4/27 : ℝ))
    (a30 : -(h 2) < (-7/54 : ℝ))
    (a33 : h 1 ≤ (4/29 : ℝ))
    (a35 : ((2 : ℝ) * (delta)) ≤ (7/34 : ℝ))
    (a36 : -(h 0) < (-5/34 : ℝ))
    (a42 : -(h 4) < (-5/47 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_2716 h delta _ctx _hno a35 f0
  by_cases p1 : h 0 ≤ (5/31 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/31 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_2717 h delta _ctx _hno a29 f1
  by_cases p2 : h 1 ≤ (6/43 : ℝ)
  swap
  · have f2 : -(h 1) < (-6/43 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_2718 h delta _ctx _hno a33 f2
  by_cases p3 : h 2 ≤ (3/22 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_2719 h delta _ctx _hno a13 a17 a36 a42 f3
  by_cases p4 : h 3 ≤ (5/43 : ℝ)
  swap
  · have f4 : -(h 3) < (-5/43 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_2720 h delta _ctx _hno a13 a23 a30 a36 a42 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_2721 h delta _ctx _hno a13 a23 a30 a36 f5
  apply _hno 228
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (5/31 : ℝ)) ∧ (h 1 ≤ (6/43 : ℝ)) ∧ (h 2 ≤ (3/22 : ℝ)) ∧ (h 3 ≤ (5/43 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_2713 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a30 : -(h 2) < (-7/54 : ℝ))
    (a41 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/17 : ℝ) * _ctx.min + (1/17 : ℝ) * _ctx.fail2 + (4/17 : ℝ) * a13 + (4/17 : ℝ) * a23 + (4/17 : ℝ) * a30 + (4/17 : ℝ) * a41 + (4/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2712 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a33 : h 1 ≤ (4/29 : ℝ))
    (a40 : -(h 2) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * _ctx.order1 + (1 : ℝ) * a33 + (1 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2711 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a33 : h 1 ≤ (4/29 : ℝ))
    (a39 : -(h 1) < (-5/34 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2710 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a29 : h 0 ≤ (4/27 : ℝ))
    (a38 : -(h 0) < (-4/27 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a38
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2709 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a35 : ((2 : ℝ) * (delta)) ≤ (7/34 : ℝ))
    (a37 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a35 + (1 : ℝ) * a37
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2708 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a30 : -(h 2) < (-7/54 : ℝ))
    (a35 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a41 : -(h 0) < (-13/90 : ℝ))
    (a47 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a23 + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a41 + (1/3 : ℝ) * a47 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2707 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a30 : -(h 2) < (-7/54 : ℝ))
    (a35 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a39 : -(h 4) < (-5/47 : ℝ))
    (a41 : -(h 0) < (-13/90 : ℝ))
    (a46 : -(h 3) < (-5/43 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a23 + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a39 + (1/6 : ℝ) * a41 + (1/6 : ℝ) * a46 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2706 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a38 : h 2 ≤ (3/23 : ℝ))
    (a45 : -(h 2) < (-3/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a38 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2705 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a33 : h 1 ≤ (4/29 : ℝ))
    (a44 : -(h 1) < (-6/43 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2704 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a29 : h 0 ≤ (4/27 : ℝ))
    (a43 : -(h 0) < (-5/31 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2703 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a31 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a42 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2702 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a30 : -(h 2) < (-7/54 : ℝ))
    (a35 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a44 : -(h 4) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/17 : ℝ) * _ctx.order3 + (4/17 : ℝ) * _ctx.min + (1/17 : ℝ) * _ctx.fail2 + (4/17 : ℝ) * a23 + (4/17 : ℝ) * a30 + (4/17 : ℝ) * a35 + (4/17 : ℝ) * a44 + (4/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2701 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a30 : -(h 2) < (-7/54 : ℝ))
    (a35 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a43 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/17 : ℝ) * _ctx.min + (1/17 : ℝ) * _ctx.fail2 + (4/17 : ℝ) * a23 + (4/17 : ℝ) * a30 + (4/17 : ℝ) * a35 + (4/17 : ℝ) * a43 + (4/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2700 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a33 : h 1 ≤ (4/29 : ℝ))
    (a42 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2699 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a29 : h 0 ≤ (4/27 : ℝ))
    (a30 : -(h 2) < (-7/54 : ℝ))
    (a31 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a33 : h 1 ≤ (4/29 : ℝ))
    (a35 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a38 : h 2 ≤ (3/23 : ℝ))
    (a39 : -(h 4) < (-5/47 : ℝ))
    (a41 : -(h 0) < (-13/90 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_2703 h delta _ctx _hno a31 f0
  by_cases p1 : h 0 ≤ (5/31 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/31 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_2704 h delta _ctx _hno a29 f1
  by_cases p2 : h 1 ≤ (6/43 : ℝ)
  swap
  · have f2 : -(h 1) < (-6/43 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_2705 h delta _ctx _hno a33 f2
  by_cases p3 : h 2 ≤ (3/22 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_2706 h delta _ctx _hno a38 f3
  by_cases p4 : h 3 ≤ (5/43 : ℝ)
  swap
  · have f4 : -(h 3) < (-5/43 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_2707 h delta _ctx _hno a23 a30 a35 a39 a41 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_2708 h delta _ctx _hno a23 a30 a35 a41 f5
  apply _hno 228
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (5/31 : ℝ)) ∧ (h 1 ≤ (6/43 : ℝ)) ∧ (h 2 ≤ (3/22 : ℝ)) ∧ (h 3 ≤ (5/43 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_2698 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a31 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a40 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2697 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a44 : h 4 ≤ (5/47 : ℝ))
    (a53 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a44 + (1 : ℝ) * a53
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2696 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a35 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a38 : -(h 2) < (-3/23 : ℝ))
    (a45 : -(h 5) < (-2/19 : ℝ))
    (a52 : -(h 3) < (-5/43 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/19 : ℝ) * _ctx.fail2 + (4/19 : ℝ) * a23 + (2/19 : ℝ) * a35 + (4/19 : ℝ) * a38 + (4/19 : ℝ) * a45 + (4/19 : ℝ) * a52 + (4/19 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2695 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a35 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a45 : -(h 5) < (-2/19 : ℝ))
    (a51 : -(h 2) < (-3/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/19 : ℝ) * _ctx.order1 + (1/19 : ℝ) * _ctx.fail2 + (4/19 : ℝ) * a17 + (2/19 : ℝ) * a35 + (4/19 : ℝ) * a45 + (8/19 : ℝ) * a51 + (4/19 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2694 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a33 : h 1 ≤ (4/29 : ℝ))
    (a50 : -(h 1) < (-6/43 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2693 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a29 : h 0 ≤ (4/27 : ℝ))
    (a49 : -(h 0) < (-5/31 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2692 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a31 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a48 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2691 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a44 : h 4 ≤ (5/47 : ℝ))
    (a50 : -(h 4) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a44 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2690 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a35 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a38 : -(h 2) < (-3/23 : ℝ))
    (a45 : -(h 5) < (-2/19 : ℝ))
    (a49 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/19 : ℝ) * _ctx.fail2 + (4/19 : ℝ) * a23 + (2/19 : ℝ) * a35 + (4/19 : ℝ) * a38 + (4/19 : ℝ) * a45 + (4/19 : ℝ) * a49 + (4/19 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2689 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a33 : h 1 ≤ (4/29 : ℝ))
    (a48 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2688 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a29 : h 0 ≤ (4/27 : ℝ))
    (a31 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a33 : h 1 ≤ (4/29 : ℝ))
    (a35 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a38 : -(h 2) < (-3/23 : ℝ))
    (a44 : h 4 ≤ (5/47 : ℝ))
    (a45 : -(h 5) < (-2/19 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_2692 h delta _ctx _hno a31 f0
  by_cases p1 : h 0 ≤ (5/31 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/31 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_2693 h delta _ctx _hno a29 f1
  by_cases p2 : h 1 ≤ (6/43 : ℝ)
  swap
  · have f2 : -(h 1) < (-6/43 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_2694 h delta _ctx _hno a33 f2
  by_cases p3 : h 2 ≤ (3/22 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_2695 h delta _ctx _hno a17 a35 a45 f3
  by_cases p4 : h 3 ≤ (5/43 : ℝ)
  swap
  · have f4 : -(h 3) < (-5/43 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_2696 h delta _ctx _hno a23 a35 a38 a45 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_2697 h delta _ctx _hno a44 f5
  apply _hno 228
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (5/31 : ℝ)) ∧ (h 1 ≤ (6/43 : ℝ)) ∧ (h 2 ≤ (3/22 : ℝ)) ∧ (h 3 ≤ (5/43 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_2687 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a38 : -(h 2) < (-3/23 : ℝ))
    (a45 : -(h 5) < (-2/19 : ℝ))
    (a46 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/19 : ℝ) * _ctx.fail2 + (4/19 : ℝ) * a17 + (4/19 : ℝ) * a23 + (4/19 : ℝ) * a38 + (4/19 : ℝ) * a45 + (2/19 : ℝ) * a46 + (4/19 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2686 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a35 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a38 : -(h 2) < (-3/23 : ℝ))
    (a46 : -(h 0) < (-13/90 : ℝ))
    (a52 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a23 + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a38 + (1/6 : ℝ) * a46 + (1/3 : ℝ) * a52 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2685 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a35 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a38 : -(h 2) < (-3/23 : ℝ))
    (a51 : -(h 3) < (-5/43 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/17 : ℝ) * _ctx.min + (1/17 : ℝ) * _ctx.fail2 + (4/17 : ℝ) * a23 + (4/17 : ℝ) * a35 + (4/17 : ℝ) * a38 + (4/17 : ℝ) * a51 + (4/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2684 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a35 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a50 : -(h 2) < (-3/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/17 : ℝ) * _ctx.order1 + (4/17 : ℝ) * _ctx.min + (1/17 : ℝ) * _ctx.fail2 + (4/17 : ℝ) * a17 + (4/17 : ℝ) * a35 + (8/17 : ℝ) * a50 + (4/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2683 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a33 : h 1 ≤ (4/29 : ℝ))
    (a49 : -(h 1) < (-6/43 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2682 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a29 : h 0 ≤ (4/27 : ℝ))
    (a48 : -(h 0) < (-5/31 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2681 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a31 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a47 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2680 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a35 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a38 : -(h 2) < (-3/23 : ℝ))
    (a49 : -(h 4) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/17 : ℝ) * _ctx.order3 + (4/17 : ℝ) * _ctx.min + (1/17 : ℝ) * _ctx.fail2 + (4/17 : ℝ) * a23 + (4/17 : ℝ) * a35 + (4/17 : ℝ) * a38 + (4/17 : ℝ) * a49 + (4/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2679 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a35 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a38 : -(h 2) < (-3/23 : ℝ))
    (a48 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/17 : ℝ) * _ctx.min + (1/17 : ℝ) * _ctx.fail2 + (4/17 : ℝ) * a23 + (4/17 : ℝ) * a35 + (4/17 : ℝ) * a38 + (4/17 : ℝ) * a48 + (4/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2678 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a33 : h 1 ≤ (4/29 : ℝ))
    (a47 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2677 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a29 : h 0 ≤ (4/27 : ℝ))
    (a31 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a33 : h 1 ≤ (4/29 : ℝ))
    (a35 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a38 : -(h 2) < (-3/23 : ℝ))
    (a46 : -(h 0) < (-13/90 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_2681 h delta _ctx _hno a31 f0
  by_cases p1 : h 0 ≤ (5/31 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/31 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_2682 h delta _ctx _hno a29 f1
  by_cases p2 : h 1 ≤ (6/43 : ℝ)
  swap
  · have f2 : -(h 1) < (-6/43 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_2683 h delta _ctx _hno a33 f2
  by_cases p3 : h 2 ≤ (3/22 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_2684 h delta _ctx _hno a17 a35 f3
  by_cases p4 : h 3 ≤ (5/43 : ℝ)
  swap
  · have f4 : -(h 3) < (-5/43 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_2685 h delta _ctx _hno a23 a35 a38 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_2686 h delta _ctx _hno a23 a35 a38 a46 f5
  apply _hno 228
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (5/31 : ℝ)) ∧ (h 1 ≤ (6/43 : ℝ)) ∧ (h 2 ≤ (3/22 : ℝ)) ∧ (h 3 ≤ (5/43 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_2676 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a31 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a45 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2675 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a29 : h 0 ≤ (4/27 : ℝ))
    (a31 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a33 : h 1 ≤ (4/29 : ℝ))
    (a35 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a38 : -(h 2) < (-3/23 : ℝ))
    (a44 : h 4 ≤ (5/47 : ℝ))
    (a45 : -(h 5) < (-2/19 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_2687 h delta _ctx _hno a17 a23 a38 a45 f0
  by_cases p1 : h 0 ≤ (13/90 : ℝ)
  swap
  · have f1 : -(h 0) < (-13/90 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_2688 h delta _ctx _hno a17 a23 a29 a31 a33 a35 a38 a44 a45
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_2689 h delta _ctx _hno a33 f2
  by_cases p3 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_2690 h delta _ctx _hno a23 a35 a38 a45 f3
  by_cases p4 : h 4 ≤ (3/26 : ℝ)
  swap
  · have f4 : -(h 4) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_2691 h delta _ctx _hno a44 f4
  apply _hno 211
  change (((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)) ∧ (h 0 ≤ (13/90 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (3/26 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_2674 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a29 : h 0 ≤ (4/27 : ℝ))
    (a31 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a33 : h 1 ≤ (4/29 : ℝ))
    (a35 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a38 : -(h 2) < (-3/23 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_2676 h delta _ctx _hno a31 f0
  by_cases p1 : h 0 ≤ (13/90 : ℝ)
  swap
  · have f1 : -(h 0) < (-13/90 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_2677 h delta _ctx _hno a17 a23 a29 a31 a33 a35 a38 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_2678 h delta _ctx _hno a33 f2
  by_cases p3 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_2679 h delta _ctx _hno a23 a35 a38 f3
  by_cases p4 : h 4 ≤ (3/26 : ℝ)
  swap
  · have f4 : -(h 4) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_2680 h delta _ctx _hno a23 a35 a38 f4
  apply _hno 211
  change (((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)) ∧ (h 0 ≤ (13/90 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (3/26 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_2673 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a35 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a38 : -(h 2) < (-3/23 : ℝ))
    (a43 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/17 : ℝ) * _ctx.min + (1/17 : ℝ) * _ctx.fail2 + (4/17 : ℝ) * a23 + (4/17 : ℝ) * a35 + (4/17 : ℝ) * a38 + (4/17 : ℝ) * a43 + (4/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2672 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a33 : h 1 ≤ (4/29 : ℝ))
    (a42 : -(h 2) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * _ctx.order1 + (1 : ℝ) * a33 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2671 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a33 : h 1 ≤ (4/29 : ℝ))
    (a41 : -(h 1) < (-5/34 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2670 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a29 : h 0 ≤ (4/27 : ℝ))
    (a40 : -(h 0) < (-4/27 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2669 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a31 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a39 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2668 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a29 : h 0 ≤ (4/27 : ℝ))
    (a30 : -(h 2) < (-7/54 : ℝ))
    (a31 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a33 : h 1 ≤ (4/29 : ℝ))
    (a35 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a38 : h 2 ≤ (3/23 : ℝ))
    (a39 : -(h 4) < (-5/47 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_2698 h delta _ctx _hno a31 f0
  by_cases p1 : h 0 ≤ (13/90 : ℝ)
  swap
  · have f1 : -(h 0) < (-13/90 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_2699 h delta _ctx _hno a23 a29 a30 a31 a33 a35 a38 a39 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_2700 h delta _ctx _hno a33 f2
  by_cases p3 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_2701 h delta _ctx _hno a23 a30 a35 f3
  by_cases p4 : h 4 ≤ (3/26 : ℝ)
  swap
  · have f4 : -(h 4) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_2702 h delta _ctx _hno a23 a30 a35 f4
  apply _hno 211
  change (((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)) ∧ (h 0 ≤ (13/90 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (3/26 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_2667 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a29 : h 0 ≤ (4/27 : ℝ))
    (a31 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a33 : h 1 ≤ (4/29 : ℝ))
    (a35 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a38 : -(h 2) < (-3/23 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_2669 h delta _ctx _hno a31 f0
  by_cases p1 : h 0 ≤ (4/27 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/27 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_2670 h delta _ctx _hno a29 f1
  by_cases p2 : h 1 ≤ (5/34 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/34 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_2671 h delta _ctx _hno a33 f2
  by_cases p3 : h 2 ≤ (1/7 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_2672 h delta _ctx _hno a33 f3
  by_cases p4 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_2673 h delta _ctx _hno a23 a35 a38 f4
  by_cases p5 : h 4 ≤ (5/47 : ℝ)
  swap
  · have f5 : -(h 4) < (-5/47 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_2674 h delta _ctx _hno a17 a23 a29 a31 a33 a35 a38
  by_cases p6 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f6 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact new_node_2675 h delta _ctx _hno a17 a23 a29 a31 a33 a35 a38 p5 f6
  apply _hno 57
  change (((2 : ℝ) * (delta)) ≤ (10/47 : ℝ)) ∧ (h 0 ≤ (4/27 : ℝ)) ∧ (h 1 ≤ (5/34 : ℝ)) ∧ (h 2 ≤ (1/7 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (5/47 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem new_node_2666 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a29 : h 0 ≤ (4/27 : ℝ))
    (a37 : -(h 0) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a37
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2665 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a31 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a36 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a36
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2664 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a30 : -(h 2) < (-7/54 : ℝ))
    (a39 : -(h 5) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/19 : ℝ) * _ctx.order3 + (4/19 : ℝ) * _ctx.order4 + (1/19 : ℝ) * _ctx.fail2 + (2/19 : ℝ) * a13 + (4/19 : ℝ) * a23 + (4/19 : ℝ) * a30 + (8/19 : ℝ) * a39 + (4/19 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2663 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a30 : -(h 2) < (-7/54 : ℝ))
    (a38 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/17 : ℝ) * _ctx.min + (1/17 : ℝ) * _ctx.fail2 + (4/17 : ℝ) * a13 + (4/17 : ℝ) * a23 + (4/17 : ℝ) * a30 + (4/17 : ℝ) * a38 + (4/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2662 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a33 : h 1 ≤ (4/29 : ℝ))
    (a37 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a37
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2661 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a29 : h 0 ≤ (4/27 : ℝ))
    (a30 : -(h 2) < (-7/54 : ℝ))
    (a33 : h 1 ≤ (4/29 : ℝ))
    (a35 : ((2 : ℝ) * (delta)) ≤ (7/34 : ℝ))
    (a36 : -(h 0) < (-5/34 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_2709 h delta _ctx _hno a35 f0
  by_cases p1 : h 0 ≤ (4/27 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/27 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_2710 h delta _ctx _hno a29 f1
  by_cases p2 : h 1 ≤ (5/34 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/34 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_2711 h delta _ctx _hno a33 f2
  by_cases p3 : h 2 ≤ (1/7 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_2712 h delta _ctx _hno a33 f3
  by_cases p4 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_2713 h delta _ctx _hno a13 a23 a30 f4
  by_cases p5 : h 4 ≤ (5/47 : ℝ)
  swap
  · have f5 : -(h 4) < (-5/47 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_2714 h delta _ctx _hno a13 a17 a23 a29 a30 a33 a35 a36 f5
  by_cases p6 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f6 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact new_node_2715 h delta _ctx _hno a13 a17 a23 a30 a36 f6
  apply _hno 57
  change (((2 : ℝ) * (delta)) ≤ (10/47 : ℝ)) ∧ (h 0 ≤ (4/27 : ℝ)) ∧ (h 1 ≤ (5/34 : ℝ)) ∧ (h 2 ≤ (1/7 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (5/47 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem new_node_2660 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a29 : h 0 ≤ (4/27 : ℝ))
    (a30 : -(h 2) < (-7/54 : ℝ))
    (a31 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a33 : h 1 ≤ (4/29 : ℝ))
    (a35 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_2665 h delta _ctx _hno a31 f0
  by_cases p1 : h 0 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_2666 h delta _ctx _hno a29 f1
  by_cases p2 : h 2 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 2) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_2667 h delta _ctx _hno a17 a23 a29 a31 a33 a35 f2
  by_cases p3 : h 4 ≤ (5/47 : ℝ)
  swap
  · have f3 : -(h 4) < (-5/47 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_2668 h delta _ctx _hno a23 a29 a30 a31 a33 a35 p2 f3
  apply _hno 143
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 4 ≤ (5/47 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_2659 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a30 : -(h 2) < (-7/54 : ℝ))
    (a33 : -(h 1) < (-4/29 : ℝ))
    (a42 : -(h 5) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/17 : ℝ) * _ctx.order3 + (4/17 : ℝ) * _ctx.order4 + (4/17 : ℝ) * _ctx.lower + (1/17 : ℝ) * _ctx.fail2 + (4/17 : ℝ) * a30 + (4/17 : ℝ) * a33 + (8/17 : ℝ) * a42 + (4/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2658 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a30 : -(h 2) < (-7/54 : ℝ))
    (a33 : -(h 1) < (-4/29 : ℝ))
    (a41 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/17 : ℝ) * _ctx.min + (1/17 : ℝ) * _ctx.fail2 + (4/17 : ℝ) * a13 + (4/17 : ℝ) * a30 + (4/17 : ℝ) * a33 + (4/17 : ℝ) * a41 + (4/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2657 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a40 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2656 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a30 : -(h 2) < (-7/54 : ℝ))
    (a33 : -(h 1) < (-4/29 : ℝ))
    (a37 : -(h 4) < (-5/47 : ℝ))
    (a39 : -(h 0) < (-5/34 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a17 + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a39 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2655 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a30 : -(h 2) < (-7/54 : ℝ))
    (a33 : -(h 1) < (-4/29 : ℝ))
    (a38 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/17 : ℝ) * _ctx.min + (1/17 : ℝ) * _ctx.fail2 + (4/17 : ℝ) * a17 + (4/17 : ℝ) * a30 + (4/17 : ℝ) * a33 + (4/17 : ℝ) * a38 + (4/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2654 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a33 : -(h 1) < (-4/29 : ℝ))
    (a36 : -(h 2) < (-3/23 : ℝ))
    (a47 : -(h 5) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/17 : ℝ) * _ctx.order3 + (4/17 : ℝ) * _ctx.order4 + (4/17 : ℝ) * _ctx.lower + (1/17 : ℝ) * _ctx.fail2 + (4/17 : ℝ) * a33 + (4/17 : ℝ) * a36 + (8/17 : ℝ) * a47 + (4/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2653 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a33 : -(h 1) < (-4/29 : ℝ))
    (a36 : -(h 2) < (-3/23 : ℝ))
    (a46 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/17 : ℝ) * _ctx.min + (1/17 : ℝ) * _ctx.fail2 + (4/17 : ℝ) * a13 + (4/17 : ℝ) * a33 + (4/17 : ℝ) * a36 + (4/17 : ℝ) * a46 + (4/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2652 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a45 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2651 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a33 : -(h 1) < (-4/29 : ℝ))
    (a36 : -(h 2) < (-3/23 : ℝ))
    (a42 : -(h 4) < (-5/47 : ℝ))
    (a44 : -(h 0) < (-5/34 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a17 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a36 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a44 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2650 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a33 : -(h 1) < (-4/29 : ℝ))
    (a36 : -(h 2) < (-3/23 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/17 : ℝ) * _ctx.min + (1/17 : ℝ) * _ctx.fail2 + (4/17 : ℝ) * a17 + (4/17 : ℝ) * a33 + (4/17 : ℝ) * a36 + (4/17 : ℝ) * a43 + (4/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2649 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a33 : -(h 1) < (-4/29 : ℝ))
    (a36 : -(h 2) < (-3/23 : ℝ))
    (a43 : -(h 5) < (-2/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/19 : ℝ) * _ctx.fail2 + (2/19 : ℝ) * a13 + (4/19 : ℝ) * a17 + (4/19 : ℝ) * a33 + (4/19 : ℝ) * a36 + (4/19 : ℝ) * a43 + (4/19 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2648 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a33 : -(h 1) < (-4/29 : ℝ))
    (a36 : -(h 2) < (-3/23 : ℝ))
    (a42 : -(h 4) < (-5/47 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_2650 h delta _ctx _hno a17 a33 a36 f0
  by_cases p1 : h 0 ≤ (5/34 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/34 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_2651 h delta _ctx _hno a13 a17 a33 a36 a42 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_2652 h delta _ctx _hno a16 f2
  by_cases p3 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_2653 h delta _ctx _hno a13 a33 a36 f3
  by_cases p4 : h 5 ≤ (3/26 : ℝ)
  swap
  · have f4 : -(h 5) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_2654 h delta _ctx _hno a33 a36 f4
  apply _hno 14
  change (((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)) ∧ (h 0 ≤ (5/34 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (3/26 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_2647 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a33 : -(h 1) < (-4/29 : ℝ))
    (a36 : -(h 2) < (-3/23 : ℝ))
    (a41 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/17 : ℝ) * _ctx.min + (1/17 : ℝ) * _ctx.fail2 + (4/17 : ℝ) * a13 + (4/17 : ℝ) * a33 + (4/17 : ℝ) * a36 + (4/17 : ℝ) * a41 + (4/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2646 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a40 : -(h 2) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/13 : ℝ) * _ctx.order1 + (4/13 : ℝ) * _ctx.min + (8/13 : ℝ) * _ctx.lower + (1/13 : ℝ) * _ctx.fail2 + (4/13 : ℝ) * a17 + (8/13 : ℝ) * a40 + (4/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2645 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a39 : -(h 1) < (-5/34 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2644 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a29 : h 0 ≤ (4/27 : ℝ))
    (a38 : -(h 0) < (-4/27 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a38
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2643 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a31 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a37 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a37
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2642 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a30 : -(h 2) < (-7/54 : ℝ))
    (a33 : -(h 1) < (-4/29 : ℝ))
    (a37 : -(h 4) < (-5/47 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_2655 h delta _ctx _hno a17 a30 a33 f0
  by_cases p1 : h 0 ≤ (5/34 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/34 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_2656 h delta _ctx _hno a13 a17 a30 a33 a37 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_2657 h delta _ctx _hno a16 f2
  by_cases p3 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_2658 h delta _ctx _hno a13 a30 a33 f3
  by_cases p4 : h 5 ≤ (3/26 : ℝ)
  swap
  · have f4 : -(h 5) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_2659 h delta _ctx _hno a30 a33 f4
  apply _hno 14
  change (((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)) ∧ (h 0 ≤ (5/34 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (3/26 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_2641 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a29 : h 0 ≤ (4/27 : ℝ))
    (a31 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a33 : -(h 1) < (-4/29 : ℝ))
    (a36 : -(h 2) < (-3/23 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_2643 h delta _ctx _hno a31 f0
  by_cases p1 : h 0 ≤ (4/27 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/27 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_2644 h delta _ctx _hno a29 f1
  by_cases p2 : h 1 ≤ (5/34 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/34 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_2645 h delta _ctx _hno a16 f2
  by_cases p3 : h 2 ≤ (1/7 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_2646 h delta _ctx _hno a17 f3
  by_cases p4 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_2647 h delta _ctx _hno a13 a33 a36 f4
  by_cases p5 : h 4 ≤ (5/47 : ℝ)
  swap
  · have f5 : -(h 4) < (-5/47 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_2648 h delta _ctx _hno a13 a16 a17 a33 a36 f5
  by_cases p6 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f6 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact new_node_2649 h delta _ctx _hno a13 a17 a33 a36 f6
  apply _hno 57
  change (((2 : ℝ) * (delta)) ≤ (10/47 : ℝ)) ∧ (h 0 ≤ (4/27 : ℝ)) ∧ (h 1 ≤ (5/34 : ℝ)) ∧ (h 2 ≤ (1/7 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (5/47 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem new_node_2640 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a29 : h 0 ≤ (4/27 : ℝ))
    (a35 : -(h 0) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a35
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2639 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a31 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a34
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2638 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a40 : h 4 ≤ (9/83 : ℝ))
    (a49 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a40 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2637 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a30 : -(h 2) < (-7/54 : ℝ))
    (a31 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a41 : -(h 5) < (-2/19 : ℝ))
    (a48 : -(h 3) < (-5/43 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/19 : ℝ) * _ctx.fail2 + (4/19 : ℝ) * a23 + (4/19 : ℝ) * a30 + (2/19 : ℝ) * a31 + (4/19 : ℝ) * a41 + (4/19 : ℝ) * a48 + (4/19 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2636 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : h 2 ≤ (3/23 : ℝ))
    (a47 : -(h 2) < (-3/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2635 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a30 : -(h 2) < (-7/54 : ℝ))
    (a31 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a41 : -(h 5) < (-2/19 : ℝ))
    (a46 : -(h 1) < (-6/43 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/19 : ℝ) * _ctx.fail2 + (4/19 : ℝ) * a17 + (4/19 : ℝ) * a30 + (2/19 : ℝ) * a31 + (4/19 : ℝ) * a41 + (4/19 : ℝ) * a46 + (4/19 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

end RealPinwheel.WeakSevenBandData
