import Pinwheel.WeakSevenBandData.CoverChunks.New115

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem new_node_3834 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a33 : -(h 2) < (-2/17 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a38 : -(h 1) < (-6/47 : ℝ))
    (a43 : -(h 3) < (-5/43 : ℝ))
    (a48 : -(h 4) < (-4/35 : ℝ))
    (a49 : ((-2 : ℝ) * (delta)) < (-9/44 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a38 + (1/6 : ℝ) * a43 + (1/6 : ℝ) * a48 + (1/6 : ℝ) * a49 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3833 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a33 : -(h 2) < (-2/17 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a43 : -(h 3) < (-5/43 : ℝ))
    (a46 : -(h 1) < (-9/70 : ℝ))
    (a57 : -(h 5) < (-3/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/13 : ℝ) * a13 + (2/13 : ℝ) * a25 + (2/13 : ℝ) * a33 + (2/13 : ℝ) * a35 + (2/13 : ℝ) * a43 + (2/13 : ℝ) * a46 + (2/13 : ℝ) * a57 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3832 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a43 : -(h 3) < (-5/43 : ℝ))
    (a46 : -(h 1) < (-9/70 : ℝ))
    (a52 : -(h 5) < (-5/48 : ℝ))
    (a56 : -(h 2) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/13 : ℝ) * a13 + (2/13 : ℝ) * a25 + (2/13 : ℝ) * a35 + (2/13 : ℝ) * a43 + (2/13 : ℝ) * a46 + (2/13 : ℝ) * a52 + (2/13 : ℝ) * a56 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3831 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a49 : h 1 ≤ (3/23 : ℝ))
    (a55 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a49 + (1 : ℝ) * a55
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3830 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a45 : h 0 ≤ (7/45 : ℝ))
    (a54 : -(h 0) < (-4/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a45 + (1 : ℝ) * a54
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3829 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a47 : ((2 : ℝ) * (delta)) ≤ (9/44 : ℝ))
    (a53 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a47 + (1 : ℝ) * a53
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3828 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a33 : -(h 2) < (-2/17 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a43 : -(h 3) < (-5/43 : ℝ))
    (a49 : -(h 1) < (-3/23 : ℝ))
    (a54 : -(h 5) < (-3/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/13 : ℝ) * a13 + (2/13 : ℝ) * a25 + (2/13 : ℝ) * a33 + (2/13 : ℝ) * a35 + (2/13 : ℝ) * a43 + (2/13 : ℝ) * a49 + (2/13 : ℝ) * a54 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3827 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a43 : -(h 3) < (-5/43 : ℝ))
    (a49 : -(h 1) < (-3/23 : ℝ))
    (a53 : -(h 2) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a43 + (1/6 : ℝ) * a49 + (1/6 : ℝ) * a53 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3826 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a33 : -(h 2) < (-2/17 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a43 : -(h 3) < (-5/43 : ℝ))
    (a52 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a43 + (1/6 : ℝ) * a52 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3825 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a45 : h 0 ≤ (7/45 : ℝ))
    (a51 : -(h 0) < (-4/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a45 + (1 : ℝ) * a51
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3824 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a47 : ((2 : ℝ) * (delta)) ≤ (9/44 : ℝ))
    (a50 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a47 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3823 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a33 : -(h 2) < (-2/17 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a43 : -(h 3) < (-5/43 : ℝ))
    (a46 : -(h 1) < (-9/70 : ℝ))
    (a47 : ((-2 : ℝ) * (delta)) < (-9/44 : ℝ))
    (a52 : -(h 5) < (-3/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * a25 + (2/13 : ℝ) * a33 + (2/13 : ℝ) * a35 + (2/13 : ℝ) * a43 + (2/13 : ℝ) * a46 + (1/13 : ℝ) * a47 + (2/13 : ℝ) * a52 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3822 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a43 : -(h 3) < (-5/43 : ℝ))
    (a46 : -(h 1) < (-9/70 : ℝ))
    (a47 : ((-2 : ℝ) * (delta)) < (-9/44 : ℝ))
    (a51 : -(h 2) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a43 + (1/6 : ℝ) * a46 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * a51 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3821 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a33 : -(h 2) < (-2/17 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a43 : -(h 3) < (-5/43 : ℝ))
    (a47 : ((-2 : ℝ) * (delta)) < (-9/44 : ℝ))
    (a50 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a43 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * a50 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3820 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a45 : h 0 ≤ (7/45 : ℝ))
    (a49 : -(h 0) < (-4/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a45 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3819 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a39 : ((2 : ℝ) * (delta)) ≤ (7/34 : ℝ))
    (a48 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a39 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3818 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a33 : -(h 2) < (-2/17 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a43 : -(h 3) < (-5/43 : ℝ))
    (a45 : h 0 ≤ (7/45 : ℝ))
    (a46 : -(h 1) < (-9/70 : ℝ))
    (a47 : ((2 : ℝ) * (delta)) ≤ (9/44 : ℝ))
    (a49 : h 1 ≤ (3/23 : ℝ))
    (a52 : -(h 5) < (-5/48 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_3829 h delta _ctx _hno a47 f0
  by_cases p1 : h 0 ≤ (4/25 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/25 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_3830 h delta _ctx _hno a45 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_3831 h delta _ctx _hno a49 f2
  by_cases p3 : h 2 ≤ (3/25 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_3832 h delta _ctx _hno a13 a25 a35 a43 a46 a52 f3
  by_cases p4 : h 5 ≤ (3/28 : ℝ)
  swap
  · have f4 : -(h 5) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_3833 h delta _ctx _hno a13 a25 a33 a35 a43 a46 f4
  apply _hno 171
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 5 ≤ (3/28 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_3817 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a33 : -(h 2) < (-2/17 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a46 : -(h 1) < (-9/70 : ℝ))
    (a51 : -(h 4) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a46 + (1/3 : ℝ) * a51 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3816 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a46 : -(h 1) < (-9/70 : ℝ))
    (a50 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order2 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a46 + (1/3 : ℝ) * a50 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3815 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a33 : -(h 2) < (-2/17 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a43 : -(h 3) < (-5/43 : ℝ))
    (a45 : h 0 ≤ (7/45 : ℝ))
    (a47 : ((2 : ℝ) * (delta)) ≤ (9/44 : ℝ))
    (a49 : -(h 1) < (-3/23 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_3824 h delta _ctx _hno a47 f0
  by_cases p1 : h 0 ≤ (4/25 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/25 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_3825 h delta _ctx _hno a45 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_3826 h delta _ctx _hno a13 a25 a33 a35 a43 f2
  by_cases p3 : h 2 ≤ (3/25 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_3827 h delta _ctx _hno a13 a25 a35 a43 a49 f3
  by_cases p4 : h 5 ≤ (3/28 : ℝ)
  swap
  · have f4 : -(h 5) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_3828 h delta _ctx _hno a13 a25 a33 a35 a43 a49 f4
  apply _hno 171
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 5 ≤ (3/28 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_3814 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a45 : h 0 ≤ (7/45 : ℝ))
    (a48 : -(h 0) < (-5/31 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a45 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3813 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a33 : -(h 2) < (-2/17 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a39 : ((2 : ℝ) * (delta)) ≤ (7/34 : ℝ))
    (a43 : -(h 3) < (-5/43 : ℝ))
    (a45 : h 0 ≤ (7/45 : ℝ))
    (a46 : -(h 1) < (-9/70 : ℝ))
    (a47 : ((-2 : ℝ) * (delta)) < (-9/44 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_3819 h delta _ctx _hno a39 f0
  by_cases p1 : h 0 ≤ (4/25 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/25 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_3820 h delta _ctx _hno a45 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_3821 h delta _ctx _hno a25 a33 a35 a43 a47 f2
  by_cases p3 : h 2 ≤ (3/25 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_3822 h delta _ctx _hno a25 a35 a43 a46 a47 f3
  by_cases p4 : h 5 ≤ (3/28 : ℝ)
  swap
  · have f4 : -(h 5) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_3823 h delta _ctx _hno a25 a33 a35 a43 a46 a47 f4
  apply _hno 171
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 5 ≤ (3/28 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_3812 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a33 : -(h 2) < (-2/17 : ℝ))
    (a38 : -(h 1) < (-6/47 : ℝ))
    (a43 : -(h 3) < (-5/43 : ℝ))
    (a45 : -(h 0) < (-7/45 : ℝ))
    (a46 : ((-2 : ℝ) * (delta)) < (-9/44 : ℝ))
    (a51 : -(h 5) < (-3/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * a25 + (2/13 : ℝ) * a33 + (2/13 : ℝ) * a38 + (2/13 : ℝ) * a43 + (2/13 : ℝ) * a45 + (1/13 : ℝ) * a46 + (2/13 : ℝ) * a51 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3811 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a38 : -(h 1) < (-6/47 : ℝ))
    (a43 : -(h 3) < (-5/43 : ℝ))
    (a45 : -(h 0) < (-7/45 : ℝ))
    (a46 : ((-2 : ℝ) * (delta)) < (-9/44 : ℝ))
    (a50 : -(h 2) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a38 + (1/6 : ℝ) * a43 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a46 + (1/6 : ℝ) * a50 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3810 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a33 : -(h 2) < (-2/17 : ℝ))
    (a43 : -(h 3) < (-5/43 : ℝ))
    (a45 : -(h 0) < (-7/45 : ℝ))
    (a46 : ((-2 : ℝ) * (delta)) < (-9/44 : ℝ))
    (a49 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a43 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a46 + (1/6 : ℝ) * a49 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3809 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a31 : h 0 ≤ (8/51 : ℝ))
    (a48 : -(h 0) < (-4/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3808 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a39 : ((2 : ℝ) * (delta)) ≤ (7/34 : ℝ))
    (a47 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a39 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3807 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a33 : -(h 2) < (-2/17 : ℝ))
    (a38 : -(h 1) < (-6/47 : ℝ))
    (a43 : -(h 3) < (-5/43 : ℝ))
    (a45 : -(h 0) < (-7/45 : ℝ))
    (a51 : -(h 5) < (-5/48 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/13 : ℝ) * a13 + (2/13 : ℝ) * a25 + (2/13 : ℝ) * a33 + (2/13 : ℝ) * a38 + (2/13 : ℝ) * a43 + (2/13 : ℝ) * a45 + (2/13 : ℝ) * a51 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3806 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a33 : -(h 2) < (-2/17 : ℝ))
    (a38 : -(h 1) < (-6/47 : ℝ))
    (a45 : -(h 0) < (-7/45 : ℝ))
    (a50 : -(h 4) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a38 + (1/6 : ℝ) * a45 + (1/3 : ℝ) * a50 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3805 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a38 : -(h 1) < (-6/47 : ℝ))
    (a45 : -(h 0) < (-7/45 : ℝ))
    (a49 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order2 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a38 + (1/6 : ℝ) * a45 + (1/3 : ℝ) * a49 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3804 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a33 : -(h 2) < (-2/17 : ℝ))
    (a43 : -(h 3) < (-5/43 : ℝ))
    (a45 : -(h 0) < (-7/45 : ℝ))
    (a48 : -(h 1) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a43 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a48 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3803 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a31 : h 0 ≤ (8/51 : ℝ))
    (a47 : -(h 0) < (-5/31 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3802 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a31 : h 0 ≤ (8/51 : ℝ))
    (a33 : -(h 2) < (-2/17 : ℝ))
    (a38 : -(h 1) < (-6/47 : ℝ))
    (a39 : ((2 : ℝ) * (delta)) ≤ (7/34 : ℝ))
    (a43 : -(h 3) < (-5/43 : ℝ))
    (a45 : -(h 0) < (-7/45 : ℝ))
    (a46 : ((-2 : ℝ) * (delta)) < (-9/44 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_3808 h delta _ctx _hno a39 f0
  by_cases p1 : h 0 ≤ (4/25 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/25 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_3809 h delta _ctx _hno a31 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_3810 h delta _ctx _hno a25 a33 a43 a45 a46 f2
  by_cases p3 : h 2 ≤ (3/25 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_3811 h delta _ctx _hno a25 a38 a43 a45 a46 f3
  by_cases p4 : h 5 ≤ (3/28 : ℝ)
  swap
  · have f4 : -(h 5) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_3812 h delta _ctx _hno a25 a33 a38 a43 a45 a46 f4
  apply _hno 171
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 5 ≤ (3/28 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_3801 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a33 : -(h 2) < (-2/17 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a38 : -(h 1) < (-6/47 : ℝ))
    (a43 : -(h 3) < (-5/43 : ℝ))
    (a45 : h 0 ≤ (7/45 : ℝ))
    (a46 : h 1 ≤ (9/70 : ℝ))
    (a48 : -(h 4) < (-4/35 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (9/44 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-9/44 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_3834 h delta _ctx _hno a33 a35 a38 a43 a48 f0
  by_cases p1 : h 0 ≤ (5/31 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/31 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_3835 h delta _ctx _hno a45 f1
  by_cases p2 : h 1 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_3836 h delta _ctx _hno a46 f2
  by_cases p3 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_3837 h delta _ctx _hno a13 a35 a38 a48 f3
  by_cases p4 : h 4 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 4) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_3838 h delta _ctx _hno a13 a33 a35 a38 f4
  by_cases p5 : h 5 ≤ (5/48 : ℝ)
  swap
  · have f5 : -(h 5) < (-5/48 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_3839 h delta _ctx _hno a13 a33 a35 a38 a43 a48 f5
  apply _hno 155
  change (((2 : ℝ) * (delta)) ≤ (9/44 : ℝ)) ∧ (h 0 ≤ (5/31 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (5/48 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_3800 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a38 : -(h 1) < (-6/47 : ℝ))
    (a43 : -(h 3) < (-5/43 : ℝ))
    (a47 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a38 + (1/6 : ℝ) * a43 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3799 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a33 : -(h 2) < (-2/17 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a39 : ((2 : ℝ) * (delta)) ≤ (7/34 : ℝ))
    (a43 : -(h 3) < (-5/43 : ℝ))
    (a45 : h 0 ≤ (7/45 : ℝ))
    (a46 : -(h 1) < (-9/70 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (9/44 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-9/44 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_3813 h delta _ctx _hno a25 a33 a35 a39 a43 a45 a46 f0
  by_cases p1 : h 0 ≤ (5/31 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/31 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_3814 h delta _ctx _hno a45 f1
  by_cases p2 : h 1 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_3815 h delta _ctx _hno a13 a25 a33 a35 a43 a45 p0 f2
  by_cases p3 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_3816 h delta _ctx _hno a13 a25 a35 a46 f3
  by_cases p4 : h 4 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 4) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_3817 h delta _ctx _hno a13 a33 a35 a46 f4
  by_cases p5 : h 5 ≤ (5/48 : ℝ)
  swap
  · have f5 : -(h 5) < (-5/48 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_3818 h delta _ctx _hno a13 a25 a33 a35 a43 a45 a46 p0 p2 f5
  apply _hno 155
  change (((2 : ℝ) * (delta)) ≤ (9/44 : ℝ)) ∧ (h 0 ≤ (5/31 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (5/48 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_3798 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a31 : h 0 ≤ (8/51 : ℝ))
    (a33 : -(h 2) < (-2/17 : ℝ))
    (a38 : -(h 1) < (-6/47 : ℝ))
    (a39 : ((2 : ℝ) * (delta)) ≤ (7/34 : ℝ))
    (a43 : -(h 3) < (-5/43 : ℝ))
    (a45 : -(h 0) < (-7/45 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (9/44 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-9/44 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_3802 h delta _ctx _hno a25 a31 a33 a38 a39 a43 a45 f0
  by_cases p1 : h 0 ≤ (5/31 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/31 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_3803 h delta _ctx _hno a31 f1
  by_cases p2 : h 1 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_3804 h delta _ctx _hno a13 a25 a33 a43 a45 f2
  by_cases p3 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_3805 h delta _ctx _hno a13 a25 a38 a45 f3
  by_cases p4 : h 4 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 4) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_3806 h delta _ctx _hno a13 a33 a38 a45 f4
  by_cases p5 : h 5 ≤ (5/48 : ℝ)
  swap
  · have f5 : -(h 5) < (-5/48 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_3807 h delta _ctx _hno a13 a25 a33 a38 a43 a45 f5
  apply _hno 155
  change (((2 : ℝ) * (delta)) ≤ (9/44 : ℝ)) ∧ (h 0 ≤ (5/31 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (5/48 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_3797 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a39 : ((2 : ℝ) * (delta)) ≤ (7/34 : ℝ))
    (a44 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a39 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3796 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a33 : -(h 2) < (-2/17 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a39 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a43 : -(h 3) < (-3/26 : ℝ))
    (a46 : -(h 1) < (-9/70 : ℝ))
    (a51 : -(h 5) < (-3/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * a25 + (2/13 : ℝ) * a33 + (2/13 : ℝ) * a35 + (1/13 : ℝ) * a39 + (2/13 : ℝ) * a43 + (2/13 : ℝ) * a46 + (2/13 : ℝ) * a51 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3795 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a39 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a43 : -(h 3) < (-3/26 : ℝ))
    (a46 : -(h 1) < (-9/70 : ℝ))
    (a50 : -(h 2) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a39 + (1/6 : ℝ) * a43 + (1/6 : ℝ) * a46 + (1/6 : ℝ) * a50 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3794 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a42 : h 1 ≤ (4/31 : ℝ))
    (a49 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a42 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3793 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a45 : h 0 ≤ (7/45 : ℝ))
    (a48 : -(h 0) < (-4/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a45 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3792 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a47 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3791 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a33 : -(h 2) < (-2/17 : ℝ))
    (a38 : -(h 1) < (-6/47 : ℝ))
    (a39 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a43 : -(h 3) < (-3/26 : ℝ))
    (a45 : -(h 0) < (-7/45 : ℝ))
    (a50 : -(h 5) < (-3/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * a25 + (2/13 : ℝ) * a33 + (2/13 : ℝ) * a38 + (1/13 : ℝ) * a39 + (2/13 : ℝ) * a43 + (2/13 : ℝ) * a45 + (2/13 : ℝ) * a50 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3790 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a38 : -(h 1) < (-6/47 : ℝ))
    (a39 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a43 : -(h 3) < (-3/26 : ℝ))
    (a45 : -(h 0) < (-7/45 : ℝ))
    (a49 : -(h 2) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a38 + (1/6 : ℝ) * a39 + (1/6 : ℝ) * a43 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a49 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3789 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a42 : h 1 ≤ (4/31 : ℝ))
    (a48 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a42 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3788 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a31 : h 0 ≤ (8/51 : ℝ))
    (a47 : -(h 0) < (-4/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3787 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a46 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3786 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a33 : -(h 2) < (-2/17 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a38 : -(h 1) < (-6/47 : ℝ))
    (a39 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a43 : -(h 3) < (-3/26 : ℝ))
    (a48 : -(h 4) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a38 + (1/6 : ℝ) * a39 + (1/6 : ℝ) * a43 + (1/6 : ℝ) * a48 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3785 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a38 : -(h 1) < (-6/47 : ℝ))
    (a39 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a43 : -(h 3) < (-3/26 : ℝ))
    (a47 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a38 + (1/6 : ℝ) * a39 + (1/6 : ℝ) * a43 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3784 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a33 : -(h 2) < (-2/17 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a39 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a42 : h 1 ≤ (4/31 : ℝ))
    (a43 : -(h 3) < (-3/26 : ℝ))
    (a45 : h 0 ≤ (7/45 : ℝ))
    (a46 : -(h 1) < (-9/70 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_3792 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (4/25 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/25 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_3793 h delta _ctx _hno a45 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_3794 h delta _ctx _hno a42 f2
  by_cases p3 : h 2 ≤ (3/25 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_3795 h delta _ctx _hno a25 a35 a39 a43 a46 f3
  by_cases p4 : h 5 ≤ (3/28 : ℝ)
  swap
  · have f4 : -(h 5) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_3796 h delta _ctx _hno a25 a33 a35 a39 a43 a46 f4
  apply _hno 171
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 5 ≤ (3/28 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_3783 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a31 : h 0 ≤ (8/51 : ℝ))
    (a33 : -(h 2) < (-2/17 : ℝ))
    (a38 : -(h 1) < (-6/47 : ℝ))
    (a39 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a42 : h 1 ≤ (4/31 : ℝ))
    (a43 : -(h 3) < (-3/26 : ℝ))
    (a45 : -(h 0) < (-7/45 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_3787 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (4/25 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/25 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_3788 h delta _ctx _hno a31 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_3789 h delta _ctx _hno a42 f2
  by_cases p3 : h 2 ≤ (3/25 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_3790 h delta _ctx _hno a25 a38 a39 a43 a45 f3
  by_cases p4 : h 5 ≤ (3/28 : ℝ)
  swap
  · have f4 : -(h 5) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_3791 h delta _ctx _hno a25 a33 a38 a39 a43 a45 f4
  apply _hno 171
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 5 ≤ (3/28 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_3782 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a44 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3781 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a33 : -(h 2) < (-2/17 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a39 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a42 : -(h 1) < (-4/31 : ℝ))
    (a52 : -(h 5) < (-4/37 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * a17 + (2/13 : ℝ) * a25 + (2/13 : ℝ) * a33 + (2/13 : ℝ) * a35 + (1/13 : ℝ) * a39 + (2/13 : ℝ) * a42 + (2/13 : ℝ) * a52 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3780 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a33 : -(h 2) < (-2/17 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a39 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a42 : -(h 1) < (-4/31 : ℝ))
    (a47 : -(h 5) < (-3/28 : ℝ))
    (a51 : -(h 3) < (-7/62 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * a25 + (2/13 : ℝ) * a33 + (2/13 : ℝ) * a35 + (1/13 : ℝ) * a39 + (2/13 : ℝ) * a42 + (2/13 : ℝ) * a47 + (2/13 : ℝ) * a51 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3779 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a33 : -(h 2) < (-2/17 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a39 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a47 : -(h 5) < (-3/28 : ℝ))
    (a50 : -(h 1) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * a17 + (2/13 : ℝ) * a25 + (2/13 : ℝ) * a33 + (2/13 : ℝ) * a35 + (1/13 : ℝ) * a39 + (2/13 : ℝ) * a47 + (2/13 : ℝ) * a50 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3778 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a31 : h 0 ≤ (8/51 : ℝ))
    (a49 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3777 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a33 : -(h 2) < (-2/17 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a42 : -(h 1) < (-4/31 : ℝ))
    (a47 : -(h 5) < (-3/28 : ℝ))
    (a48 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * a17 + (2/13 : ℝ) * a25 + (2/13 : ℝ) * a33 + (2/13 : ℝ) * a35 + (2/13 : ℝ) * a42 + (2/13 : ℝ) * a47 + (1/13 : ℝ) * a48 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3776 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a39 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a42 : -(h 1) < (-4/31 : ℝ))
    (a46 : -(h 2) < (-3/25 : ℝ))
    (a63 : -(h 5) < (-4/37 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order3 + (4/13 : ℝ) * a25 + (2/13 : ℝ) * a35 + (1/13 : ℝ) * a39 + (2/13 : ℝ) * a42 + (2/13 : ℝ) * a46 + (2/13 : ℝ) * a63 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3775 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a39 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a42 : -(h 1) < (-4/31 : ℝ))
    (a46 : -(h 2) < (-3/25 : ℝ))
    (a58 : -(h 5) < (-2/19 : ℝ))
    (a62 : -(h 3) < (-7/62 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * a25 + (2/13 : ℝ) * a35 + (1/13 : ℝ) * a39 + (2/13 : ℝ) * a42 + (2/13 : ℝ) * a46 + (2/13 : ℝ) * a58 + (2/13 : ℝ) * a62 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3774 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a39 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a46 : -(h 2) < (-3/25 : ℝ))
    (a58 : -(h 5) < (-2/19 : ℝ))
    (a61 : -(h 1) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * a17 + (2/13 : ℝ) * a25 + (2/13 : ℝ) * a35 + (1/13 : ℝ) * a39 + (2/13 : ℝ) * a46 + (2/13 : ℝ) * a58 + (2/13 : ℝ) * a61 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3773 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a31 : h 0 ≤ (8/51 : ℝ))
    (a60 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a60
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3772 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a47 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a59 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a47 + (1 : ℝ) * a59
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3771 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a31 : h 0 ≤ (8/51 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a39 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a42 : -(h 1) < (-4/31 : ℝ))
    (a46 : -(h 2) < (-3/25 : ℝ))
    (a47 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a58 : -(h 5) < (-2/19 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_3772 h delta _ctx _hno a47 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_3773 h delta _ctx _hno a31 f1
  by_cases p2 : h 1 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_3774 h delta _ctx _hno a17 a25 a35 a39 a46 a58 f2
  by_cases p3 : h 3 ≤ (7/62 : ℝ)
  swap
  · have f3 : -(h 3) < (-7/62 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_3775 h delta _ctx _hno a25 a35 a39 a42 a46 a58 f3
  by_cases p4 : h 5 ≤ (4/37 : ℝ)
  swap
  · have f4 : -(h 5) < (-4/37 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_3776 h delta _ctx _hno a25 a35 a39 a42 a46 f4
  apply _hno 185
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (7/62 : ℝ)) ∧ (h 5 ≤ (4/37 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_3770 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a39 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a42 : -(h 1) < (-4/31 : ℝ))
    (a46 : -(h 2) < (-3/25 : ℝ))
    (a52 : -(h 5) < (-3/29 : ℝ))
    (a57 : -(h 4) < (-9/80 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order3 + (2/13 : ℝ) * a35 + (1/13 : ℝ) * a39 + (2/13 : ℝ) * a42 + (2/13 : ℝ) * a46 + (2/13 : ℝ) * a52 + (4/13 : ℝ) * a57 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3769 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a39 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a42 : -(h 1) < (-4/31 : ℝ))
    (a46 : -(h 2) < (-3/25 : ℝ))
    (a52 : -(h 5) < (-3/29 : ℝ))
    (a56 : -(h 3) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * a25 + (2/13 : ℝ) * a35 + (1/13 : ℝ) * a39 + (2/13 : ℝ) * a42 + (2/13 : ℝ) * a46 + (2/13 : ℝ) * a52 + (2/13 : ℝ) * a56 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3768 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : h 1 ≤ (2/15 : ℝ))
    (a55 : -(h 1) < (-3/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a23 + (1 : ℝ) * a55
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3767 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a31 : h 0 ≤ (8/51 : ℝ))
    (a54 : -(h 0) < (-3/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a54
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3766 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a47 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a53 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a47 + (1 : ℝ) * a53
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3765 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a42 : -(h 1) < (-4/31 : ℝ))
    (a46 : -(h 2) < (-3/25 : ℝ))
    (a47 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a53 : -(h 5) < (-2/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * a17 + (2/13 : ℝ) * a25 + (2/13 : ℝ) * a35 + (2/13 : ℝ) * a42 + (2/13 : ℝ) * a46 + (1/13 : ℝ) * a47 + (2/13 : ℝ) * a53 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3764 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a42 : -(h 1) < (-4/31 : ℝ))
    (a46 : -(h 2) < (-3/25 : ℝ))
    (a47 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a52 : -(h 4) < (-9/80 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a46 + (1/6 : ℝ) * a47 + (1/3 : ℝ) * a52 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3763 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a42 : -(h 1) < (-4/31 : ℝ))
    (a46 : -(h 2) < (-3/25 : ℝ))
    (a47 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a51 : -(h 3) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a46 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * a51 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3762 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : h 1 ≤ (2/15 : ℝ))
    (a50 : -(h 1) < (-3/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a23 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3761 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a31 : h 0 ≤ (8/51 : ℝ))
    (a49 : -(h 0) < (-3/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3760 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a42 : -(h 1) < (-4/31 : ℝ))
    (a46 : -(h 2) < (-3/25 : ℝ))
    (a48 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/3 : ℝ) * a25 + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a46 + (1/6 : ℝ) * a48 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3759 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a23 : h 1 ≤ (2/15 : ℝ))
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a31 : h 0 ≤ (8/51 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a39 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a42 : -(h 1) < (-4/31 : ℝ))
    (a46 : -(h 2) < (-3/25 : ℝ))
    (a47 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a52 : -(h 5) < (-3/29 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_3766 h delta _ctx _hno a47 f0
  by_cases p1 : h 0 ≤ (3/19 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/19 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_3767 h delta _ctx _hno a31 f1
  by_cases p2 : h 1 ≤ (3/22 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_3768 h delta _ctx _hno a23 f2
  by_cases p3 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f3 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_3769 h delta _ctx _hno a25 a35 a39 a42 a46 a52 f3
  by_cases p4 : h 4 ≤ (9/80 : ℝ)
  swap
  · have f4 : -(h 4) < (-9/80 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_3770 h delta _ctx _hno a35 a39 a42 a46 a52 f4
  by_cases p5 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_3771 h delta _ctx _hno a17 a25 a31 a35 a39 a42 a46 a47 f5
  apply _hno 202
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 4 ≤ (9/80 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_3758 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a39 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a42 : -(h 1) < (-4/31 : ℝ))
    (a46 : -(h 2) < (-3/25 : ℝ))
    (a51 : -(h 3) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a39 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a46 + (1/6 : ℝ) * a51 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3757 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a39 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a42 : -(h 1) < (-4/31 : ℝ))
    (a50 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/3 : ℝ) * a25 + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a39 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a50 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3756 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : h 1 ≤ (2/15 : ℝ))
    (a49 : -(h 1) < (-4/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a23 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_3755 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a31 : h 0 ≤ (8/51 : ℝ))
    (a48 : -(h 0) < (-5/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

end RealPinwheel.WeakSevenBandData
