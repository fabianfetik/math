import Pinwheel.WeakSevenBandData.CoverChunks.Upper005

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem upper_node_3827 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a58 : -(h 0) < (-9/62 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a58
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3826 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a35 : -(h 1) < (-1/8 : ℝ))
    (a47 : -(h 0) < (-6/43 : ℝ))
    (a51 : -(h 3) < (-4/33 : ℝ))
    (a56 : -(h 5) < (-3/28 : ℝ))
    (a57 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order2 + (2/13 : ℝ) * a32 + (2/13 : ℝ) * a35 + (2/13 : ℝ) * a47 + (4/13 : ℝ) * a51 + (2/13 : ℝ) * a56 + (1/13 : ℝ) * a57 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3825 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a35 : -(h 1) < (-1/8 : ℝ))
    (a47 : -(h 0) < (-6/43 : ℝ))
    (a50 : h 1 ≤ (6/47 : ℝ))
    (a51 : -(h 3) < (-4/33 : ℝ))
    (a56 : -(h 5) < (-3/28 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3826 h delta _ctx _hno a32 a35 a47 a51 a56 f0
  by_cases p1 : h 0 ≤ (9/62 : ℝ)
  swap
  · have f1 : -(h 0) < (-9/62 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3827 h delta _ctx _hno a30 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3828 h delta _ctx _hno a50 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3829 h delta _ctx _hno a13 a32 a35 a47 a51 a56 f3
  by_cases p4 : h 4 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 4) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3830 h delta _ctx _hno a13 a35 a47 a51 a56 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_3831 h delta _ctx _hno a13 a32 a35 a47 a51 f5
  apply _hno 143
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (9/62 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_3824 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a47 : -(h 0) < (-6/43 : ℝ))
    (a55 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/13 : ℝ) * _ctx.order2 + (3/13 : ℝ) * _ctx.min + (1/13 : ℝ) * a13 + (3/13 : ℝ) * a32 + (3/13 : ℝ) * a47 + (6/13 : ℝ) * a55 + (3/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3823 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a50 : h 1 ≤ (6/47 : ℝ))
    (a54 : -(h 1) < (-4/31 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a50 + (1 : ℝ) * a54
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3822 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a35 : -(h 1) < (-1/8 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    (a51 : -(h 3) < (-4/33 : ℝ))
    (a53 : -(h 0) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/17 : ℝ) * _ctx.order2 + (1/34 : ℝ) * a13 + (3/17 : ℝ) * a32 + (3/34 : ℝ) * a35 + (3/17 : ℝ) * a42 + (6/17 : ℝ) * a51 + (3/17 : ℝ) * a53 + (3/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3821 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a38 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a52 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a38 + (1 : ℝ) * a52
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3820 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a35 : -(h 1) < (-1/8 : ℝ))
    (a38 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    (a47 : -(h 0) < (-6/43 : ℝ))
    (a50 : h 1 ≤ (6/47 : ℝ))
    (a51 : -(h 3) < (-4/33 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3821 h delta _ctx _hno a38 f0
  by_cases p1 : h 0 ≤ (1/7 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3822 h delta _ctx _hno a13 a32 a35 a42 a51 f1
  by_cases p2 : h 1 ≤ (4/31 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/31 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3823 h delta _ctx _hno a50 f2
  by_cases p3 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3824 h delta _ctx _hno a13 a32 a47 f3
  by_cases p4 : h 5 ≤ (3/28 : ℝ)
  swap
  · have f4 : -(h 5) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3825 h delta _ctx _hno a13 a30 a32 a35 a47 a50 a51 f4
  apply _hno 149
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (1/7 : ℝ)) ∧ (h 1 ≤ (4/31 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 5 ≤ (3/28 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_3819 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a45 : -(h 3) < (-5/42 : ℝ))
    (a47 : -(h 0) < (-6/43 : ℝ))
    (a50 : -(h 1) < (-6/47 : ℝ))
    (a56 : -(h 5) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.order4 + (6/29 : ℝ) * _ctx.lower + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a45 + (4/29 : ℝ) * a47 + (6/29 : ℝ) * a50 + (12/29 : ℝ) * a56 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3818 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a47 : -(h 0) < (-6/43 : ℝ))
    (a50 : -(h 1) < (-6/47 : ℝ))
    (a55 : -(h 3) < (-3/25 : ℝ))
    (a66 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.lower + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a32 + (4/29 : ℝ) * a47 + (6/29 : ℝ) * a50 + (6/29 : ℝ) * a55 + (6/29 : ℝ) * a66 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3817 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a47 : -(h 0) < (-6/43 : ℝ))
    (a50 : -(h 1) < (-6/47 : ℝ))
    (a55 : -(h 3) < (-3/25 : ℝ))
    (a60 : -(h 5) < (-3/28 : ℝ))
    (a65 : -(h 4) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.lower + (1/29 : ℝ) * _ctx.fail1 + (4/29 : ℝ) * a47 + (6/29 : ℝ) * a50 + (6/29 : ℝ) * a55 + (6/29 : ℝ) * a60 + (6/29 : ℝ) * a65 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3816 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a54 : h 2 ≤ (4/33 : ℝ))
    (a64 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a54 + (1 : ℝ) * a64
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3815 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a58 : h 1 ≤ (4/31 : ℝ))
    (a63 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a58 + (1 : ℝ) * a63
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3814 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a62 : -(h 0) < (-9/62 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a62
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3813 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a47 : -(h 0) < (-6/43 : ℝ))
    (a50 : -(h 1) < (-6/47 : ℝ))
    (a55 : -(h 3) < (-3/25 : ℝ))
    (a60 : -(h 5) < (-3/28 : ℝ))
    (a61 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/32 : ℝ) * _ctx.fail1 + (3/16 : ℝ) * a32 + (1/8 : ℝ) * a47 + (3/16 : ℝ) * a50 + (3/16 : ℝ) * a55 + (3/16 : ℝ) * a60 + (3/32 : ℝ) * a61 + (3/16 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3812 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a47 : -(h 0) < (-6/43 : ℝ))
    (a50 : -(h 1) < (-6/47 : ℝ))
    (a54 : h 2 ≤ (4/33 : ℝ))
    (a55 : -(h 3) < (-3/25 : ℝ))
    (a58 : h 1 ≤ (4/31 : ℝ))
    (a60 : -(h 5) < (-3/28 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3813 h delta _ctx _hno a32 a47 a50 a55 a60 f0
  by_cases p1 : h 0 ≤ (9/62 : ℝ)
  swap
  · have f1 : -(h 0) < (-9/62 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3814 h delta _ctx _hno a30 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3815 h delta _ctx _hno a58 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3816 h delta _ctx _hno a54 f3
  by_cases p4 : h 4 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 4) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3817 h delta _ctx _hno a47 a50 a55 a60 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_3818 h delta _ctx _hno a32 a47 a50 a55 f5
  apply _hno 143
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (9/62 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_3811 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a54 : h 2 ≤ (4/33 : ℝ))
    (a59 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * _ctx.order2 + (1 : ℝ) * a54 + (1 : ℝ) * a59
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3810 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a47 : -(h 0) < (-6/43 : ℝ))
    (a55 : -(h 3) < (-3/25 : ℝ))
    (a58 : -(h 1) < (-4/31 : ℝ))
    (a64 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.lower + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a32 + (4/29 : ℝ) * a47 + (6/29 : ℝ) * a55 + (6/29 : ℝ) * a58 + (6/29 : ℝ) * a64 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3809 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a42 : -(h 5) < (-2/19 : ℝ))
    (a47 : -(h 0) < (-6/43 : ℝ))
    (a55 : -(h 3) < (-3/25 : ℝ))
    (a58 : -(h 1) < (-4/31 : ℝ))
    (a63 : -(h 4) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.lower + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a42 + (4/29 : ℝ) * a47 + (6/29 : ℝ) * a55 + (6/29 : ℝ) * a58 + (6/29 : ℝ) * a63 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3808 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a54 : h 2 ≤ (4/33 : ℝ))
    (a62 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a54 + (1 : ℝ) * a62
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3807 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    (a47 : -(h 0) < (-6/43 : ℝ))
    (a55 : -(h 3) < (-3/25 : ℝ))
    (a61 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.lower + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a32 + (6/29 : ℝ) * a42 + (4/29 : ℝ) * a47 + (6/29 : ℝ) * a55 + (6/29 : ℝ) * a61 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3806 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a60 : -(h 0) < (-9/62 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a60
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3805 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a47 : -(h 0) < (-6/43 : ℝ))
    (a55 : -(h 3) < (-3/25 : ℝ))
    (a58 : -(h 1) < (-4/31 : ℝ))
    (a59 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.min + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a32 + (4/29 : ℝ) * a47 + (6/29 : ℝ) * a55 + (6/29 : ℝ) * a58 + (6/29 : ℝ) * a59 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3804 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    (a47 : -(h 0) < (-6/43 : ℝ))
    (a54 : h 2 ≤ (4/33 : ℝ))
    (a55 : -(h 3) < (-3/25 : ℝ))
    (a58 : -(h 1) < (-4/31 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3805 h delta _ctx _hno a32 a47 a55 a58 f0
  by_cases p1 : h 0 ≤ (9/62 : ℝ)
  swap
  · have f1 : -(h 0) < (-9/62 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3806 h delta _ctx _hno a30 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3807 h delta _ctx _hno a32 a42 a47 a55 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3808 h delta _ctx _hno a54 f3
  by_cases p4 : h 4 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 4) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3809 h delta _ctx _hno a42 a47 a55 a58 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_3810 h delta _ctx _hno a32 a47 a55 a58 f5
  apply _hno 143
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (9/62 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_3803 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    (a50 : -(h 1) < (-6/47 : ℝ))
    (a55 : -(h 3) < (-3/25 : ℝ))
    (a57 : -(h 0) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order2 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a32 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a50 + (1/3 : ℝ) * a55 + (1/6 : ℝ) * a57 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3802 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a38 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a56 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a38 + (1 : ℝ) * a56
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3801 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a38 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    (a47 : -(h 0) < (-6/43 : ℝ))
    (a50 : -(h 1) < (-6/47 : ℝ))
    (a54 : h 2 ≤ (4/33 : ℝ))
    (a55 : -(h 3) < (-3/25 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3802 h delta _ctx _hno a38 f0
  by_cases p1 : h 0 ≤ (1/7 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3803 h delta _ctx _hno a32 a42 a50 a55 f1
  by_cases p2 : h 1 ≤ (4/31 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/31 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3804 h delta _ctx _hno a30 a32 a42 a47 a54 a55 f2
  by_cases p3 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3811 h delta _ctx _hno a54 f3
  by_cases p4 : h 5 ≤ (3/28 : ℝ)
  swap
  · have f4 : -(h 5) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3812 h delta _ctx _hno a30 a32 a47 a50 a54 a55 p2 f4
  apply _hno 149
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (1/7 : ℝ)) ∧ (h 1 ≤ (4/31 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 5 ≤ (3/28 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_3800 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a45 : -(h 3) < (-5/42 : ℝ))
    (a47 : -(h 0) < (-6/43 : ℝ))
    (a50 : -(h 1) < (-6/47 : ℝ))
    (a54 : -(h 2) < (-4/33 : ℝ))
    (a65 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a32 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * a50 + (1/6 : ℝ) * a54 + (1/6 : ℝ) * a65 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3799 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a45 : -(h 3) < (-5/42 : ℝ))
    (a47 : -(h 0) < (-6/43 : ℝ))
    (a50 : -(h 1) < (-6/47 : ℝ))
    (a54 : -(h 2) < (-4/33 : ℝ))
    (a59 : -(h 5) < (-3/28 : ℝ))
    (a64 : -(h 4) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * a50 + (1/6 : ℝ) * a54 + (1/6 : ℝ) * a59 + (1/6 : ℝ) * a64 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3798 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a45 : -(h 3) < (-5/42 : ℝ))
    (a47 : -(h 0) < (-6/43 : ℝ))
    (a50 : -(h 1) < (-6/47 : ℝ))
    (a59 : -(h 5) < (-3/28 : ℝ))
    (a63 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a32 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * a50 + (1/6 : ℝ) * a59 + (1/6 : ℝ) * a63 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3797 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a57 : h 1 ≤ (4/31 : ℝ))
    (a62 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a57 + (1 : ℝ) * a62
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3796 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a61 : -(h 0) < (-9/62 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a61
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3795 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a45 : -(h 3) < (-5/42 : ℝ))
    (a47 : -(h 0) < (-6/43 : ℝ))
    (a50 : -(h 1) < (-6/47 : ℝ))
    (a54 : -(h 2) < (-4/33 : ℝ))
    (a59 : -(h 5) < (-3/28 : ℝ))
    (a60 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * a32 + (2/13 : ℝ) * a45 + (2/13 : ℝ) * a47 + (2/13 : ℝ) * a50 + (2/13 : ℝ) * a54 + (2/13 : ℝ) * a59 + (1/13 : ℝ) * a60 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3794 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a45 : -(h 3) < (-5/42 : ℝ))
    (a47 : -(h 0) < (-6/43 : ℝ))
    (a50 : -(h 1) < (-6/47 : ℝ))
    (a54 : -(h 2) < (-4/33 : ℝ))
    (a57 : h 1 ≤ (4/31 : ℝ))
    (a59 : -(h 5) < (-3/28 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3795 h delta _ctx _hno a32 a45 a47 a50 a54 a59 f0
  by_cases p1 : h 0 ≤ (9/62 : ℝ)
  swap
  · have f1 : -(h 0) < (-9/62 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3796 h delta _ctx _hno a30 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3797 h delta _ctx _hno a57 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3798 h delta _ctx _hno a32 a45 a47 a50 a59 f3
  by_cases p4 : h 4 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 4) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3799 h delta _ctx _hno a45 a47 a50 a54 a59 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_3800 h delta _ctx _hno a32 a45 a47 a50 a54 f5
  apply _hno 143
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (9/62 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_3793 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a47 : -(h 0) < (-6/43 : ℝ))
    (a50 : -(h 1) < (-6/47 : ℝ))
    (a58 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order2 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a32 + (1/5 : ℝ) * a47 + (1/5 : ℝ) * a50 + (2/5 : ℝ) * a58 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3792 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a45 : -(h 3) < (-5/42 : ℝ))
    (a47 : -(h 0) < (-6/43 : ℝ))
    (a54 : -(h 2) < (-4/33 : ℝ))
    (a57 : -(h 1) < (-4/31 : ℝ))
    (a63 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a32 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * a54 + (1/6 : ℝ) * a57 + (1/6 : ℝ) * a63 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3791 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a42 : -(h 5) < (-2/19 : ℝ))
    (a45 : -(h 3) < (-5/42 : ℝ))
    (a47 : -(h 0) < (-6/43 : ℝ))
    (a54 : -(h 2) < (-4/33 : ℝ))
    (a57 : -(h 1) < (-4/31 : ℝ))
    (a62 : -(h 4) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * a54 + (1/6 : ℝ) * a57 + (1/6 : ℝ) * a62 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3790 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    (a45 : -(h 3) < (-5/42 : ℝ))
    (a47 : -(h 0) < (-6/43 : ℝ))
    (a57 : -(h 1) < (-4/31 : ℝ))
    (a61 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a32 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * a57 + (1/6 : ℝ) * a61 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3789 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    (a45 : -(h 3) < (-5/42 : ℝ))
    (a47 : -(h 0) < (-6/43 : ℝ))
    (a54 : -(h 2) < (-4/33 : ℝ))
    (a60 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a32 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * a54 + (1/6 : ℝ) * a60 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3788 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a59 : -(h 0) < (-9/62 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a59
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3787 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a45 : -(h 3) < (-5/42 : ℝ))
    (a47 : -(h 0) < (-6/43 : ℝ))
    (a54 : -(h 2) < (-4/33 : ℝ))
    (a57 : -(h 1) < (-4/31 : ℝ))
    (a58 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a32 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * a54 + (1/6 : ℝ) * a57 + (1/6 : ℝ) * a58 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3786 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    (a45 : -(h 3) < (-5/42 : ℝ))
    (a47 : -(h 0) < (-6/43 : ℝ))
    (a54 : -(h 2) < (-4/33 : ℝ))
    (a57 : -(h 1) < (-4/31 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3787 h delta _ctx _hno a32 a45 a47 a54 a57 f0
  by_cases p1 : h 0 ≤ (9/62 : ℝ)
  swap
  · have f1 : -(h 0) < (-9/62 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3788 h delta _ctx _hno a30 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3789 h delta _ctx _hno a32 a42 a45 a47 a54 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3790 h delta _ctx _hno a32 a42 a45 a47 a57 f3
  by_cases p4 : h 4 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 4) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3791 h delta _ctx _hno a42 a45 a47 a54 a57 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_3792 h delta _ctx _hno a32 a45 a47 a54 a57 f5
  apply _hno 143
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (9/62 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_3785 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    (a45 : -(h 3) < (-5/42 : ℝ))
    (a50 : -(h 1) < (-6/47 : ℝ))
    (a54 : -(h 2) < (-4/33 : ℝ))
    (a56 : -(h 0) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a32 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a50 + (1/6 : ℝ) * a54 + (1/6 : ℝ) * a56 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3784 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a38 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a55 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a38 + (1 : ℝ) * a55
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3783 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a38 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    (a45 : -(h 3) < (-5/42 : ℝ))
    (a47 : -(h 0) < (-6/43 : ℝ))
    (a50 : -(h 1) < (-6/47 : ℝ))
    (a54 : -(h 2) < (-4/33 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3784 h delta _ctx _hno a38 f0
  by_cases p1 : h 0 ≤ (1/7 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3785 h delta _ctx _hno a32 a42 a45 a50 a54 f1
  by_cases p2 : h 1 ≤ (4/31 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/31 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3786 h delta _ctx _hno a30 a32 a42 a45 a47 a54 f2
  by_cases p3 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3793 h delta _ctx _hno a32 a47 a50 f3
  by_cases p4 : h 5 ≤ (3/28 : ℝ)
  swap
  · have f4 : -(h 5) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3794 h delta _ctx _hno a30 a32 a45 a47 a50 a54 p2 f4
  apply _hno 149
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (1/7 : ℝ)) ∧ (h 1 ≤ (4/31 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 5 ≤ (3/28 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_3782 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a45 : -(h 3) < (-5/42 : ℝ))
    (a53 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/23 : ℝ) * _ctx.order0 + (6/23 : ℝ) * _ctx.min + (12/23 : ℝ) * _ctx.lower + (1/23 : ℝ) * _ctx.fail1 + (6/23 : ℝ) * a32 + (6/23 : ℝ) * a45 + (10/23 : ℝ) * a53 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3781 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a52 : -(h 0) < (-6/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a52
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3780 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a38 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a51 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a38 + (1 : ℝ) * a51
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3779 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a38 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    (a45 : -(h 3) < (-5/42 : ℝ))
    (a47 : -(h 0) < (-6/43 : ℝ))
    (a50 : -(h 1) < (-6/47 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3780 h delta _ctx _hno a38 f0
  by_cases p1 : h 0 ≤ (6/41 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/41 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3781 h delta _ctx _hno a30 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3782 h delta _ctx _hno a32 a45 f2
  by_cases p3 : h 2 ≤ (4/33 : ℝ)
  swap
  · have f3 : -(h 2) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3783 h delta _ctx _hno a30 a32 a38 a42 a45 a47 a50 f3
  by_cases p4 : h 3 ≤ (3/25 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3801 h delta _ctx _hno a30 a32 a38 a42 a47 a50 p3 f4
  by_cases p5 : h 5 ≤ (2/17 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_3819 h delta _ctx _hno a45 a47 a50 f5
  apply _hno 137
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (6/41 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (4/33 : ℝ)) ∧ (h 3 ≤ (3/25 : ℝ)) ∧ (h 5 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_3778 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a49 : -(h 0) < (-6/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3777 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a38 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a48 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a38 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3776 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a35 : -(h 1) < (-1/8 : ℝ))
    (a38 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    (a45 : -(h 3) < (-5/42 : ℝ))
    (a47 : -(h 0) < (-6/43 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3777 h delta _ctx _hno a38 f0
  by_cases p1 : h 0 ≤ (6/41 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/41 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3778 h delta _ctx _hno a30 f1
  by_cases p2 : h 1 ≤ (6/47 : ℝ)
  swap
  · have f2 : -(h 1) < (-6/47 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3779 h delta _ctx _hno a30 a32 a38 a42 a45 a47 f2
  by_cases p3 : h 3 ≤ (4/33 : ℝ)
  swap
  · have f3 : -(h 3) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3820 h delta _ctx _hno a13 a30 a32 a35 a38 a42 a47 p2 f3
  by_cases p4 : h 4 ≤ (3/25 : ℝ)
  swap
  · have f4 : -(h 4) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3832 h delta _ctx _hno a13 a35 a42 a47 f4
  by_cases p5 : h 5 ≤ (2/17 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_3833 h delta _ctx _hno a13 a35 a45 a47 f5
  apply _hno 145
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (6/41 : ℝ)) ∧ (h 1 ≤ (6/47 : ℝ)) ∧ (h 3 ≤ (4/33 : ℝ)) ∧ (h 4 ≤ (3/25 : ℝ)) ∧ (h 5 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_3775 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a38 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a46 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a38 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3774 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a31 : h 2 ≤ (1/8 : ℝ))
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a35 : -(h 1) < (-1/8 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a38 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    (a45 : -(h 3) < (-5/42 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3775 h delta _ctx _hno a38 f0
  by_cases p1 : h 0 ≤ (6/43 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/43 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3776 h delta _ctx _hno a13 a30 a32 a35 a38 a42 a45 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3834 h delta _ctx _hno a32 a37 a42 a45 f2
  by_cases p3 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3835 h delta _ctx _hno a13 a32 a35 a37 a42 f3
  by_cases p4 : h 5 ≤ (5/46 : ℝ)
  swap
  · have f4 : -(h 5) < (-5/46 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3836 h delta _ctx _hno a13 a31 a32 a35 a37 a38 a45 p1 p2 f4
  apply _hno 20
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (6/43 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 5 ≤ (5/46 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_3773 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a44 : -(h 0) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3772 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a38 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a38 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3771 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a31 : h 2 ≤ (1/8 : ℝ))
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a35 : -(h 1) < (-1/8 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a38 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3772 h delta _ctx _hno a38 f0
  by_cases p1 : h 0 ≤ (1/7 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3773 h delta _ctx _hno a30 f1
  by_cases p2 : h 3 ≤ (5/42 : ℝ)
  swap
  · have f2 : -(h 3) < (-5/42 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3774 h delta _ctx _hno a13 a30 a31 a32 a35 a37 a38 a42 f2
  by_cases p3 : h 4 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 4) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3921 h delta _ctx _hno a13 a30 a31 a35 a37 a38 a42 p2 f3
  apply _hno 21
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (1/7 : ℝ)) ∧ (h 3 ≤ (5/42 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_3770 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a41 : -(h 4) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/13 : ℝ) * _ctx.order2 + (6/13 : ℝ) * _ctx.order3 + (3/13 : ℝ) * _ctx.min + (1/13 : ℝ) * a13 + (3/13 : ℝ) * a37 + (9/13 : ℝ) * a41 + (3/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3769 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : h 2 ≤ (1/8 : ℝ))
    (a40 : -(h 2) < (-5/38 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3768 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a39 : -(h 0) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3767 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a35 : -(h 1) < (-1/8 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a42 : -(h 4) < (-2/17 : ℝ))
    (a48 : -(h 5) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/9 : ℝ) * _ctx.order3 + (1/27 : ℝ) * _ctx.fail1 + (1/27 : ℝ) * a13 + (1/9 : ℝ) * a35 + (4/27 : ℝ) * a37 + (4/9 : ℝ) * a42 + (2/9 : ℝ) * a48 + (2/9 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3766 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a41 : h 3 ≤ (5/42 : ℝ))
    (a47 : -(h 3) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a41 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3765 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a35 : -(h 1) < (-1/8 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a42 : -(h 4) < (-2/17 : ℝ))
    (a57 : -(h 5) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/9 : ℝ) * _ctx.order3 + (1/27 : ℝ) * _ctx.fail1 + (1/27 : ℝ) * a13 + (1/9 : ℝ) * a35 + (4/27 : ℝ) * a37 + (4/9 : ℝ) * a42 + (2/9 : ℝ) * a57 + (2/9 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3764 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a41 : h 3 ≤ (5/42 : ℝ))
    (a56 : -(h 4) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * _ctx.order3 + (1 : ℝ) * a41 + (1 : ℝ) * a56
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3763 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a41 : h 3 ≤ (5/42 : ℝ))
    (a55 : -(h 3) < (-4/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a41 + (1 : ℝ) * a55
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3762 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a38 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a42 : -(h 4) < (-2/17 : ℝ))
    (a51 : -(h 5) < (-5/46 : ℝ))
    (a54 : -(h 1) < (-6/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/16 : ℝ) * _ctx.order3 + (1/32 : ℝ) * _ctx.fail1 + (1/8 : ℝ) * a37 + (3/32 : ℝ) * a38 + (3/8 : ℝ) * a42 + (3/16 : ℝ) * a51 + (3/16 : ℝ) * a54 + (3/16 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3761 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a48 : h 0 ≤ (6/43 : ℝ))
    (a53 : -(h 0) < (-6/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a48 + (1 : ℝ) * a53
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3760 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a52 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a52
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3759 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a33 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a35 : -(h 1) < (-1/8 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a38 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a41 : h 3 ≤ (5/42 : ℝ))
    (a42 : -(h 4) < (-2/17 : ℝ))
    (a48 : h 0 ≤ (6/43 : ℝ))
    (a51 : -(h 5) < (-5/46 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3760 h delta _ctx _hno a33 f0
  by_cases p1 : h 0 ≤ (6/41 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/41 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3761 h delta _ctx _hno a48 f1
  by_cases p2 : h 1 ≤ (6/47 : ℝ)
  swap
  · have f2 : -(h 1) < (-6/47 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3762 h delta _ctx _hno a37 a38 a42 a51 f2
  by_cases p3 : h 3 ≤ (4/33 : ℝ)
  swap
  · have f3 : -(h 3) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3763 h delta _ctx _hno a41 f3
  by_cases p4 : h 4 ≤ (3/25 : ℝ)
  swap
  · have f4 : -(h 4) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3764 h delta _ctx _hno a41 f4
  by_cases p5 : h 5 ≤ (2/17 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_3765 h delta _ctx _hno a13 a35 a37 a42 f5
  apply _hno 145
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (6/41 : ℝ)) ∧ (h 1 ≤ (6/47 : ℝ)) ∧ (h 3 ≤ (4/33 : ℝ)) ∧ (h 4 ≤ (3/25 : ℝ)) ∧ (h 5 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_3758 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a41 : h 3 ≤ (5/42 : ℝ))
    (a50 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a41 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3757 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a38 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a42 : -(h 4) < (-2/17 : ℝ))
    (a49 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.order3 + (6/29 : ℝ) * _ctx.min + (1/29 : ℝ) * _ctx.fail1 + (4/29 : ℝ) * a37 + (6/29 : ℝ) * a38 + (12/29 : ℝ) * a42 + (6/29 : ℝ) * a49 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3756 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a35 : -(h 1) < (-1/8 : ℝ))
    (a42 : -(h 4) < (-2/17 : ℝ))
    (a48 : -(h 0) < (-6/43 : ℝ))
    (a54 : -(h 5) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/9 : ℝ) * _ctx.order3 + (1/27 : ℝ) * _ctx.fail1 + (1/27 : ℝ) * a13 + (1/9 : ℝ) * a35 + (4/9 : ℝ) * a42 + (4/27 : ℝ) * a48 + (2/9 : ℝ) * a54 + (2/9 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3755 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a41 : h 3 ≤ (5/42 : ℝ))
    (a53 : -(h 4) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * _ctx.order3 + (1 : ℝ) * a41 + (1 : ℝ) * a53
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3754 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a41 : h 3 ≤ (5/42 : ℝ))
    (a52 : -(h 3) < (-4/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a41 + (1 : ℝ) * a52
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3753 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a38 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a42 : -(h 4) < (-2/17 : ℝ))
    (a46 : -(h 2) < (-4/33 : ℝ))
    (a48 : -(h 0) < (-6/43 : ℝ))
    (a51 : -(h 1) < (-6/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a38 + (1/3 : ℝ) * a42 + (1/6 : ℝ) * a46 + (1/6 : ℝ) * a48 + (1/6 : ℝ) * a51 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3752 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a50 : -(h 0) < (-6/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3751 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a49 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3750 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a33 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a35 : -(h 1) < (-1/8 : ℝ))
    (a38 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a41 : h 3 ≤ (5/42 : ℝ))
    (a42 : -(h 4) < (-2/17 : ℝ))
    (a46 : -(h 2) < (-4/33 : ℝ))
    (a48 : -(h 0) < (-6/43 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3751 h delta _ctx _hno a33 f0
  by_cases p1 : h 0 ≤ (6/41 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/41 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3752 h delta _ctx _hno a30 f1
  by_cases p2 : h 1 ≤ (6/47 : ℝ)
  swap
  · have f2 : -(h 1) < (-6/47 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3753 h delta _ctx _hno a38 a42 a46 a48 f2
  by_cases p3 : h 3 ≤ (4/33 : ℝ)
  swap
  · have f3 : -(h 3) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3754 h delta _ctx _hno a41 f3
  by_cases p4 : h 4 ≤ (3/25 : ℝ)
  swap
  · have f4 : -(h 4) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3755 h delta _ctx _hno a41 f4
  by_cases p5 : h 5 ≤ (2/17 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_3756 h delta _ctx _hno a13 a35 a42 a48 f5
  apply _hno 145
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (6/41 : ℝ)) ∧ (h 1 ≤ (6/47 : ℝ)) ∧ (h 3 ≤ (4/33 : ℝ)) ∧ (h 4 ≤ (3/25 : ℝ)) ∧ (h 5 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_3749 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a47 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3748 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a33 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a35 : -(h 1) < (-1/8 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a38 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a41 : h 3 ≤ (5/42 : ℝ))
    (a42 : -(h 4) < (-2/17 : ℝ))
    (a46 : -(h 2) < (-4/33 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3749 h delta _ctx _hno a33 f0
  by_cases p1 : h 0 ≤ (6/43 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/43 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3750 h delta _ctx _hno a13 a30 a33 a35 a38 a41 a42 a46 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3757 h delta _ctx _hno a37 a38 a42 f2
  by_cases p3 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3758 h delta _ctx _hno a41 f3
  by_cases p4 : h 5 ≤ (5/46 : ℝ)
  swap
  · have f4 : -(h 5) < (-5/46 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3759 h delta _ctx _hno a13 a33 a35 a37 a38 a41 a42 p1 f4
  apply _hno 20
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (6/43 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 5 ≤ (5/46 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

end RealPinwheel.WeakSevenBandData
