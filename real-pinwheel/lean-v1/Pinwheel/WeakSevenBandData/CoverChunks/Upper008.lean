import Pinwheel.WeakSevenBandData.CoverChunks.Upper007

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem upper_node_3667 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a36 : -(h 1) < (-1/8 : ℝ))
    (a43 : -(h 3) < (-3/25 : ℝ))
    (a45 : -(h 0) < (-6/43 : ℝ))
    (a51 : -(h 5) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/16 : ℝ) * _ctx.order4 + (1/32 : ℝ) * _ctx.fail1 + (3/32 : ℝ) * a33 + (3/16 : ℝ) * a36 + (3/16 : ℝ) * a43 + (1/8 : ℝ) * a45 + (3/8 : ℝ) * a51 + (3/16 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3666 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a36 : -(h 1) < (-1/8 : ℝ))
    (a43 : -(h 3) < (-3/25 : ℝ))
    (a45 : -(h 0) < (-6/43 : ℝ))
    (a50 : -(h 4) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.min + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a33 + (6/29 : ℝ) * a36 + (6/29 : ℝ) * a43 + (4/29 : ℝ) * a45 + (6/29 : ℝ) * a50 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3665 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a33 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a36 : -(h 1) < (-1/8 : ℝ))
    (a45 : -(h 0) < (-6/43 : ℝ))
    (a49 : -(h 3) < (-4/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order2 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a32 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a36 + (1/6 : ℝ) * a45 + (1/3 : ℝ) * a49 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3664 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a33 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a43 : -(h 3) < (-3/25 : ℝ))
    (a45 : -(h 0) < (-6/43 : ℝ))
    (a48 : -(h 1) < (-6/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.min + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a32 + (6/29 : ℝ) * a33 + (6/29 : ℝ) * a43 + (4/29 : ℝ) * a45 + (6/29 : ℝ) * a48 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3663 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a47 : -(h 0) < (-6/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3662 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a44 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a46 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a44 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3661 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a33 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a36 : -(h 1) < (-1/8 : ℝ))
    (a43 : -(h 3) < (-3/25 : ℝ))
    (a44 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a45 : -(h 0) < (-6/43 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3662 h delta _ctx _hno a44 f0
  by_cases p1 : h 0 ≤ (6/41 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/41 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3663 h delta _ctx _hno a30 f1
  by_cases p2 : h 1 ≤ (6/47 : ℝ)
  swap
  · have f2 : -(h 1) < (-6/47 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3664 h delta _ctx _hno a32 a33 a43 a45 f2
  by_cases p3 : h 3 ≤ (4/33 : ℝ)
  swap
  · have f3 : -(h 3) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3665 h delta _ctx _hno a32 a33 a36 a45 f3
  by_cases p4 : h 4 ≤ (3/25 : ℝ)
  swap
  · have f4 : -(h 4) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3666 h delta _ctx _hno a33 a36 a43 a45 f4
  by_cases p5 : h 5 ≤ (2/17 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_3667 h delta _ctx _hno a33 a36 a43 a45 f5
  apply _hno 145
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (6/41 : ℝ)) ∧ (h 1 ≤ (6/47 : ℝ)) ∧ (h 3 ≤ (4/33 : ℝ)) ∧ (h 4 ≤ (3/25 : ℝ)) ∧ (h 5 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_3660 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a36 : -(h 1) < (-1/8 : ℝ))
    (a42 : h 2 ≤ (4/33 : ℝ))
    (a43 : -(h 3) < (-3/25 : ℝ))
    (a44 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a50 : -(h 5) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order4 + (1/10 : ℝ) * _ctx.fail1 + (1/5 : ℝ) * a36 + (2/5 : ℝ) * a42 + (1/5 : ℝ) * a43 + (1/10 : ℝ) * a44 + (2/5 : ℝ) * a50 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3659 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a36 : -(h 1) < (-1/8 : ℝ))
    (a38 : -(h 0) < (-11/80 : ℝ))
    (a43 : -(h 3) < (-3/25 : ℝ))
    (a44 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a49 : -(h 4) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.min + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a36 + (4/29 : ℝ) * a38 + (6/29 : ℝ) * a43 + (6/29 : ℝ) * a44 + (6/29 : ℝ) * a49 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3658 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a36 : -(h 1) < (-1/8 : ℝ))
    (a38 : -(h 0) < (-11/80 : ℝ))
    (a44 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a48 : -(h 3) < (-4/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order2 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a32 + (1/6 : ℝ) * a36 + (1/6 : ℝ) * a38 + (1/6 : ℝ) * a44 + (1/3 : ℝ) * a48 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3657 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a38 : -(h 0) < (-11/80 : ℝ))
    (a43 : -(h 3) < (-3/25 : ℝ))
    (a44 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a47 : -(h 1) < (-6/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.min + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a32 + (4/29 : ℝ) * a38 + (6/29 : ℝ) * a43 + (6/29 : ℝ) * a44 + (6/29 : ℝ) * a47 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3656 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a46 : -(h 0) < (-6/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3655 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a38 : -(h 0) < (-11/80 : ℝ))
    (a45 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * a14 + (1/5 : ℝ) * a38 + (4/5 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3654 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a36 : -(h 1) < (-1/8 : ℝ))
    (a38 : -(h 0) < (-11/80 : ℝ))
    (a42 : h 2 ≤ (4/33 : ℝ))
    (a43 : -(h 3) < (-3/25 : ℝ))
    (a44 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3655 h delta _ctx _hno a14 a38 f0
  by_cases p1 : h 0 ≤ (6/41 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/41 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3656 h delta _ctx _hno a30 f1
  by_cases p2 : h 1 ≤ (6/47 : ℝ)
  swap
  · have f2 : -(h 1) < (-6/47 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3657 h delta _ctx _hno a32 a38 a43 a44 f2
  by_cases p3 : h 3 ≤ (4/33 : ℝ)
  swap
  · have f3 : -(h 3) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3658 h delta _ctx _hno a32 a36 a38 a44 f3
  by_cases p4 : h 4 ≤ (3/25 : ℝ)
  swap
  · have f4 : -(h 4) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3659 h delta _ctx _hno a36 a38 a43 a44 f4
  by_cases p5 : h 5 ≤ (2/17 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_3660 h delta _ctx _hno a36 a42 a43 a44 f5
  apply _hno 145
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (6/41 : ℝ)) ∧ (h 1 ≤ (6/47 : ℝ)) ∧ (h 3 ≤ (4/33 : ℝ)) ∧ (h 4 ≤ (3/25 : ℝ)) ∧ (h 5 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_3653 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a33 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a36 : -(h 1) < (-1/8 : ℝ))
    (a38 : -(h 0) < (-11/80 : ℝ))
    (a42 : h 2 ≤ (4/33 : ℝ))
    (a43 : -(h 3) < (-3/25 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3654 h delta _ctx _hno a14 a30 a32 a36 a38 a42 a43 f0
  by_cases p1 : h 0 ≤ (6/43 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/43 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3661 h delta _ctx _hno a30 a32 a33 a36 a43 p0 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3668 h delta _ctx _hno a32 a33 a43 f2
  by_cases p3 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3669 h delta _ctx _hno a42 f3
  by_cases p4 : h 5 ≤ (5/46 : ℝ)
  swap
  · have f4 : -(h 5) < (-5/46 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3670 h delta _ctx _hno a32 a33 a36 a38 a43 p0 p1 f4
  apply _hno 20
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (6/43 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 5 ≤ (5/46 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_3652 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a36 : -(h 1) < (-1/8 : ℝ))
    (a38 : -(h 0) < (-11/80 : ℝ))
    (a42 : -(h 2) < (-4/33 : ℝ))
    (a46 : -(h 4) < (-2/17 : ℝ))
    (a51 : -(h 5) < (-5/46 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order3 + (1/13 : ℝ) * a33 + (2/13 : ℝ) * a36 + (2/13 : ℝ) * a38 + (2/13 : ℝ) * a42 + (4/13 : ℝ) * a46 + (2/13 : ℝ) * a51 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3651 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a45 : h 3 ≤ (5/42 : ℝ))
    (a50 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a45 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3650 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a38 : -(h 0) < (-11/80 : ℝ))
    (a46 : -(h 4) < (-2/17 : ℝ))
    (a49 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.order3 + (6/29 : ℝ) * _ctx.min + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a33 + (4/29 : ℝ) * a38 + (12/29 : ℝ) * a46 + (6/29 : ℝ) * a49 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3649 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a36 : -(h 1) < (-1/8 : ℝ))
    (a42 : -(h 2) < (-4/33 : ℝ))
    (a46 : -(h 4) < (-2/17 : ℝ))
    (a48 : -(h 0) < (-6/43 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a36 + (1/6 : ℝ) * a42 + (1/3 : ℝ) * a46 + (1/6 : ℝ) * a48 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3648 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a43 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a47 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a43 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3647 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a36 : -(h 1) < (-1/8 : ℝ))
    (a38 : -(h 0) < (-11/80 : ℝ))
    (a42 : -(h 2) < (-4/33 : ℝ))
    (a43 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a45 : h 3 ≤ (5/42 : ℝ))
    (a46 : -(h 4) < (-2/17 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3648 h delta _ctx _hno a43 f0
  by_cases p1 : h 0 ≤ (6/43 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/43 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3649 h delta _ctx _hno a33 a36 a42 a46 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3650 h delta _ctx _hno a33 a38 a46 f2
  by_cases p3 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3651 h delta _ctx _hno a45 f3
  by_cases p4 : h 5 ≤ (5/46 : ℝ)
  swap
  · have f4 : -(h 5) < (-5/46 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3652 h delta _ctx _hno a33 a36 a38 a42 a46 f4
  apply _hno 20
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (6/43 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 5 ≤ (5/46 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_3646 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a36 : -(h 1) < (-1/8 : ℝ))
    (a38 : -(h 0) < (-11/80 : ℝ))
    (a45 : -(h 3) < (-5/42 : ℝ))
    (a56 : -(h 5) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/16 : ℝ) * _ctx.order4 + (1/32 : ℝ) * _ctx.fail1 + (3/32 : ℝ) * a33 + (3/16 : ℝ) * a36 + (1/8 : ℝ) * a38 + (3/16 : ℝ) * a45 + (3/8 : ℝ) * a56 + (3/16 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3645 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a36 : -(h 1) < (-1/8 : ℝ))
    (a38 : -(h 0) < (-11/80 : ℝ))
    (a50 : -(h 5) < (-5/46 : ℝ))
    (a55 : -(h 4) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/16 : ℝ) * _ctx.order3 + (1/32 : ℝ) * _ctx.fail1 + (3/32 : ℝ) * a33 + (3/16 : ℝ) * a36 + (1/8 : ℝ) * a38 + (3/16 : ℝ) * a50 + (3/8 : ℝ) * a55 + (3/16 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3644 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a33 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a36 : -(h 1) < (-1/8 : ℝ))
    (a38 : -(h 0) < (-11/80 : ℝ))
    (a42 : -(h 2) < (-4/33 : ℝ))
    (a50 : -(h 5) < (-5/46 : ℝ))
    (a54 : -(h 3) < (-4/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * a32 + (1/13 : ℝ) * a33 + (2/13 : ℝ) * a36 + (2/13 : ℝ) * a38 + (2/13 : ℝ) * a42 + (2/13 : ℝ) * a50 + (2/13 : ℝ) * a54 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3643 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a33 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a38 : -(h 0) < (-11/80 : ℝ))
    (a42 : -(h 2) < (-4/33 : ℝ))
    (a45 : -(h 3) < (-5/42 : ℝ))
    (a50 : -(h 5) < (-5/46 : ℝ))
    (a53 : -(h 1) < (-6/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * a32 + (1/13 : ℝ) * a33 + (2/13 : ℝ) * a38 + (2/13 : ℝ) * a42 + (2/13 : ℝ) * a45 + (2/13 : ℝ) * a50 + (2/13 : ℝ) * a53 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3642 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a47 : h 0 ≤ (6/43 : ℝ))
    (a52 : -(h 0) < (-6/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a47 + (1 : ℝ) * a52
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3641 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a43 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a51 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a43 + (1 : ℝ) * a51
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3640 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a33 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a36 : -(h 1) < (-1/8 : ℝ))
    (a38 : -(h 0) < (-11/80 : ℝ))
    (a42 : -(h 2) < (-4/33 : ℝ))
    (a43 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a45 : -(h 3) < (-5/42 : ℝ))
    (a47 : h 0 ≤ (6/43 : ℝ))
    (a50 : -(h 5) < (-5/46 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3641 h delta _ctx _hno a43 f0
  by_cases p1 : h 0 ≤ (6/41 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/41 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3642 h delta _ctx _hno a47 f1
  by_cases p2 : h 1 ≤ (6/47 : ℝ)
  swap
  · have f2 : -(h 1) < (-6/47 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3643 h delta _ctx _hno a32 a33 a38 a42 a45 a50 f2
  by_cases p3 : h 3 ≤ (4/33 : ℝ)
  swap
  · have f3 : -(h 3) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3644 h delta _ctx _hno a32 a33 a36 a38 a42 a50 f3
  by_cases p4 : h 4 ≤ (3/25 : ℝ)
  swap
  · have f4 : -(h 4) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3645 h delta _ctx _hno a33 a36 a38 a50 f4
  by_cases p5 : h 5 ≤ (2/17 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_3646 h delta _ctx _hno a33 a36 a38 a45 f5
  apply _hno 145
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (6/41 : ℝ)) ∧ (h 1 ≤ (6/47 : ℝ)) ∧ (h 3 ≤ (4/33 : ℝ)) ∧ (h 4 ≤ (3/25 : ℝ)) ∧ (h 5 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_3639 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a36 : -(h 1) < (-1/8 : ℝ))
    (a49 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/17 : ℝ) * _ctx.order2 + (4/17 : ℝ) * _ctx.min + (1/17 : ℝ) * _ctx.fail2 + (4/17 : ℝ) * a33 + (4/17 : ℝ) * a36 + (8/17 : ℝ) * a49 + (4/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3638 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a33 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a38 : -(h 0) < (-11/80 : ℝ))
    (a45 : -(h 3) < (-5/42 : ℝ))
    (a48 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.min + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a32 + (6/29 : ℝ) * a33 + (4/29 : ℝ) * a38 + (6/29 : ℝ) * a45 + (6/29 : ℝ) * a48 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3637 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a36 : -(h 1) < (-1/8 : ℝ))
    (a45 : -(h 3) < (-5/42 : ℝ))
    (a47 : -(h 0) < (-6/43 : ℝ))
    (a53 : -(h 5) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/16 : ℝ) * _ctx.order4 + (1/32 : ℝ) * _ctx.fail1 + (3/32 : ℝ) * a33 + (3/16 : ℝ) * a36 + (3/16 : ℝ) * a45 + (1/8 : ℝ) * a47 + (3/8 : ℝ) * a53 + (3/16 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3636 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a36 : -(h 1) < (-1/8 : ℝ))
    (a42 : -(h 2) < (-4/33 : ℝ))
    (a47 : -(h 0) < (-6/43 : ℝ))
    (a52 : -(h 4) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a36 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a47 + (1/3 : ℝ) * a52 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3635 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a33 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a36 : -(h 1) < (-1/8 : ℝ))
    (a42 : -(h 2) < (-4/33 : ℝ))
    (a47 : -(h 0) < (-6/43 : ℝ))
    (a51 : -(h 3) < (-4/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a32 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a36 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * a51 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3634 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a33 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a42 : -(h 2) < (-4/33 : ℝ))
    (a45 : -(h 3) < (-5/42 : ℝ))
    (a47 : -(h 0) < (-6/43 : ℝ))
    (a50 : -(h 1) < (-6/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a32 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * a50 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3633 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a49 : -(h 0) < (-6/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3632 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a43 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a48 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a43 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3631 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a33 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a36 : -(h 1) < (-1/8 : ℝ))
    (a42 : -(h 2) < (-4/33 : ℝ))
    (a43 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a45 : -(h 3) < (-5/42 : ℝ))
    (a47 : -(h 0) < (-6/43 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3632 h delta _ctx _hno a43 f0
  by_cases p1 : h 0 ≤ (6/41 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/41 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3633 h delta _ctx _hno a30 f1
  by_cases p2 : h 1 ≤ (6/47 : ℝ)
  swap
  · have f2 : -(h 1) < (-6/47 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3634 h delta _ctx _hno a32 a33 a42 a45 a47 f2
  by_cases p3 : h 3 ≤ (4/33 : ℝ)
  swap
  · have f3 : -(h 3) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3635 h delta _ctx _hno a32 a33 a36 a42 a47 f3
  by_cases p4 : h 4 ≤ (3/25 : ℝ)
  swap
  · have f4 : -(h 4) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3636 h delta _ctx _hno a33 a36 a42 a47 f4
  by_cases p5 : h 5 ≤ (2/17 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_3637 h delta _ctx _hno a33 a36 a45 a47 f5
  apply _hno 145
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (6/41 : ℝ)) ∧ (h 1 ≤ (6/47 : ℝ)) ∧ (h 3 ≤ (4/33 : ℝ)) ∧ (h 4 ≤ (3/25 : ℝ)) ∧ (h 5 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_3630 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a43 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a46 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a43 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3629 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a33 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a36 : -(h 1) < (-1/8 : ℝ))
    (a38 : -(h 0) < (-11/80 : ℝ))
    (a42 : -(h 2) < (-4/33 : ℝ))
    (a43 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a45 : -(h 3) < (-5/42 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3630 h delta _ctx _hno a43 f0
  by_cases p1 : h 0 ≤ (6/43 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/43 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3631 h delta _ctx _hno a30 a32 a33 a36 a42 a43 a45 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3638 h delta _ctx _hno a32 a33 a38 a45 f2
  by_cases p3 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3639 h delta _ctx _hno a33 a36 f3
  by_cases p4 : h 5 ≤ (5/46 : ℝ)
  swap
  · have f4 : -(h 5) < (-5/46 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3640 h delta _ctx _hno a32 a33 a36 a38 a42 a43 a45 p1 f4
  apply _hno 20
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (6/43 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 5 ≤ (5/46 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_3628 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a44 : -(h 0) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3627 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a36 : -(h 1) < (-1/8 : ℝ))
    (a38 : -(h 0) < (-11/80 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a47 : -(h 3) < (-2/17 : ℝ))
    (a53 : -(h 5) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/16 : ℝ) * _ctx.order4 + (1/32 : ℝ) * _ctx.fail1 + (3/16 : ℝ) * a36 + (1/8 : ℝ) * a38 + (3/32 : ℝ) * a43 + (3/16 : ℝ) * a47 + (3/8 : ℝ) * a53 + (3/16 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3626 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a36 : -(h 1) < (-1/8 : ℝ))
    (a38 : -(h 0) < (-11/80 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a52 : -(h 4) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.order3 + (6/29 : ℝ) * _ctx.min + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a36 + (4/29 : ℝ) * a38 + (6/29 : ℝ) * a43 + (12/29 : ℝ) * a52 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3625 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a36 : -(h 1) < (-1/8 : ℝ))
    (a38 : -(h 0) < (-11/80 : ℝ))
    (a42 : -(h 2) < (-4/33 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a51 : -(h 3) < (-4/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a32 + (1/6 : ℝ) * a36 + (1/6 : ℝ) * a38 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a43 + (1/6 : ℝ) * a51 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3624 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a38 : -(h 0) < (-11/80 : ℝ))
    (a42 : -(h 2) < (-4/33 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a47 : -(h 3) < (-2/17 : ℝ))
    (a50 : -(h 1) < (-6/47 : ℝ))
    (a56 : -(h 5) < (-7/64 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * a32 + (2/13 : ℝ) * a38 + (2/13 : ℝ) * a42 + (1/13 : ℝ) * a43 + (2/13 : ℝ) * a47 + (2/13 : ℝ) * a50 + (2/13 : ℝ) * a56 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3623 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a38 : -(h 0) < (-11/80 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a50 : -(h 1) < (-6/47 : ℝ))
    (a55 : -(h 4) < (-4/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.order3 + (6/29 : ℝ) * _ctx.min + (1/29 : ℝ) * _ctx.fail1 + (4/29 : ℝ) * a38 + (6/29 : ℝ) * a43 + (6/29 : ℝ) * a50 + (12/29 : ℝ) * a55 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3622 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a38 : -(h 0) < (-11/80 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a50 : -(h 1) < (-6/47 : ℝ))
    (a54 : -(h 3) < (-5/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order2 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a32 + (1/6 : ℝ) * a38 + (1/6 : ℝ) * a43 + (1/6 : ℝ) * a50 + (1/3 : ℝ) * a54 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3621 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a38 : -(h 0) < (-11/80 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a47 : -(h 3) < (-2/17 : ℝ))
    (a50 : -(h 1) < (-6/47 : ℝ))
    (a53 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a32 + (1/6 : ℝ) * a38 + (1/6 : ℝ) * a43 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * a50 + (1/6 : ℝ) * a53 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3620 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a47 : -(h 3) < (-2/17 : ℝ))
    (a50 : -(h 1) < (-6/47 : ℝ))
    (a52 : -(h 0) < (-4/29 : ℝ))
    (a59 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/32 : ℝ) * _ctx.fail1 + (3/16 : ℝ) * a32 + (3/32 : ℝ) * a43 + (3/16 : ℝ) * a47 + (3/16 : ℝ) * a50 + (1/8 : ℝ) * a52 + (3/16 : ℝ) * a59 + (3/16 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3619 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a43 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a47 : -(h 3) < (-2/17 : ℝ))
    (a50 : -(h 1) < (-6/47 : ℝ))
    (a52 : -(h 0) < (-4/29 : ℝ))
    (a58 : -(h 4) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.min + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a43 + (6/29 : ℝ) * a47 + (6/29 : ℝ) * a50 + (4/29 : ℝ) * a52 + (6/29 : ℝ) * a58 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3618 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a42 : -(h 2) < (-4/33 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a50 : -(h 1) < (-6/47 : ℝ))
    (a52 : -(h 0) < (-4/29 : ℝ))
    (a57 : -(h 3) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a32 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a43 + (1/6 : ℝ) * a50 + (1/6 : ℝ) * a52 + (1/6 : ℝ) * a57 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3617 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a47 : -(h 3) < (-2/17 : ℝ))
    (a50 : -(h 1) < (-6/47 : ℝ))
    (a52 : -(h 0) < (-4/29 : ℝ))
    (a56 : -(h 2) < (-7/57 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a32 + (1/6 : ℝ) * a43 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * a50 + (1/6 : ℝ) * a52 + (1/6 : ℝ) * a56 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3616 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a42 : -(h 2) < (-4/33 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a47 : -(h 3) < (-2/17 : ℝ))
    (a52 : -(h 0) < (-4/29 : ℝ))
    (a55 : -(h 1) < (-5/39 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a32 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a43 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * a52 + (1/6 : ℝ) * a55 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3615 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a42 : -(h 2) < (-4/33 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a47 : -(h 3) < (-2/17 : ℝ))
    (a50 : -(h 1) < (-6/47 : ℝ))
    (a54 : -(h 0) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a32 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a43 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * a50 + (1/6 : ℝ) * a54 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3614 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a52 : -(h 0) < (-4/29 : ℝ))
    (a53 : ((-2 : ℝ) * (delta)) < (-12/55 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * a14 + (1/5 : ℝ) * a52 + (4/5 : ℝ) * a53
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3613 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a42 : -(h 2) < (-4/33 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a47 : -(h 3) < (-2/17 : ℝ))
    (a50 : -(h 1) < (-6/47 : ℝ))
    (a52 : -(h 0) < (-4/29 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (12/55 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-12/55 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3614 h delta _ctx _hno a14 a52 f0
  by_cases p1 : h 0 ≤ (1/7 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3615 h delta _ctx _hno a32 a42 a43 a47 a50 f1
  by_cases p2 : h 1 ≤ (5/39 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/39 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3616 h delta _ctx _hno a32 a42 a43 a47 a52 f2
  by_cases p3 : h 2 ≤ (7/57 : ℝ)
  swap
  · have f3 : -(h 2) < (-7/57 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3617 h delta _ctx _hno a32 a43 a47 a50 a52 f3
  by_cases p4 : h 3 ≤ (3/25 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3618 h delta _ctx _hno a32 a42 a43 a50 a52 f4
  by_cases p5 : h 4 ≤ (2/17 : ℝ)
  swap
  · have f5 : -(h 4) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_3619 h delta _ctx _hno a43 a47 a50 a52 f5
  by_cases p6 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f6 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact upper_node_3620 h delta _ctx _hno a32 a43 a47 a50 a52 f6
  apply _hno 100
  change (((2 : ℝ) * (delta)) ≤ (12/55 : ℝ)) ∧ (h 0 ≤ (1/7 : ℝ)) ∧ (h 1 ≤ (5/39 : ℝ)) ∧ (h 2 ≤ (7/57 : ℝ)) ∧ (h 3 ≤ (3/25 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem upper_node_3612 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a38 : -(h 0) < (-11/80 : ℝ))
    (a51 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * a14 + (1/5 : ℝ) * a38 + (4/5 : ℝ) * a51
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3611 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a38 : -(h 0) < (-11/80 : ℝ))
    (a42 : -(h 2) < (-4/33 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a47 : -(h 3) < (-2/17 : ℝ))
    (a50 : -(h 1) < (-6/47 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3612 h delta _ctx _hno a14 a38 f0
  by_cases p1 : h 0 ≤ (4/29 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/29 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3613 h delta _ctx _hno a14 a32 a42 a43 a47 a50 f1
  by_cases p2 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3621 h delta _ctx _hno a32 a38 a43 a47 a50 f2
  by_cases p3 : h 3 ≤ (5/41 : ℝ)
  swap
  · have f3 : -(h 3) < (-5/41 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3622 h delta _ctx _hno a32 a38 a43 a50 f3
  by_cases p4 : h 4 ≤ (4/33 : ℝ)
  swap
  · have f4 : -(h 4) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3623 h delta _ctx _hno a38 a43 a50 f4
  by_cases p5 : h 5 ≤ (7/64 : ℝ)
  swap
  · have f5 : -(h 5) < (-7/64 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_3624 h delta _ctx _hno a32 a38 a42 a43 a47 a50 f5
  apply _hno 98
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (4/29 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (5/41 : ℝ)) ∧ (h 4 ≤ (4/33 : ℝ)) ∧ (h 5 ≤ (7/64 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_3610 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a49 : -(h 0) < (-6/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3609 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a38 : -(h 0) < (-11/80 : ℝ))
    (a48 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * a14 + (1/5 : ℝ) * a38 + (4/5 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3608 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a36 : -(h 1) < (-1/8 : ℝ))
    (a38 : -(h 0) < (-11/80 : ℝ))
    (a42 : -(h 2) < (-4/33 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a47 : -(h 3) < (-2/17 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3609 h delta _ctx _hno a14 a38 f0
  by_cases p1 : h 0 ≤ (6/41 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/41 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3610 h delta _ctx _hno a30 f1
  by_cases p2 : h 1 ≤ (6/47 : ℝ)
  swap
  · have f2 : -(h 1) < (-6/47 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3611 h delta _ctx _hno a14 a32 a38 a42 a43 a47 f2
  by_cases p3 : h 3 ≤ (4/33 : ℝ)
  swap
  · have f3 : -(h 3) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3625 h delta _ctx _hno a32 a36 a38 a42 a43 f3
  by_cases p4 : h 4 ≤ (3/25 : ℝ)
  swap
  · have f4 : -(h 4) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3626 h delta _ctx _hno a36 a38 a43 f4
  by_cases p5 : h 5 ≤ (2/17 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_3627 h delta _ctx _hno a36 a38 a43 a47 f5
  apply _hno 145
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (6/41 : ℝ)) ∧ (h 1 ≤ (6/47 : ℝ)) ∧ (h 3 ≤ (4/33 : ℝ)) ∧ (h 4 ≤ (3/25 : ℝ)) ∧ (h 5 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_3607 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a38 : -(h 0) < (-11/80 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a46 : -(h 1) < (-3/23 : ℝ))
    (a51 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/16 : ℝ) * _ctx.order3 + (1/32 : ℝ) * _ctx.fail1 + (3/8 : ℝ) * a32 + (1/8 : ℝ) * a38 + (3/32 : ℝ) * a43 + (3/16 : ℝ) * a46 + (3/16 : ℝ) * a51 + (3/16 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3606 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a38 : -(h 0) < (-11/80 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a46 : -(h 1) < (-3/23 : ℝ))
    (a50 : -(h 3) < (-3/26 : ℝ))
    (a57 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/32 : ℝ) * _ctx.fail1 + (3/16 : ℝ) * a32 + (1/8 : ℝ) * a38 + (3/32 : ℝ) * a43 + (3/16 : ℝ) * a46 + (3/16 : ℝ) * a50 + (3/16 : ℝ) * a57 + (3/16 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3605 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a38 : -(h 0) < (-11/80 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a46 : -(h 1) < (-3/23 : ℝ))
    (a56 : -(h 4) < (-5/43 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.order3 + (6/29 : ℝ) * _ctx.min + (1/29 : ℝ) * _ctx.fail1 + (4/29 : ℝ) * a38 + (6/29 : ℝ) * a43 + (6/29 : ℝ) * a46 + (12/29 : ℝ) * a56 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3604 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a38 : -(h 0) < (-11/80 : ℝ))
    (a42 : -(h 2) < (-4/33 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a46 : -(h 1) < (-3/23 : ℝ))
    (a55 : -(h 3) < (-7/60 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a32 + (1/6 : ℝ) * a38 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a43 + (1/6 : ℝ) * a46 + (1/6 : ℝ) * a55 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3603 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : h 2 ≤ (1/8 : ℝ))
    (a54 : -(h 2) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a54
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3602 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a38 : -(h 0) < (-11/80 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a50 : -(h 3) < (-3/26 : ℝ))
    (a53 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.min + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a32 + (4/29 : ℝ) * a38 + (6/29 : ℝ) * a43 + (6/29 : ℝ) * a50 + (6/29 : ℝ) * a53 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3601 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a52 : -(h 0) < (-4/27 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a52
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3600 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a38 : -(h 0) < (-11/80 : ℝ))
    (a51 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * a14 + (1/5 : ℝ) * a38 + (4/5 : ℝ) * a51
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3599 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a31 : h 2 ≤ (1/8 : ℝ))
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a38 : -(h 0) < (-11/80 : ℝ))
    (a42 : -(h 2) < (-4/33 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a46 : -(h 1) < (-3/23 : ℝ))
    (a50 : -(h 3) < (-3/26 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3600 h delta _ctx _hno a14 a38 f0
  by_cases p1 : h 0 ≤ (4/27 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/27 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3601 h delta _ctx _hno a30 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3602 h delta _ctx _hno a32 a38 a43 a50 f2
  by_cases p3 : h 2 ≤ (3/23 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3603 h delta _ctx _hno a31 f3
  by_cases p4 : h 3 ≤ (7/60 : ℝ)
  swap
  · have f4 : -(h 3) < (-7/60 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3604 h delta _ctx _hno a32 a38 a42 a43 a46 f4
  by_cases p5 : h 4 ≤ (5/43 : ℝ)
  swap
  · have f5 : -(h 4) < (-5/43 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_3605 h delta _ctx _hno a38 a43 a46 f5
  by_cases p6 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f6 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact upper_node_3606 h delta _ctx _hno a32 a38 a43 a46 a50 f6
  apply _hno 139
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (4/27 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (7/60 : ℝ)) ∧ (h 4 ≤ (5/43 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem upper_node_3598 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a38 : -(h 0) < (-11/80 : ℝ))
    (a42 : -(h 2) < (-4/33 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a49 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/3 : ℝ) * a32 + (1/6 : ℝ) * a38 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a43 + (1/6 : ℝ) * a49 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3597 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a48 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3596 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a38 : -(h 0) < (-11/80 : ℝ))
    (a47 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * a14 + (1/5 : ℝ) * a38 + (4/5 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3595 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a31 : h 2 ≤ (1/8 : ℝ))
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a38 : -(h 0) < (-11/80 : ℝ))
    (a42 : -(h 2) < (-4/33 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a46 : -(h 1) < (-3/23 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3596 h delta _ctx _hno a14 a38 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3597 h delta _ctx _hno a30 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3598 h delta _ctx _hno a32 a38 a42 a43 f2
  by_cases p3 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f3 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3599 h delta _ctx _hno a14 a30 a31 a32 a38 a42 a43 a46 f3
  by_cases p4 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3607 h delta _ctx _hno a32 a38 a43 a46 f4
  apply _hno 19
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_3594 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a45 : -(h 0) < (-5/34 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3593 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a38 : -(h 0) < (-11/80 : ℝ))
    (a44 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * a14 + (1/5 : ℝ) * a38 + (4/5 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3592 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a31 : h 2 ≤ (1/8 : ℝ))
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a36 : -(h 1) < (-1/8 : ℝ))
    (a38 : -(h 0) < (-11/80 : ℝ))
    (a42 : -(h 2) < (-4/33 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3593 h delta _ctx _hno a14 a38 f0
  by_cases p1 : h 0 ≤ (5/34 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/34 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3594 h delta _ctx _hno a30 f1
  by_cases p2 : h 1 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3595 h delta _ctx _hno a14 a30 a31 a32 a38 a42 a43 f2
  by_cases p3 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3608 h delta _ctx _hno a14 a30 a32 a36 a38 a42 a43 f3
  apply _hno 92
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (5/34 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_3591 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a31 : h 2 ≤ (1/8 : ℝ))
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a33 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a36 : -(h 1) < (-1/8 : ℝ))
    (a38 : -(h 0) < (-11/80 : ℝ))
    (a42 : -(h 2) < (-4/33 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3592 h delta _ctx _hno a14 a30 a31 a32 a36 a38 a42 f0
  by_cases p1 : h 0 ≤ (1/7 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3628 h delta _ctx _hno a30 f1
  by_cases p2 : h 3 ≤ (5/42 : ℝ)
  swap
  · have f2 : -(h 3) < (-5/42 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3629 h delta _ctx _hno a30 a32 a33 a36 a38 a42 p0 f2
  by_cases p3 : h 4 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 4) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3647 h delta _ctx _hno a33 a36 a38 a42 p0 p2 f3
  apply _hno 21
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (1/7 : ℝ)) ∧ (h 3 ≤ (5/42 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_3590 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a33 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a41 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/29 : ℝ) * _ctx.order0 + (6/29 : ℝ) * _ctx.order3 + (6/29 : ℝ) * _ctx.min + (1/29 : ℝ) * _ctx.fail1 + (12/29 : ℝ) * a32 + (6/29 : ℝ) * a33 + (10/29 : ℝ) * a41 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3589 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a40 : -(h 0) < (-6/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3588 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a38 : -(h 0) < (-11/80 : ℝ))
    (a39 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * a14 + (1/5 : ℝ) * a38 + (4/5 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

end RealPinwheel.WeakSevenBandData
