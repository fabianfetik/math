import Pinwheel.WeakSevenBandData.CoverChunks.Upper004

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem upper_node_3907 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a50 : -(h 5) < (-5/46 : ℝ))
    (a51 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ))
    (a52 : -(h 0) < (-5/36 : ℝ))
    (a61 : -(h 4) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/25 : ℝ) * _ctx.order3 + (1/25 : ℝ) * _ctx.fail1 + (2/25 : ℝ) * a13 + (6/25 : ℝ) * a50 + (3/25 : ℝ) * a51 + (4/25 : ℝ) * a52 + (12/25 : ℝ) * a61 + (6/25 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3906 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a50 : -(h 5) < (-5/46 : ℝ))
    (a51 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ))
    (a52 : -(h 0) < (-5/36 : ℝ))
    (a56 : -(h 2) < (-4/33 : ℝ))
    (a60 : -(h 3) < (-4/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/16 : ℝ) * a13 + (3/16 : ℝ) * a32 + (3/16 : ℝ) * a50 + (3/32 : ℝ) * a51 + (3/16 : ℝ) * a52 + (3/16 : ℝ) * a56 + (3/16 : ℝ) * a60 + (3/16 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3905 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a45 : -(h 3) < (-5/42 : ℝ))
    (a50 : -(h 5) < (-5/46 : ℝ))
    (a52 : -(h 0) < (-5/36 : ℝ))
    (a56 : -(h 2) < (-4/33 : ℝ))
    (a59 : -(h 1) < (-6/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a32 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a50 + (1/6 : ℝ) * a52 + (1/6 : ℝ) * a56 + (1/6 : ℝ) * a59 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3904 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a47 : h 0 ≤ (6/43 : ℝ))
    (a58 : -(h 0) < (-6/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a47 + (1 : ℝ) * a58
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3903 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a51 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ))
    (a57 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a51 + (1 : ℝ) * a57
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3902 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a45 : -(h 3) < (-5/42 : ℝ))
    (a47 : h 0 ≤ (6/43 : ℝ))
    (a50 : -(h 5) < (-5/46 : ℝ))
    (a51 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ))
    (a52 : -(h 0) < (-5/36 : ℝ))
    (a56 : -(h 2) < (-4/33 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3903 h delta _ctx _hno a51 f0
  by_cases p1 : h 0 ≤ (6/41 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/41 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3904 h delta _ctx _hno a47 f1
  by_cases p2 : h 1 ≤ (6/47 : ℝ)
  swap
  · have f2 : -(h 1) < (-6/47 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3905 h delta _ctx _hno a32 a45 a50 a52 a56 f2
  by_cases p3 : h 3 ≤ (4/33 : ℝ)
  swap
  · have f3 : -(h 3) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3906 h delta _ctx _hno a13 a32 a50 a51 a52 a56 f3
  by_cases p4 : h 4 ≤ (3/25 : ℝ)
  swap
  · have f4 : -(h 4) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3907 h delta _ctx _hno a13 a50 a51 a52 f4
  by_cases p5 : h 5 ≤ (2/17 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_3908 h delta _ctx _hno a13 a45 a51 a52 f5
  apply _hno 145
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (6/41 : ℝ)) ∧ (h 1 ≤ (6/47 : ℝ)) ∧ (h 3 ≤ (4/33 : ℝ)) ∧ (h 4 ≤ (3/25 : ℝ)) ∧ (h 5 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_3901 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a48 : h 1 ≤ (2/15 : ℝ))
    (a55 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a48 + (1 : ℝ) * a55
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3900 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a47 : h 0 ≤ (6/43 : ℝ))
    (a54 : -(h 0) < (-6/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a47 + (1 : ℝ) * a54
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3899 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a51 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ))
    (a53 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a51 + (1 : ℝ) * a53
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3898 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a45 : -(h 3) < (-5/42 : ℝ))
    (a47 : h 0 ≤ (6/43 : ℝ))
    (a48 : h 1 ≤ (2/15 : ℝ))
    (a50 : -(h 5) < (-5/46 : ℝ))
    (a51 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ))
    (a52 : -(h 0) < (-5/36 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3899 h delta _ctx _hno a51 f0
  by_cases p1 : h 0 ≤ (6/41 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/41 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3900 h delta _ctx _hno a47 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3901 h delta _ctx _hno a48 f2
  by_cases p3 : h 2 ≤ (4/33 : ℝ)
  swap
  · have f3 : -(h 2) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3902 h delta _ctx _hno a13 a32 a45 a47 a50 a51 a52 f3
  by_cases p4 : h 3 ≤ (3/25 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3909 h delta _ctx _hno a13 a32 a47 a50 a51 a52 f4
  by_cases p5 : h 5 ≤ (2/17 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_3916 h delta _ctx _hno a13 a45 a51 a52 f5
  apply _hno 137
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (6/41 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (4/33 : ℝ)) ∧ (h 3 ≤ (3/25 : ℝ)) ∧ (h 5 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_3897 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a35 : -(h 1) < (-1/8 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a45 : -(h 3) < (-5/42 : ℝ))
    (a57 : -(h 5) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/9 : ℝ) * _ctx.order4 + (1/27 : ℝ) * _ctx.fail1 + (1/27 : ℝ) * a13 + (1/9 : ℝ) * a35 + (4/27 : ℝ) * a37 + (2/9 : ℝ) * a45 + (4/9 : ℝ) * a57 + (2/9 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3896 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a35 : -(h 1) < (-1/8 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a56 : -(h 3) < (-3/25 : ℝ))
    (a62 : -(h 5) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/9 : ℝ) * _ctx.order4 + (1/27 : ℝ) * _ctx.fail1 + (1/27 : ℝ) * a13 + (1/9 : ℝ) * a35 + (4/27 : ℝ) * a37 + (2/9 : ℝ) * a56 + (4/9 : ℝ) * a62 + (2/9 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3895 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a35 : -(h 1) < (-1/8 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a50 : -(h 5) < (-5/46 : ℝ))
    (a56 : -(h 3) < (-3/25 : ℝ))
    (a61 : -(h 4) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/27 : ℝ) * _ctx.fail1 + (1/27 : ℝ) * a13 + (1/9 : ℝ) * a35 + (4/27 : ℝ) * a37 + (2/9 : ℝ) * a50 + (2/9 : ℝ) * a56 + (2/9 : ℝ) * a61 + (2/9 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3894 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a55 : h 2 ≤ (4/33 : ℝ))
    (a60 : -(h 3) < (-4/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * _ctx.order2 + (1 : ℝ) * a55 + (1 : ℝ) * a60
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3893 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a56 : -(h 3) < (-3/25 : ℝ))
    (a59 : -(h 1) < (-6/47 : ℝ))
    (a65 : -(h 5) < (-7/64 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.lower + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a32 + (4/29 : ℝ) * a37 + (6/29 : ℝ) * a56 + (6/29 : ℝ) * a59 + (6/29 : ℝ) * a65 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3892 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a50 : -(h 5) < (-5/46 : ℝ))
    (a59 : -(h 1) < (-6/47 : ℝ))
    (a64 : -(h 4) < (-4/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.order3 + (6/29 : ℝ) * _ctx.lower + (1/29 : ℝ) * _ctx.fail1 + (4/29 : ℝ) * a37 + (6/29 : ℝ) * a50 + (6/29 : ℝ) * a59 + (12/29 : ℝ) * a64 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3891 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a55 : h 2 ≤ (4/33 : ℝ))
    (a63 : -(h 3) < (-5/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * _ctx.order2 + (1 : ℝ) * a55 + (1 : ℝ) * a63
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3890 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a55 : h 2 ≤ (4/33 : ℝ))
    (a62 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a55 + (1 : ℝ) * a62
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3889 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a50 : -(h 5) < (-5/46 : ℝ))
    (a56 : -(h 3) < (-3/25 : ℝ))
    (a59 : -(h 1) < (-6/47 : ℝ))
    (a61 : -(h 0) < (-4/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.lower + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a32 + (6/29 : ℝ) * a50 + (6/29 : ℝ) * a56 + (6/29 : ℝ) * a59 + (4/29 : ℝ) * a61 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3888 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a38 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a60 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a38 + (1 : ℝ) * a60
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3887 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a38 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a50 : -(h 5) < (-5/46 : ℝ))
    (a55 : h 2 ≤ (4/33 : ℝ))
    (a56 : -(h 3) < (-3/25 : ℝ))
    (a59 : -(h 1) < (-6/47 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3888 h delta _ctx _hno a38 f0
  by_cases p1 : h 0 ≤ (4/29 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/29 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3889 h delta _ctx _hno a32 a50 a56 a59 f1
  by_cases p2 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3890 h delta _ctx _hno a55 f2
  by_cases p3 : h 3 ≤ (5/41 : ℝ)
  swap
  · have f3 : -(h 3) < (-5/41 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3891 h delta _ctx _hno a55 f3
  by_cases p4 : h 4 ≤ (4/33 : ℝ)
  swap
  · have f4 : -(h 4) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3892 h delta _ctx _hno a37 a50 a59 f4
  by_cases p5 : h 5 ≤ (7/64 : ℝ)
  swap
  · have f5 : -(h 5) < (-7/64 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_3893 h delta _ctx _hno a32 a37 a56 a59 f5
  apply _hno 98
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (4/29 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (5/41 : ℝ)) ∧ (h 4 ≤ (4/33 : ℝ)) ∧ (h 5 ≤ (7/64 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_3886 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a47 : h 0 ≤ (6/43 : ℝ))
    (a58 : -(h 0) < (-6/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a47 + (1 : ℝ) * a58
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3885 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a38 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a57 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a38 + (1 : ℝ) * a57
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3884 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a35 : -(h 1) < (-1/8 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a38 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a47 : h 0 ≤ (6/43 : ℝ))
    (a50 : -(h 5) < (-5/46 : ℝ))
    (a55 : h 2 ≤ (4/33 : ℝ))
    (a56 : -(h 3) < (-3/25 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3885 h delta _ctx _hno a38 f0
  by_cases p1 : h 0 ≤ (6/41 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/41 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3886 h delta _ctx _hno a47 f1
  by_cases p2 : h 1 ≤ (6/47 : ℝ)
  swap
  · have f2 : -(h 1) < (-6/47 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3887 h delta _ctx _hno a32 a37 a38 a50 a55 a56 f2
  by_cases p3 : h 3 ≤ (4/33 : ℝ)
  swap
  · have f3 : -(h 3) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3894 h delta _ctx _hno a55 f3
  by_cases p4 : h 4 ≤ (3/25 : ℝ)
  swap
  · have f4 : -(h 4) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3895 h delta _ctx _hno a13 a35 a37 a50 a56 f4
  by_cases p5 : h 5 ≤ (2/17 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_3896 h delta _ctx _hno a13 a35 a37 a56 f5
  apply _hno 145
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (6/41 : ℝ)) ∧ (h 1 ≤ (6/47 : ℝ)) ∧ (h 3 ≤ (4/33 : ℝ)) ∧ (h 4 ≤ (3/25 : ℝ)) ∧ (h 5 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_3883 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a35 : -(h 1) < (-1/8 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a45 : -(h 3) < (-5/42 : ℝ))
    (a61 : -(h 5) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/9 : ℝ) * _ctx.order4 + (1/27 : ℝ) * _ctx.fail1 + (1/27 : ℝ) * a13 + (1/9 : ℝ) * a35 + (4/27 : ℝ) * a37 + (2/9 : ℝ) * a45 + (4/9 : ℝ) * a61 + (2/9 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3882 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a35 : -(h 1) < (-1/8 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a50 : -(h 5) < (-5/46 : ℝ))
    (a60 : -(h 4) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/9 : ℝ) * _ctx.order3 + (1/27 : ℝ) * _ctx.fail1 + (1/27 : ℝ) * a13 + (1/9 : ℝ) * a35 + (4/27 : ℝ) * a37 + (2/9 : ℝ) * a50 + (4/9 : ℝ) * a60 + (2/9 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3881 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a35 : -(h 1) < (-1/8 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a55 : -(h 2) < (-4/33 : ℝ))
    (a59 : -(h 3) < (-4/33 : ℝ))
    (a71 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/34 : ℝ) * a13 + (3/17 : ℝ) * a32 + (3/34 : ℝ) * a35 + (3/17 : ℝ) * a37 + (3/17 : ℝ) * a55 + (3/17 : ℝ) * a59 + (3/17 : ℝ) * a71 + (3/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3880 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a35 : -(h 1) < (-1/8 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a59 : -(h 3) < (-4/33 : ℝ))
    (a65 : -(h 5) < (-7/64 : ℝ))
    (a70 : -(h 4) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/27 : ℝ) * _ctx.fail1 + (1/27 : ℝ) * a13 + (1/9 : ℝ) * a35 + (4/27 : ℝ) * a37 + (2/9 : ℝ) * a59 + (2/9 : ℝ) * a65 + (2/9 : ℝ) * a70 + (2/9 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3879 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a35 : -(h 1) < (-1/8 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a59 : -(h 3) < (-4/33 : ℝ))
    (a65 : -(h 5) < (-7/64 : ℝ))
    (a69 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/34 : ℝ) * a13 + (3/17 : ℝ) * a32 + (3/34 : ℝ) * a35 + (3/17 : ℝ) * a37 + (3/17 : ℝ) * a59 + (3/17 : ℝ) * a65 + (3/17 : ℝ) * a69 + (3/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3878 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a58 : h 1 ≤ (6/47 : ℝ))
    (a68 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a58 + (1 : ℝ) * a68
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3877 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a61 : h 0 ≤ (4/29 : ℝ))
    (a67 : -(h 0) < (-9/62 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a61 + (1 : ℝ) * a67
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3876 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a35 : -(h 1) < (-1/8 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a55 : -(h 2) < (-4/33 : ℝ))
    (a59 : -(h 3) < (-4/33 : ℝ))
    (a65 : -(h 5) < (-7/64 : ℝ))
    (a66 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * a32 + (2/13 : ℝ) * a35 + (2/13 : ℝ) * a37 + (2/13 : ℝ) * a55 + (2/13 : ℝ) * a59 + (2/13 : ℝ) * a65 + (1/13 : ℝ) * a66 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3875 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a35 : -(h 1) < (-1/8 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a55 : -(h 2) < (-4/33 : ℝ))
    (a58 : h 1 ≤ (6/47 : ℝ))
    (a59 : -(h 3) < (-4/33 : ℝ))
    (a61 : h 0 ≤ (4/29 : ℝ))
    (a65 : -(h 5) < (-7/64 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3876 h delta _ctx _hno a32 a35 a37 a55 a59 a65 f0
  by_cases p1 : h 0 ≤ (9/62 : ℝ)
  swap
  · have f1 : -(h 0) < (-9/62 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3877 h delta _ctx _hno a61 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3878 h delta _ctx _hno a58 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3879 h delta _ctx _hno a13 a32 a35 a37 a59 a65 f3
  by_cases p4 : h 4 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 4) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3880 h delta _ctx _hno a13 a35 a37 a59 a65 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_3881 h delta _ctx _hno a13 a32 a35 a37 a55 a59 f5
  apply _hno 143
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (9/62 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_3874 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a35 : -(h 1) < (-1/8 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a50 : -(h 5) < (-5/46 : ℝ))
    (a59 : -(h 3) < (-4/33 : ℝ))
    (a64 : -(h 4) < (-4/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/27 : ℝ) * _ctx.fail1 + (1/27 : ℝ) * a13 + (1/9 : ℝ) * a35 + (4/27 : ℝ) * a37 + (2/9 : ℝ) * a50 + (2/9 : ℝ) * a59 + (2/9 : ℝ) * a64 + (2/9 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3873 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a35 : -(h 1) < (-1/8 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a50 : -(h 5) < (-5/46 : ℝ))
    (a63 : -(h 3) < (-5/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/17 : ℝ) * _ctx.order2 + (1/34 : ℝ) * a13 + (3/17 : ℝ) * a32 + (3/34 : ℝ) * a35 + (3/17 : ℝ) * a37 + (3/17 : ℝ) * a50 + (6/17 : ℝ) * a63 + (3/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3872 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a35 : -(h 1) < (-1/8 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a50 : -(h 5) < (-5/46 : ℝ))
    (a59 : -(h 3) < (-4/33 : ℝ))
    (a62 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/34 : ℝ) * a13 + (3/17 : ℝ) * a32 + (3/34 : ℝ) * a35 + (3/17 : ℝ) * a37 + (3/17 : ℝ) * a50 + (3/17 : ℝ) * a59 + (3/17 : ℝ) * a62 + (3/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3871 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a35 : -(h 1) < (-1/8 : ℝ))
    (a55 : -(h 2) < (-4/33 : ℝ))
    (a59 : -(h 3) < (-4/33 : ℝ))
    (a61 : -(h 0) < (-4/29 : ℝ))
    (a67 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/34 : ℝ) * a13 + (3/17 : ℝ) * a32 + (3/34 : ℝ) * a35 + (3/17 : ℝ) * a55 + (3/17 : ℝ) * a59 + (3/17 : ℝ) * a61 + (3/17 : ℝ) * a67 + (3/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3870 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a35 : -(h 1) < (-1/8 : ℝ))
    (a50 : -(h 5) < (-5/46 : ℝ))
    (a55 : -(h 2) < (-4/33 : ℝ))
    (a59 : -(h 3) < (-4/33 : ℝ))
    (a61 : -(h 0) < (-4/29 : ℝ))
    (a66 : -(h 4) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/34 : ℝ) * a13 + (3/34 : ℝ) * a35 + (3/17 : ℝ) * a50 + (3/17 : ℝ) * a55 + (3/17 : ℝ) * a59 + (3/17 : ℝ) * a61 + (3/17 : ℝ) * a66 + (3/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3869 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a35 : -(h 1) < (-1/8 : ℝ))
    (a50 : -(h 5) < (-5/46 : ℝ))
    (a59 : -(h 3) < (-4/33 : ℝ))
    (a61 : -(h 0) < (-4/29 : ℝ))
    (a65 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/34 : ℝ) * a13 + (3/17 : ℝ) * a32 + (3/34 : ℝ) * a35 + (3/17 : ℝ) * a50 + (3/17 : ℝ) * a59 + (3/17 : ℝ) * a61 + (3/17 : ℝ) * a65 + (3/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3868 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a58 : h 1 ≤ (6/47 : ℝ))
    (a64 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a58 + (1 : ℝ) * a64
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3867 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a47 : h 0 ≤ (6/43 : ℝ))
    (a63 : -(h 0) < (-9/62 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a47 + (1 : ℝ) * a63
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3866 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a35 : -(h 1) < (-1/8 : ℝ))
    (a50 : -(h 5) < (-5/46 : ℝ))
    (a55 : -(h 2) < (-4/33 : ℝ))
    (a59 : -(h 3) < (-4/33 : ℝ))
    (a61 : -(h 0) < (-4/29 : ℝ))
    (a62 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * a32 + (2/13 : ℝ) * a35 + (2/13 : ℝ) * a50 + (2/13 : ℝ) * a55 + (2/13 : ℝ) * a59 + (2/13 : ℝ) * a61 + (1/13 : ℝ) * a62 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3865 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a35 : -(h 1) < (-1/8 : ℝ))
    (a47 : h 0 ≤ (6/43 : ℝ))
    (a50 : -(h 5) < (-5/46 : ℝ))
    (a55 : -(h 2) < (-4/33 : ℝ))
    (a58 : h 1 ≤ (6/47 : ℝ))
    (a59 : -(h 3) < (-4/33 : ℝ))
    (a61 : -(h 0) < (-4/29 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3866 h delta _ctx _hno a32 a35 a50 a55 a59 a61 f0
  by_cases p1 : h 0 ≤ (9/62 : ℝ)
  swap
  · have f1 : -(h 0) < (-9/62 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3867 h delta _ctx _hno a47 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3868 h delta _ctx _hno a58 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3869 h delta _ctx _hno a13 a32 a35 a50 a59 a61 f3
  by_cases p4 : h 4 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 4) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3870 h delta _ctx _hno a13 a35 a50 a55 a59 a61 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_3871 h delta _ctx _hno a13 a32 a35 a55 a59 a61 f5
  apply _hno 143
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (9/62 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_3864 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a38 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a60 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a38 + (1 : ℝ) * a60
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3863 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a35 : -(h 1) < (-1/8 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a38 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a47 : h 0 ≤ (6/43 : ℝ))
    (a50 : -(h 5) < (-5/46 : ℝ))
    (a55 : -(h 2) < (-4/33 : ℝ))
    (a58 : h 1 ≤ (6/47 : ℝ))
    (a59 : -(h 3) < (-4/33 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3864 h delta _ctx _hno a38 f0
  by_cases p1 : h 0 ≤ (4/29 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/29 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3865 h delta _ctx _hno a13 a32 a35 a47 a50 a55 a58 a59 f1
  by_cases p2 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3872 h delta _ctx _hno a13 a32 a35 a37 a50 a59 f2
  by_cases p3 : h 3 ≤ (5/41 : ℝ)
  swap
  · have f3 : -(h 3) < (-5/41 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3873 h delta _ctx _hno a13 a32 a35 a37 a50 f3
  by_cases p4 : h 4 ≤ (4/33 : ℝ)
  swap
  · have f4 : -(h 4) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3874 h delta _ctx _hno a13 a35 a37 a50 a59 f4
  by_cases p5 : h 5 ≤ (7/64 : ℝ)
  swap
  · have f5 : -(h 5) < (-7/64 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_3875 h delta _ctx _hno a13 a32 a35 a37 a55 a58 a59 p1 f5
  apply _hno 98
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (4/29 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (5/41 : ℝ)) ∧ (h 4 ≤ (4/33 : ℝ)) ∧ (h 5 ≤ (7/64 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_3862 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a45 : -(h 3) < (-5/42 : ℝ))
    (a55 : -(h 2) < (-4/33 : ℝ))
    (a58 : -(h 1) < (-6/47 : ℝ))
    (a70 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a32 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a55 + (1/6 : ℝ) * a58 + (1/6 : ℝ) * a70 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3861 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a45 : -(h 3) < (-5/42 : ℝ))
    (a58 : -(h 1) < (-6/47 : ℝ))
    (a64 : -(h 5) < (-7/64 : ℝ))
    (a69 : -(h 4) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.lower + (1/29 : ℝ) * _ctx.fail1 + (4/29 : ℝ) * a37 + (6/29 : ℝ) * a45 + (6/29 : ℝ) * a58 + (6/29 : ℝ) * a64 + (6/29 : ℝ) * a69 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3860 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a45 : -(h 3) < (-5/42 : ℝ))
    (a58 : -(h 1) < (-6/47 : ℝ))
    (a64 : -(h 5) < (-7/64 : ℝ))
    (a68 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a32 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a58 + (1/6 : ℝ) * a64 + (1/6 : ℝ) * a68 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3859 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a45 : -(h 3) < (-5/42 : ℝ))
    (a64 : -(h 5) < (-7/64 : ℝ))
    (a67 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/11 : ℝ) * _ctx.lower + (1/22 : ℝ) * _ctx.fail1 + (1/22 : ℝ) * _ctx.fail2 + (1/11 : ℝ) * a32 + (3/11 : ℝ) * a45 + (3/11 : ℝ) * a64 + (3/11 : ℝ) * a67 + (3/11 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3858 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a60 : h 0 ≤ (4/29 : ℝ))
    (a66 : -(h 0) < (-9/62 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a60 + (1 : ℝ) * a66
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3857 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a45 : -(h 3) < (-5/42 : ℝ))
    (a55 : -(h 2) < (-4/33 : ℝ))
    (a58 : -(h 1) < (-6/47 : ℝ))
    (a64 : -(h 5) < (-7/64 : ℝ))
    (a65 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * a32 + (2/13 : ℝ) * a37 + (2/13 : ℝ) * a45 + (2/13 : ℝ) * a55 + (2/13 : ℝ) * a58 + (2/13 : ℝ) * a64 + (1/13 : ℝ) * a65 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3856 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a45 : -(h 3) < (-5/42 : ℝ))
    (a55 : -(h 2) < (-4/33 : ℝ))
    (a58 : -(h 1) < (-6/47 : ℝ))
    (a60 : h 0 ≤ (4/29 : ℝ))
    (a64 : -(h 5) < (-7/64 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3857 h delta _ctx _hno a32 a37 a45 a55 a58 a64 f0
  by_cases p1 : h 0 ≤ (9/62 : ℝ)
  swap
  · have f1 : -(h 0) < (-9/62 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3858 h delta _ctx _hno a60 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3859 h delta _ctx _hno a32 a45 a64 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3860 h delta _ctx _hno a32 a37 a45 a58 a64 f3
  by_cases p4 : h 4 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 4) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3861 h delta _ctx _hno a37 a45 a58 a64 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_3862 h delta _ctx _hno a32 a37 a45 a55 a58 f5
  apply _hno 143
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (9/62 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_3855 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a50 : -(h 5) < (-5/46 : ℝ))
    (a58 : -(h 1) < (-6/47 : ℝ))
    (a63 : -(h 4) < (-4/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.order3 + (6/29 : ℝ) * _ctx.lower + (1/29 : ℝ) * _ctx.fail1 + (4/29 : ℝ) * a37 + (6/29 : ℝ) * a50 + (6/29 : ℝ) * a58 + (12/29 : ℝ) * a63 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3854 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a50 : -(h 5) < (-5/46 : ℝ))
    (a58 : -(h 1) < (-6/47 : ℝ))
    (a62 : -(h 3) < (-5/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order2 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a32 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a50 + (1/6 : ℝ) * a58 + (1/3 : ℝ) * a62 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3853 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a45 : -(h 3) < (-5/42 : ℝ))
    (a50 : -(h 5) < (-5/46 : ℝ))
    (a58 : -(h 1) < (-6/47 : ℝ))
    (a61 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a32 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a50 + (1/6 : ℝ) * a58 + (1/6 : ℝ) * a61 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3852 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a45 : -(h 3) < (-5/42 : ℝ))
    (a55 : -(h 2) < (-4/33 : ℝ))
    (a58 : -(h 1) < (-6/47 : ℝ))
    (a60 : -(h 0) < (-4/29 : ℝ))
    (a66 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a32 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a55 + (1/6 : ℝ) * a58 + (1/6 : ℝ) * a60 + (1/6 : ℝ) * a66 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3851 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a45 : -(h 3) < (-5/42 : ℝ))
    (a50 : -(h 5) < (-5/46 : ℝ))
    (a58 : -(h 1) < (-6/47 : ℝ))
    (a60 : -(h 0) < (-4/29 : ℝ))
    (a65 : -(h 4) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.lower + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a45 + (6/29 : ℝ) * a50 + (6/29 : ℝ) * a58 + (4/29 : ℝ) * a60 + (6/29 : ℝ) * a65 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3850 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a45 : -(h 3) < (-5/42 : ℝ))
    (a50 : -(h 5) < (-5/46 : ℝ))
    (a58 : -(h 1) < (-6/47 : ℝ))
    (a60 : -(h 0) < (-4/29 : ℝ))
    (a64 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a32 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a50 + (1/6 : ℝ) * a58 + (1/6 : ℝ) * a60 + (1/6 : ℝ) * a64 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3849 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a45 : -(h 3) < (-5/42 : ℝ))
    (a50 : -(h 5) < (-5/46 : ℝ))
    (a60 : -(h 0) < (-4/29 : ℝ))
    (a63 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.lower + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a32 + (6/29 : ℝ) * a45 + (6/29 : ℝ) * a50 + (4/29 : ℝ) * a60 + (6/29 : ℝ) * a63 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3848 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a47 : h 0 ≤ (6/43 : ℝ))
    (a62 : -(h 0) < (-9/62 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a47 + (1 : ℝ) * a62
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3847 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a45 : -(h 3) < (-5/42 : ℝ))
    (a50 : -(h 5) < (-5/46 : ℝ))
    (a55 : -(h 2) < (-4/33 : ℝ))
    (a58 : -(h 1) < (-6/47 : ℝ))
    (a60 : -(h 0) < (-4/29 : ℝ))
    (a61 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * a32 + (2/13 : ℝ) * a45 + (2/13 : ℝ) * a50 + (2/13 : ℝ) * a55 + (2/13 : ℝ) * a58 + (2/13 : ℝ) * a60 + (1/13 : ℝ) * a61 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3846 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a45 : -(h 3) < (-5/42 : ℝ))
    (a47 : h 0 ≤ (6/43 : ℝ))
    (a50 : -(h 5) < (-5/46 : ℝ))
    (a55 : -(h 2) < (-4/33 : ℝ))
    (a58 : -(h 1) < (-6/47 : ℝ))
    (a60 : -(h 0) < (-4/29 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3847 h delta _ctx _hno a32 a45 a50 a55 a58 a60 f0
  by_cases p1 : h 0 ≤ (9/62 : ℝ)
  swap
  · have f1 : -(h 0) < (-9/62 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3848 h delta _ctx _hno a47 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3849 h delta _ctx _hno a32 a45 a50 a60 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3850 h delta _ctx _hno a32 a45 a50 a58 a60 f3
  by_cases p4 : h 4 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 4) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3851 h delta _ctx _hno a45 a50 a58 a60 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_3852 h delta _ctx _hno a32 a45 a55 a58 a60 f5
  apply _hno 143
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (9/62 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_3845 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a38 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a59 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a38 + (1 : ℝ) * a59
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3844 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a38 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a45 : -(h 3) < (-5/42 : ℝ))
    (a47 : h 0 ≤ (6/43 : ℝ))
    (a50 : -(h 5) < (-5/46 : ℝ))
    (a55 : -(h 2) < (-4/33 : ℝ))
    (a58 : -(h 1) < (-6/47 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3845 h delta _ctx _hno a38 f0
  by_cases p1 : h 0 ≤ (4/29 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/29 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3846 h delta _ctx _hno a32 a45 a47 a50 a55 a58 f1
  by_cases p2 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3853 h delta _ctx _hno a32 a37 a45 a50 a58 f2
  by_cases p3 : h 3 ≤ (5/41 : ℝ)
  swap
  · have f3 : -(h 3) < (-5/41 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3854 h delta _ctx _hno a32 a37 a50 a58 f3
  by_cases p4 : h 4 ≤ (4/33 : ℝ)
  swap
  · have f4 : -(h 4) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3855 h delta _ctx _hno a37 a50 a58 f4
  by_cases p5 : h 5 ≤ (7/64 : ℝ)
  swap
  · have f5 : -(h 5) < (-7/64 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_3856 h delta _ctx _hno a32 a37 a45 a55 a58 p1 f5
  apply _hno 98
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (4/29 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (5/41 : ℝ)) ∧ (h 4 ≤ (4/33 : ℝ)) ∧ (h 5 ≤ (7/64 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_3843 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a47 : h 0 ≤ (6/43 : ℝ))
    (a57 : -(h 0) < (-6/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a47 + (1 : ℝ) * a57
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3842 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a38 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a56 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a38 + (1 : ℝ) * a56
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3841 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a35 : -(h 1) < (-1/8 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a38 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a45 : -(h 3) < (-5/42 : ℝ))
    (a47 : h 0 ≤ (6/43 : ℝ))
    (a50 : -(h 5) < (-5/46 : ℝ))
    (a55 : -(h 2) < (-4/33 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3842 h delta _ctx _hno a38 f0
  by_cases p1 : h 0 ≤ (6/41 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/41 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3843 h delta _ctx _hno a47 f1
  by_cases p2 : h 1 ≤ (6/47 : ℝ)
  swap
  · have f2 : -(h 1) < (-6/47 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3844 h delta _ctx _hno a32 a37 a38 a45 a47 a50 a55 f2
  by_cases p3 : h 3 ≤ (4/33 : ℝ)
  swap
  · have f3 : -(h 3) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3863 h delta _ctx _hno a13 a32 a35 a37 a38 a47 a50 a55 p2 f3
  by_cases p4 : h 4 ≤ (3/25 : ℝ)
  swap
  · have f4 : -(h 4) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3882 h delta _ctx _hno a13 a35 a37 a50 f4
  by_cases p5 : h 5 ≤ (2/17 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_3883 h delta _ctx _hno a13 a35 a37 a45 f5
  apply _hno 145
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (6/41 : ℝ)) ∧ (h 1 ≤ (6/47 : ℝ)) ∧ (h 3 ≤ (4/33 : ℝ)) ∧ (h 4 ≤ (3/25 : ℝ)) ∧ (h 5 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_3840 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a48 : h 1 ≤ (2/15 : ℝ))
    (a54 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a48 + (1 : ℝ) * a54
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3839 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a47 : h 0 ≤ (6/43 : ℝ))
    (a53 : -(h 0) < (-6/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a47 + (1 : ℝ) * a53
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3838 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a38 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a52 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a38 + (1 : ℝ) * a52
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3837 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a35 : -(h 1) < (-1/8 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a38 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a45 : -(h 3) < (-5/42 : ℝ))
    (a47 : h 0 ≤ (6/43 : ℝ))
    (a48 : h 1 ≤ (2/15 : ℝ))
    (a50 : -(h 5) < (-5/46 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3838 h delta _ctx _hno a38 f0
  by_cases p1 : h 0 ≤ (6/41 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/41 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3839 h delta _ctx _hno a47 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3840 h delta _ctx _hno a48 f2
  by_cases p3 : h 2 ≤ (4/33 : ℝ)
  swap
  · have f3 : -(h 2) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3841 h delta _ctx _hno a13 a32 a35 a37 a38 a45 a47 a50 f3
  by_cases p4 : h 3 ≤ (3/25 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3884 h delta _ctx _hno a13 a32 a35 a37 a38 a47 a50 p3 f4
  by_cases p5 : h 5 ≤ (2/17 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_3897 h delta _ctx _hno a13 a35 a37 a45 f5
  apply _hno 137
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (6/41 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (4/33 : ℝ)) ∧ (h 3 ≤ (3/25 : ℝ)) ∧ (h 5 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_3836 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a31 : h 2 ≤ (1/8 : ℝ))
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a35 : -(h 1) < (-1/8 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a38 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a45 : -(h 3) < (-5/42 : ℝ))
    (a47 : h 0 ≤ (6/43 : ℝ))
    (a48 : h 1 ≤ (2/15 : ℝ))
    (a50 : -(h 5) < (-5/46 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3837 h delta _ctx _hno a13 a32 a35 a37 a38 a45 a47 a48 a50
  by_cases p1 : h 0 ≤ (5/36 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/36 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3898 h delta _ctx _hno a13 a32 a45 a47 a48 a50 p0 f1
  by_cases p2 : h 1 ≤ (9/65 : ℝ)
  swap
  · have f2 : -(h 1) < (-9/65 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3917 h delta _ctx _hno a48 f2
  by_cases p3 : h 2 ≤ (3/22 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3918 h delta _ctx _hno a31 f3
  by_cases p4 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3919 h delta _ctx _hno a13 a50 p0 f4
  by_cases p5 : h 4 ≤ (5/41 : ℝ)
  swap
  · have f5 : -(h 4) < (-5/41 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_3920 h delta _ctx _hno a13 a37 a50 p0 f5
  apply _hno 22
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (5/36 : ℝ)) ∧ (h 1 ≤ (9/65 : ℝ)) ∧ (h 2 ≤ (3/22 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (5/41 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_3835 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a35 : -(h 1) < (-1/8 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    (a49 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/17 : ℝ) * _ctx.order2 + (1/34 : ℝ) * a13 + (3/17 : ℝ) * a32 + (3/34 : ℝ) * a35 + (3/17 : ℝ) * a37 + (3/17 : ℝ) * a42 + (6/17 : ℝ) * a49 + (3/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3834 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    (a45 : -(h 3) < (-5/42 : ℝ))
    (a48 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.lower + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a32 + (4/29 : ℝ) * a37 + (6/29 : ℝ) * a42 + (6/29 : ℝ) * a45 + (6/29 : ℝ) * a48 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3833 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a35 : -(h 1) < (-1/8 : ℝ))
    (a45 : -(h 3) < (-5/42 : ℝ))
    (a47 : -(h 0) < (-6/43 : ℝ))
    (a53 : -(h 5) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/9 : ℝ) * _ctx.order4 + (1/27 : ℝ) * _ctx.fail1 + (1/27 : ℝ) * a13 + (1/9 : ℝ) * a35 + (2/9 : ℝ) * a45 + (4/27 : ℝ) * a47 + (4/9 : ℝ) * a53 + (2/9 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3832 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a35 : -(h 1) < (-1/8 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    (a47 : -(h 0) < (-6/43 : ℝ))
    (a52 : -(h 4) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/9 : ℝ) * _ctx.order3 + (1/27 : ℝ) * _ctx.fail1 + (1/27 : ℝ) * a13 + (1/9 : ℝ) * a35 + (2/9 : ℝ) * a42 + (4/27 : ℝ) * a47 + (4/9 : ℝ) * a52 + (2/9 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3831 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a35 : -(h 1) < (-1/8 : ℝ))
    (a47 : -(h 0) < (-6/43 : ℝ))
    (a51 : -(h 3) < (-4/33 : ℝ))
    (a62 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/17 : ℝ) * _ctx.order2 + (1/34 : ℝ) * a13 + (3/17 : ℝ) * a32 + (3/34 : ℝ) * a35 + (3/17 : ℝ) * a47 + (6/17 : ℝ) * a51 + (3/17 : ℝ) * a62 + (3/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3830 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a35 : -(h 1) < (-1/8 : ℝ))
    (a47 : -(h 0) < (-6/43 : ℝ))
    (a51 : -(h 3) < (-4/33 : ℝ))
    (a56 : -(h 5) < (-3/28 : ℝ))
    (a61 : -(h 4) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/17 : ℝ) * _ctx.order2 + (1/34 : ℝ) * a13 + (3/34 : ℝ) * a35 + (3/17 : ℝ) * a47 + (6/17 : ℝ) * a51 + (3/17 : ℝ) * a56 + (3/17 : ℝ) * a61 + (3/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3829 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a35 : -(h 1) < (-1/8 : ℝ))
    (a47 : -(h 0) < (-6/43 : ℝ))
    (a51 : -(h 3) < (-4/33 : ℝ))
    (a56 : -(h 5) < (-3/28 : ℝ))
    (a60 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/34 : ℝ) * a13 + (3/17 : ℝ) * a32 + (3/34 : ℝ) * a35 + (3/17 : ℝ) * a47 + (3/17 : ℝ) * a51 + (3/17 : ℝ) * a56 + (3/17 : ℝ) * a60 + (3/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3828 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a50 : h 1 ≤ (6/47 : ℝ))
    (a59 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a50 + (1 : ℝ) * a59
  exact (lt_irrefl (0 : ℝ)) hbad

end RealPinwheel.WeakSevenBandData
