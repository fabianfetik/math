import Pinwheel.WeakSevenBandData.CoverChunks.Upper017

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem upper_node_2867 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a42 : -(h 4) < (-1/9 : ℝ))
    (a54 : -(h 5) < (-2/19 : ℝ))
    (a59 : -(h 3) < (-7/60 : ℝ))
    (a61 : -(h 0) < (-5/34 : ℝ))
    (a64 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.lower + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a42 + (6/29 : ℝ) * a54 + (6/29 : ℝ) * a59 + (4/29 : ℝ) * a61 + (6/29 : ℝ) * a64 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2866 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a50 : h 0 ≤ (4/27 : ℝ))
    (a63 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a50 + (1 : ℝ) * a63
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2865 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a49 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a62 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a49 + (1 : ℝ) * a62
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2864 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a33 : -(h 1) < (-9/70 : ℝ))
    (a37 : h 2 ≤ (5/41 : ℝ))
    (a42 : -(h 4) < (-1/9 : ℝ))
    (a47 : h 1 ≤ (2/15 : ℝ))
    (a49 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a50 : h 0 ≤ (4/27 : ℝ))
    (a54 : -(h 5) < (-2/19 : ℝ))
    (a59 : -(h 3) < (-7/60 : ℝ))
    (a61 : -(h 0) < (-5/34 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2865 h delta _ctx _hno a49 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2866 h delta _ctx _hno a50 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2867 h delta _ctx _hno a42 a54 a59 a61 f2
  by_cases p3 : h 2 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2868 h delta _ctx _hno a25 a28 a33 a37 a42 a47 a49 a50 a54 a59 a61
  by_cases p4 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2895 h delta _ctx _hno a33 a42 a59 p3 f4
  apply _hno 118
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_2863 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a49 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a60 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a49 + (1 : ℝ) * a60
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2862 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a33 : -(h 1) < (-9/70 : ℝ))
    (a37 : h 2 ≤ (5/41 : ℝ))
    (a42 : -(h 4) < (-1/9 : ℝ))
    (a44 : -(h 0) < (-6/41 : ℝ))
    (a47 : h 1 ≤ (2/15 : ℝ))
    (a49 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a50 : h 0 ≤ (4/27 : ℝ))
    (a54 : -(h 5) < (-2/19 : ℝ))
    (a59 : -(h 3) < (-7/60 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2863 h delta _ctx _hno a49 f0
  by_cases p1 : h 0 ≤ (5/34 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/34 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2864 h delta _ctx _hno a25 a28 a33 a37 a42 a47 a49 a50 a54 a59 f1
  by_cases p2 : h 1 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2896 h delta _ctx _hno a28 a42 a44 a47 a49 a54 a59 p1 f2
  by_cases p3 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2909 h delta _ctx _hno a28 a33 a42 a44 a49 a54 p1 p2 f3
  apply _hno 92
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (5/34 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_2861 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a37 : h 2 ≤ (5/41 : ℝ))
    (a58 : -(h 2) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a37 + (1 : ℝ) * a58
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2860 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a42 : -(h 4) < (-1/9 : ℝ))
    (a44 : -(h 0) < (-6/41 : ℝ))
    (a48 : -(h 3) < (-3/26 : ℝ))
    (a54 : -(h 5) < (-2/19 : ℝ))
    (a57 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.lower + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a42 + (4/29 : ℝ) * a44 + (6/29 : ℝ) * a48 + (6/29 : ℝ) * a54 + (6/29 : ℝ) * a57 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2859 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a48 : -(h 3) < (-3/26 : ℝ))
    (a56 : -(h 0) < (-4/27 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/7 : ℝ) * a25 + (1/7 : ℝ) * a48 + (6/7 : ℝ) * a56
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2858 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a49 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a55 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a49 + (1 : ℝ) * a55
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2857 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a33 : -(h 1) < (-9/70 : ℝ))
    (a37 : h 2 ≤ (5/41 : ℝ))
    (a42 : -(h 4) < (-1/9 : ℝ))
    (a44 : -(h 0) < (-6/41 : ℝ))
    (a47 : h 1 ≤ (2/15 : ℝ))
    (a48 : -(h 3) < (-3/26 : ℝ))
    (a49 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a50 : h 0 ≤ (4/27 : ℝ))
    (a54 : -(h 5) < (-2/19 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2858 h delta _ctx _hno a49 f0
  by_cases p1 : h 0 ≤ (4/27 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/27 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2859 h delta _ctx _hno a25 a48 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2860 h delta _ctx _hno a42 a44 a48 a54 f2
  by_cases p3 : h 2 ≤ (3/23 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2861 h delta _ctx _hno a37 f3
  by_cases p4 : h 3 ≤ (7/60 : ℝ)
  swap
  · have f4 : -(h 3) < (-7/60 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2862 h delta _ctx _hno a25 a28 a33 a37 a42 a44 a47 a49 a50 a54 f4
  by_cases p5 : h 4 ≤ (5/43 : ℝ)
  swap
  · have f5 : -(h 4) < (-5/43 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_2923 h delta _ctx _hno a33 a44 a54 f5
  by_cases p6 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f6 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact upper_node_2924 h delta _ctx _hno a33 a42 a44 a48 f6
  apply _hno 139
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (4/27 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (7/60 : ℝ)) ∧ (h 4 ≤ (5/43 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem upper_node_2856 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : -(h 1) < (-9/70 : ℝ))
    (a44 : -(h 0) < (-6/41 : ℝ))
    (a53 : -(h 4) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.order3 + (6/23 : ℝ) * _ctx.min + (12/23 : ℝ) * _ctx.lower + (1/23 : ℝ) * _ctx.fail1 + (6/23 : ℝ) * a33 + (4/23 : ℝ) * a44 + (12/23 : ℝ) * a53 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2855 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a37 : h 2 ≤ (5/41 : ℝ))
    (a52 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a37 + (1 : ℝ) * a52
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2854 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a47 : h 1 ≤ (2/15 : ℝ))
    (a51 : -(h 1) < (-6/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a47 + (1 : ℝ) * a51
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2853 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a48 : -(h 3) < (-3/26 : ℝ))
    (a50 : -(h 0) < (-4/27 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/7 : ℝ) * a25 + (1/7 : ℝ) * a48 + (6/7 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2852 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : -(h 1) < (-9/70 : ℝ))
    (a42 : -(h 4) < (-1/9 : ℝ))
    (a44 : -(h 0) < (-6/41 : ℝ))
    (a48 : -(h 3) < (-3/26 : ℝ))
    (a49 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a56 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/32 : ℝ) * _ctx.fail1 + (3/16 : ℝ) * a33 + (3/16 : ℝ) * a42 + (1/8 : ℝ) * a44 + (3/16 : ℝ) * a48 + (3/32 : ℝ) * a49 + (3/16 : ℝ) * a56 + (3/16 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2851 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : -(h 1) < (-9/70 : ℝ))
    (a44 : -(h 0) < (-6/41 : ℝ))
    (a49 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a55 : -(h 4) < (-5/43 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.order3 + (6/29 : ℝ) * _ctx.min + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a33 + (4/29 : ℝ) * a44 + (6/29 : ℝ) * a49 + (12/29 : ℝ) * a55 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2850 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a33 : -(h 1) < (-9/70 : ℝ))
    (a44 : -(h 0) < (-6/41 : ℝ))
    (a49 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a58 : -(h 3) < (-2/17 : ℝ))
    (a64 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/26 : ℝ) * _ctx.fail1 + (3/104 : ℝ) * a28 + (3/13 : ℝ) * a33 + (2/13 : ℝ) * a44 + (3/26 : ℝ) * a49 + (21/104 : ℝ) * a58 + (3/13 : ℝ) * a64 + (3/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2849 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : -(h 1) < (-9/70 : ℝ))
    (a44 : -(h 0) < (-6/41 : ℝ))
    (a49 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a58 : -(h 3) < (-2/17 : ℝ))
    (a63 : -(h 4) < (-5/44 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.min + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a33 + (4/29 : ℝ) * a44 + (6/29 : ℝ) * a49 + (6/29 : ℝ) * a58 + (6/29 : ℝ) * a63 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2848 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : -(h 1) < (-9/70 : ℝ))
    (a42 : -(h 4) < (-1/9 : ℝ))
    (a44 : -(h 0) < (-6/41 : ℝ))
    (a49 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a58 : -(h 3) < (-2/17 : ℝ))
    (a62 : -(h 2) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a44 + (1/6 : ℝ) * a49 + (1/6 : ℝ) * a58 + (1/6 : ℝ) * a62 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2847 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a42 : -(h 4) < (-1/9 : ℝ))
    (a44 : -(h 0) < (-6/41 : ℝ))
    (a49 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a58 : -(h 3) < (-2/17 : ℝ))
    (a61 : -(h 1) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.min + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a42 + (4/29 : ℝ) * a44 + (6/29 : ℝ) * a49 + (6/29 : ℝ) * a58 + (6/29 : ℝ) * a61 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2846 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a56 : h 0 ≤ (5/34 : ℝ))
    (a60 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a56 + (1 : ℝ) * a60
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2845 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a44 : -(h 0) < (-6/41 : ℝ))
    (a59 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * a14 + (1/5 : ℝ) * a44 + (4/5 : ℝ) * a59
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2844 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a33 : -(h 1) < (-9/70 : ℝ))
    (a42 : -(h 4) < (-1/9 : ℝ))
    (a44 : -(h 0) < (-6/41 : ℝ))
    (a49 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a56 : h 0 ≤ (5/34 : ℝ))
    (a58 : -(h 3) < (-2/17 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2845 h delta _ctx _hno a14 a44 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2846 h delta _ctx _hno a56 f1
  by_cases p2 : h 1 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2847 h delta _ctx _hno a42 a44 a49 a58 f2
  by_cases p3 : h 2 ≤ (3/25 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2848 h delta _ctx _hno a33 a42 a44 a49 a58 f3
  by_cases p4 : h 4 ≤ (5/44 : ℝ)
  swap
  · have f4 : -(h 4) < (-5/44 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2849 h delta _ctx _hno a33 a44 a49 a58 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_2850 h delta _ctx _hno a28 a33 a44 a49 a58 f5
  apply _hno 125
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 4 ≤ (5/44 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_2843 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a44 : -(h 0) < (-6/41 : ℝ))
    (a49 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a54 : -(h 3) < (-7/60 : ℝ))
    (a57 : -(h 1) < (-3/23 : ℝ))
    (a63 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/26 : ℝ) * _ctx.fail1 + (3/104 : ℝ) * a28 + (2/13 : ℝ) * a44 + (3/26 : ℝ) * a49 + (21/104 : ℝ) * a54 + (3/13 : ℝ) * a57 + (3/13 : ℝ) * a63 + (3/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2842 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a42 : -(h 4) < (-1/9 : ℝ))
    (a44 : -(h 0) < (-6/41 : ℝ))
    (a49 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a57 : -(h 1) < (-3/23 : ℝ))
    (a62 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.min + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a42 + (4/29 : ℝ) * a44 + (6/29 : ℝ) * a49 + (6/29 : ℝ) * a57 + (6/29 : ℝ) * a62 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2841 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a42 : -(h 4) < (-1/9 : ℝ))
    (a44 : -(h 0) < (-6/41 : ℝ))
    (a49 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a54 : -(h 3) < (-7/60 : ℝ))
    (a57 : -(h 1) < (-3/23 : ℝ))
    (a61 : -(h 2) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a44 + (1/6 : ℝ) * a49 + (1/6 : ℝ) * a54 + (1/6 : ℝ) * a57 + (1/6 : ℝ) * a61 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2840 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a47 : h 1 ≤ (2/15 : ℝ))
    (a60 : -(h 1) < (-3/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a47 + (1 : ℝ) * a60
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2839 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a56 : h 0 ≤ (5/34 : ℝ))
    (a59 : -(h 0) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a56 + (1 : ℝ) * a59
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2838 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a44 : -(h 0) < (-6/41 : ℝ))
    (a58 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * a14 + (1/5 : ℝ) * a44 + (4/5 : ℝ) * a58
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2837 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a42 : -(h 4) < (-1/9 : ℝ))
    (a44 : -(h 0) < (-6/41 : ℝ))
    (a47 : h 1 ≤ (2/15 : ℝ))
    (a49 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a54 : -(h 3) < (-7/60 : ℝ))
    (a56 : h 0 ≤ (5/34 : ℝ))
    (a57 : -(h 1) < (-3/23 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2838 h delta _ctx _hno a14 a44 f0
  by_cases p1 : h 0 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2839 h delta _ctx _hno a56 f1
  by_cases p2 : h 1 ≤ (3/22 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2840 h delta _ctx _hno a47 f2
  by_cases p3 : h 2 ≤ (3/25 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2841 h delta _ctx _hno a42 a44 a49 a54 a57 f3
  by_cases p4 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2842 h delta _ctx _hno a42 a44 a49 a57 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_2843 h delta _ctx _hno a28 a44 a49 a54 a57 f5
  apply _hno 141
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_2836 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : -(h 1) < (-9/70 : ℝ))
    (a49 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a54 : -(h 3) < (-7/60 : ℝ))
    (a56 : -(h 0) < (-5/34 : ℝ))
    (a62 : -(h 4) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.min + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a33 + (6/29 : ℝ) * a49 + (6/29 : ℝ) * a54 + (4/29 : ℝ) * a56 + (6/29 : ℝ) * a62 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2835 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a56 : -(h 0) < (-5/34 : ℝ))
    (a61 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/7 : ℝ) * a25 + (6/7 : ℝ) * a56 + (1/7 : ℝ) * a61
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2834 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : -(h 1) < (-9/70 : ℝ))
    (a42 : -(h 4) < (-1/9 : ℝ))
    (a49 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a54 : -(h 3) < (-7/60 : ℝ))
    (a56 : -(h 0) < (-5/34 : ℝ))
    (a60 : -(h 2) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a49 + (1/6 : ℝ) * a54 + (1/6 : ℝ) * a56 + (1/6 : ℝ) * a60 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2833 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a49 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a54 : -(h 3) < (-7/60 : ℝ))
    (a56 : -(h 0) < (-5/34 : ℝ))
    (a59 : -(h 1) < (-4/31 : ℝ))
    (a65 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/26 : ℝ) * _ctx.fail1 + (3/104 : ℝ) * a28 + (3/26 : ℝ) * a49 + (21/104 : ℝ) * a54 + (2/13 : ℝ) * a56 + (3/13 : ℝ) * a59 + (3/13 : ℝ) * a65 + (3/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2832 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a56 : -(h 0) < (-5/34 : ℝ))
    (a64 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/7 : ℝ) * a25 + (6/7 : ℝ) * a56 + (1/7 : ℝ) * a64
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2831 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a42 : -(h 4) < (-1/9 : ℝ))
    (a49 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a54 : -(h 3) < (-7/60 : ℝ))
    (a56 : -(h 0) < (-5/34 : ℝ))
    (a59 : -(h 1) < (-4/31 : ℝ))
    (a63 : -(h 2) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a49 + (1/6 : ℝ) * a54 + (1/6 : ℝ) * a56 + (1/6 : ℝ) * a59 + (1/6 : ℝ) * a63 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2830 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a47 : h 1 ≤ (2/15 : ℝ))
    (a62 : -(h 1) < (-3/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a47 + (1 : ℝ) * a62
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2829 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a54 : -(h 3) < (-7/60 : ℝ))
    (a61 : -(h 0) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/7 : ℝ) * a25 + (1/7 : ℝ) * a54 + (6/7 : ℝ) * a61
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2828 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a56 : -(h 0) < (-5/34 : ℝ))
    (a60 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * a14 + (1/5 : ℝ) * a56 + (4/5 : ℝ) * a60
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2827 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a42 : -(h 4) < (-1/9 : ℝ))
    (a47 : h 1 ≤ (2/15 : ℝ))
    (a49 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a54 : -(h 3) < (-7/60 : ℝ))
    (a56 : -(h 0) < (-5/34 : ℝ))
    (a59 : -(h 1) < (-4/31 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2828 h delta _ctx _hno a14 a56 f0
  by_cases p1 : h 0 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2829 h delta _ctx _hno a25 a54 f1
  by_cases p2 : h 1 ≤ (3/22 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2830 h delta _ctx _hno a47 f2
  by_cases p3 : h 2 ≤ (3/25 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2831 h delta _ctx _hno a42 a49 a54 a56 a59 f3
  by_cases p4 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2832 h delta _ctx _hno a25 a56 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_2833 h delta _ctx _hno a28 a49 a54 a56 a59 f5
  apply _hno 141
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_2826 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a51 : h 0 ≤ (4/27 : ℝ))
    (a58 : -(h 0) < (-3/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a51 + (1 : ℝ) * a58
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2825 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a56 : -(h 0) < (-5/34 : ℝ))
    (a57 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * a14 + (1/5 : ℝ) * a56 + (4/5 : ℝ) * a57
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2824 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a33 : -(h 1) < (-9/70 : ℝ))
    (a42 : -(h 4) < (-1/9 : ℝ))
    (a47 : h 1 ≤ (2/15 : ℝ))
    (a49 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a51 : h 0 ≤ (4/27 : ℝ))
    (a54 : -(h 3) < (-7/60 : ℝ))
    (a56 : -(h 0) < (-5/34 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2825 h delta _ctx _hno a14 a56 f0
  by_cases p1 : h 0 ≤ (3/19 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/19 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2826 h delta _ctx _hno a51 f1
  by_cases p2 : h 1 ≤ (4/31 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/31 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2827 h delta _ctx _hno a14 a25 a28 a42 a47 a49 a54 a56 f2
  by_cases p3 : h 2 ≤ (3/25 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2834 h delta _ctx _hno a33 a42 a49 a54 a56 f3
  by_cases p4 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2835 h delta _ctx _hno a25 a56 f4
  by_cases p5 : h 4 ≤ (3/26 : ℝ)
  swap
  · have f5 : -(h 4) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_2836 h delta _ctx _hno a33 a49 a54 a56 f5
  apply _hno 113
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (4/31 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (3/26 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_2823 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a44 : -(h 0) < (-6/41 : ℝ))
    (a55 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * a14 + (1/5 : ℝ) * a44 + (4/5 : ℝ) * a55
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2822 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a33 : -(h 1) < (-9/70 : ℝ))
    (a42 : -(h 4) < (-1/9 : ℝ))
    (a44 : -(h 0) < (-6/41 : ℝ))
    (a47 : h 1 ≤ (2/15 : ℝ))
    (a49 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a51 : h 0 ≤ (4/27 : ℝ))
    (a54 : -(h 3) < (-7/60 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2823 h delta _ctx _hno a14 a44 f0
  by_cases p1 : h 0 ≤ (5/34 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/34 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2824 h delta _ctx _hno a14 a25 a28 a33 a42 a47 a49 a51 a54 f1
  by_cases p2 : h 1 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2837 h delta _ctx _hno a14 a28 a42 a44 a47 a49 a54 p1 f2
  by_cases p3 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2844 h delta _ctx _hno a14 a28 a33 a42 a44 a49 p1 f3
  apply _hno 92
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (5/34 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_2821 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a37 : h 2 ≤ (5/41 : ℝ))
    (a53 : -(h 2) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a37 + (1 : ℝ) * a53
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2820 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a42 : -(h 4) < (-1/9 : ℝ))
    (a44 : -(h 0) < (-6/41 : ℝ))
    (a48 : -(h 3) < (-3/26 : ℝ))
    (a49 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a52 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.min + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a42 + (4/29 : ℝ) * a44 + (6/29 : ℝ) * a48 + (6/29 : ℝ) * a49 + (6/29 : ℝ) * a52 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2819 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a48 : -(h 3) < (-3/26 : ℝ))
    (a51 : -(h 0) < (-4/27 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/7 : ℝ) * a25 + (1/7 : ℝ) * a48 + (6/7 : ℝ) * a51
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2818 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a44 : -(h 0) < (-6/41 : ℝ))
    (a50 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * a14 + (1/5 : ℝ) * a44 + (4/5 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2817 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a33 : -(h 1) < (-9/70 : ℝ))
    (a37 : h 2 ≤ (5/41 : ℝ))
    (a42 : -(h 4) < (-1/9 : ℝ))
    (a44 : -(h 0) < (-6/41 : ℝ))
    (a47 : h 1 ≤ (2/15 : ℝ))
    (a48 : -(h 3) < (-3/26 : ℝ))
    (a49 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2818 h delta _ctx _hno a14 a44 f0
  by_cases p1 : h 0 ≤ (4/27 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/27 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2819 h delta _ctx _hno a25 a48 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2820 h delta _ctx _hno a42 a44 a48 a49 f2
  by_cases p3 : h 2 ≤ (3/23 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2821 h delta _ctx _hno a37 f3
  by_cases p4 : h 3 ≤ (7/60 : ℝ)
  swap
  · have f4 : -(h 3) < (-7/60 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2822 h delta _ctx _hno a14 a25 a28 a33 a42 a44 a47 a49 p1 f4
  by_cases p5 : h 4 ≤ (5/43 : ℝ)
  swap
  · have f5 : -(h 4) < (-5/43 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_2851 h delta _ctx _hno a33 a44 a49 f5
  by_cases p6 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f6 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact upper_node_2852 h delta _ctx _hno a33 a42 a44 a48 a49 f6
  apply _hno 139
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (4/27 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (7/60 : ℝ)) ∧ (h 4 ≤ (5/43 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem upper_node_2816 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a33 : -(h 1) < (-9/70 : ℝ))
    (a37 : h 2 ≤ (5/41 : ℝ))
    (a42 : -(h 4) < (-1/9 : ℝ))
    (a44 : -(h 0) < (-6/41 : ℝ))
    (a47 : h 1 ≤ (2/15 : ℝ))
    (a48 : -(h 3) < (-3/26 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2817 h delta _ctx _hno a14 a25 a28 a33 a37 a42 a44 a47 a48 f0
  by_cases p1 : h 0 ≤ (4/27 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/27 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2853 h delta _ctx _hno a25 a48 f1
  by_cases p2 : h 1 ≤ (6/41 : ℝ)
  swap
  · have f2 : -(h 1) < (-6/41 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2854 h delta _ctx _hno a47 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2855 h delta _ctx _hno a37 f3
  by_cases p4 : h 4 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 4) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2856 h delta _ctx _hno a33 a44 f4
  by_cases p5 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_2857 h delta _ctx _hno a25 a28 a33 a37 a42 a44 a47 a48 p0 p1 f5
  apply _hno 9
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (4/27 : ℝ)) ∧ (h 1 ≤ (6/41 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_2815 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a38 : -(h 3) < (-4/35 : ℝ))
    (a44 : -(h 0) < (-6/41 : ℝ))
    (a47 : -(h 1) < (-2/15 : ℝ))
    (a59 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.lower + (1/23 : ℝ) * _ctx.fail1 + (3/92 : ℝ) * a28 + (21/92 : ℝ) * a38 + (4/23 : ℝ) * a44 + (6/23 : ℝ) * a47 + (6/23 : ℝ) * a59 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2814 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a42 : -(h 4) < (-1/9 : ℝ))
    (a44 : -(h 0) < (-6/41 : ℝ))
    (a47 : -(h 1) < (-2/15 : ℝ))
    (a53 : -(h 5) < (-2/19 : ℝ))
    (a58 : -(h 3) < (-5/43 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.lower + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a42 + (4/29 : ℝ) * a44 + (6/29 : ℝ) * a47 + (6/29 : ℝ) * a53 + (6/29 : ℝ) * a58 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2813 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a38 : -(h 3) < (-4/35 : ℝ))
    (a44 : -(h 0) < (-6/41 : ℝ))
    (a47 : -(h 1) < (-2/15 : ℝ))
    (a63 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.lower + (1/23 : ℝ) * _ctx.fail1 + (3/92 : ℝ) * a28 + (21/92 : ℝ) * a38 + (4/23 : ℝ) * a44 + (6/23 : ℝ) * a47 + (6/23 : ℝ) * a63 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2812 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a42 : -(h 4) < (-1/9 : ℝ))
    (a44 : -(h 0) < (-6/41 : ℝ))
    (a47 : -(h 1) < (-2/15 : ℝ))
    (a53 : -(h 5) < (-2/19 : ℝ))
    (a62 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.lower + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a42 + (4/29 : ℝ) * a44 + (6/29 : ℝ) * a47 + (6/29 : ℝ) * a53 + (6/29 : ℝ) * a62 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2811 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a38 : -(h 3) < (-4/35 : ℝ))
    (a42 : -(h 4) < (-1/9 : ℝ))
    (a44 : -(h 0) < (-6/41 : ℝ))
    (a47 : -(h 1) < (-2/15 : ℝ))
    (a53 : -(h 5) < (-2/19 : ℝ))
    (a61 : -(h 2) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a38 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a44 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * a53 + (1/6 : ℝ) * a61 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2810 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a38 : -(h 3) < (-4/35 : ℝ))
    (a44 : -(h 0) < (-6/41 : ℝ))
    (a53 : -(h 5) < (-2/19 : ℝ))
    (a57 : -(h 2) < (-9/76 : ℝ))
    (a60 : -(h 1) < (-3/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.lower + (1/40 : ℝ) * a28 + (7/40 : ℝ) * a38 + (1/5 : ℝ) * a44 + (1/5 : ℝ) * a53 + (1/5 : ℝ) * a57 + (1/5 : ℝ) * a60 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2809 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a38 : -(h 3) < (-4/35 : ℝ))
    (a59 : -(h 0) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/7 : ℝ) * a25 + (1/7 : ℝ) * a38 + (6/7 : ℝ) * a59
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2808 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a48 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a58 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a48 + (1 : ℝ) * a58
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2807 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a38 : -(h 3) < (-4/35 : ℝ))
    (a42 : -(h 4) < (-1/9 : ℝ))
    (a44 : -(h 0) < (-6/41 : ℝ))
    (a47 : -(h 1) < (-2/15 : ℝ))
    (a48 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a53 : -(h 5) < (-2/19 : ℝ))
    (a57 : -(h 2) < (-9/76 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2808 h delta _ctx _hno a48 f0
  by_cases p1 : h 0 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2809 h delta _ctx _hno a25 a38 f1
  by_cases p2 : h 1 ≤ (3/22 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2810 h delta _ctx _hno a28 a38 a44 a53 a57 f2
  by_cases p3 : h 2 ≤ (3/25 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2811 h delta _ctx _hno a38 a42 a44 a47 a53 f3
  by_cases p4 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2812 h delta _ctx _hno a42 a44 a47 a53 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_2813 h delta _ctx _hno a28 a38 a44 a47 f5
  apply _hno 141
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_2806 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a38 : -(h 3) < (-4/35 : ℝ))
    (a44 : -(h 0) < (-6/41 : ℝ))
    (a53 : -(h 5) < (-2/19 : ℝ))
    (a56 : -(h 1) < (-3/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.lower + (1/23 : ℝ) * _ctx.fail1 + (3/92 : ℝ) * a28 + (21/92 : ℝ) * a38 + (4/23 : ℝ) * a44 + (6/23 : ℝ) * a53 + (6/23 : ℝ) * a56 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2805 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a49 : h 0 ≤ (4/27 : ℝ))
    (a55 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a49 + (1 : ℝ) * a55
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2804 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a38 : -(h 3) < (-4/35 : ℝ))
    (a42 : -(h 4) < (-1/9 : ℝ))
    (a44 : -(h 0) < (-6/41 : ℝ))
    (a47 : -(h 1) < (-2/15 : ℝ))
    (a54 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.min + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a38 + (6/29 : ℝ) * a42 + (4/29 : ℝ) * a44 + (6/29 : ℝ) * a47 + (6/29 : ℝ) * a54 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2803 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a38 : -(h 3) < (-4/35 : ℝ))
    (a42 : -(h 4) < (-1/9 : ℝ))
    (a44 : -(h 0) < (-6/41 : ℝ))
    (a47 : -(h 1) < (-2/15 : ℝ))
    (a48 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a49 : h 0 ≤ (4/27 : ℝ))
    (a53 : -(h 5) < (-2/19 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2804 h delta _ctx _hno a38 a42 a44 a47 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2805 h delta _ctx _hno a49 f1
  by_cases p2 : h 1 ≤ (3/22 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2806 h delta _ctx _hno a28 a38 a44 a53 f2
  by_cases p3 : h 2 ≤ (9/76 : ℝ)
  swap
  · have f3 : -(h 2) < (-9/76 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2807 h delta _ctx _hno a25 a28 a38 a42 a44 a47 a48 a53 f3
  by_cases p4 : h 3 ≤ (5/43 : ℝ)
  swap
  · have f4 : -(h 3) < (-5/43 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2814 h delta _ctx _hno a42 a44 a47 a53 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_2815 h delta _ctx _hno a28 a38 a44 a47 f5
  apply _hno 121
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 2 ≤ (9/76 : ℝ)) ∧ (h 3 ≤ (5/43 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_2802 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a44 : -(h 0) < (-6/41 : ℝ))
    (a47 : -(h 1) < (-2/15 : ℝ))
    (a52 : -(h 4) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.order3 + (6/23 : ℝ) * _ctx.min + (12/23 : ℝ) * _ctx.lower + (1/23 : ℝ) * _ctx.fail1 + (4/23 : ℝ) * a44 + (6/23 : ℝ) * a47 + (12/23 : ℝ) * a52 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2801 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a37 : h 2 ≤ (5/41 : ℝ))
    (a51 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a37 + (1 : ℝ) * a51
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2800 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a36 : h 1 ≤ (3/22 : ℝ))
    (a50 : -(h 1) < (-6/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a36 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2799 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a38 : -(h 3) < (-4/35 : ℝ))
    (a49 : -(h 0) < (-4/27 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/7 : ℝ) * a25 + (1/7 : ℝ) * a38 + (6/7 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2798 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a38 : -(h 3) < (-4/35 : ℝ))
    (a42 : -(h 4) < (-1/9 : ℝ))
    (a44 : -(h 0) < (-6/41 : ℝ))
    (a47 : -(h 1) < (-2/15 : ℝ))
    (a48 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.min + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a38 + (6/29 : ℝ) * a42 + (4/29 : ℝ) * a44 + (6/29 : ℝ) * a47 + (6/29 : ℝ) * a48 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2797 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a36 : h 1 ≤ (3/22 : ℝ))
    (a37 : h 2 ≤ (5/41 : ℝ))
    (a38 : -(h 3) < (-4/35 : ℝ))
    (a42 : -(h 4) < (-1/9 : ℝ))
    (a44 : -(h 0) < (-6/41 : ℝ))
    (a47 : -(h 1) < (-2/15 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2798 h delta _ctx _hno a38 a42 a44 a47 f0
  by_cases p1 : h 0 ≤ (4/27 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/27 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2799 h delta _ctx _hno a25 a38 f1
  by_cases p2 : h 1 ≤ (6/41 : ℝ)
  swap
  · have f2 : -(h 1) < (-6/41 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2800 h delta _ctx _hno a36 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2801 h delta _ctx _hno a37 f3
  by_cases p4 : h 4 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 4) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2802 h delta _ctx _hno a44 a47 f4
  by_cases p5 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_2803 h delta _ctx _hno a25 a28 a38 a42 a44 a47 p0 p1 f5
  apply _hno 9
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (4/27 : ℝ)) ∧ (h 1 ≤ (6/41 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_2796 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a46 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/55 : ℝ) * a20 + (1/55 : ℝ) * a23 + (8/55 : ℝ) * a25 + (54/55 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2795 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a44 : -(h 0) < (-6/41 : ℝ))
    (a45 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * a14 + (1/5 : ℝ) * a44 + (4/5 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2794 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a20 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a33 : -(h 1) < (-9/70 : ℝ))
    (a36 : h 1 ≤ (3/22 : ℝ))
    (a37 : h 2 ≤ (5/41 : ℝ))
    (a38 : -(h 3) < (-4/35 : ℝ))
    (a42 : -(h 4) < (-1/9 : ℝ))
    (a44 : -(h 0) < (-6/41 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2795 h delta _ctx _hno a14 a44 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2796 h delta _ctx _hno a20 a23 a25 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2797 h delta _ctx _hno a25 a28 a36 a37 a38 a42 a44 f2
  by_cases p3 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f3 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2816 h delta _ctx _hno a14 a25 a28 a33 a37 a42 a44 p2 f3
  by_cases p4 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2925 h delta _ctx _hno a33 a38 a42 a44 f4
  apply _hno 19
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_2793 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * a14 + (1/5 : ℝ) * a30 + (4/5 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2792 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a20 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a33 : -(h 1) < (-9/70 : ℝ))
    (a36 : h 1 ≤ (3/22 : ℝ))
    (a37 : h 2 ≤ (5/41 : ℝ))
    (a38 : -(h 3) < (-4/35 : ℝ))
    (a42 : -(h 4) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2793 h delta _ctx _hno a14 a30 f0
  by_cases p1 : h 0 ≤ (6/41 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/41 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2794 h delta _ctx _hno a14 a20 a23 a25 a28 a33 a36 a37 a38 a42 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2926 h delta _ctx _hno a36 f2
  by_cases p3 : h 2 ≤ (4/33 : ℝ)
  swap
  · have f3 : -(h 2) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2927 h delta _ctx _hno a14 a28 a30 a33 a36 a37 a38 a42 p1 f3
  by_cases p4 : h 3 ≤ (3/25 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3038 h delta _ctx _hno a30 a33 a36 a42 p1 p3 f4
  by_cases p5 : h 5 ≤ (2/17 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_3057 h delta _ctx _hno a30 a33 f5
  apply _hno 137
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (6/41 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (4/33 : ℝ)) ∧ (h 3 ≤ (3/25 : ℝ)) ∧ (h 5 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_2791 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a37 : h 2 ≤ (5/41 : ℝ))
    (a41 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a37 + (1 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2790 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a38 : -(h 3) < (-4/35 : ℝ))
    (a40 : -(h 0) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/7 : ℝ) * a25 + (1/7 : ℝ) * a38 + (6/7 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2789 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a39 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * a14 + (1/5 : ℝ) * a30 + (4/5 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2788 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a20 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a33 : -(h 1) < (-9/70 : ℝ))
    (a36 : h 1 ≤ (3/22 : ℝ))
    (a37 : h 2 ≤ (5/41 : ℝ))
    (a38 : -(h 3) < (-4/35 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2789 h delta _ctx _hno a14 a30 f0
  by_cases p1 : h 0 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2790 h delta _ctx _hno a25 a38 f1
  by_cases p2 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2791 h delta _ctx _hno a37 f2
  by_cases p3 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f3 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2792 h delta _ctx _hno a14 a20 a23 a25 a28 a30 a33 a36 a37 a38 f3
  apply _hno 8
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

end RealPinwheel.WeakSevenBandData
