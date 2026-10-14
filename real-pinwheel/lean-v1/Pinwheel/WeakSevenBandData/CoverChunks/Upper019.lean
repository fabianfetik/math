import Pinwheel.WeakSevenBandData.CoverChunks.Upper018

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem upper_node_2787 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a41 : h 3 ≤ (3/26 : ℝ))
    (a46 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a41 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2786 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a37 : -(h 2) < (-5/41 : ℝ))
    (a45 : -(h 1) < (-3/23 : ℝ))
    (a52 : -(h 5) < (-6/53 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/3 : ℝ) * _ctx.order4 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a45 + (1/2 : ℝ) * a52 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2785 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a37 : -(h 2) < (-5/41 : ℝ))
    (a42 : -(h 5) < (-1/9 : ℝ))
    (a45 : -(h 1) < (-3/23 : ℝ))
    (a51 : -(h 4) < (-5/44 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a45 + (1/3 : ℝ) * a51 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2784 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a37 : -(h 2) < (-5/41 : ℝ))
    (a42 : -(h 5) < (-1/9 : ℝ))
    (a45 : -(h 1) < (-3/23 : ℝ))
    (a50 : -(h 3) < (-7/61 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.lower + (1/40 : ℝ) * a28 + (1/5 : ℝ) * a30 + (1/5 : ℝ) * a37 + (1/5 : ℝ) * a42 + (1/5 : ℝ) * a45 + (7/40 : ℝ) * a50 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2783 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a42 : -(h 5) < (-1/9 : ℝ))
    (a49 : -(h 2) < (-3/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/13 : ℝ) * _ctx.order1 + (4/13 : ℝ) * _ctx.lower + (1/13 : ℝ) * _ctx.fail2 + (1/26 : ℝ) * a23 + (7/26 : ℝ) * a42 + (8/13 : ℝ) * a49 + (4/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2782 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a40 : h 1 ≤ (2/15 : ℝ))
    (a48 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a40 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2781 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a37 : -(h 2) < (-5/41 : ℝ))
    (a42 : -(h 5) < (-1/9 : ℝ))
    (a45 : -(h 1) < (-3/23 : ℝ))
    (a47 : -(h 0) < (-25/173 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (8/33 : ℝ) * _ctx.lower + (7/264 : ℝ) * a23 + (1/33 : ℝ) * a28 + (8/33 : ℝ) * a37 + (19/88 : ℝ) * a42 + (8/33 : ℝ) * a45 + (8/33 : ℝ) * a47 + (8/33 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2780 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a37 : -(h 2) < (-5/41 : ℝ))
    (a45 : -(h 1) < (-3/23 : ℝ))
    (a52 : -(h 5) < (-6/53 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/3 : ℝ) * _ctx.order4 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a45 + (1/2 : ℝ) * a52 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2779 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a37 : -(h 2) < (-5/41 : ℝ))
    (a42 : -(h 5) < (-1/9 : ℝ))
    (a45 : -(h 1) < (-3/23 : ℝ))
    (a51 : -(h 3) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.lower + (1/40 : ℝ) * a28 + (1/5 : ℝ) * a30 + (1/5 : ℝ) * a37 + (1/5 : ℝ) * a42 + (1/5 : ℝ) * a45 + (7/40 : ℝ) * a51 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2778 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a42 : -(h 5) < (-1/9 : ℝ))
    (a45 : -(h 1) < (-3/23 : ℝ))
    (a50 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (8/33 : ℝ) * _ctx.lower + (7/264 : ℝ) * a23 + (1/33 : ℝ) * a28 + (8/33 : ℝ) * a30 + (19/88 : ℝ) * a42 + (8/33 : ℝ) * a45 + (8/33 : ℝ) * a50 + (8/33 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2777 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a40 : h 1 ≤ (2/15 : ℝ))
    (a49 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a40 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2776 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a37 : -(h 2) < (-5/41 : ℝ))
    (a42 : -(h 5) < (-1/9 : ℝ))
    (a45 : -(h 1) < (-3/23 : ℝ))
    (a48 : -(h 0) < (-8/55 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (8/33 : ℝ) * _ctx.lower + (7/264 : ℝ) * a23 + (1/33 : ℝ) * a28 + (8/33 : ℝ) * a37 + (19/88 : ℝ) * a42 + (8/33 : ℝ) * a45 + (8/33 : ℝ) * a48 + (8/33 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2775 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a47 : ((-2 : ℝ) * (delta)) < (-7/31 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * a14 + (1/5 : ℝ) * a30 + (4/5 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2774 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a37 : -(h 2) < (-5/41 : ℝ))
    (a40 : h 1 ≤ (2/15 : ℝ))
    (a42 : -(h 5) < (-1/9 : ℝ))
    (a45 : -(h 1) < (-3/23 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/31 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/31 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2775 h delta _ctx _hno a14 a30 f0
  by_cases p1 : h 0 ≤ (8/55 : ℝ)
  swap
  · have f1 : -(h 0) < (-8/55 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2776 h delta _ctx _hno a23 a28 a37 a42 a45 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2777 h delta _ctx _hno a40 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2778 h delta _ctx _hno a23 a28 a30 a42 a45 f3
  by_cases p4 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2779 h delta _ctx _hno a28 a30 a37 a42 a45 f4
  by_cases p5 : h 5 ≤ (6/53 : ℝ)
  swap
  · have f5 : -(h 5) < (-6/53 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_2780 h delta _ctx _hno a30 a37 a45 f5
  apply _hno 39
  change (((2 : ℝ) * (delta)) ≤ (7/31 : ℝ)) ∧ (h 0 ≤ (8/55 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (6/53 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_2773 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a37 : -(h 2) < (-5/41 : ℝ))
    (a40 : h 1 ≤ (2/15 : ℝ))
    (a42 : -(h 5) < (-1/9 : ℝ))
    (a45 : -(h 1) < (-3/23 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2774 h delta _ctx _hno a14 a23 a28 a30 a37 a40 a42 a45
  by_cases p1 : h 0 ≤ (25/173 : ℝ)
  swap
  · have f1 : -(h 0) < (-25/173 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2781 h delta _ctx _hno a23 a28 a37 a42 a45 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2782 h delta _ctx _hno a40 f2
  by_cases p3 : h 2 ≤ (3/22 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2783 h delta _ctx _hno a23 a42 f3
  by_cases p4 : h 3 ≤ (7/61 : ℝ)
  swap
  · have f4 : -(h 3) < (-7/61 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2784 h delta _ctx _hno a28 a30 a37 a42 a45 f4
  by_cases p5 : h 4 ≤ (5/44 : ℝ)
  swap
  · have f5 : -(h 4) < (-5/44 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_2785 h delta _ctx _hno a30 a37 a42 a45 f5
  by_cases p6 : h 5 ≤ (6/53 : ℝ)
  swap
  · have f6 : -(h 5) < (-6/53 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact upper_node_2786 h delta _ctx _hno a30 a37 a45 f6
  apply _hno 27
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (25/173 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (3/22 : ℝ)) ∧ (h 3 ≤ (7/61 : ℝ)) ∧ (h 4 ≤ (5/44 : ℝ)) ∧ (h 5 ≤ (6/53 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem upper_node_2772 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a33 : -(h 1) < (-9/70 : ℝ))
    (a37 : -(h 2) < (-5/41 : ℝ))
    (a42 : -(h 5) < (-1/9 : ℝ))
    (a44 : -(h 0) < (-5/34 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (8/33 : ℝ) * _ctx.lower + (7/264 : ℝ) * a23 + (1/33 : ℝ) * a28 + (8/33 : ℝ) * a33 + (8/33 : ℝ) * a37 + (19/88 : ℝ) * a42 + (8/33 : ℝ) * a44 + (8/33 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2771 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * a14 + (1/5 : ℝ) * a30 + (4/5 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2770 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a33 : -(h 1) < (-9/70 : ℝ))
    (a37 : -(h 2) < (-5/41 : ℝ))
    (a40 : h 1 ≤ (2/15 : ℝ))
    (a41 : h 3 ≤ (3/26 : ℝ))
    (a42 : -(h 5) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2771 h delta _ctx _hno a14 a30 f0
  by_cases p1 : h 0 ≤ (5/34 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/34 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2772 h delta _ctx _hno a23 a28 a33 a37 a42 f1
  by_cases p2 : h 1 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2773 h delta _ctx _hno a14 a23 a28 a30 a37 a40 a42 f2
  by_cases p3 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2787 h delta _ctx _hno a41 f3
  apply _hno 92
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (5/34 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_2769 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a33 : -(h 1) < (-9/70 : ℝ))
    (a37 : -(h 2) < (-5/41 : ℝ))
    (a45 : -(h 4) < (-1/9 : ℝ))
    (a49 : -(h 3) < (-2/17 : ℝ))
    (a61 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a49 + (1/6 : ℝ) * a61 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2768 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a33 : -(h 1) < (-9/70 : ℝ))
    (a37 : -(h 2) < (-5/41 : ℝ))
    (a49 : -(h 3) < (-2/17 : ℝ))
    (a55 : -(h 5) < (-2/19 : ℝ))
    (a60 : -(h 4) < (-6/53 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a49 + (1/6 : ℝ) * a55 + (1/6 : ℝ) * a60 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2767 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a33 : -(h 1) < (-9/70 : ℝ))
    (a45 : -(h 4) < (-1/9 : ℝ))
    (a49 : -(h 3) < (-2/17 : ℝ))
    (a55 : -(h 5) < (-2/19 : ℝ))
    (a59 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a49 + (1/6 : ℝ) * a55 + (1/6 : ℝ) * a59 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2766 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a37 : -(h 2) < (-5/41 : ℝ))
    (a45 : -(h 4) < (-1/9 : ℝ))
    (a49 : -(h 3) < (-2/17 : ℝ))
    (a55 : -(h 5) < (-2/19 : ℝ))
    (a58 : -(h 1) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a49 + (1/6 : ℝ) * a55 + (1/6 : ℝ) * a58 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2765 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : -(h 1) < (-9/70 : ℝ))
    (a37 : -(h 2) < (-5/41 : ℝ))
    (a45 : -(h 4) < (-1/9 : ℝ))
    (a49 : -(h 3) < (-2/17 : ℝ))
    (a55 : -(h 5) < (-2/19 : ℝ))
    (a57 : -(h 0) < (-9/62 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a49 + (1/6 : ℝ) * a55 + (1/6 : ℝ) * a57 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2764 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a50 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a56 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a50 + (1 : ℝ) * a56
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2763 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a33 : -(h 1) < (-9/70 : ℝ))
    (a37 : -(h 2) < (-5/41 : ℝ))
    (a45 : -(h 4) < (-1/9 : ℝ))
    (a49 : -(h 3) < (-2/17 : ℝ))
    (a50 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a55 : -(h 5) < (-2/19 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2764 h delta _ctx _hno a50 f0
  by_cases p1 : h 0 ≤ (9/62 : ℝ)
  swap
  · have f1 : -(h 0) < (-9/62 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2765 h delta _ctx _hno a33 a37 a45 a49 a55 f1
  by_cases p2 : h 1 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2766 h delta _ctx _hno a30 a37 a45 a49 a55 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2767 h delta _ctx _hno a30 a33 a45 a49 a55 f3
  by_cases p4 : h 4 ≤ (6/53 : ℝ)
  swap
  · have f4 : -(h 4) < (-6/53 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2768 h delta _ctx _hno a30 a33 a37 a49 a55 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_2769 h delta _ctx _hno a30 a33 a37 a45 a49 f5
  apply _hno 140
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (9/62 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (6/53 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_2762 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a33 : -(h 1) < (-9/70 : ℝ))
    (a37 : -(h 2) < (-5/41 : ℝ))
    (a54 : -(h 4) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a30 + (1/5 : ℝ) * a33 + (1/5 : ℝ) * a37 + (2/5 : ℝ) * a54 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2761 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a33 : -(h 1) < (-9/70 : ℝ))
    (a45 : -(h 4) < (-1/9 : ℝ))
    (a49 : -(h 3) < (-2/17 : ℝ))
    (a53 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a30 + (1/5 : ℝ) * a33 + (1/5 : ℝ) * a45 + (1/5 : ℝ) * a49 + (1/5 : ℝ) * a53 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2760 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a48 : h 1 ≤ (3/23 : ℝ))
    (a52 : -(h 1) < (-6/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a48 + (1 : ℝ) * a52
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2759 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a47 : h 0 ≤ (5/34 : ℝ))
    (a51 : -(h 0) < (-4/27 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a47 + (1 : ℝ) * a51
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2758 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a33 : -(h 1) < (-9/70 : ℝ))
    (a37 : -(h 2) < (-5/41 : ℝ))
    (a45 : -(h 4) < (-1/9 : ℝ))
    (a49 : -(h 3) < (-2/17 : ℝ))
    (a50 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a56 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * a30 + (2/13 : ℝ) * a33 + (2/13 : ℝ) * a37 + (2/13 : ℝ) * a45 + (2/13 : ℝ) * a49 + (1/13 : ℝ) * a50 + (2/13 : ℝ) * a56 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2757 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a33 : -(h 1) < (-9/70 : ℝ))
    (a37 : -(h 2) < (-5/41 : ℝ))
    (a49 : -(h 3) < (-2/17 : ℝ))
    (a50 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a55 : -(h 4) < (-6/53 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a49 + (1/6 : ℝ) * a50 + (1/6 : ℝ) * a55 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2756 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a33 : -(h 1) < (-9/70 : ℝ))
    (a45 : -(h 4) < (-1/9 : ℝ))
    (a49 : -(h 3) < (-2/17 : ℝ))
    (a50 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a54 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a49 + (1/6 : ℝ) * a50 + (1/6 : ℝ) * a54 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2755 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a37 : -(h 2) < (-5/41 : ℝ))
    (a45 : -(h 4) < (-1/9 : ℝ))
    (a49 : -(h 3) < (-2/17 : ℝ))
    (a50 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a53 : -(h 1) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a49 + (1/6 : ℝ) * a50 + (1/6 : ℝ) * a53 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2754 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : -(h 1) < (-9/70 : ℝ))
    (a37 : -(h 2) < (-5/41 : ℝ))
    (a45 : -(h 4) < (-1/9 : ℝ))
    (a49 : -(h 3) < (-2/17 : ℝ))
    (a50 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a52 : -(h 0) < (-9/62 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a49 + (1/6 : ℝ) * a50 + (1/6 : ℝ) * a52 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2753 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a33 : -(h 1) < (-9/70 : ℝ))
    (a37 : -(h 2) < (-5/41 : ℝ))
    (a45 : -(h 4) < (-1/9 : ℝ))
    (a49 : -(h 3) < (-2/17 : ℝ))
    (a51 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a49 + (1/6 : ℝ) * a51 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2752 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a33 : -(h 1) < (-9/70 : ℝ))
    (a37 : -(h 2) < (-5/41 : ℝ))
    (a45 : -(h 4) < (-1/9 : ℝ))
    (a49 : -(h 3) < (-2/17 : ℝ))
    (a50 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2753 h delta _ctx _hno a30 a33 a37 a45 a49 f0
  by_cases p1 : h 0 ≤ (9/62 : ℝ)
  swap
  · have f1 : -(h 0) < (-9/62 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2754 h delta _ctx _hno a33 a37 a45 a49 a50 f1
  by_cases p2 : h 1 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2755 h delta _ctx _hno a30 a37 a45 a49 a50 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2756 h delta _ctx _hno a30 a33 a45 a49 a50 f3
  by_cases p4 : h 4 ≤ (6/53 : ℝ)
  swap
  · have f4 : -(h 4) < (-6/53 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2757 h delta _ctx _hno a30 a33 a37 a49 a50 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_2758 h delta _ctx _hno a30 a33 a37 a45 a49 a50 f5
  apply _hno 140
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (9/62 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (6/53 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_2751 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a33 : -(h 1) < (-9/70 : ℝ))
    (a37 : -(h 2) < (-5/41 : ℝ))
    (a45 : -(h 4) < (-1/9 : ℝ))
    (a47 : h 0 ≤ (5/34 : ℝ))
    (a48 : h 1 ≤ (3/23 : ℝ))
    (a49 : -(h 3) < (-2/17 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2752 h delta _ctx _hno a30 a33 a37 a45 a49 f0
  by_cases p1 : h 0 ≤ (4/27 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/27 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2759 h delta _ctx _hno a47 f1
  by_cases p2 : h 1 ≤ (6/41 : ℝ)
  swap
  · have f2 : -(h 1) < (-6/41 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2760 h delta _ctx _hno a48 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2761 h delta _ctx _hno a30 a33 a45 a49 f3
  by_cases p4 : h 4 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 4) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2762 h delta _ctx _hno a30 a33 a37 f4
  by_cases p5 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_2763 h delta _ctx _hno a30 a33 a37 a45 a49 p0 f5
  apply _hno 9
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (4/27 : ℝ)) ∧ (h 1 ≤ (6/41 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_2750 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a37 : -(h 2) < (-5/41 : ℝ))
    (a41 : -(h 3) < (-3/26 : ℝ))
    (a48 : -(h 1) < (-3/23 : ℝ))
    (a61 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.lower + (1/40 : ℝ) * a28 + (1/5 : ℝ) * a30 + (1/5 : ℝ) * a37 + (7/40 : ℝ) * a41 + (1/5 : ℝ) * a48 + (1/5 : ℝ) * a61 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2749 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a37 : -(h 2) < (-5/41 : ℝ))
    (a48 : -(h 1) < (-3/23 : ℝ))
    (a54 : -(h 5) < (-2/19 : ℝ))
    (a60 : -(h 4) < (-5/43 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a48 + (1/6 : ℝ) * a54 + (1/3 : ℝ) * a60 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2748 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a37 : -(h 2) < (-5/41 : ℝ))
    (a48 : -(h 1) < (-3/23 : ℝ))
    (a59 : -(h 3) < (-7/60 : ℝ))
    (a66 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.lower + (1/40 : ℝ) * a28 + (1/5 : ℝ) * a30 + (1/5 : ℝ) * a37 + (1/5 : ℝ) * a48 + (7/40 : ℝ) * a59 + (1/5 : ℝ) * a66 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2747 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a37 : -(h 2) < (-5/41 : ℝ))
    (a48 : -(h 1) < (-3/23 : ℝ))
    (a54 : -(h 5) < (-2/19 : ℝ))
    (a59 : -(h 3) < (-7/60 : ℝ))
    (a65 : -(h 4) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a48 + (1/6 : ℝ) * a54 + (1/6 : ℝ) * a59 + (1/6 : ℝ) * a65 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2746 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a37 : -(h 2) < (-5/41 : ℝ))
    (a45 : -(h 4) < (-1/9 : ℝ))
    (a48 : -(h 1) < (-3/23 : ℝ))
    (a54 : -(h 5) < (-2/19 : ℝ))
    (a64 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a48 + (1/6 : ℝ) * a54 + (1/6 : ℝ) * a64 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2745 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a45 : -(h 4) < (-1/9 : ℝ))
    (a48 : -(h 1) < (-3/23 : ℝ))
    (a54 : -(h 5) < (-2/19 : ℝ))
    (a59 : -(h 3) < (-7/60 : ℝ))
    (a63 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a48 + (1/6 : ℝ) * a54 + (1/6 : ℝ) * a59 + (1/6 : ℝ) * a63 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2744 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a40 : h 1 ≤ (2/15 : ℝ))
    (a62 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a40 + (1 : ℝ) * a62
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2743 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a37 : -(h 2) < (-5/41 : ℝ))
    (a45 : -(h 4) < (-1/9 : ℝ))
    (a48 : -(h 1) < (-3/23 : ℝ))
    (a54 : -(h 5) < (-2/19 : ℝ))
    (a59 : -(h 3) < (-7/60 : ℝ))
    (a61 : -(h 0) < (-22/151 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a48 + (1/6 : ℝ) * a54 + (1/6 : ℝ) * a59 + (1/6 : ℝ) * a61 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2742 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a49 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a60 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a49 + (1 : ℝ) * a60
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2741 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a37 : -(h 2) < (-5/41 : ℝ))
    (a40 : h 1 ≤ (2/15 : ℝ))
    (a45 : -(h 4) < (-1/9 : ℝ))
    (a48 : -(h 1) < (-3/23 : ℝ))
    (a49 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a54 : -(h 5) < (-2/19 : ℝ))
    (a59 : -(h 3) < (-7/60 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2742 h delta _ctx _hno a49 f0
  by_cases p1 : h 0 ≤ (22/151 : ℝ)
  swap
  · have f1 : -(h 0) < (-22/151 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2743 h delta _ctx _hno a37 a45 a48 a54 a59 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2744 h delta _ctx _hno a40 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2745 h delta _ctx _hno a30 a45 a48 a54 a59 f3
  by_cases p4 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2746 h delta _ctx _hno a30 a37 a45 a48 a54 f4
  by_cases p5 : h 4 ≤ (4/35 : ℝ)
  swap
  · have f5 : -(h 4) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_2747 h delta _ctx _hno a30 a37 a48 a54 a59 f5
  by_cases p6 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f6 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact upper_node_2748 h delta _ctx _hno a28 a30 a37 a48 a59 f6
  apply _hno 138
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (22/151 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem upper_node_2740 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a44 : h 2 ≤ (1/8 : ℝ))
    (a58 : -(h 2) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a44 + (1 : ℝ) * a58
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2739 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a37 : -(h 2) < (-5/41 : ℝ))
    (a41 : -(h 3) < (-3/26 : ℝ))
    (a45 : -(h 4) < (-1/9 : ℝ))
    (a54 : -(h 5) < (-2/19 : ℝ))
    (a57 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a41 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a54 + (1/6 : ℝ) * a57 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2738 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a47 : h 0 ≤ (5/34 : ℝ))
    (a56 : -(h 0) < (-4/27 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a47 + (1 : ℝ) * a56
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2737 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a49 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a55 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a49 + (1 : ℝ) * a55
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2736 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a37 : -(h 2) < (-5/41 : ℝ))
    (a40 : h 1 ≤ (2/15 : ℝ))
    (a41 : -(h 3) < (-3/26 : ℝ))
    (a44 : h 2 ≤ (1/8 : ℝ))
    (a45 : -(h 4) < (-1/9 : ℝ))
    (a47 : h 0 ≤ (5/34 : ℝ))
    (a48 : -(h 1) < (-3/23 : ℝ))
    (a49 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a54 : -(h 5) < (-2/19 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2737 h delta _ctx _hno a49 f0
  by_cases p1 : h 0 ≤ (4/27 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/27 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2738 h delta _ctx _hno a47 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2739 h delta _ctx _hno a30 a37 a41 a45 a54 f2
  by_cases p3 : h 2 ≤ (3/23 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2740 h delta _ctx _hno a44 f3
  by_cases p4 : h 3 ≤ (7/60 : ℝ)
  swap
  · have f4 : -(h 3) < (-7/60 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2741 h delta _ctx _hno a28 a30 a37 a40 a45 a48 a49 a54 f4
  by_cases p5 : h 4 ≤ (5/43 : ℝ)
  swap
  · have f5 : -(h 4) < (-5/43 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_2749 h delta _ctx _hno a30 a37 a48 a54 f5
  by_cases p6 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f6 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact upper_node_2750 h delta _ctx _hno a28 a30 a37 a41 a48 f6
  apply _hno 139
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (4/27 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (7/60 : ℝ)) ∧ (h 4 ≤ (5/43 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem upper_node_2735 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a37 : -(h 2) < (-5/41 : ℝ))
    (a48 : -(h 1) < (-3/23 : ℝ))
    (a53 : -(h 4) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a30 + (1/5 : ℝ) * a37 + (1/5 : ℝ) * a48 + (2/5 : ℝ) * a53 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2734 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a44 : h 2 ≤ (1/8 : ℝ))
    (a52 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a44 + (1 : ℝ) * a52
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2733 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a40 : h 1 ≤ (2/15 : ℝ))
    (a51 : -(h 1) < (-6/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a40 + (1 : ℝ) * a51
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2732 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a47 : h 0 ≤ (5/34 : ℝ))
    (a50 : -(h 0) < (-4/27 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a47 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2731 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a37 : -(h 2) < (-5/41 : ℝ))
    (a41 : -(h 3) < (-3/26 : ℝ))
    (a48 : -(h 1) < (-3/23 : ℝ))
    (a49 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a56 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/44 : ℝ) * a28 + (2/11 : ℝ) * a30 + (2/11 : ℝ) * a37 + (7/44 : ℝ) * a41 + (2/11 : ℝ) * a48 + (1/11 : ℝ) * a49 + (2/11 : ℝ) * a56 + (2/11 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2730 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a37 : -(h 2) < (-5/41 : ℝ))
    (a48 : -(h 1) < (-3/23 : ℝ))
    (a49 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a55 : -(h 4) < (-5/43 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a48 + (1/6 : ℝ) * a49 + (1/3 : ℝ) * a55 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2729 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a37 : -(h 2) < (-5/41 : ℝ))
    (a45 : -(h 4) < (-1/9 : ℝ))
    (a48 : -(h 1) < (-3/23 : ℝ))
    (a49 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a54 : -(h 3) < (-7/60 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a48 + (1/6 : ℝ) * a49 + (1/6 : ℝ) * a54 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2728 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a44 : h 2 ≤ (1/8 : ℝ))
    (a53 : -(h 2) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a44 + (1 : ℝ) * a53
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2727 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a37 : -(h 2) < (-5/41 : ℝ))
    (a41 : -(h 3) < (-3/26 : ℝ))
    (a45 : -(h 4) < (-1/9 : ℝ))
    (a49 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a52 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a41 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a49 + (1/6 : ℝ) * a52 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2726 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a47 : h 0 ≤ (5/34 : ℝ))
    (a51 : -(h 0) < (-4/27 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a47 + (1 : ℝ) * a51
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2725 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a50 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * a14 + (1/5 : ℝ) * a30 + (4/5 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2724 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a37 : -(h 2) < (-5/41 : ℝ))
    (a41 : -(h 3) < (-3/26 : ℝ))
    (a44 : h 2 ≤ (1/8 : ℝ))
    (a45 : -(h 4) < (-1/9 : ℝ))
    (a47 : h 0 ≤ (5/34 : ℝ))
    (a48 : -(h 1) < (-3/23 : ℝ))
    (a49 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2725 h delta _ctx _hno a14 a30 f0
  by_cases p1 : h 0 ≤ (4/27 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/27 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2726 h delta _ctx _hno a47 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2727 h delta _ctx _hno a30 a37 a41 a45 a49 f2
  by_cases p3 : h 2 ≤ (3/23 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2728 h delta _ctx _hno a44 f3
  by_cases p4 : h 3 ≤ (7/60 : ℝ)
  swap
  · have f4 : -(h 3) < (-7/60 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2729 h delta _ctx _hno a30 a37 a45 a48 a49 f4
  by_cases p5 : h 4 ≤ (5/43 : ℝ)
  swap
  · have f5 : -(h 4) < (-5/43 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_2730 h delta _ctx _hno a30 a37 a48 a49 f5
  by_cases p6 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f6 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact upper_node_2731 h delta _ctx _hno a28 a30 a37 a41 a48 a49 f6
  apply _hno 139
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (4/27 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (7/60 : ℝ)) ∧ (h 4 ≤ (5/43 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem upper_node_2723 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a37 : -(h 2) < (-5/41 : ℝ))
    (a40 : h 1 ≤ (2/15 : ℝ))
    (a41 : -(h 3) < (-3/26 : ℝ))
    (a44 : h 2 ≤ (1/8 : ℝ))
    (a45 : -(h 4) < (-1/9 : ℝ))
    (a47 : h 0 ≤ (5/34 : ℝ))
    (a48 : -(h 1) < (-3/23 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2724 h delta _ctx _hno a14 a28 a30 a37 a41 a44 a45 a47 a48 f0
  by_cases p1 : h 0 ≤ (4/27 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/27 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2732 h delta _ctx _hno a47 f1
  by_cases p2 : h 1 ≤ (6/41 : ℝ)
  swap
  · have f2 : -(h 1) < (-6/41 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2733 h delta _ctx _hno a40 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2734 h delta _ctx _hno a44 f3
  by_cases p4 : h 4 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 4) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2735 h delta _ctx _hno a30 a37 a48 f4
  by_cases p5 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_2736 h delta _ctx _hno a28 a30 a37 a40 a41 a44 a45 a47 a48 p0 f5
  apply _hno 9
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (4/27 : ℝ)) ∧ (h 1 ≤ (6/41 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_2722 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : -(h 1) < (-9/70 : ℝ))
    (a37 : -(h 2) < (-5/41 : ℝ))
    (a41 : -(h 3) < (-3/26 : ℝ))
    (a45 : -(h 4) < (-1/9 : ℝ))
    (a47 : -(h 0) < (-5/34 : ℝ))
    (a53 : -(h 5) < (-2/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a41 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * a53 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2721 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : -(h 1) < (-9/70 : ℝ))
    (a37 : -(h 2) < (-5/41 : ℝ))
    (a47 : -(h 0) < (-5/34 : ℝ))
    (a52 : -(h 4) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a33 + (1/5 : ℝ) * a37 + (1/5 : ℝ) * a47 + (2/5 : ℝ) * a52 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2720 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : -(h 1) < (-9/70 : ℝ))
    (a41 : -(h 3) < (-3/26 : ℝ))
    (a45 : -(h 4) < (-1/9 : ℝ))
    (a47 : -(h 0) < (-5/34 : ℝ))
    (a51 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a33 + (1/5 : ℝ) * a41 + (1/5 : ℝ) * a45 + (1/5 : ℝ) * a47 + (1/5 : ℝ) * a51 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2719 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a40 : h 1 ≤ (2/15 : ℝ))
    (a50 : -(h 1) < (-6/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a40 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2718 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a41 : -(h 3) < (-3/26 : ℝ))
    (a49 : -(h 0) < (-4/27 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/7 : ℝ) * a25 + (1/7 : ℝ) * a41 + (6/7 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2717 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : -(h 1) < (-9/70 : ℝ))
    (a37 : -(h 2) < (-5/41 : ℝ))
    (a41 : -(h 3) < (-3/26 : ℝ))
    (a45 : -(h 4) < (-1/9 : ℝ))
    (a47 : -(h 0) < (-5/34 : ℝ))
    (a48 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a41 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * a48 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2716 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a33 : -(h 1) < (-9/70 : ℝ))
    (a37 : -(h 2) < (-5/41 : ℝ))
    (a40 : h 1 ≤ (2/15 : ℝ))
    (a41 : -(h 3) < (-3/26 : ℝ))
    (a45 : -(h 4) < (-1/9 : ℝ))
    (a47 : -(h 0) < (-5/34 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2717 h delta _ctx _hno a33 a37 a41 a45 a47 f0
  by_cases p1 : h 0 ≤ (4/27 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/27 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2718 h delta _ctx _hno a25 a41 f1
  by_cases p2 : h 1 ≤ (6/41 : ℝ)
  swap
  · have f2 : -(h 1) < (-6/41 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2719 h delta _ctx _hno a40 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2720 h delta _ctx _hno a33 a41 a45 a47 f3
  by_cases p4 : h 4 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 4) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2721 h delta _ctx _hno a33 a37 a47 f4
  by_cases p5 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_2722 h delta _ctx _hno a33 a37 a41 a45 a47 f5
  apply _hno 9
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (4/27 : ℝ)) ∧ (h 1 ≤ (6/41 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_2715 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a46 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * a14 + (1/5 : ℝ) * a30 + (4/5 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2714 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a33 : -(h 1) < (-9/70 : ℝ))
    (a37 : -(h 2) < (-5/41 : ℝ))
    (a40 : h 1 ≤ (2/15 : ℝ))
    (a41 : -(h 3) < (-3/26 : ℝ))
    (a44 : h 2 ≤ (1/8 : ℝ))
    (a45 : -(h 4) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2715 h delta _ctx _hno a14 a30 f0
  by_cases p1 : h 0 ≤ (5/34 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/34 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2716 h delta _ctx _hno a25 a33 a37 a40 a41 a45 f1
  by_cases p2 : h 1 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2723 h delta _ctx _hno a14 a28 a30 a37 a40 a41 a44 a45 p1 f2
  by_cases p3 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2751 h delta _ctx _hno a30 a33 a37 a45 p1 p2 f3
  apply _hno 92
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (5/34 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_2713 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a33 : -(h 1) < (-9/70 : ℝ))
    (a44 : -(h 2) < (-1/8 : ℝ))
    (a49 : -(h 4) < (-1/9 : ℝ))
    (a53 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a30 + (1/5 : ℝ) * a33 + (1/5 : ℝ) * a44 + (1/5 : ℝ) * a49 + (1/5 : ℝ) * a53 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2712 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a47 : h 1 ≤ (7/54 : ℝ))
    (a52 : -(h 1) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a47 + (1 : ℝ) * a52
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2711 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : -(h 1) < (-9/70 : ℝ))
    (a41 : -(h 3) < (-3/26 : ℝ))
    (a44 : -(h 2) < (-1/8 : ℝ))
    (a49 : -(h 4) < (-1/9 : ℝ))
    (a51 : -(h 0) < (-5/34 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a33 + (1/5 : ℝ) * a41 + (1/5 : ℝ) * a44 + (1/5 : ℝ) * a49 + (1/5 : ℝ) * a51 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2710 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a45 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a50 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a45 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2709 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a33 : -(h 1) < (-9/70 : ℝ))
    (a41 : -(h 3) < (-3/26 : ℝ))
    (a44 : -(h 2) < (-1/8 : ℝ))
    (a45 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a47 : h 1 ≤ (7/54 : ℝ))
    (a49 : -(h 4) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2710 h delta _ctx _hno a45 f0
  by_cases p1 : h 0 ≤ (5/34 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/34 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2711 h delta _ctx _hno a33 a41 a44 a49 f1
  by_cases p2 : h 1 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2712 h delta _ctx _hno a47 f2
  by_cases p3 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2713 h delta _ctx _hno a30 a33 a44 a49 f3
  apply _hno 92
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (5/34 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_2708 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a33 : -(h 1) < (-9/70 : ℝ))
    (a44 : -(h 2) < (-1/8 : ℝ))
    (a48 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.min + (1/2 : ℝ) * _ctx.lower + (1/32 : ℝ) * a28 + (1/4 : ℝ) * a30 + (1/4 : ℝ) * a33 + (1/4 : ℝ) * a44 + (7/32 : ℝ) * a48 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

end RealPinwheel.WeakSevenBandData
