import Pinwheel.WeakSevenBandData.CoverChunks.Upper043

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem upper_node_787 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a16 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a21 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a31 : -(h 1) < (-9/70 : ℝ))
    (a35 : -(h 3) < (-3/26 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_788 h delta _ctx _hno a21 a28 a31 a35 f0
  by_cases p1 : h 0 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_789 h delta _ctx _hno a14 a16 f1
  by_cases p2 : h 1 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_790 h delta _ctx _hno a14 a21 a28 a35 f2
  by_cases p3 : h 2 ≤ (33/278 : ℝ)
  swap
  · have f3 : -(h 2) < (-33/278 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_791 h delta _ctx _hno a14 a21 a28 a31 a35 f3
  by_cases p4 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_792 h delta _ctx _hno a14 a21 a28 a31 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_793 h delta _ctx _hno a14 a21 a28 a31 a35 f5
  apply _hno 91
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 2 ≤ (33/278 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_786 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a21 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a34 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2042/5983 : ℝ) * _ctx.min + (385/5983 : ℝ) * _ctx.fail1 + (544/5983 : ℝ) * a14 + (268/5983 : ℝ) * a19 + (166/5983 : ℝ) * a21 + (2310/5983 : ℝ) * a28 + (2310/5983 : ℝ) * a34 + (2310/5983 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_785 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a16 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a33 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/48 : ℝ) * a14 + (1/6 : ℝ) * a16 + (47/48 : ℝ) * a33
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_784 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a22 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a32 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a22 + (1 : ℝ) * a32
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_783 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a16 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a21 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a22 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a31 : -(h 1) < (-9/70 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_784 h delta _ctx _hno a22 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_785 h delta _ctx _hno a14 a16 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_786 h delta _ctx _hno a14 a19 a21 a28 f2
  by_cases p3 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f3 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_787 h delta _ctx _hno a14 a16 a21 a28 a31 f3
  by_cases p4 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_794 h delta _ctx _hno a14 a19 a21 a28 a31 f4
  apply _hno 19
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_782 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a16 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a30 : -(h 0) < (-7/45 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/48 : ℝ) * a14 + (1/6 : ℝ) * a16 + (47/48 : ℝ) * a30
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_781 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a22 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a29 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a22 + (1 : ℝ) * a29
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_780 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a16 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a21 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a22 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a24 : -(h 1) < (-1/8 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_781 h delta _ctx _hno a22 f0
  by_cases p1 : h 0 ≤ (7/45 : ℝ)
  swap
  · have f1 : -(h 0) < (-7/45 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_782 h delta _ctx _hno a14 a16 f1
  by_cases p2 : h 1 ≤ (9/70 : ℝ)
  swap
  · have f2 : -(h 1) < (-9/70 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_783 h delta _ctx _hno a14 a16 a19 a21 a22 a28 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_795 h delta _ctx _hno a14 a19 a21 a24 a28 f3
  by_cases p4 : h 4 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 4) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_796 h delta _ctx _hno a14 a16 a21 a22 a24 p2 f4
  apply _hno 55
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (7/45 : ℝ)) ∧ (h 1 ≤ (9/70 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (4/35 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_779 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a21 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a24 : -(h 1) < (-1/8 : ℝ))
    (a27 : -(h 2) < (-1/8 : ℝ))
    (a32 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (49/191 : ℝ) * _ctx.min + (13/191 : ℝ) * a14 + (6/191 : ℝ) * a19 + (7/191 : ℝ) * a21 + (55/191 : ℝ) * a24 + (55/191 : ℝ) * a27 + (55/191 : ℝ) * a32 + (55/191 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_778 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a21 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a27 : -(h 2) < (-1/8 : ℝ))
    (a31 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (8/27 : ℝ) * _ctx.order1 + (8/27 : ℝ) * _ctx.order4 + (16/27 : ℝ) * _ctx.min + (1/9 : ℝ) * a14 + (5/162 : ℝ) * a21 + (16/27 : ℝ) * a27 + (43/162 : ℝ) * a31 + (8/27 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_777 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a21 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a27 : -(h 2) < (-1/8 : ℝ))
    (a30 : -(h 1) < (-7/54 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (385/993 : ℝ) * _ctx.order4 + (727/993 : ℝ) * _ctx.min + (139/993 : ℝ) * a14 + (43/993 : ℝ) * a19 + (41/993 : ℝ) * a21 + (385/993 : ℝ) * a27 + (385/993 : ℝ) * a30 + (385/993 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_776 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a16 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a29 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a16 + (1 : ℝ) * a29
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_775 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a21 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a24 : -(h 1) < (-1/8 : ℝ))
    (a27 : -(h 2) < (-1/8 : ℝ))
    (a28 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a33 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/14 : ℝ) * _ctx.order4 + (5/224 : ℝ) * a19 + (1/28 : ℝ) * a21 + (3/14 : ℝ) * a24 + (3/14 : ℝ) * a27 + (3/28 : ℝ) * a28 + (13/32 : ℝ) * a33 + (3/14 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_774 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a21 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a27 : -(h 2) < (-1/8 : ℝ))
    (a28 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a32 : -(h 3) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/9 : ℝ) * _ctx.order1 + (2/9 : ℝ) * _ctx.order4 + (4/9 : ℝ) * _ctx.min + (1/27 : ℝ) * a21 + (4/9 : ℝ) * a27 + (1/3 : ℝ) * a28 + (5/27 : ℝ) * a32 + (2/9 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_773 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a21 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a27 : -(h 2) < (-1/8 : ℝ))
    (a28 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a31 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (32/119 : ℝ) * _ctx.order4 + (26/51 : ℝ) * _ctx.min + (10/357 : ℝ) * a19 + (16/357 : ℝ) * a21 + (32/119 : ℝ) * a27 + (139/357 : ℝ) * a28 + (32/119 : ℝ) * a31 + (32/119 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_772 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a16 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a30 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/48 : ℝ) * a14 + (1/6 : ℝ) * a16 + (47/48 : ℝ) * a30
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_771 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a22 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a29 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a22 + (1 : ℝ) * a29
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_770 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a16 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a21 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a22 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a24 : -(h 1) < (-1/8 : ℝ))
    (a27 : -(h 2) < (-1/8 : ℝ))
    (a28 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_771 h delta _ctx _hno a22 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_772 h delta _ctx _hno a14 a16 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_773 h delta _ctx _hno a19 a21 a27 a28 f2
  by_cases p3 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f3 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_774 h delta _ctx _hno a21 a27 a28 f3
  by_cases p4 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_775 h delta _ctx _hno a19 a21 a24 a27 a28 f4
  apply _hno 19
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_769 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a16 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a21 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a22 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a24 : -(h 1) < (-1/8 : ℝ))
    (a27 : -(h 2) < (-1/8 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_770 h delta _ctx _hno a14 a16 a19 a21 a22 a24 a27 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_776 h delta _ctx _hno a16 f1
  by_cases p2 : h 1 ≤ (7/54 : ℝ)
  swap
  · have f2 : -(h 1) < (-7/54 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_777 h delta _ctx _hno a14 a19 a21 a27 f2
  by_cases p3 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_778 h delta _ctx _hno a14 a21 a27 f3
  by_cases p4 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_779 h delta _ctx _hno a14 a19 a21 a24 a27 f4
  apply _hno 14
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (7/54 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_768 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a16 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a26 : -(h 0) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/48 : ℝ) * a14 + (1/6 : ℝ) * a16 + (47/48 : ℝ) * a26
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_767 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a22 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a25 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a22 + (1 : ℝ) * a25
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_766 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a16 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a21 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a22 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a24 : -(h 1) < (-1/8 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_767 h delta _ctx _hno a22 f0
  by_cases p1 : h 0 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_768 h delta _ctx _hno a14 a16 f1
  by_cases p2 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_769 h delta _ctx _hno a14 a16 a19 a21 a22 a24 f2
  by_cases p3 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f3 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_780 h delta _ctx _hno a14 a16 a19 a21 a22 a24 f3
  apply _hno 8
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_765 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a16 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a23 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/48 : ℝ) * a14 + (1/6 : ℝ) * a16 + (47/48 : ℝ) * a23
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_764 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a21 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a22 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a25 : -(h 1) < (-1/8 : ℝ))
    (a34 : -(h 4) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (16/75 : ℝ) * _ctx.order3 + (6/25 : ℝ) * _ctx.min + (1/25 : ℝ) * _ctx.fail1 + (2/75 : ℝ) * a21 + (6/25 : ℝ) * a22 + (6/25 : ℝ) * a25 + (34/75 : ℝ) * a34 + (6/25 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_763 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a21 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a22 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a25 : -(h 1) < (-1/8 : ℝ))
    (a29 : -(h 4) < (-1/9 : ℝ))
    (a33 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (86/405 : ℝ) * _ctx.min + (2/81 : ℝ) * a19 + (16/405 : ℝ) * a21 + (91/405 : ℝ) * a22 + (32/135 : ℝ) * a25 + (32/135 : ℝ) * a29 + (32/135 : ℝ) * a33 + (32/135 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_762 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a21 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a22 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a29 : -(h 4) < (-1/9 : ℝ))
    (a32 : -(h 1) < (-9/70 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/15 : ℝ) * _ctx.min + (1/20 : ℝ) * _ctx.fail1 + (1/30 : ℝ) * a19 + (1/30 : ℝ) * a21 + (17/60 : ℝ) * a22 + (3/10 : ℝ) * a29 + (3/10 : ℝ) * a32 + (3/10 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_761 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a16 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a22 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a31 : -(h 0) < (-7/45 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.min + (2/13 : ℝ) * a16 + (1/13 : ℝ) * a22 + (12/13 : ℝ) * a31
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_760 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a21 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a25 : -(h 1) < (-1/8 : ℝ))
    (a30 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/17 : ℝ) * _ctx.order4 + (2/3 : ℝ) * _ctx.min + (1/17 : ℝ) * _ctx.fail1 + (2/51 : ℝ) * a19 + (2/51 : ℝ) * a21 + (6/17 : ℝ) * a25 + (26/51 : ℝ) * a30 + (6/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_759 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a16 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a21 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a22 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a25 : -(h 1) < (-1/8 : ℝ))
    (a29 : -(h 4) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_760 h delta _ctx _hno a19 a21 a25 f0
  by_cases p1 : h 0 ≤ (7/45 : ℝ)
  swap
  · have f1 : -(h 0) < (-7/45 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_761 h delta _ctx _hno a16 a22 f1
  by_cases p2 : h 1 ≤ (9/70 : ℝ)
  swap
  · have f2 : -(h 1) < (-9/70 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_762 h delta _ctx _hno a19 a21 a22 a29 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_763 h delta _ctx _hno a19 a21 a22 a25 a29 f3
  by_cases p4 : h 4 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 4) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_764 h delta _ctx _hno a21 a22 a25 f4
  apply _hno 55
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (7/45 : ℝ)) ∧ (h 1 ≤ (9/70 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (4/35 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_758 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a21 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a22 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a25 : -(h 1) < (-1/8 : ℝ))
    (a28 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (32/119 : ℝ) * _ctx.order4 + (26/51 : ℝ) * _ctx.min + (10/357 : ℝ) * a19 + (16/357 : ℝ) * a21 + (139/357 : ℝ) * a22 + (32/119 : ℝ) * a25 + (32/119 : ℝ) * a28 + (32/119 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_757 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a16 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a22 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a27 : -(h 0) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.min + (2/13 : ℝ) * a16 + (1/13 : ℝ) * a22 + (12/13 : ℝ) * a27
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_756 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a21 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a25 : -(h 1) < (-1/8 : ℝ))
    (a26 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/17 : ℝ) * _ctx.order4 + (2/3 : ℝ) * _ctx.min + (1/17 : ℝ) * _ctx.fail1 + (2/51 : ℝ) * a19 + (2/51 : ℝ) * a21 + (6/17 : ℝ) * a25 + (26/51 : ℝ) * a26 + (6/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_755 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a16 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a21 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a22 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a25 : -(h 1) < (-1/8 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_756 h delta _ctx _hno a19 a21 a25 f0
  by_cases p1 : h 0 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_757 h delta _ctx _hno a16 a22 f1
  by_cases p2 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_758 h delta _ctx _hno a19 a21 a22 a25 f2
  by_cases p3 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f3 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_759 h delta _ctx _hno a16 a19 a21 a22 a25 f3
  apply _hno 8
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_754 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a16 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a22 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a24 : -(h 0) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.min + (2/13 : ℝ) * a16 + (1/13 : ℝ) * a22 + (12/13 : ℝ) * a24
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_753 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : h 5 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a23 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/9 : ℝ) * _ctx.min + (2/9 : ℝ) * a15 + (1 : ℝ) * a23
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_752 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : h 5 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a16 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a21 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a22 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_753 h delta _ctx _hno a15 f0
  by_cases p1 : h 0 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_754 h delta _ctx _hno a16 a22 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_755 h delta _ctx _hno a16 a19 a21 a22 f2
  apply _hno 3
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem upper_node_751 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a15 : h 5 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a16 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a21 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_752 h delta _ctx _hno a15 a16 a19 a21 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_765 h delta _ctx _hno a14 a16 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_766 h delta _ctx _hno a14 a16 a19 a21 p0 f2
  apply _hno 2
  change (((2 : ℝ) * (delta)) ≤ (7/32 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem upper_node_750 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : -(h 3) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a23 : -(h 1) < (-1/8 : ℝ))
    (a31 : -(h 3) < (-4/35 : ℝ))
    (a40 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/13 : ℝ) * _ctx.min + (1/13 : ℝ) * _ctx.fail2 + (1/13 : ℝ) * a20 + (4/13 : ℝ) * a23 + (3/13 : ℝ) * a31 + (4/13 : ℝ) * a40 + (4/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_749 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a34 : h 1 ≤ (9/70 : ℝ))
    (a39 : -(h 1) < (-7/51 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_748 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : -(h 3) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a23 : -(h 1) < (-1/8 : ℝ))
    (a31 : -(h 3) < (-4/35 : ℝ))
    (a36 : -(h 4) < (-4/35 : ℝ))
    (a38 : -(h 0) < (-11/80 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.min + (1/23 : ℝ) * _ctx.fail1 + (3/46 : ℝ) * a20 + (6/23 : ℝ) * a23 + (9/46 : ℝ) * a31 + (6/23 : ℝ) * a36 + (4/23 : ℝ) * a38 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_747 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a21 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ))
    (a37 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a21 + (1 : ℝ) * a37
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_746 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : -(h 3) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a21 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ))
    (a23 : -(h 1) < (-1/8 : ℝ))
    (a31 : -(h 3) < (-4/35 : ℝ))
    (a34 : h 1 ≤ (9/70 : ℝ))
    (a36 : -(h 4) < (-4/35 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_747 h delta _ctx _hno a21 f0
  by_cases p1 : h 0 ≤ (11/80 : ℝ)
  swap
  · have f1 : -(h 0) < (-11/80 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_748 h delta _ctx _hno a20 a23 a31 a36 f1
  by_cases p2 : h 1 ≤ (7/51 : ℝ)
  swap
  · have f2 : -(h 1) < (-7/51 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_749 h delta _ctx _hno a34 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_750 h delta _ctx _hno a20 a23 a31 f3
  apply _hno 6
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (11/80 : ℝ)) ∧ (h 1 ≤ (7/51 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_745 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : -(h 3) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a23 : -(h 1) < (-1/8 : ℝ))
    (a31 : -(h 3) < (-4/35 : ℝ))
    (a35 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/13 : ℝ) * _ctx.min + (1/13 : ℝ) * _ctx.fail2 + (1/13 : ℝ) * a20 + (4/13 : ℝ) * a23 + (3/13 : ℝ) * a31 + (4/13 : ℝ) * a35 + (4/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_744 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : -(h 3) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a31 : -(h 3) < (-4/35 : ℝ))
    (a34 : -(h 1) < (-9/70 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/7 : ℝ) * _ctx.order4 + (4/7 : ℝ) * _ctx.min + (1/14 : ℝ) * _ctx.fail1 + (1/14 : ℝ) * _ctx.fail2 + (1/8 : ℝ) * a20 + (17/56 : ℝ) * a31 + (3/7 : ℝ) * a34 + (3/7 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_743 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : h 0 ≤ (1/7 : ℝ))
    (a33 : -(h 0) < (-7/45 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a33
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_742 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a21 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ))
    (a32 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a21 + (1 : ℝ) * a32
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_741 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : -(h 3) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a21 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ))
    (a23 : -(h 1) < (-1/8 : ℝ))
    (a29 : h 0 ≤ (1/7 : ℝ))
    (a31 : -(h 3) < (-4/35 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_742 h delta _ctx _hno a21 f0
  by_cases p1 : h 0 ≤ (7/45 : ℝ)
  swap
  · have f1 : -(h 0) < (-7/45 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_743 h delta _ctx _hno a29 f1
  by_cases p2 : h 1 ≤ (9/70 : ℝ)
  swap
  · have f2 : -(h 1) < (-9/70 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_744 h delta _ctx _hno a20 a31 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_745 h delta _ctx _hno a20 a23 a31 f3
  by_cases p4 : h 4 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 4) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_746 h delta _ctx _hno a20 a21 a23 a31 p2 f4
  apply _hno 55
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (7/45 : ℝ)) ∧ (h 1 ≤ (9/70 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (4/35 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_740 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a26 : h 2 ≤ (1/8 : ℝ))
    (a30 : -(h 2) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a26 + (1 : ℝ) * a30
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_739 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : -(h 3) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a23 : -(h 1) < (-1/8 : ℝ))
    (a29 : -(h 0) < (-1/7 : ℝ))
    (a34 : -(h 4) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (9/46 : ℝ) * _ctx.order3 + (6/23 : ℝ) * _ctx.min + (1/23 : ℝ) * _ctx.fail1 + (3/46 : ℝ) * a20 + (6/23 : ℝ) * a23 + (4/23 : ℝ) * a29 + (21/46 : ℝ) * a34 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_738 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a20 : -(h 3) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a23 : -(h 1) < (-1/8 : ℝ))
    (a29 : -(h 0) < (-1/7 : ℝ))
    (a33 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (9/31 : ℝ) * _ctx.order4 + (121/217 : ℝ) * _ctx.min + (5/217 : ℝ) * a19 + (23/217 : ℝ) * a20 + (9/31 : ℝ) * a23 + (9/31 : ℝ) * a29 + (9/31 : ℝ) * a33 + (9/31 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_737 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a20 : -(h 3) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a29 : -(h 0) < (-1/7 : ℝ))
    (a32 : -(h 1) < (-9/70 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (18/41 : ℝ) * _ctx.order4 + (242/287 : ℝ) * _ctx.min + (3/41 : ℝ) * _ctx.fail1 + (10/287 : ℝ) * a19 + (46/287 : ℝ) * a20 + (12/41 : ℝ) * a29 + (18/41 : ℝ) * a32 + (18/41 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_736 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a16 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a20 : -(h 3) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a31 : -(h 0) < (-7/45 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/130 : ℝ) * _ctx.order1 + (1/65 : ℝ) * _ctx.order2 + (1/130 : ℝ) * _ctx.order4 + (23/130 : ℝ) * _ctx.min + (21/130 : ℝ) * a16 + (3/130 : ℝ) * a20 + (127/130 : ℝ) * a31 + (1/130 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_735 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a21 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ))
    (a30 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a21 + (1 : ℝ) * a30
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_734 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a16 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a20 : -(h 3) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a21 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ))
    (a23 : -(h 1) < (-1/8 : ℝ))
    (a29 : -(h 0) < (-1/7 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_735 h delta _ctx _hno a21 f0
  by_cases p1 : h 0 ≤ (7/45 : ℝ)
  swap
  · have f1 : -(h 0) < (-7/45 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_736 h delta _ctx _hno a16 a20 f1
  by_cases p2 : h 1 ≤ (9/70 : ℝ)
  swap
  · have f2 : -(h 1) < (-9/70 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_737 h delta _ctx _hno a19 a20 a29 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_738 h delta _ctx _hno a19 a20 a23 a29 f3
  by_cases p4 : h 4 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 4) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_739 h delta _ctx _hno a20 a23 a29 f4
  apply _hno 55
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (7/45 : ℝ)) ∧ (h 1 ≤ (9/70 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (4/35 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_733 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a21 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ))
    (a28 : ((-2 : ℝ) * (delta)) < (-8/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a21 + (1 : ℝ) * a28
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_732 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a16 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a20 : -(h 3) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a21 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ))
    (a23 : -(h 1) < (-1/8 : ℝ))
    (a26 : h 2 ≤ (1/8 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (8/35 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-8/35 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_733 h delta _ctx _hno a21 f0
  by_cases p1 : h 0 ≤ (1/7 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_734 h delta _ctx _hno a16 a19 a20 a21 a23 f1
  by_cases p2 : h 2 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 2) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_740 h delta _ctx _hno a26 f2
  by_cases p3 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f3 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_741 h delta _ctx _hno a20 a21 a23 p1 f3
  apply _hno 33
  change (((2 : ℝ) * (delta)) ≤ (8/35 : ℝ)) ∧ (h 0 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_731 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a20 : -(h 3) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a23 : -(h 1) < (-1/8 : ℝ))
    (a26 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (76/217 : ℝ) * _ctx.min + (3/31 : ℝ) * _ctx.fail2 + (8/217 : ℝ) * a19 + (20/217 : ℝ) * a20 + (12/31 : ℝ) * a23 + (12/31 : ℝ) * a26 + (12/31 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_730 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a16 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a20 : -(h 3) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a23 : -(h 1) < (-1/8 : ℝ))
    (a25 : -(h 0) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/197 : ℝ) * _ctx.order4 + (42/197 : ℝ) * _ctx.min + (1/197 : ℝ) * _ctx.fail1 + (30/197 : ℝ) * a16 + (6/197 : ℝ) * a20 + (6/197 : ℝ) * a23 + (184/197 : ℝ) * a25 + (6/197 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_729 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a21 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ))
    (a24 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a21 + (1 : ℝ) * a24
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_728 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a16 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a20 : -(h 3) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a21 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ))
    (a23 : -(h 1) < (-1/8 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_729 h delta _ctx _hno a21 f0
  by_cases p1 : h 0 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_730 h delta _ctx _hno a16 a20 a23 f1
  by_cases p2 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_731 h delta _ctx _hno a19 a20 a23 f2
  by_cases p3 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f3 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_732 h delta _ctx _hno a16 a19 a20 a21 a23 p2
  apply _hno 8
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_727 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a16 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a20 : -(h 3) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a22 : -(h 0) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/130 : ℝ) * _ctx.order1 + (1/65 : ℝ) * _ctx.order2 + (1/130 : ℝ) * _ctx.order4 + (23/130 : ℝ) * _ctx.min + (21/130 : ℝ) * a16 + (3/130 : ℝ) * a20 + (127/130 : ℝ) * a22 + (1/130 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_726 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : h 5 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a21 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/9 : ℝ) * _ctx.min + (2/9 : ℝ) * a15 + (1 : ℝ) * a21
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_725 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : h 5 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a16 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a20 : -(h 3) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_726 h delta _ctx _hno a15 f0
  by_cases p1 : h 0 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_727 h delta _ctx _hno a16 a20 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_728 h delta _ctx _hno a16 a19 a20 p0 f2
  apply _hno 3
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem upper_node_724 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a15 : h 5 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a16 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    : False := by
  by_cases p0 : h 3 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ)
  swap
  · have f0 : -(h 3) + ((-8 : ℝ) * (delta)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_725 h delta _ctx _hno a15 a16 a19 f0
  by_cases p1 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ)
  swap
  · have f1 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_751 h delta _ctx _hno a14 a15 a16 a19 f1
  by_cases p2 : ((6 : ℝ) * (h 1)) + h 3 ≤ (1 : ℝ)
  swap
  · have f2 : ((-6 : ℝ) * (h 1)) + -(h 3) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_808 h delta _ctx _hno a14 a19 f2
  by_cases p3 : ((6 : ℝ) * (h 2)) + h 3 ≤ (1 : ℝ)
  swap
  · have f3 : ((-6 : ℝ) * (h 2)) + -(h 3) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_809 h delta _ctx _hno a19 f3
  by_cases p4 : h 3 + ((8 : ℝ) * (h 4)) ≤ (1 : ℝ)
  swap
  · have f4 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_810 h delta _ctx _hno a14 a15 a16 a19 p0 p1 f4
  by_cases p5 : h 3 + ((8 : ℝ) * (h 5)) ≤ (1 : ℝ)
  swap
  · have f5 : -(h 3) + ((-8 : ℝ) * (h 5)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1035 h delta _ctx _hno p4 f5
  apply _hno 90
  change (h 3 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ)) ∧ (((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ)) ∧ (((6 : ℝ) * (h 1)) + h 3 ≤ (1 : ℝ)) ∧ (((6 : ℝ) * (h 2)) + h 3 ≤ (1 : ℝ)) ∧ (h 3 + ((8 : ℝ) * (h 4)) ≤ (1 : ℝ)) ∧ (h 3 + ((8 : ℝ) * (h 5)) ≤ (1 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_723 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : ((-6 : ℝ) * (h 2)) + -(h 5) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.order0 + (4 : ℝ) * _ctx.order1 + (2 : ℝ) * _ctx.order3 + (4 : ℝ) * _ctx.order4 + (5 : ℝ) * _ctx.min + (7 : ℝ) * _ctx.lower + (1 : ℝ) * a18 + (2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_722 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a17 : ((-6 : ℝ) * (h 1)) + -(h 5) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (18/79 : ℝ) * _ctx.order0 + (94/79 : ℝ) * _ctx.order3 + (188/79 : ℝ) * _ctx.order4 + (10/3 : ℝ) * _ctx.min + (47/237 : ℝ) * _ctx.fail1 + (134/237 : ℝ) * a14 + (56/237 : ℝ) * a17 + (94/79 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_721 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a16 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a19 : -(h 1) < (-1/8 : ℝ))
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a37 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (24/103 : ℝ) * _ctx.order3 + (4/103 : ℝ) * _ctx.fail1 + (3/103 : ℝ) * a14 + (13/618 : ℝ) * a16 + (24/103 : ℝ) * a19 + (48/103 : ℝ) * a32 + (131/618 : ℝ) * a37 + (24/103 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_720 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a16 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a19 : -(h 1) < (-1/8 : ℝ))
    (a32 : -(h 4) < (-4/35 : ℝ))
    (a36 : -(h 3) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (262/981 : ℝ) * _ctx.min + (47/981 : ℝ) * _ctx.fail1 + (68/981 : ℝ) * a14 + (20/981 : ℝ) * a16 + (94/327 : ℝ) * a19 + (94/327 : ℝ) * a32 + (94/327 : ℝ) * a36 + (94/327 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_719 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : h 1 ≤ (9/70 : ℝ))
    (a35 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a35
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_718 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : h 0 ≤ (3/20 : ℝ))
    (a34 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a25 + (1 : ℝ) * a34
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_717 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a33 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a33
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_716 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a16 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a17 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a19 : -(h 1) < (-1/8 : ℝ))
    (a25 : h 0 ≤ (3/20 : ℝ))
    (a30 : h 1 ≤ (9/70 : ℝ))
    (a32 : -(h 4) < (-4/35 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_717 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_718 h delta _ctx _hno a25 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_719 h delta _ctx _hno a30 f2
  by_cases p3 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f3 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_720 h delta _ctx _hno a14 a16 a19 a32 f3
  by_cases p4 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_721 h delta _ctx _hno a14 a16 a19 a32 f4
  apply _hno 19
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_715 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a16 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a27 : -(h 4) < (-1/9 : ℝ))
    (a31 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (47/205 : ℝ) * _ctx.order1 + (1/5 : ℝ) * _ctx.min + (11/205 : ℝ) * a14 + (6/205 : ℝ) * a16 + (47/205 : ℝ) * a23 + (47/205 : ℝ) * a27 + (94/205 : ℝ) * a31 + (47/205 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_714 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a16 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a27 : -(h 4) < (-1/9 : ℝ))
    (a30 : -(h 1) < (-9/70 : ℝ))
    (a35 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/103 : ℝ) * _ctx.fail1 + (3/103 : ℝ) * a14 + (13/618 : ℝ) * a16 + (24/103 : ℝ) * a23 + (24/103 : ℝ) * a27 + (24/103 : ℝ) * a30 + (131/618 : ℝ) * a35 + (24/103 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_713 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a16 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a27 : -(h 4) < (-1/9 : ℝ))
    (a30 : -(h 1) < (-9/70 : ℝ))
    (a34 : -(h 3) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (262/981 : ℝ) * _ctx.min + (47/981 : ℝ) * _ctx.fail1 + (68/981 : ℝ) * a14 + (20/981 : ℝ) * a16 + (94/327 : ℝ) * a27 + (94/327 : ℝ) * a30 + (94/327 : ℝ) * a34 + (94/327 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_712 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a16 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a27 : -(h 4) < (-1/9 : ℝ))
    (a33 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (262/981 : ℝ) * _ctx.min + (47/981 : ℝ) * _ctx.fail1 + (68/981 : ℝ) * a14 + (20/981 : ℝ) * a16 + (94/327 : ℝ) * a23 + (94/327 : ℝ) * a27 + (94/327 : ℝ) * a33 + (94/327 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_711 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : h 0 ≤ (3/20 : ℝ))
    (a32 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a25 + (1 : ℝ) * a32
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_710 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a31 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a31
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_709 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a16 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a17 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a25 : h 0 ≤ (3/20 : ℝ))
    (a27 : -(h 4) < (-1/9 : ℝ))
    (a30 : -(h 1) < (-9/70 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_710 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_711 h delta _ctx _hno a25 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_712 h delta _ctx _hno a14 a16 a23 a27 f2
  by_cases p3 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f3 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_713 h delta _ctx _hno a14 a16 a27 a30 f3
  by_cases p4 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_714 h delta _ctx _hno a14 a16 a23 a27 a30 f4
  apply _hno 19
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_708 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : h 0 ≤ (3/20 : ℝ))
    (a29 : -(h 0) < (-7/45 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a25 + (1 : ℝ) * a29
  exact (lt_irrefl (0 : ℝ)) hbad

end RealPinwheel.WeakSevenBandData
