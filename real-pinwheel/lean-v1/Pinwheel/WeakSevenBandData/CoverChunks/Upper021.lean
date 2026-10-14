import Pinwheel.WeakSevenBandData.CoverChunks.Upper020

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem upper_node_2627 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a36 : h 1 ≤ (3/22 : ℝ))
    (a37 : -(h 2) < (-5/41 : ℝ))
    (a40 : -(h 1) < (-2/15 : ℝ))
    (a41 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a44 : h 2 ≤ (1/8 : ℝ))
    (a46 : -(h 5) < (-2/19 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2628 h delta _ctx _hno a41 f0
  by_cases p1 : h 0 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2629 h delta _ctx _hno a23 a25 a28 a37 a40 f1
  by_cases p2 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2630 h delta _ctx _hno a23 a28 a30 a40 a46 f2
  by_cases p3 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f3 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2631 h delta _ctx _hno a23 a28 a30 a36 a37 a40 a41 a44 a46 f3
  apply _hno 8
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_2626 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a37 : -(h 2) < (-5/41 : ℝ))
    (a40 : -(h 1) < (-2/15 : ℝ))
    (a45 : -(h 4) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a30 + (1/5 : ℝ) * a37 + (1/5 : ℝ) * a40 + (2/5 : ℝ) * a45 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2625 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a40 : -(h 1) < (-2/15 : ℝ))
    (a44 : -(h 2) < (-1/8 : ℝ))
    (a51 : -(h 5) < (-6/53 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/3 : ℝ) * _ctx.order4 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a40 + (1/6 : ℝ) * a44 + (1/2 : ℝ) * a51 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2624 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a40 : -(h 1) < (-2/15 : ℝ))
    (a44 : -(h 2) < (-1/8 : ℝ))
    (a50 : -(h 4) < (-5/44 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a30 + (1/5 : ℝ) * a40 + (1/5 : ℝ) * a44 + (2/5 : ℝ) * a50 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2623 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a40 : -(h 1) < (-2/15 : ℝ))
    (a44 : -(h 2) < (-1/8 : ℝ))
    (a49 : -(h 3) < (-7/61 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.min + (1/2 : ℝ) * _ctx.lower + (1/32 : ℝ) * a28 + (1/4 : ℝ) * a30 + (1/4 : ℝ) * a40 + (1/4 : ℝ) * a44 + (7/32 : ℝ) * a49 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2622 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a48 : -(h 2) < (-3/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (64/207 : ℝ) * _ctx.order1 + (19/69 : ℝ) * _ctx.min + (121/207 : ℝ) * _ctx.lower + (7/207 : ℝ) * a23 + (8/207 : ℝ) * a28 + (64/207 : ℝ) * a30 + (128/207 : ℝ) * a48 + (64/207 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2621 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a36 : h 1 ≤ (3/22 : ℝ))
    (a47 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a36 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2620 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a40 : -(h 1) < (-2/15 : ℝ))
    (a44 : -(h 2) < (-1/8 : ℝ))
    (a46 : -(h 0) < (-25/173 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (19/69 : ℝ) * _ctx.min + (121/207 : ℝ) * _ctx.lower + (7/207 : ℝ) * a23 + (8/207 : ℝ) * a28 + (64/207 : ℝ) * a40 + (64/207 : ℝ) * a44 + (64/207 : ℝ) * a46 + (64/207 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2619 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a40 : -(h 1) < (-2/15 : ℝ))
    (a44 : -(h 2) < (-1/8 : ℝ))
    (a51 : -(h 5) < (-2/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (8/33 : ℝ) * _ctx.lower + (7/264 : ℝ) * a23 + (1/33 : ℝ) * a28 + (8/33 : ℝ) * a30 + (8/33 : ℝ) * a40 + (8/33 : ℝ) * a44 + (19/88 : ℝ) * a51 + (8/33 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2618 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a40 : -(h 1) < (-2/15 : ℝ))
    (a44 : -(h 2) < (-1/8 : ℝ))
    (a50 : -(h 3) < (-7/62 : ℝ))
    (a57 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.lower + (1/40 : ℝ) * a28 + (1/5 : ℝ) * a30 + (1/5 : ℝ) * a40 + (1/5 : ℝ) * a44 + (7/40 : ℝ) * a50 + (1/5 : ℝ) * a57 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2617 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a40 : -(h 1) < (-2/15 : ℝ))
    (a44 : -(h 2) < (-1/8 : ℝ))
    (a56 : -(h 4) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a30 + (1/5 : ℝ) * a40 + (1/5 : ℝ) * a44 + (2/5 : ℝ) * a56 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2616 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a40 : -(h 1) < (-2/15 : ℝ))
    (a44 : -(h 2) < (-1/8 : ℝ))
    (a55 : -(h 3) < (-15/131 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.min + (1/2 : ℝ) * _ctx.lower + (1/32 : ℝ) * a28 + (1/4 : ℝ) * a30 + (1/4 : ℝ) * a40 + (1/4 : ℝ) * a44 + (7/32 : ℝ) * a55 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2615 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a40 : -(h 1) < (-2/15 : ℝ))
    (a54 : -(h 2) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (19/69 : ℝ) * _ctx.min + (121/207 : ℝ) * _ctx.lower + (7/207 : ℝ) * a23 + (8/207 : ℝ) * a28 + (64/207 : ℝ) * a30 + (64/207 : ℝ) * a40 + (64/207 : ℝ) * a54 + (64/207 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2614 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a44 : -(h 2) < (-1/8 : ℝ))
    (a50 : -(h 3) < (-7/62 : ℝ))
    (a53 : -(h 1) < (-5/37 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.min + (1/2 : ℝ) * _ctx.lower + (1/32 : ℝ) * a28 + (1/4 : ℝ) * a30 + (1/4 : ℝ) * a44 + (7/32 : ℝ) * a50 + (1/4 : ℝ) * a53 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2613 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a40 : -(h 1) < (-2/15 : ℝ))
    (a44 : -(h 2) < (-1/8 : ℝ))
    (a50 : -(h 3) < (-7/62 : ℝ))
    (a52 : -(h 0) < (-13/90 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.min + (1/2 : ℝ) * _ctx.lower + (1/32 : ℝ) * a28 + (1/4 : ℝ) * a40 + (1/4 : ℝ) * a44 + (7/32 : ℝ) * a50 + (1/4 : ℝ) * a52 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2612 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a41 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a51 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a41 + (1 : ℝ) * a51
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2611 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a40 : -(h 1) < (-2/15 : ℝ))
    (a41 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a44 : -(h 2) < (-1/8 : ℝ))
    (a50 : -(h 3) < (-7/62 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2612 h delta _ctx _hno a41 f0
  by_cases p1 : h 0 ≤ (13/90 : ℝ)
  swap
  · have f1 : -(h 0) < (-13/90 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2613 h delta _ctx _hno a28 a40 a44 a50 f1
  by_cases p2 : h 1 ≤ (5/37 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/37 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2614 h delta _ctx _hno a28 a30 a44 a50 f2
  by_cases p3 : h 2 ≤ (3/23 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2615 h delta _ctx _hno a23 a28 a30 a40 f3
  by_cases p4 : h 3 ≤ (15/131 : ℝ)
  swap
  · have f4 : -(h 3) < (-15/131 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2616 h delta _ctx _hno a28 a30 a40 a44 f4
  by_cases p5 : h 4 ≤ (4/35 : ℝ)
  swap
  · have f5 : -(h 4) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_2617 h delta _ctx _hno a30 a40 a44 f5
  by_cases p6 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f6 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact upper_node_2618 h delta _ctx _hno a28 a30 a40 a44 a50 f6
  apply _hno 28
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (13/90 : ℝ)) ∧ (h 1 ≤ (5/37 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (15/131 : ℝ)) ∧ (h 4 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem upper_node_2610 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a49 : -(h 2) < (-4/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (8/19 : ℝ) * _ctx.order1 + (7/19 : ℝ) * _ctx.min + (15/19 : ℝ) * _ctx.lower + (2/19 : ℝ) * _ctx.fail2 + (1/19 : ℝ) * a23 + (16/19 : ℝ) * a49 + (8/19 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2609 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a36 : h 1 ≤ (3/22 : ℝ))
    (a48 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a36 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2608 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a42 : h 0 ≤ (4/27 : ℝ))
    (a47 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a42 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2607 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a41 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a46 : ((-2 : ℝ) * (delta)) < (-11/52 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a41 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2606 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a36 : h 1 ≤ (3/22 : ℝ))
    (a40 : -(h 1) < (-2/15 : ℝ))
    (a41 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a42 : h 0 ≤ (4/27 : ℝ))
    (a44 : -(h 2) < (-1/8 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (11/52 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-11/52 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2607 h delta _ctx _hno a41 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2608 h delta _ctx _hno a42 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2609 h delta _ctx _hno a36 f2
  by_cases p3 : h 2 ≤ (4/29 : ℝ)
  swap
  · have f3 : -(h 2) < (-4/29 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2610 h delta _ctx _hno a23 f3
  by_cases p4 : h 3 ≤ (7/62 : ℝ)
  swap
  · have f4 : -(h 3) < (-7/62 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2611 h delta _ctx _hno a23 a28 a30 a40 a41 a44 f4
  by_cases p5 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_2619 h delta _ctx _hno a23 a28 a30 a40 a44 f5
  apply _hno 29
  change (((2 : ℝ) * (delta)) ≤ (11/52 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (4/29 : ℝ)) ∧ (h 3 ≤ (7/62 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_2605 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a36 : h 1 ≤ (3/22 : ℝ))
    (a40 : -(h 1) < (-2/15 : ℝ))
    (a41 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a42 : h 0 ≤ (4/27 : ℝ))
    (a44 : -(h 2) < (-1/8 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2606 h delta _ctx _hno a23 a28 a30 a36 a40 a41 a42 a44
  by_cases p1 : h 0 ≤ (25/173 : ℝ)
  swap
  · have f1 : -(h 0) < (-25/173 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2620 h delta _ctx _hno a23 a28 a40 a44 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2621 h delta _ctx _hno a36 f2
  by_cases p3 : h 2 ≤ (3/22 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2622 h delta _ctx _hno a23 a28 a30 f3
  by_cases p4 : h 3 ≤ (7/61 : ℝ)
  swap
  · have f4 : -(h 3) < (-7/61 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2623 h delta _ctx _hno a28 a30 a40 a44 f4
  by_cases p5 : h 4 ≤ (5/44 : ℝ)
  swap
  · have f5 : -(h 4) < (-5/44 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_2624 h delta _ctx _hno a30 a40 a44 f5
  by_cases p6 : h 5 ≤ (6/53 : ℝ)
  swap
  · have f6 : -(h 5) < (-6/53 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact upper_node_2625 h delta _ctx _hno a30 a40 a44 f6
  apply _hno 27
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (25/173 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (3/22 : ℝ)) ∧ (h 3 ≤ (7/61 : ℝ)) ∧ (h 4 ≤ (5/44 : ℝ)) ∧ (h 5 ≤ (6/53 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem upper_node_2604 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a36 : h 1 ≤ (3/22 : ℝ))
    (a43 : -(h 1) < (-6/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a36 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2603 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a37 : -(h 2) < (-5/41 : ℝ))
    (a40 : -(h 1) < (-2/15 : ℝ))
    (a42 : -(h 0) < (-4/27 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (19/69 : ℝ) * _ctx.min + (121/207 : ℝ) * _ctx.lower + (7/207 : ℝ) * a23 + (8/207 : ℝ) * a28 + (64/207 : ℝ) * a37 + (64/207 : ℝ) * a40 + (64/207 : ℝ) * a42 + (64/207 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2602 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a37 : -(h 2) < (-5/41 : ℝ))
    (a40 : -(h 1) < (-2/15 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a51 : -(h 5) < (-6/53 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order3 + (4/13 : ℝ) * _ctx.order4 + (2/13 : ℝ) * a30 + (2/13 : ℝ) * a37 + (2/13 : ℝ) * a40 + (1/13 : ℝ) * a41 + (6/13 : ℝ) * a51 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2601 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a37 : -(h 2) < (-5/41 : ℝ))
    (a40 : -(h 1) < (-2/15 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a45 : -(h 4) < (-1/9 : ℝ))
    (a50 : -(h 3) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a40 + (1/6 : ℝ) * a41 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a50 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2600 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a40 : -(h 1) < (-2/15 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a49 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (114/535 : ℝ) * _ctx.min + (14/535 : ℝ) * a23 + (16/535 : ℝ) * a28 + (128/535 : ℝ) * a30 + (128/535 : ℝ) * a40 + (121/535 : ℝ) * a41 + (128/535 : ℝ) * a49 + (128/535 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2599 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a36 : h 1 ≤ (3/22 : ℝ))
    (a48 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a36 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2598 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a37 : -(h 2) < (-5/41 : ℝ))
    (a40 : -(h 1) < (-2/15 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a47 : -(h 0) < (-8/55 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (114/535 : ℝ) * _ctx.min + (14/535 : ℝ) * a23 + (16/535 : ℝ) * a28 + (128/535 : ℝ) * a37 + (128/535 : ℝ) * a40 + (121/535 : ℝ) * a41 + (128/535 : ℝ) * a47 + (128/535 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2597 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a46 : ((-2 : ℝ) * (delta)) < (-7/31 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * a14 + (1/5 : ℝ) * a30 + (4/5 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2596 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a36 : h 1 ≤ (3/22 : ℝ))
    (a37 : -(h 2) < (-5/41 : ℝ))
    (a40 : -(h 1) < (-2/15 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a45 : -(h 4) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/31 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/31 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2597 h delta _ctx _hno a14 a30 f0
  by_cases p1 : h 0 ≤ (8/55 : ℝ)
  swap
  · have f1 : -(h 0) < (-8/55 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2598 h delta _ctx _hno a23 a28 a37 a40 a41 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2599 h delta _ctx _hno a36 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2600 h delta _ctx _hno a23 a28 a30 a40 a41 f3
  by_cases p4 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2601 h delta _ctx _hno a30 a37 a40 a41 a45 f4
  by_cases p5 : h 5 ≤ (6/53 : ℝ)
  swap
  · have f5 : -(h 5) < (-6/53 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_2602 h delta _ctx _hno a30 a37 a40 a41 f5
  apply _hno 39
  change (((2 : ℝ) * (delta)) ≤ (7/31 : ℝ)) ∧ (h 0 ≤ (8/55 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (6/53 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_2595 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a40 : -(h 1) < (-2/15 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a44 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (114/535 : ℝ) * _ctx.min + (14/535 : ℝ) * a23 + (16/535 : ℝ) * a28 + (128/535 : ℝ) * a30 + (128/535 : ℝ) * a40 + (121/535 : ℝ) * a41 + (128/535 : ℝ) * a44 + (128/535 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2594 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a37 : -(h 2) < (-5/41 : ℝ))
    (a40 : -(h 1) < (-2/15 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a43 : -(h 0) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (8/379 : ℝ) * a23 + (57/379 : ℝ) * a25 + (1/379 : ℝ) * a28 + (8/379 : ℝ) * a37 + (8/379 : ℝ) * a40 + (4/379 : ℝ) * a41 + (350/379 : ℝ) * a43 + (8/379 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2593 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a42 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * a14 + (1/5 : ℝ) * a30 + (4/5 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2592 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a36 : h 1 ≤ (3/22 : ℝ))
    (a37 : -(h 2) < (-5/41 : ℝ))
    (a40 : -(h 1) < (-2/15 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2593 h delta _ctx _hno a14 a30 f0
  by_cases p1 : h 0 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2594 h delta _ctx _hno a23 a25 a28 a37 a40 a41 f1
  by_cases p2 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2595 h delta _ctx _hno a23 a28 a30 a40 a41 f2
  by_cases p3 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f3 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2596 h delta _ctx _hno a14 a23 a28 a30 a36 a37 a40 a41 f3
  apply _hno 8
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_2591 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a36 : h 1 ≤ (3/22 : ℝ))
    (a37 : -(h 2) < (-5/41 : ℝ))
    (a40 : -(h 1) < (-2/15 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2592 h delta _ctx _hno a14 a23 a25 a28 a30 a36 a37 a40 f0
  by_cases p1 : h 0 ≤ (4/27 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/27 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2603 h delta _ctx _hno a23 a28 a37 a40 f1
  by_cases p2 : h 1 ≤ (6/41 : ℝ)
  swap
  · have f2 : -(h 1) < (-6/41 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2604 h delta _ctx _hno a36 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2605 h delta _ctx _hno a23 a28 a30 a36 a40 p0 p1 f3
  by_cases p4 : h 4 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 4) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2626 h delta _ctx _hno a30 a37 a40 f4
  by_cases p5 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_2627 h delta _ctx _hno a23 a25 a28 a30 a36 a37 a40 p0 p3 f5
  apply _hno 9
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (4/27 : ℝ)) ∧ (h 1 ≤ (6/41 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_2590 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a39 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/55 : ℝ) * a20 + (1/55 : ℝ) * a23 + (8/55 : ℝ) * a25 + (54/55 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2589 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a38 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * a14 + (1/5 : ℝ) * a30 + (4/5 : ℝ) * a38
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2588 (h : Fin 6 → ℝ) (delta : ℝ)
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
    (a37 : -(h 2) < (-5/41 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2589 h delta _ctx _hno a14 a30 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2590 h delta _ctx _hno a20 a23 a25 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2591 h delta _ctx _hno a14 a23 a25 a28 a30 a36 a37 f2
  by_cases p3 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f3 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2678 h delta _ctx _hno a14 a25 a28 a30 a33 a37 p2 f3
  by_cases p4 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2770 h delta _ctx _hno a14 a23 a28 a30 a33 a37 p2 p3 f4
  apply _hno 19
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_2587 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a36 : -(h 1) < (-3/22 : ℝ))
    (a49 : -(h 5) < (-6/53 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.order3 + (12/29 : ℝ) * _ctx.order4 + (6/29 : ℝ) * _ctx.lower + (1/29 : ℝ) * _ctx.fail1 + (4/29 : ℝ) * a30 + (6/29 : ℝ) * a36 + (18/29 : ℝ) * a49 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2586 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a36 : -(h 1) < (-3/22 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    (a48 : -(h 4) < (-5/44 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.order3 + (6/29 : ℝ) * _ctx.lower + (1/29 : ℝ) * _ctx.fail1 + (4/29 : ℝ) * a30 + (6/29 : ℝ) * a36 + (6/29 : ℝ) * a42 + (12/29 : ℝ) * a48 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2585 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a36 : -(h 1) < (-3/22 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    (a47 : -(h 3) < (-7/61 : ℝ))
    (a51 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.lower + (1/29 : ℝ) * _ctx.fail1 + (4/29 : ℝ) * a30 + (6/29 : ℝ) * a36 + (6/29 : ℝ) * a42 + (6/29 : ℝ) * a47 + (6/29 : ℝ) * a51 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2584 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a36 : -(h 1) < (-3/22 : ℝ))
    (a47 : -(h 3) < (-7/61 : ℝ))
    (a50 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.min + (1/2 : ℝ) * _ctx.lower + (1/32 : ℝ) * a28 + (1/4 : ℝ) * a30 + (1/4 : ℝ) * a36 + (7/32 : ℝ) * a47 + (1/4 : ℝ) * a50 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2583 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a44 : h 0 ≤ (25/173 : ℝ))
    (a49 : -(h 0) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a44 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2582 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a43 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ))
    (a48 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a43 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2581 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a36 : -(h 1) < (-3/22 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    (a43 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ))
    (a44 : h 0 ≤ (25/173 : ℝ))
    (a47 : -(h 3) < (-7/61 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2582 h delta _ctx _hno a43 f0
  by_cases p1 : h 0 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2583 h delta _ctx _hno a44 f1
  by_cases p2 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2584 h delta _ctx _hno a28 a30 a36 a47 f2
  by_cases p3 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f3 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2585 h delta _ctx _hno a30 a36 a42 a47 f3
  apply _hno 8
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_2580 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a40 : h 2 ≤ (1/8 : ℝ))
    (a46 : -(h 2) < (-3/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a40 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2579 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a45 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (128/397 : ℝ) * _ctx.order0 + (171/397 : ℝ) * _ctx.min + (363/397 : ℝ) * _ctx.lower + (32/397 : ℝ) * _ctx.fail1 + (21/397 : ℝ) * a23 + (24/397 : ℝ) * a28 + (320/397 : ℝ) * a45 + (192/397 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2578 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a36 : -(h 1) < (-3/22 : ℝ))
    (a44 : -(h 0) < (-25/173 : ℝ))
    (a54 : -(h 5) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.order3 + (12/29 : ℝ) * _ctx.order4 + (6/29 : ℝ) * _ctx.lower + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a36 + (4/29 : ℝ) * a44 + (18/29 : ℝ) * a54 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2577 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a36 : -(h 1) < (-3/22 : ℝ))
    (a44 : -(h 0) < (-25/173 : ℝ))
    (a53 : -(h 3) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/17 : ℝ) * _ctx.min + (12/17 : ℝ) * _ctx.lower + (1/17 : ℝ) * _ctx.fail1 + (3/68 : ℝ) * a28 + (6/17 : ℝ) * a36 + (4/17 : ℝ) * a44 + (21/68 : ℝ) * a53 + (6/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2576 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a36 : -(h 1) < (-3/22 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    (a44 : -(h 0) < (-25/173 : ℝ))
    (a52 : -(h 2) < (-4/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (8/33 : ℝ) * _ctx.lower + (7/264 : ℝ) * a23 + (1/33 : ℝ) * a28 + (8/33 : ℝ) * a36 + (19/88 : ℝ) * a42 + (8/33 : ℝ) * a44 + (8/33 : ℝ) * a52 + (8/33 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2575 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a44 : -(h 0) < (-25/173 : ℝ))
    (a51 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (171/397 : ℝ) * _ctx.min + (363/397 : ℝ) * _ctx.lower + (32/397 : ℝ) * _ctx.fail1 + (21/397 : ℝ) * a23 + (24/397 : ℝ) * a28 + (128/397 : ℝ) * a44 + (192/397 : ℝ) * a51 + (192/397 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2574 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a36 : -(h 1) < (-3/22 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    (a48 : -(h 4) < (-1/9 : ℝ))
    (a50 : -(h 0) < (-6/41 : ℝ))
    (a55 : -(h 3) < (-5/44 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.lower + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a36 + (6/29 : ℝ) * a42 + (6/29 : ℝ) * a48 + (4/29 : ℝ) * a50 + (6/29 : ℝ) * a55 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2573 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a36 : -(h 1) < (-3/22 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    (a50 : -(h 0) < (-6/41 : ℝ))
    (a54 : -(h 2) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (8/33 : ℝ) * _ctx.lower + (7/264 : ℝ) * a23 + (1/33 : ℝ) * a28 + (8/33 : ℝ) * a36 + (19/88 : ℝ) * a42 + (8/33 : ℝ) * a50 + (8/33 : ℝ) * a54 + (8/33 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2572 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a50 : -(h 0) < (-6/41 : ℝ))
    (a53 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (171/397 : ℝ) * _ctx.min + (363/397 : ℝ) * _ctx.lower + (32/397 : ℝ) * _ctx.fail1 + (21/397 : ℝ) * a23 + (24/397 : ℝ) * a28 + (128/397 : ℝ) * a50 + (192/397 : ℝ) * a53 + (192/397 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2571 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a36 : -(h 1) < (-3/22 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    (a48 : -(h 4) < (-1/9 : ℝ))
    (a52 : -(h 0) < (-5/34 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.lower + (1/23 : ℝ) * _ctx.fail1 + (3/92 : ℝ) * a23 + (6/23 : ℝ) * a36 + (21/92 : ℝ) * a42 + (6/23 : ℝ) * a48 + (4/23 : ℝ) * a52 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2570 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a43 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ))
    (a51 : ((-2 : ℝ) * (delta)) < (-16/71 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a43 + (1 : ℝ) * a51
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2569 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a36 : -(h 1) < (-3/22 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    (a43 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ))
    (a48 : -(h 4) < (-1/9 : ℝ))
    (a50 : -(h 0) < (-6/41 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (16/71 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-16/71 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2570 h delta _ctx _hno a43 f0
  by_cases p1 : h 0 ≤ (5/34 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/34 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2571 h delta _ctx _hno a23 a36 a42 a48 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2572 h delta _ctx _hno a23 a28 a50 f2
  by_cases p3 : h 2 ≤ (3/25 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2573 h delta _ctx _hno a23 a28 a36 a42 a50 f3
  by_cases p4 : h 3 ≤ (5/44 : ℝ)
  swap
  · have f4 : -(h 3) < (-5/44 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2574 h delta _ctx _hno a36 a42 a48 a50 f4
  apply _hno 40
  change (((2 : ℝ) * (delta)) ≤ (16/71 : ℝ)) ∧ (h 0 ≤ (5/34 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (5/44 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_2568 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a43 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ))
    (a49 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a43 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2567 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a36 : -(h 1) < (-3/22 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    (a43 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ))
    (a44 : -(h 0) < (-25/173 : ℝ))
    (a48 : -(h 4) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2568 h delta _ctx _hno a43 f0
  by_cases p1 : h 0 ≤ (6/41 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/41 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2569 h delta _ctx _hno a23 a28 a36 a42 a43 a48 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2575 h delta _ctx _hno a23 a28 a44 f2
  by_cases p3 : h 2 ≤ (4/33 : ℝ)
  swap
  · have f3 : -(h 2) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2576 h delta _ctx _hno a23 a28 a36 a42 a44 f3
  by_cases p4 : h 3 ≤ (3/25 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2577 h delta _ctx _hno a28 a36 a44 f4
  by_cases p5 : h 5 ≤ (2/17 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_2578 h delta _ctx _hno a36 a44 f5
  apply _hno 137
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (6/41 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (4/33 : ℝ)) ∧ (h 3 ≤ (3/25 : ℝ)) ∧ (h 5 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_2566 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a36 : -(h 1) < (-3/22 : ℝ))
    (a44 : -(h 0) < (-25/173 : ℝ))
    (a47 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (19/69 : ℝ) * _ctx.min + (121/207 : ℝ) * _ctx.lower + (7/207 : ℝ) * a23 + (8/207 : ℝ) * a28 + (64/207 : ℝ) * a36 + (64/207 : ℝ) * a44 + (64/207 : ℝ) * a47 + (64/207 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2565 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a36 : -(h 1) < (-3/22 : ℝ))
    (a46 : -(h 0) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (24/1097 : ℝ) * _ctx.lower + (4/1097 : ℝ) * _ctx.fail1 + (24/1097 : ℝ) * a23 + (171/1097 : ℝ) * a25 + (3/1097 : ℝ) * a28 + (24/1097 : ℝ) * a36 + (1042/1097 : ℝ) * a46 + (24/1097 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2564 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a43 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ))
    (a45 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a43 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2563 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a36 : -(h 1) < (-3/22 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    (a43 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ))
    (a44 : -(h 0) < (-25/173 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2564 h delta _ctx _hno a43 f0
  by_cases p1 : h 0 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2565 h delta _ctx _hno a23 a25 a28 a36 f1
  by_cases p2 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2566 h delta _ctx _hno a23 a28 a36 a44 f2
  by_cases p3 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f3 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2567 h delta _ctx _hno a23 a28 a36 a42 a43 a44 f3
  apply _hno 8
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_2562 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a36 : -(h 1) < (-3/22 : ℝ))
    (a49 : -(h 5) < (-6/53 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.order3 + (12/29 : ℝ) * _ctx.order4 + (6/29 : ℝ) * _ctx.lower + (1/29 : ℝ) * _ctx.fail1 + (4/29 : ℝ) * a30 + (6/29 : ℝ) * a36 + (18/29 : ℝ) * a49 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2561 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a36 : -(h 1) < (-3/22 : ℝ))
    (a58 : -(h 5) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.order3 + (12/29 : ℝ) * _ctx.order4 + (6/29 : ℝ) * _ctx.lower + (1/29 : ℝ) * _ctx.fail1 + (4/29 : ℝ) * a30 + (6/29 : ℝ) * a36 + (18/29 : ℝ) * a58 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2560 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a36 : -(h 1) < (-3/22 : ℝ))
    (a57 : -(h 3) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/17 : ℝ) * _ctx.min + (12/17 : ℝ) * _ctx.lower + (1/17 : ℝ) * _ctx.fail1 + (3/68 : ℝ) * a28 + (4/17 : ℝ) * a30 + (6/17 : ℝ) * a36 + (21/68 : ℝ) * a57 + (6/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2559 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a36 : -(h 1) < (-3/22 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    (a48 : -(h 3) < (-4/35 : ℝ))
    (a52 : -(h 4) < (-1/9 : ℝ))
    (a56 : -(h 2) < (-4/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a36 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a48 + (1/6 : ℝ) * a52 + (1/6 : ℝ) * a56 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2558 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a48 : -(h 3) < (-4/35 : ℝ))
    (a55 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/17 : ℝ) * _ctx.min + (12/17 : ℝ) * _ctx.lower + (1/17 : ℝ) * _ctx.fail1 + (3/68 : ℝ) * a28 + (4/17 : ℝ) * a30 + (21/68 : ℝ) * a48 + (6/17 : ℝ) * a55 + (6/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2557 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a45 : h 0 ≤ (8/55 : ℝ))
    (a54 : -(h 0) < (-6/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a45 + (1 : ℝ) * a54
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2556 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a37 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a53 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a37 + (1 : ℝ) * a53
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2555 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a36 : -(h 1) < (-3/22 : ℝ))
    (a37 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    (a45 : h 0 ≤ (8/55 : ℝ))
    (a48 : -(h 3) < (-4/35 : ℝ))
    (a52 : -(h 4) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2556 h delta _ctx _hno a37 f0
  by_cases p1 : h 0 ≤ (6/41 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/41 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2557 h delta _ctx _hno a45 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2558 h delta _ctx _hno a28 a30 a48 f2
  by_cases p3 : h 2 ≤ (4/33 : ℝ)
  swap
  · have f3 : -(h 2) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2559 h delta _ctx _hno a30 a36 a42 a48 a52 f3
  by_cases p4 : h 3 ≤ (3/25 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2560 h delta _ctx _hno a28 a30 a36 f4
  by_cases p5 : h 5 ≤ (2/17 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_2561 h delta _ctx _hno a30 a36 f5
  apply _hno 137
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (6/41 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (4/33 : ℝ)) ∧ (h 3 ≤ (3/25 : ℝ)) ∧ (h 5 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_2554 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a36 : -(h 1) < (-3/22 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    (a48 : -(h 3) < (-4/35 : ℝ))
    (a51 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.lower + (1/40 : ℝ) * a28 + (1/5 : ℝ) * a30 + (1/5 : ℝ) * a36 + (1/5 : ℝ) * a42 + (7/40 : ℝ) * a48 + (1/5 : ℝ) * a51 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2553 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a45 : h 0 ≤ (8/55 : ℝ))
    (a50 : -(h 0) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a45 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2552 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a37 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a49 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a37 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2551 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a36 : -(h 1) < (-3/22 : ℝ))
    (a37 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    (a45 : h 0 ≤ (8/55 : ℝ))
    (a48 : -(h 3) < (-4/35 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2552 h delta _ctx _hno a37 f0
  by_cases p1 : h 0 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2553 h delta _ctx _hno a45 f1
  by_cases p2 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2554 h delta _ctx _hno a28 a30 a36 a42 a48 f2
  by_cases p3 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f3 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2555 h delta _ctx _hno a28 a30 a36 a37 a42 a45 a48 f3
  apply _hno 8
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_2550 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a36 : -(h 1) < (-3/22 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    (a47 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (8/33 : ℝ) * _ctx.lower + (7/264 : ℝ) * a23 + (1/33 : ℝ) * a28 + (8/33 : ℝ) * a30 + (8/33 : ℝ) * a36 + (19/88 : ℝ) * a42 + (8/33 : ℝ) * a47 + (8/33 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2549 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a28 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a46 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (128/397 : ℝ) * _ctx.order0 + (171/397 : ℝ) * _ctx.min + (363/397 : ℝ) * _ctx.lower + (32/397 : ℝ) * _ctx.fail1 + (21/397 : ℝ) * a23 + (24/397 : ℝ) * a28 + (320/397 : ℝ) * a46 + (192/397 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2548 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a36 : -(h 1) < (-3/22 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    (a45 : -(h 0) < (-8/55 : ℝ))
    (a49 : -(h 4) < (-1/9 : ℝ))
    (a54 : -(h 3) < (-5/44 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.lower + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a36 + (6/29 : ℝ) * a42 + (4/29 : ℝ) * a45 + (6/29 : ℝ) * a49 + (6/29 : ℝ) * a54 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

end RealPinwheel.WeakSevenBandData
