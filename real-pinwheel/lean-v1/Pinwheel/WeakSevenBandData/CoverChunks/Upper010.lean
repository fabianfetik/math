import Pinwheel.WeakSevenBandData.CoverChunks.Upper009

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem upper_node_3507 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 3) < (-5/42 : ℝ))
    (a40 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ))
    (a47 : -(h 0) < (-6/43 : ℝ))
    (a53 : -(h 5) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/16 : ℝ) * _ctx.order4 + (1/16 : ℝ) * a13 + (3/16 : ℝ) * a31 + (3/16 : ℝ) * a34 + (3/32 : ℝ) * a40 + (3/16 : ℝ) * a47 + (3/8 : ℝ) * a53 + (3/16 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3506 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a39 : -(h 5) < (-2/19 : ℝ))
    (a40 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ))
    (a47 : -(h 0) < (-6/43 : ℝ))
    (a52 : -(h 4) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/16 : ℝ) * _ctx.order3 + (1/16 : ℝ) * a13 + (3/16 : ℝ) * a31 + (3/16 : ℝ) * a39 + (3/32 : ℝ) * a40 + (3/16 : ℝ) * a47 + (3/8 : ℝ) * a52 + (3/16 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3505 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a39 : -(h 5) < (-2/19 : ℝ))
    (a40 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ))
    (a45 : -(h 4) < (-4/35 : ℝ))
    (a47 : -(h 0) < (-6/43 : ℝ))
    (a51 : -(h 3) < (-4/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/16 : ℝ) * a13 + (3/16 : ℝ) * a31 + (3/16 : ℝ) * a39 + (3/32 : ℝ) * a40 + (3/16 : ℝ) * a45 + (3/16 : ℝ) * a47 + (3/16 : ℝ) * a51 + (3/16 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3504 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 3) < (-5/42 : ℝ))
    (a39 : -(h 5) < (-2/19 : ℝ))
    (a45 : -(h 4) < (-4/35 : ℝ))
    (a47 : -(h 0) < (-6/43 : ℝ))
    (a50 : -(h 1) < (-6/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a31 + (1/6 : ℝ) * a34 + (1/6 : ℝ) * a39 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * a50 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3503 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a49 : -(h 0) < (-6/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3502 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a40 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ))
    (a48 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a40 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3501 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 3) < (-5/42 : ℝ))
    (a39 : -(h 5) < (-2/19 : ℝ))
    (a40 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ))
    (a45 : -(h 4) < (-4/35 : ℝ))
    (a47 : -(h 0) < (-6/43 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3502 h delta _ctx _hno a40 f0
  by_cases p1 : h 0 ≤ (6/41 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/41 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3503 h delta _ctx _hno a30 f1
  by_cases p2 : h 1 ≤ (6/47 : ℝ)
  swap
  · have f2 : -(h 1) < (-6/47 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3504 h delta _ctx _hno a31 a34 a39 a45 a47 f2
  by_cases p3 : h 3 ≤ (4/33 : ℝ)
  swap
  · have f3 : -(h 3) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3505 h delta _ctx _hno a13 a31 a39 a40 a45 a47 f3
  by_cases p4 : h 4 ≤ (3/25 : ℝ)
  swap
  · have f4 : -(h 4) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3506 h delta _ctx _hno a13 a31 a39 a40 a47 f4
  by_cases p5 : h 5 ≤ (2/17 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_3507 h delta _ctx _hno a13 a31 a34 a40 a47 f5
  apply _hno 145
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (6/41 : ℝ)) ∧ (h 1 ≤ (6/47 : ℝ)) ∧ (h 3 ≤ (4/33 : ℝ)) ∧ (h 4 ≤ (3/25 : ℝ)) ∧ (h 5 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_3500 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a40 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ))
    (a46 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a40 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3499 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 3) < (-5/42 : ℝ))
    (a39 : -(h 5) < (-2/19 : ℝ))
    (a40 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ))
    (a41 : -(h 0) < (-5/36 : ℝ))
    (a45 : -(h 4) < (-4/35 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3500 h delta _ctx _hno a40 f0
  by_cases p1 : h 0 ≤ (6/43 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/43 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3501 h delta _ctx _hno a13 a30 a31 a34 a39 a40 a45 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3508 h delta _ctx _hno a31 a34 a41 a45 f2
  by_cases p3 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3509 h delta _ctx _hno a13 a39 a40 a41 a45 f3
  by_cases p4 : h 5 ≤ (5/46 : ℝ)
  swap
  · have f4 : -(h 5) < (-5/46 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3510 h delta _ctx _hno a13 a31 a34 a40 a41 a45 f4
  apply _hno 20
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (6/43 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 5 ≤ (5/46 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_3498 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a39 : -(h 5) < (-2/19 : ℝ))
    (a40 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ))
    (a44 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/43 : ℝ) * _ctx.fail2 + (4/43 : ℝ) * a13 + (12/43 : ℝ) * a31 + (12/43 : ℝ) * a39 + (6/43 : ℝ) * a40 + (12/43 : ℝ) * a44 + (12/43 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3497 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a43 : -(h 0) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3496 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a40 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ))
    (a42 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a40 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3495 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 3) < (-5/42 : ℝ))
    (a39 : -(h 5) < (-2/19 : ℝ))
    (a40 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ))
    (a41 : -(h 0) < (-5/36 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3496 h delta _ctx _hno a40 f0
  by_cases p1 : h 0 ≤ (1/7 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3497 h delta _ctx _hno a30 f1
  by_cases p2 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3498 h delta _ctx _hno a13 a31 a39 a40 f2
  by_cases p3 : h 4 ≤ (4/35 : ℝ)
  swap
  · have f3 : -(h 4) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3499 h delta _ctx _hno a13 a30 a31 a34 a39 a40 a41 f3
  by_cases p4 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3511 h delta _ctx _hno a13 a31 a34 a40 f4
  apply _hno 25
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (1/7 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_3494 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 3) < (-5/42 : ℝ))
    (a55 : -(h 5) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/47 : ℝ) * _ctx.order1 + (3/47 : ℝ) * _ctx.fail2 + (2/47 : ℝ) * a13 + (18/47 : ℝ) * a31 + (12/47 : ℝ) * a34 + (12/47 : ℝ) * a55 + (12/47 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3493 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a49 : -(h 5) < (-5/46 : ℝ))
    (a54 : -(h 4) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (12/89 : ℝ) * _ctx.order1 + (18/89 : ℝ) * _ctx.order3 + (3/89 : ℝ) * _ctx.fail3 + (2/89 : ℝ) * a13 + (30/89 : ℝ) * a31 + (18/89 : ℝ) * a49 + (36/89 : ℝ) * a54 + (18/89 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3492 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a49 : -(h 5) < (-5/46 : ℝ))
    (a53 : -(h 3) < (-4/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/47 : ℝ) * _ctx.order1 + (3/47 : ℝ) * _ctx.fail2 + (2/47 : ℝ) * a13 + (18/47 : ℝ) * a31 + (12/47 : ℝ) * a49 + (12/47 : ℝ) * a53 + (12/47 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3491 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 3) < (-5/42 : ℝ))
    (a49 : -(h 5) < (-5/46 : ℝ))
    (a52 : -(h 1) < (-6/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/17 : ℝ) * _ctx.lower + (1/17 : ℝ) * _ctx.fail2 + (4/17 : ℝ) * a31 + (4/17 : ℝ) * a34 + (4/17 : ℝ) * a49 + (4/17 : ℝ) * a52 + (4/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3490 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a42 : h 0 ≤ (5/37 : ℝ))
    (a51 : -(h 0) < (-6/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a42 + (1 : ℝ) * a51
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3489 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a35 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a50 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a35 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3488 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 3) < (-5/42 : ℝ))
    (a35 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a42 : h 0 ≤ (5/37 : ℝ))
    (a49 : -(h 5) < (-5/46 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3489 h delta _ctx _hno a35 f0
  by_cases p1 : h 0 ≤ (6/41 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/41 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3490 h delta _ctx _hno a42 f1
  by_cases p2 : h 1 ≤ (6/47 : ℝ)
  swap
  · have f2 : -(h 1) < (-6/47 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3491 h delta _ctx _hno a31 a34 a49 f2
  by_cases p3 : h 3 ≤ (4/33 : ℝ)
  swap
  · have f3 : -(h 3) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3492 h delta _ctx _hno a13 a31 a49 f3
  by_cases p4 : h 4 ≤ (3/25 : ℝ)
  swap
  · have f4 : -(h 4) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3493 h delta _ctx _hno a13 a31 a49 f4
  by_cases p5 : h 5 ≤ (2/17 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_3494 h delta _ctx _hno a13 a31 a34 f5
  apply _hno 145
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (6/41 : ℝ)) ∧ (h 1 ≤ (6/47 : ℝ)) ∧ (h 3 ≤ (4/33 : ℝ)) ∧ (h 4 ≤ (3/25 : ℝ)) ∧ (h 5 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_3487 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a44 : -(h 5) < (-4/37 : ℝ))
    (a48 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/47 : ℝ) * _ctx.order1 + (18/47 : ℝ) * _ctx.order2 + (3/47 : ℝ) * _ctx.fail2 + (2/47 : ℝ) * a13 + (12/47 : ℝ) * a44 + (30/47 : ℝ) * a48 + (12/47 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3486 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 3) < (-5/42 : ℝ))
    (a44 : -(h 5) < (-4/37 : ℝ))
    (a47 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/17 : ℝ) * _ctx.lower + (1/17 : ℝ) * _ctx.fail2 + (4/17 : ℝ) * a31 + (4/17 : ℝ) * a34 + (4/17 : ℝ) * a44 + (4/17 : ℝ) * a47 + (4/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3485 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a42 : h 0 ≤ (5/37 : ℝ))
    (a46 : -(h 0) < (-6/43 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a42 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3484 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a35 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a45 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a35 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3483 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 3) < (-5/42 : ℝ))
    (a35 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a42 : h 0 ≤ (5/37 : ℝ))
    (a44 : -(h 5) < (-4/37 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3484 h delta _ctx _hno a35 f0
  by_cases p1 : h 0 ≤ (6/43 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/43 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3485 h delta _ctx _hno a42 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3486 h delta _ctx _hno a31 a34 a44 f2
  by_cases p3 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3487 h delta _ctx _hno a13 a44 f3
  by_cases p4 : h 5 ≤ (5/46 : ℝ)
  swap
  · have f4 : -(h 5) < (-5/46 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3488 h delta _ctx _hno a13 a31 a34 a35 a42 f4
  apply _hno 20
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (6/43 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 5 ≤ (5/46 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_3482 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a34 : -(h 3) < (-5/42 : ℝ))
    (a43 : -(h 2) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/13 : ℝ) * _ctx.order1 + (4/13 : ℝ) * _ctx.min + (8/13 : ℝ) * _ctx.lower + (1/13 : ℝ) * _ctx.fail2 + (4/13 : ℝ) * a34 + (8/13 : ℝ) * a43 + (4/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3481 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 3) < (-5/42 : ℝ))
    (a47 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/47 : ℝ) * _ctx.order1 + (3/47 : ℝ) * _ctx.fail2 + (2/47 : ℝ) * a13 + (18/47 : ℝ) * a31 + (12/47 : ℝ) * a34 + (12/47 : ℝ) * a47 + (12/47 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3480 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 3) < (-5/42 : ℝ))
    (a57 : -(h 5) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/47 : ℝ) * _ctx.order1 + (3/47 : ℝ) * _ctx.fail2 + (2/47 : ℝ) * a13 + (18/47 : ℝ) * a31 + (12/47 : ℝ) * a34 + (12/47 : ℝ) * a57 + (12/47 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3479 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a42 : -(h 0) < (-5/37 : ℝ))
    (a51 : -(h 5) < (-5/46 : ℝ))
    (a56 : -(h 4) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/34 : ℝ) * _ctx.order1 + (3/17 : ℝ) * _ctx.order3 + (1/34 : ℝ) * a13 + (9/34 : ℝ) * a31 + (3/17 : ℝ) * a42 + (3/17 : ℝ) * a51 + (6/17 : ℝ) * a56 + (3/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3478 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a51 : -(h 5) < (-5/46 : ℝ))
    (a55 : -(h 3) < (-4/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/47 : ℝ) * _ctx.order1 + (3/47 : ℝ) * _ctx.fail2 + (2/47 : ℝ) * a13 + (18/47 : ℝ) * a31 + (12/47 : ℝ) * a51 + (12/47 : ℝ) * a55 + (12/47 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3477 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 3) < (-5/42 : ℝ))
    (a51 : -(h 5) < (-5/46 : ℝ))
    (a54 : -(h 1) < (-6/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/17 : ℝ) * _ctx.lower + (1/17 : ℝ) * _ctx.fail2 + (4/17 : ℝ) * a31 + (4/17 : ℝ) * a34 + (4/17 : ℝ) * a51 + (4/17 : ℝ) * a54 + (4/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3476 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a48 : h 0 ≤ (6/43 : ℝ))
    (a53 : -(h 0) < (-6/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a48 + (1 : ℝ) * a53
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3475 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a35 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a52 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a35 + (1 : ℝ) * a52
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3474 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 3) < (-5/42 : ℝ))
    (a35 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a42 : -(h 0) < (-5/37 : ℝ))
    (a48 : h 0 ≤ (6/43 : ℝ))
    (a51 : -(h 5) < (-5/46 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3475 h delta _ctx _hno a35 f0
  by_cases p1 : h 0 ≤ (6/41 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/41 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3476 h delta _ctx _hno a48 f1
  by_cases p2 : h 1 ≤ (6/47 : ℝ)
  swap
  · have f2 : -(h 1) < (-6/47 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3477 h delta _ctx _hno a31 a34 a51 f2
  by_cases p3 : h 3 ≤ (4/33 : ℝ)
  swap
  · have f3 : -(h 3) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3478 h delta _ctx _hno a13 a31 a51 f3
  by_cases p4 : h 4 ≤ (3/25 : ℝ)
  swap
  · have f4 : -(h 4) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3479 h delta _ctx _hno a13 a31 a42 a51 f4
  by_cases p5 : h 5 ≤ (2/17 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_3480 h delta _ctx _hno a13 a31 a34 f5
  apply _hno 145
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (6/41 : ℝ)) ∧ (h 1 ≤ (6/47 : ℝ)) ∧ (h 3 ≤ (4/33 : ℝ)) ∧ (h 4 ≤ (3/25 : ℝ)) ∧ (h 5 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_3473 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a39 : -(h 5) < (-2/19 : ℝ))
    (a50 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/47 : ℝ) * _ctx.order1 + (18/47 : ℝ) * _ctx.order2 + (3/47 : ℝ) * _ctx.fail2 + (2/47 : ℝ) * a13 + (12/47 : ℝ) * a39 + (30/47 : ℝ) * a50 + (12/47 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3472 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 3) < (-5/42 : ℝ))
    (a39 : -(h 5) < (-2/19 : ℝ))
    (a49 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/17 : ℝ) * _ctx.lower + (1/17 : ℝ) * _ctx.fail2 + (4/17 : ℝ) * a31 + (4/17 : ℝ) * a34 + (4/17 : ℝ) * a39 + (4/17 : ℝ) * a49 + (4/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3471 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 3) < (-5/42 : ℝ))
    (a48 : -(h 0) < (-6/43 : ℝ))
    (a54 : -(h 5) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/34 : ℝ) * _ctx.order1 + (3/17 : ℝ) * _ctx.order4 + (1/34 : ℝ) * a13 + (9/34 : ℝ) * a31 + (3/17 : ℝ) * a34 + (3/17 : ℝ) * a48 + (6/17 : ℝ) * a54 + (3/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3470 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a48 : -(h 0) < (-6/43 : ℝ))
    (a53 : -(h 4) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/13 : ℝ) * _ctx.order3 + (3/13 : ℝ) * _ctx.min + (1/13 : ℝ) * a13 + (3/13 : ℝ) * a31 + (3/13 : ℝ) * a48 + (6/13 : ℝ) * a53 + (3/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3469 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a39 : -(h 5) < (-2/19 : ℝ))
    (a46 : -(h 4) < (-4/35 : ℝ))
    (a48 : -(h 0) < (-6/43 : ℝ))
    (a52 : -(h 3) < (-4/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/34 : ℝ) * _ctx.order1 + (1/34 : ℝ) * a13 + (9/34 : ℝ) * a31 + (3/17 : ℝ) * a39 + (3/17 : ℝ) * a46 + (3/17 : ℝ) * a48 + (3/17 : ℝ) * a52 + (3/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3468 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 3) < (-5/42 : ℝ))
    (a39 : -(h 5) < (-2/19 : ℝ))
    (a46 : -(h 4) < (-4/35 : ℝ))
    (a48 : -(h 0) < (-6/43 : ℝ))
    (a51 : -(h 1) < (-6/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a31 + (1/6 : ℝ) * a34 + (1/6 : ℝ) * a39 + (1/6 : ℝ) * a46 + (1/6 : ℝ) * a48 + (1/6 : ℝ) * a51 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3467 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a50 : -(h 0) < (-6/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3466 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a35 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a49 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a35 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3465 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 3) < (-5/42 : ℝ))
    (a35 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a39 : -(h 5) < (-2/19 : ℝ))
    (a46 : -(h 4) < (-4/35 : ℝ))
    (a48 : -(h 0) < (-6/43 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3466 h delta _ctx _hno a35 f0
  by_cases p1 : h 0 ≤ (6/41 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/41 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3467 h delta _ctx _hno a30 f1
  by_cases p2 : h 1 ≤ (6/47 : ℝ)
  swap
  · have f2 : -(h 1) < (-6/47 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3468 h delta _ctx _hno a31 a34 a39 a46 a48 f2
  by_cases p3 : h 3 ≤ (4/33 : ℝ)
  swap
  · have f3 : -(h 3) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3469 h delta _ctx _hno a13 a31 a39 a46 a48 f3
  by_cases p4 : h 4 ≤ (3/25 : ℝ)
  swap
  · have f4 : -(h 4) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3470 h delta _ctx _hno a13 a31 a48 f4
  by_cases p5 : h 5 ≤ (2/17 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_3471 h delta _ctx _hno a13 a31 a34 a48 f5
  apply _hno 145
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (6/41 : ℝ)) ∧ (h 1 ≤ (6/47 : ℝ)) ∧ (h 3 ≤ (4/33 : ℝ)) ∧ (h 4 ≤ (3/25 : ℝ)) ∧ (h 5 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_3464 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a35 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a47 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a35 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3463 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 3) < (-5/42 : ℝ))
    (a35 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a39 : -(h 5) < (-2/19 : ℝ))
    (a42 : -(h 0) < (-5/37 : ℝ))
    (a46 : -(h 4) < (-4/35 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3464 h delta _ctx _hno a35 f0
  by_cases p1 : h 0 ≤ (6/43 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/43 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3465 h delta _ctx _hno a13 a30 a31 a34 a35 a39 a46 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3472 h delta _ctx _hno a31 a34 a39 f2
  by_cases p3 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3473 h delta _ctx _hno a13 a39 f3
  by_cases p4 : h 5 ≤ (5/46 : ℝ)
  swap
  · have f4 : -(h 5) < (-5/46 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3474 h delta _ctx _hno a13 a31 a34 a35 a42 p1 f4
  apply _hno 20
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (6/43 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 5 ≤ (5/46 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_3462 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a39 : -(h 5) < (-2/19 : ℝ))
    (a45 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/47 : ℝ) * _ctx.order1 + (3/47 : ℝ) * _ctx.fail2 + (2/47 : ℝ) * a13 + (18/47 : ℝ) * a31 + (12/47 : ℝ) * a39 + (12/47 : ℝ) * a45 + (12/47 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3461 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a44 : -(h 0) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3460 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a35 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a35 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3459 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 3) < (-5/42 : ℝ))
    (a35 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a39 : -(h 5) < (-2/19 : ℝ))
    (a42 : -(h 0) < (-5/37 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3460 h delta _ctx _hno a35 f0
  by_cases p1 : h 0 ≤ (1/7 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3461 h delta _ctx _hno a30 f1
  by_cases p2 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3462 h delta _ctx _hno a13 a31 a39 f2
  by_cases p3 : h 4 ≤ (4/35 : ℝ)
  swap
  · have f3 : -(h 4) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3463 h delta _ctx _hno a13 a30 a31 a34 a35 a39 a42 f3
  by_cases p4 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3481 h delta _ctx _hno a13 a31 a34 f4
  apply _hno 25
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (1/7 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_3458 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a35 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-7/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a35 + (1 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3457 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 3) < (-5/42 : ℝ))
    (a35 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a39 : -(h 5) < (-2/19 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/33 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/33 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3458 h delta _ctx _hno a35 f0
  by_cases p1 : h 0 ≤ (5/37 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/37 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3459 h delta _ctx _hno a13 a30 a31 a34 a35 a39 f1
  by_cases p2 : h 2 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 2) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3482 h delta _ctx _hno a34 f2
  by_cases p3 : h 5 ≤ (4/37 : ℝ)
  swap
  · have f3 : -(h 5) < (-4/37 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3483 h delta _ctx _hno a13 a31 a34 a35 p1 f3
  apply _hno 23
  change (((2 : ℝ) * (delta)) ≤ (7/33 : ℝ)) ∧ (h 0 ≤ (5/37 : ℝ)) ∧ (h 2 ≤ (2/15 : ℝ)) ∧ (h 5 ≤ (4/37 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_3456 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 3) < (-5/42 : ℝ))
    (a35 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a39 : -(h 5) < (-2/19 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3457 h delta _ctx _hno a13 a30 a31 a34 a35 a39
  by_cases p1 : h 0 ≤ (5/36 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/36 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3495 h delta _ctx _hno a13 a30 a31 a34 a39 p0 f1
  by_cases p2 : h 1 ≤ (9/65 : ℝ)
  swap
  · have f2 : -(h 1) < (-9/65 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3512 h delta _ctx _hno a31 a34 f2
  by_cases p3 : h 2 ≤ (3/22 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3513 h delta _ctx _hno a34 f3
  by_cases p4 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3514 h delta _ctx _hno a13 a31 a39 p0 f4
  by_cases p5 : h 4 ≤ (5/41 : ℝ)
  swap
  · have f5 : -(h 4) < (-5/41 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_3515 h delta _ctx _hno a13 a31 a39 p0 f5
  apply _hno 22
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (5/36 : ℝ)) ∧ (h 1 ≤ (9/65 : ℝ)) ∧ (h 2 ≤ (3/22 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (5/41 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_3455 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a38 : -(h 4) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/65 : ℝ) * _ctx.order1 + (21/65 : ℝ) * _ctx.order2 + (3/5 : ℝ) * _ctx.order3 + (18/65 : ℝ) * _ctx.min + (3/65 : ℝ) * _ctx.fail3 + (1/13 : ℝ) * a13 + (57/65 : ℝ) * a38 + (18/65 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3454 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a34 : -(h 3) < (-5/42 : ℝ))
    (a37 : -(h 2) < (-5/38 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/13 : ℝ) * _ctx.order1 + (4/13 : ℝ) * _ctx.min + (8/13 : ℝ) * _ctx.lower + (1/13 : ℝ) * _ctx.fail2 + (4/13 : ℝ) * a34 + (8/13 : ℝ) * a37 + (4/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3453 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : h 0 ≤ (1/7 : ℝ))
    (a36 : -(h 0) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a36
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3452 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 3) < (-5/42 : ℝ))
    (a51 : -(h 5) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/47 : ℝ) * _ctx.order1 + (3/47 : ℝ) * _ctx.fail2 + (2/47 : ℝ) * a13 + (18/47 : ℝ) * a31 + (12/47 : ℝ) * a34 + (12/47 : ℝ) * a51 + (12/47 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3451 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a35 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a45 : -(h 5) < (-5/46 : ℝ))
    (a50 : -(h 4) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/11 : ℝ) * _ctx.order1 + (2/11 : ℝ) * _ctx.order3 + (1/33 : ℝ) * _ctx.fail3 + (4/11 : ℝ) * a31 + (2/33 : ℝ) * a35 + (2/11 : ℝ) * a45 + (4/11 : ℝ) * a50 + (2/11 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3450 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a35 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a45 : -(h 5) < (-5/46 : ℝ))
    (a49 : -(h 3) < (-4/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/19 : ℝ) * _ctx.order1 + (1/19 : ℝ) * _ctx.fail2 + (8/19 : ℝ) * a31 + (2/19 : ℝ) * a35 + (4/19 : ℝ) * a45 + (4/19 : ℝ) * a49 + (4/19 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3449 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 3) < (-5/42 : ℝ))
    (a35 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a45 : -(h 5) < (-5/46 : ℝ))
    (a48 : -(h 1) < (-6/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/19 : ℝ) * _ctx.fail2 + (4/19 : ℝ) * a31 + (4/19 : ℝ) * a34 + (2/19 : ℝ) * a35 + (4/19 : ℝ) * a45 + (4/19 : ℝ) * a48 + (4/19 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3448 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a42 : h 0 ≤ (6/43 : ℝ))
    (a47 : -(h 0) < (-6/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a42 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3447 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a46 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a32 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3446 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a32 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a34 : -(h 3) < (-5/42 : ℝ))
    (a35 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a42 : h 0 ≤ (6/43 : ℝ))
    (a45 : -(h 5) < (-5/46 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3447 h delta _ctx _hno a32 f0
  by_cases p1 : h 0 ≤ (6/41 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/41 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3448 h delta _ctx _hno a42 f1
  by_cases p2 : h 1 ≤ (6/47 : ℝ)
  swap
  · have f2 : -(h 1) < (-6/47 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3449 h delta _ctx _hno a31 a34 a35 a45 f2
  by_cases p3 : h 3 ≤ (4/33 : ℝ)
  swap
  · have f3 : -(h 3) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3450 h delta _ctx _hno a31 a35 a45 f3
  by_cases p4 : h 4 ≤ (3/25 : ℝ)
  swap
  · have f4 : -(h 4) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3451 h delta _ctx _hno a31 a35 a45 f4
  by_cases p5 : h 5 ≤ (2/17 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_3452 h delta _ctx _hno a13 a31 a34 f5
  apply _hno 145
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (6/41 : ℝ)) ∧ (h 1 ≤ (6/47 : ℝ)) ∧ (h 3 ≤ (4/33 : ℝ)) ∧ (h 4 ≤ (3/25 : ℝ)) ∧ (h 5 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_3445 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a35 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a44 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/17 : ℝ) * _ctx.order1 + (4/17 : ℝ) * _ctx.min + (1/17 : ℝ) * _ctx.fail2 + (8/17 : ℝ) * a31 + (4/17 : ℝ) * a35 + (4/17 : ℝ) * a44 + (4/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3444 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a38 : h 1 ≤ (7/54 : ℝ))
    (a43 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a38 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3443 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 3) < (-5/42 : ℝ))
    (a42 : -(h 0) < (-6/43 : ℝ))
    (a48 : -(h 5) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/34 : ℝ) * _ctx.order1 + (3/17 : ℝ) * _ctx.order4 + (1/34 : ℝ) * a13 + (9/34 : ℝ) * a31 + (3/17 : ℝ) * a34 + (3/17 : ℝ) * a42 + (6/17 : ℝ) * a48 + (3/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3442 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a35 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a42 : -(h 0) < (-6/43 : ℝ))
    (a47 : -(h 4) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order1 + (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/3 : ℝ) * a31 + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a42 + (1/3 : ℝ) * a47 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3441 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a35 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a40 : -(h 4) < (-1/9 : ℝ))
    (a42 : -(h 0) < (-6/43 : ℝ))
    (a46 : -(h 3) < (-4/33 : ℝ))
    (a51 : -(h 5) < (-3/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order1 + (4/13 : ℝ) * a31 + (1/13 : ℝ) * a35 + (2/13 : ℝ) * a40 + (2/13 : ℝ) * a42 + (2/13 : ℝ) * a46 + (2/13 : ℝ) * a51 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3440 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a35 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a50 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/17 : ℝ) * _ctx.order1 + (4/17 : ℝ) * _ctx.min + (1/17 : ℝ) * _ctx.fail2 + (8/17 : ℝ) * a31 + (4/17 : ℝ) * a35 + (4/17 : ℝ) * a50 + (4/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3439 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a45 : h 1 ≤ (6/47 : ℝ))
    (a49 : -(h 1) < (-4/31 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a45 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3438 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a35 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a40 : -(h 4) < (-1/9 : ℝ))
    (a46 : -(h 3) < (-4/33 : ℝ))
    (a48 : -(h 0) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order1 + (1/6 : ℝ) * _ctx.min + (1/3 : ℝ) * a31 + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a40 + (1/6 : ℝ) * a46 + (1/6 : ℝ) * a48 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3437 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a46 : -(h 3) < (-4/33 : ℝ))
    (a47 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/17 : ℝ) * _ctx.order1 + (4/17 : ℝ) * _ctx.min + (1/17 : ℝ) * _ctx.fail2 + (8/17 : ℝ) * a31 + (4/17 : ℝ) * a46 + (4/17 : ℝ) * a47 + (4/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3436 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a35 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a40 : -(h 4) < (-1/9 : ℝ))
    (a42 : -(h 0) < (-6/43 : ℝ))
    (a45 : h 1 ≤ (6/47 : ℝ))
    (a46 : -(h 3) < (-4/33 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3437 h delta _ctx _hno a31 a46 f0
  by_cases p1 : h 0 ≤ (1/7 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3438 h delta _ctx _hno a31 a35 a40 a46 f1
  by_cases p2 : h 1 ≤ (4/31 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/31 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3439 h delta _ctx _hno a45 f2
  by_cases p3 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3440 h delta _ctx _hno a31 a35 f3
  by_cases p4 : h 5 ≤ (3/28 : ℝ)
  swap
  · have f4 : -(h 5) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3441 h delta _ctx _hno a31 a35 a40 a42 a46 f4
  apply _hno 149
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (1/7 : ℝ)) ∧ (h 1 ≤ (4/31 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 5 ≤ (3/28 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_3435 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 3) < (-5/42 : ℝ))
    (a35 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a45 : -(h 1) < (-6/47 : ℝ))
    (a52 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/19 : ℝ) * _ctx.fail2 + (4/19 : ℝ) * a31 + (4/19 : ℝ) * a34 + (2/19 : ℝ) * a35 + (4/19 : ℝ) * a45 + (4/19 : ℝ) * a52 + (4/19 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3434 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 3) < (-5/42 : ℝ))
    (a35 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a42 : -(h 0) < (-6/43 : ℝ))
    (a45 : -(h 1) < (-6/47 : ℝ))
    (a51 : -(h 4) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a31 + (1/6 : ℝ) * a34 + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a51 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3433 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a35 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a40 : -(h 4) < (-1/9 : ℝ))
    (a42 : -(h 0) < (-6/43 : ℝ))
    (a45 : -(h 1) < (-6/47 : ℝ))
    (a50 : -(h 3) < (-8/67 : ℝ))
    (a55 : -(h 5) < (-3/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * a31 + (1/13 : ℝ) * a35 + (2/13 : ℝ) * a40 + (2/13 : ℝ) * a42 + (2/13 : ℝ) * a45 + (2/13 : ℝ) * a50 + (2/13 : ℝ) * a55 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3432 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a35 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a45 : -(h 1) < (-6/47 : ℝ))
    (a54 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/17 : ℝ) * _ctx.order2 + (4/17 : ℝ) * _ctx.min + (1/17 : ℝ) * _ctx.fail2 + (4/17 : ℝ) * a35 + (4/17 : ℝ) * a45 + (8/17 : ℝ) * a54 + (4/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3431 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a35 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a40 : -(h 4) < (-1/9 : ℝ))
    (a42 : -(h 0) < (-6/43 : ℝ))
    (a50 : -(h 3) < (-8/67 : ℝ))
    (a53 : -(h 1) < (-4/31 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a31 + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a40 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a50 + (1/6 : ℝ) * a53 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3430 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a35 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a40 : -(h 4) < (-1/9 : ℝ))
    (a45 : -(h 1) < (-6/47 : ℝ))
    (a50 : -(h 3) < (-8/67 : ℝ))
    (a52 : -(h 0) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a31 + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a40 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a50 + (1/6 : ℝ) * a52 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3429 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a45 : -(h 1) < (-6/47 : ℝ))
    (a50 : -(h 3) < (-8/67 : ℝ))
    (a51 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/17 : ℝ) * _ctx.min + (1/17 : ℝ) * _ctx.fail2 + (4/17 : ℝ) * a31 + (4/17 : ℝ) * a45 + (4/17 : ℝ) * a50 + (4/17 : ℝ) * a51 + (4/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3428 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : -(h 2) < (-1/8 : ℝ))
    (a35 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a40 : -(h 4) < (-1/9 : ℝ))
    (a42 : -(h 0) < (-6/43 : ℝ))
    (a45 : -(h 1) < (-6/47 : ℝ))
    (a50 : -(h 3) < (-8/67 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3429 h delta _ctx _hno a31 a45 a50 f0
  by_cases p1 : h 0 ≤ (1/7 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3430 h delta _ctx _hno a31 a35 a40 a45 a50 f1
  by_cases p2 : h 1 ≤ (4/31 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/31 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3431 h delta _ctx _hno a31 a35 a40 a42 a50 f2
  by_cases p3 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3432 h delta _ctx _hno a35 a45 f3
  by_cases p4 : h 5 ≤ (3/28 : ℝ)
  swap
  · have f4 : -(h 5) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3433 h delta _ctx _hno a31 a35 a40 a42 a45 a50 f4
  apply _hno 149
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (1/7 : ℝ)) ∧ (h 1 ≤ (4/31 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 5 ≤ (3/28 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

end RealPinwheel.WeakSevenBandData
