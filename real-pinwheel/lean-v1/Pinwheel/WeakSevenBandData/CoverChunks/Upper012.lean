import Pinwheel.WeakSevenBandData.CoverChunks.Upper011

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem upper_node_3347 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a40 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * a14 + (1/5 : ℝ) * a30 + (4/5 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3346 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a30 : -(h 0) < (-1/7 : ℝ))
    (a33 : h 1 ≤ (9/70 : ℝ))
    (a35 : -(h 4) < (-4/35 : ℝ))
    (a37 : h 0 ≤ (6/41 : ℝ))
    (a39 : -(h 2) < (-4/33 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3347 h delta _ctx _hno a14 a30 f0
  by_cases p1 : h 0 ≤ (5/34 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/34 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3348 h delta _ctx _hno a37 f1
  by_cases p2 : h 1 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3349 h delta _ctx _hno a33 f2
  by_cases p3 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3350 h delta _ctx _hno a13 a14 a30 a33 a35 a37 a39 f3
  apply _hno 92
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (5/34 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_3345 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : h 1 ≤ (9/70 : ℝ))
    (a38 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a38
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3344 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a41 : h 3 ≤ (3/26 : ℝ))
    (a49 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a41 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3343 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : h 1 ≤ (9/70 : ℝ))
    (a48 : -(h 1) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3342 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a35 : -(h 4) < (-4/35 : ℝ))
    (a42 : -(h 5) < (-1/9 : ℝ))
    (a45 : -(h 1) < (-1/8 : ℝ))
    (a47 : -(h 0) < (-5/34 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/9 : ℝ) * _ctx.order3 + (1/27 : ℝ) * _ctx.fail1 + (1/27 : ℝ) * a13 + (4/9 : ℝ) * a35 + (2/9 : ℝ) * a42 + (1/9 : ℝ) * a45 + (4/27 : ℝ) * a47 + (2/9 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3341 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a37 : -(h 0) < (-6/41 : ℝ))
    (a46 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * a14 + (1/5 : ℝ) * a37 + (4/5 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3340 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a33 : h 1 ≤ (9/70 : ℝ))
    (a35 : -(h 4) < (-4/35 : ℝ))
    (a37 : -(h 0) < (-6/41 : ℝ))
    (a41 : h 3 ≤ (3/26 : ℝ))
    (a42 : -(h 5) < (-1/9 : ℝ))
    (a45 : -(h 1) < (-1/8 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3341 h delta _ctx _hno a14 a37 f0
  by_cases p1 : h 0 ≤ (5/34 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/34 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3342 h delta _ctx _hno a13 a35 a42 a45 f1
  by_cases p2 : h 1 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3343 h delta _ctx _hno a33 f2
  by_cases p3 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3344 h delta _ctx _hno a41 f3
  apply _hno 92
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (5/34 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_3339 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a44 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/55 : ℝ) * a20 + (1/55 : ℝ) * a23 + (8/55 : ℝ) * a25 + (54/55 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3338 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a37 : -(h 0) < (-6/41 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * a14 + (1/5 : ℝ) * a37 + (4/5 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3337 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a20 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a33 : h 1 ≤ (9/70 : ℝ))
    (a35 : -(h 4) < (-4/35 : ℝ))
    (a37 : -(h 0) < (-6/41 : ℝ))
    (a41 : h 3 ≤ (3/26 : ℝ))
    (a42 : -(h 5) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3338 h delta _ctx _hno a14 a37 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3339 h delta _ctx _hno a20 a23 a25 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3340 h delta _ctx _hno a13 a14 a33 a35 a37 a41 a42 f2
  apply _hno 2
  change (((2 : ℝ) * (delta)) ≤ (7/32 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem upper_node_3336 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a35 : -(h 4) < (-4/35 : ℝ))
    (a37 : -(h 0) < (-6/41 : ℝ))
    (a41 : -(h 3) < (-3/26 : ℝ))
    (a53 : -(h 5) < (-1/9 : ℝ))
    (a56 : -(h 1) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/27 : ℝ) * _ctx.fail1 + (1/27 : ℝ) * a13 + (2/9 : ℝ) * a35 + (4/27 : ℝ) * a37 + (2/9 : ℝ) * a41 + (2/9 : ℝ) * a53 + (1/9 : ℝ) * a56 + (2/9 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3335 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a43 : h 0 ≤ (4/27 : ℝ))
    (a55 : -(h 0) < (-4/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a43 + (1 : ℝ) * a55
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3334 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a42 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a54 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a42 + (1 : ℝ) * a54
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3333 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a35 : -(h 4) < (-4/35 : ℝ))
    (a37 : -(h 0) < (-6/41 : ℝ))
    (a41 : -(h 3) < (-3/26 : ℝ))
    (a42 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a43 : h 0 ≤ (4/27 : ℝ))
    (a53 : -(h 5) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3334 h delta _ctx _hno a42 f0
  by_cases p1 : h 0 ≤ (4/25 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/25 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3335 h delta _ctx _hno a43 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3336 h delta _ctx _hno a13 a35 a37 a41 a53 f2
  apply _hno 83
  change (((2 : ℝ) * (delta)) ≤ (10/47 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem upper_node_3332 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a35 : -(h 4) < (-4/35 : ℝ))
    (a37 : -(h 0) < (-6/41 : ℝ))
    (a52 : -(h 3) < (-2/17 : ℝ))
    (a55 : -(h 1) < (-1/8 : ℝ))
    (a60 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/27 : ℝ) * _ctx.fail1 + (1/27 : ℝ) * a13 + (2/9 : ℝ) * a35 + (4/27 : ℝ) * a37 + (2/9 : ℝ) * a52 + (1/9 : ℝ) * a55 + (2/9 : ℝ) * a60 + (2/9 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3331 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a51 : h 2 ≤ (3/25 : ℝ))
    (a59 : -(h 2) < (-4/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a51 + (1 : ℝ) * a59
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3330 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a37 : -(h 0) < (-6/41 : ℝ))
    (a47 : -(h 5) < (-2/19 : ℝ))
    (a58 : -(h 1) < (-15/118 : ℝ))
    (a63 : -(h 4) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.order3 + (6/29 : ℝ) * _ctx.lower + (1/29 : ℝ) * _ctx.fail1 + (4/29 : ℝ) * a37 + (6/29 : ℝ) * a47 + (6/29 : ℝ) * a58 + (12/29 : ℝ) * a63 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3329 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a35 : -(h 4) < (-4/35 : ℝ))
    (a37 : -(h 0) < (-6/41 : ℝ))
    (a47 : -(h 5) < (-2/19 : ℝ))
    (a52 : -(h 3) < (-2/17 : ℝ))
    (a58 : -(h 1) < (-15/118 : ℝ))
    (a62 : -(h 2) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * a52 + (1/6 : ℝ) * a58 + (1/6 : ℝ) * a62 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3328 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a35 : -(h 4) < (-4/35 : ℝ))
    (a37 : -(h 0) < (-6/41 : ℝ))
    (a47 : -(h 5) < (-2/19 : ℝ))
    (a52 : -(h 3) < (-2/17 : ℝ))
    (a61 : -(h 1) < (-5/39 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.lower + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a35 + (4/29 : ℝ) * a37 + (6/29 : ℝ) * a47 + (6/29 : ℝ) * a52 + (6/29 : ℝ) * a61 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3327 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a52 : -(h 3) < (-2/17 : ℝ))
    (a60 : -(h 0) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/7 : ℝ) * a25 + (1/7 : ℝ) * a52 + (6/7 : ℝ) * a60
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3326 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a35 : -(h 4) < (-4/35 : ℝ))
    (a37 : -(h 0) < (-6/41 : ℝ))
    (a52 : -(h 3) < (-2/17 : ℝ))
    (a58 : -(h 1) < (-15/118 : ℝ))
    (a59 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.min + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a35 + (4/29 : ℝ) * a37 + (6/29 : ℝ) * a52 + (6/29 : ℝ) * a58 + (6/29 : ℝ) * a59 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3325 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a35 : -(h 4) < (-4/35 : ℝ))
    (a37 : -(h 0) < (-6/41 : ℝ))
    (a47 : -(h 5) < (-2/19 : ℝ))
    (a52 : -(h 3) < (-2/17 : ℝ))
    (a58 : -(h 1) < (-15/118 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3326 h delta _ctx _hno a35 a37 a52 a58 f0
  by_cases p1 : h 0 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3327 h delta _ctx _hno a25 a52 f1
  by_cases p2 : h 1 ≤ (5/39 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/39 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3328 h delta _ctx _hno a35 a37 a47 a52 f2
  by_cases p3 : h 2 ≤ (3/25 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3329 h delta _ctx _hno a35 a37 a47 a52 a58 f3
  by_cases p4 : h 4 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 4) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3330 h delta _ctx _hno a37 a47 a58 f4
  apply _hno 135
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 1 ≤ (5/39 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_3324 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a52 : -(h 3) < (-2/17 : ℝ))
    (a57 : -(h 0) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/7 : ℝ) * a25 + (1/7 : ℝ) * a52 + (6/7 : ℝ) * a57
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3323 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a42 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a56 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a42 + (1 : ℝ) * a56
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3322 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a35 : -(h 4) < (-4/35 : ℝ))
    (a37 : -(h 0) < (-6/41 : ℝ))
    (a42 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a47 : -(h 5) < (-2/19 : ℝ))
    (a51 : h 2 ≤ (3/25 : ℝ))
    (a52 : -(h 3) < (-2/17 : ℝ))
    (a55 : -(h 1) < (-1/8 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3323 h delta _ctx _hno a42 f0
  by_cases p1 : h 0 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3324 h delta _ctx _hno a25 a52 f1
  by_cases p2 : h 1 ≤ (15/118 : ℝ)
  swap
  · have f2 : -(h 1) < (-15/118 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3325 h delta _ctx _hno a25 a35 a37 a47 a52 f2
  by_cases p3 : h 2 ≤ (4/33 : ℝ)
  swap
  · have f3 : -(h 2) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3331 h delta _ctx _hno a51 f3
  by_cases p4 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3332 h delta _ctx _hno a13 a35 a37 a52 a55 f4
  apply _hno 148
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 1 ≤ (15/118 : ℝ)) ∧ (h 2 ≤ (4/33 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_3321 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a43 : h 0 ≤ (4/27 : ℝ))
    (a54 : -(h 0) < (-4/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a43 + (1 : ℝ) * a54
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3320 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a42 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a53 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a42 + (1 : ℝ) * a53
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3319 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a35 : -(h 4) < (-4/35 : ℝ))
    (a37 : -(h 0) < (-6/41 : ℝ))
    (a42 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a43 : h 0 ≤ (4/27 : ℝ))
    (a47 : -(h 5) < (-2/19 : ℝ))
    (a51 : h 2 ≤ (3/25 : ℝ))
    (a52 : -(h 3) < (-2/17 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3320 h delta _ctx _hno a42 f0
  by_cases p1 : h 0 ≤ (4/25 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/25 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3321 h delta _ctx _hno a43 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3322 h delta _ctx _hno a13 a25 a35 a37 a42 a47 a51 a52 f2
  apply _hno 83
  change (((2 : ℝ) * (delta)) ≤ (10/47 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem upper_node_3318 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a35 : -(h 4) < (-4/35 : ℝ))
    (a37 : -(h 0) < (-6/41 : ℝ))
    (a51 : -(h 2) < (-3/25 : ℝ))
    (a54 : -(h 1) < (-1/8 : ℝ))
    (a58 : -(h 3) < (-2/17 : ℝ))
    (a63 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/34 : ℝ) * a13 + (3/17 : ℝ) * a35 + (3/17 : ℝ) * a37 + (3/17 : ℝ) * a51 + (3/34 : ℝ) * a54 + (3/17 : ℝ) * a58 + (3/17 : ℝ) * a63 + (3/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3317 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a35 : -(h 4) < (-4/35 : ℝ))
    (a37 : -(h 0) < (-6/41 : ℝ))
    (a47 : -(h 5) < (-2/19 : ℝ))
    (a54 : -(h 1) < (-1/8 : ℝ))
    (a58 : -(h 3) < (-2/17 : ℝ))
    (a62 : -(h 2) < (-4/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/34 : ℝ) * a13 + (3/17 : ℝ) * a35 + (3/17 : ℝ) * a37 + (3/17 : ℝ) * a47 + (3/34 : ℝ) * a54 + (3/17 : ℝ) * a58 + (3/17 : ℝ) * a62 + (3/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3316 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a35 : -(h 4) < (-4/35 : ℝ))
    (a37 : -(h 0) < (-6/41 : ℝ))
    (a47 : -(h 5) < (-2/19 : ℝ))
    (a51 : -(h 2) < (-3/25 : ℝ))
    (a58 : -(h 3) < (-2/17 : ℝ))
    (a61 : -(h 1) < (-15/118 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * a51 + (1/6 : ℝ) * a58 + (1/6 : ℝ) * a61 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3315 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a56 : h 0 ≤ (5/34 : ℝ))
    (a60 : -(h 0) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a56 + (1 : ℝ) * a60
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3314 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a42 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a59 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a42 + (1 : ℝ) * a59
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3313 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a35 : -(h 4) < (-4/35 : ℝ))
    (a37 : -(h 0) < (-6/41 : ℝ))
    (a42 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a47 : -(h 5) < (-2/19 : ℝ))
    (a51 : -(h 2) < (-3/25 : ℝ))
    (a54 : -(h 1) < (-1/8 : ℝ))
    (a56 : h 0 ≤ (5/34 : ℝ))
    (a58 : -(h 3) < (-2/17 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3314 h delta _ctx _hno a42 f0
  by_cases p1 : h 0 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3315 h delta _ctx _hno a56 f1
  by_cases p2 : h 1 ≤ (15/118 : ℝ)
  swap
  · have f2 : -(h 1) < (-15/118 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3316 h delta _ctx _hno a35 a37 a47 a51 a58 f2
  by_cases p3 : h 2 ≤ (4/33 : ℝ)
  swap
  · have f3 : -(h 2) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3317 h delta _ctx _hno a13 a35 a37 a47 a54 a58 f3
  by_cases p4 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3318 h delta _ctx _hno a13 a35 a37 a51 a54 a58 f4
  apply _hno 148
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 1 ≤ (15/118 : ℝ)) ∧ (h 2 ≤ (4/33 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_3312 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : h 1 ≤ (9/70 : ℝ))
    (a57 : -(h 1) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a57
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3311 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a35 : -(h 4) < (-4/35 : ℝ))
    (a41 : -(h 3) < (-3/26 : ℝ))
    (a51 : -(h 2) < (-3/25 : ℝ))
    (a54 : -(h 1) < (-1/8 : ℝ))
    (a56 : -(h 0) < (-5/34 : ℝ))
    (a63 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/34 : ℝ) * a13 + (3/17 : ℝ) * a35 + (3/17 : ℝ) * a41 + (3/17 : ℝ) * a51 + (3/34 : ℝ) * a54 + (3/17 : ℝ) * a56 + (3/17 : ℝ) * a63 + (3/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3310 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a47 : -(h 5) < (-2/19 : ℝ))
    (a51 : -(h 2) < (-3/25 : ℝ))
    (a54 : -(h 1) < (-1/8 : ℝ))
    (a56 : -(h 0) < (-5/34 : ℝ))
    (a62 : -(h 4) < (-5/43 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/17 : ℝ) * _ctx.order3 + (1/34 : ℝ) * a13 + (3/17 : ℝ) * a47 + (3/17 : ℝ) * a51 + (3/34 : ℝ) * a54 + (3/17 : ℝ) * a56 + (6/17 : ℝ) * a62 + (3/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3309 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a35 : -(h 4) < (-4/35 : ℝ))
    (a51 : -(h 2) < (-3/25 : ℝ))
    (a54 : -(h 1) < (-1/8 : ℝ))
    (a56 : -(h 0) < (-5/34 : ℝ))
    (a61 : -(h 3) < (-7/60 : ℝ))
    (a66 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/34 : ℝ) * a13 + (3/17 : ℝ) * a35 + (3/17 : ℝ) * a51 + (3/34 : ℝ) * a54 + (3/17 : ℝ) * a56 + (3/17 : ℝ) * a61 + (3/17 : ℝ) * a66 + (3/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3308 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a35 : -(h 4) < (-4/35 : ℝ))
    (a47 : -(h 5) < (-2/19 : ℝ))
    (a54 : -(h 1) < (-1/8 : ℝ))
    (a56 : -(h 0) < (-5/34 : ℝ))
    (a61 : -(h 3) < (-7/60 : ℝ))
    (a65 : -(h 2) < (-4/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/34 : ℝ) * a13 + (3/17 : ℝ) * a35 + (3/17 : ℝ) * a47 + (3/34 : ℝ) * a54 + (3/17 : ℝ) * a56 + (3/17 : ℝ) * a61 + (3/17 : ℝ) * a65 + (3/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3307 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a35 : -(h 4) < (-4/35 : ℝ))
    (a47 : -(h 5) < (-2/19 : ℝ))
    (a51 : -(h 2) < (-3/25 : ℝ))
    (a56 : -(h 0) < (-5/34 : ℝ))
    (a61 : -(h 3) < (-7/60 : ℝ))
    (a64 : -(h 1) < (-15/118 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * a51 + (1/6 : ℝ) * a56 + (1/6 : ℝ) * a61 + (1/6 : ℝ) * a64 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3306 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a61 : -(h 3) < (-7/60 : ℝ))
    (a63 : -(h 0) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/7 : ℝ) * a25 + (1/7 : ℝ) * a61 + (6/7 : ℝ) * a63
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3305 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a42 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a62 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a42 + (1 : ℝ) * a62
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3304 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a35 : -(h 4) < (-4/35 : ℝ))
    (a42 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a47 : -(h 5) < (-2/19 : ℝ))
    (a51 : -(h 2) < (-3/25 : ℝ))
    (a54 : -(h 1) < (-1/8 : ℝ))
    (a56 : -(h 0) < (-5/34 : ℝ))
    (a61 : -(h 3) < (-7/60 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3305 h delta _ctx _hno a42 f0
  by_cases p1 : h 0 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3306 h delta _ctx _hno a25 a61 f1
  by_cases p2 : h 1 ≤ (15/118 : ℝ)
  swap
  · have f2 : -(h 1) < (-15/118 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3307 h delta _ctx _hno a35 a47 a51 a56 a61 f2
  by_cases p3 : h 2 ≤ (4/33 : ℝ)
  swap
  · have f3 : -(h 2) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3308 h delta _ctx _hno a13 a35 a47 a54 a56 a61 f3
  by_cases p4 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3309 h delta _ctx _hno a13 a35 a51 a54 a56 a61 f4
  apply _hno 148
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 1 ≤ (15/118 : ℝ)) ∧ (h 2 ≤ (4/33 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_3303 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a34 : h 2 ≤ (1/8 : ℝ))
    (a60 : -(h 2) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a60
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3302 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : h 1 ≤ (9/70 : ℝ))
    (a59 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a59
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3301 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a41 : -(h 3) < (-3/26 : ℝ))
    (a58 : -(h 0) < (-4/27 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/7 : ℝ) * a25 + (1/7 : ℝ) * a41 + (6/7 : ℝ) * a58
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3300 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a42 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a57 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a42 + (1 : ℝ) * a57
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3299 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a33 : h 1 ≤ (9/70 : ℝ))
    (a34 : h 2 ≤ (1/8 : ℝ))
    (a35 : -(h 4) < (-4/35 : ℝ))
    (a41 : -(h 3) < (-3/26 : ℝ))
    (a42 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a47 : -(h 5) < (-2/19 : ℝ))
    (a51 : -(h 2) < (-3/25 : ℝ))
    (a54 : -(h 1) < (-1/8 : ℝ))
    (a56 : -(h 0) < (-5/34 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3300 h delta _ctx _hno a42 f0
  by_cases p1 : h 0 ≤ (4/27 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/27 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3301 h delta _ctx _hno a25 a41 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3302 h delta _ctx _hno a33 f2
  by_cases p3 : h 2 ≤ (3/23 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3303 h delta _ctx _hno a34 f3
  by_cases p4 : h 3 ≤ (7/60 : ℝ)
  swap
  · have f4 : -(h 3) < (-7/60 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3304 h delta _ctx _hno a13 a25 a35 a42 a47 a51 a54 a56 f4
  by_cases p5 : h 4 ≤ (5/43 : ℝ)
  swap
  · have f5 : -(h 4) < (-5/43 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_3310 h delta _ctx _hno a13 a47 a51 a54 a56 f5
  by_cases p6 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f6 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact upper_node_3311 h delta _ctx _hno a13 a35 a41 a51 a54 a56 f6
  apply _hno 139
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (4/27 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (7/60 : ℝ)) ∧ (h 4 ≤ (5/43 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem upper_node_3298 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a42 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a55 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a42 + (1 : ℝ) * a55
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3297 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a33 : h 1 ≤ (9/70 : ℝ))
    (a34 : h 2 ≤ (1/8 : ℝ))
    (a35 : -(h 4) < (-4/35 : ℝ))
    (a37 : -(h 0) < (-6/41 : ℝ))
    (a41 : -(h 3) < (-3/26 : ℝ))
    (a42 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a47 : -(h 5) < (-2/19 : ℝ))
    (a51 : -(h 2) < (-3/25 : ℝ))
    (a54 : -(h 1) < (-1/8 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3298 h delta _ctx _hno a42 f0
  by_cases p1 : h 0 ≤ (5/34 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/34 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3299 h delta _ctx _hno a13 a25 a33 a34 a35 a41 a42 a47 a51 a54 f1
  by_cases p2 : h 1 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3312 h delta _ctx _hno a33 f2
  by_cases p3 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3313 h delta _ctx _hno a13 a35 a37 a42 a47 a51 a54 p1 f3
  apply _hno 92
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (5/34 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_3296 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a43 : h 0 ≤ (4/27 : ℝ))
    (a53 : -(h 0) < (-4/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a43 + (1 : ℝ) * a53
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3295 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a42 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a52 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a42 + (1 : ℝ) * a52
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3294 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a33 : h 1 ≤ (9/70 : ℝ))
    (a34 : h 2 ≤ (1/8 : ℝ))
    (a35 : -(h 4) < (-4/35 : ℝ))
    (a37 : -(h 0) < (-6/41 : ℝ))
    (a41 : -(h 3) < (-3/26 : ℝ))
    (a42 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a43 : h 0 ≤ (4/27 : ℝ))
    (a47 : -(h 5) < (-2/19 : ℝ))
    (a51 : -(h 2) < (-3/25 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3295 h delta _ctx _hno a42 f0
  by_cases p1 : h 0 ≤ (4/25 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/25 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3296 h delta _ctx _hno a43 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3297 h delta _ctx _hno a13 a25 a33 a34 a35 a37 a41 a42 a47 a51 f2
  apply _hno 83
  change (((2 : ℝ) * (delta)) ≤ (10/47 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem upper_node_3293 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : h 1 ≤ (9/70 : ℝ))
    (a50 : -(h 1) < (-3/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3292 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a41 : -(h 3) < (-3/26 : ℝ))
    (a49 : -(h 0) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/7 : ℝ) * a25 + (1/7 : ℝ) * a41 + (6/7 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3291 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a42 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a48 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a42 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3290 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a33 : h 1 ≤ (9/70 : ℝ))
    (a34 : h 2 ≤ (1/8 : ℝ))
    (a35 : -(h 4) < (-4/35 : ℝ))
    (a37 : -(h 0) < (-6/41 : ℝ))
    (a41 : -(h 3) < (-3/26 : ℝ))
    (a42 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a43 : h 0 ≤ (4/27 : ℝ))
    (a47 : -(h 5) < (-2/19 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3291 h delta _ctx _hno a42 f0
  by_cases p1 : h 0 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3292 h delta _ctx _hno a25 a41 f1
  by_cases p2 : h 1 ≤ (3/22 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3293 h delta _ctx _hno a33 f2
  by_cases p3 : h 2 ≤ (3/25 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3294 h delta _ctx _hno a13 a25 a33 a34 a35 a37 a41 a42 a43 a47 f3
  by_cases p4 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3319 h delta _ctx _hno a13 a25 a35 a37 a42 a43 a47 p3 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_3333 h delta _ctx _hno a13 a35 a37 a41 a42 a43 f5
  apply _hno 141
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_3289 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a37 : -(h 0) < (-6/41 : ℝ))
    (a42 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a46 : -(h 4) < (-2/17 : ℝ))
    (a51 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/25 : ℝ) * _ctx.order3 + (1/25 : ℝ) * _ctx.fail1 + (2/25 : ℝ) * a13 + (4/25 : ℝ) * a37 + (3/25 : ℝ) * a42 + (12/25 : ℝ) * a46 + (6/25 : ℝ) * a51 + (6/25 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3288 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a37 : -(h 0) < (-6/41 : ℝ))
    (a46 : -(h 4) < (-2/17 : ℝ))
    (a50 : -(h 2) < (-4/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/13 : ℝ) * _ctx.order3 + (3/13 : ℝ) * _ctx.min + (1/13 : ℝ) * a13 + (3/13 : ℝ) * a37 + (6/13 : ℝ) * a46 + (3/13 : ℝ) * a50 + (3/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3287 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a37 : -(h 0) < (-6/41 : ℝ))
    (a46 : -(h 4) < (-2/17 : ℝ))
    (a49 : -(h 1) < (-15/118 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.order3 + (6/23 : ℝ) * _ctx.min + (12/23 : ℝ) * _ctx.lower + (1/23 : ℝ) * _ctx.fail1 + (4/23 : ℝ) * a37 + (12/23 : ℝ) * a46 + (6/23 : ℝ) * a49 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3286 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a46 : -(h 4) < (-2/17 : ℝ))
    (a48 : -(h 0) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/7 : ℝ) * _ctx.order3 + (1/7 : ℝ) * a25 + (1/7 : ℝ) * a46 + (6/7 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3285 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a42 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a47 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a42 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3284 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a37 : -(h 0) < (-6/41 : ℝ))
    (a42 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a46 : -(h 4) < (-2/17 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3285 h delta _ctx _hno a42 f0
  by_cases p1 : h 0 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3286 h delta _ctx _hno a25 a46 f1
  by_cases p2 : h 1 ≤ (15/118 : ℝ)
  swap
  · have f2 : -(h 1) < (-15/118 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3287 h delta _ctx _hno a37 a46 f2
  by_cases p3 : h 2 ≤ (4/33 : ℝ)
  swap
  · have f3 : -(h 2) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3288 h delta _ctx _hno a13 a37 a46 f3
  by_cases p4 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3289 h delta _ctx _hno a13 a37 a42 a46 f4
  apply _hno 148
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 1 ≤ (15/118 : ℝ)) ∧ (h 2 ≤ (4/33 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_3283 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a35 : -(h 4) < (-4/35 : ℝ))
    (a37 : -(h 0) < (-6/41 : ℝ))
    (a41 : -(h 3) < (-3/26 : ℝ))
    (a45 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/13 : ℝ) * _ctx.min + (1/13 : ℝ) * a13 + (3/13 : ℝ) * a35 + (3/13 : ℝ) * a37 + (3/13 : ℝ) * a41 + (3/13 : ℝ) * a45 + (3/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3282 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : h 1 ≤ (9/70 : ℝ))
    (a44 : -(h 1) < (-6/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3281 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a41 : -(h 3) < (-3/26 : ℝ))
    (a43 : -(h 0) < (-4/27 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/7 : ℝ) * a25 + (1/7 : ℝ) * a41 + (6/7 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3280 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a35 : -(h 4) < (-4/35 : ℝ))
    (a37 : -(h 0) < (-6/41 : ℝ))
    (a41 : -(h 3) < (-3/26 : ℝ))
    (a42 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a45 : -(h 1) < (-1/8 : ℝ))
    (a52 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/32 : ℝ) * _ctx.fail1 + (3/16 : ℝ) * a35 + (1/8 : ℝ) * a37 + (3/16 : ℝ) * a41 + (3/32 : ℝ) * a42 + (3/16 : ℝ) * a45 + (3/16 : ℝ) * a52 + (3/16 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3279 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a50 : h 3 ≤ (7/60 : ℝ))
    (a55 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a50 + (1 : ℝ) * a55
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3278 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : h 1 ≤ (9/70 : ℝ))
    (a54 : -(h 1) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a54
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3277 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a42 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a45 : -(h 1) < (-1/8 : ℝ))
    (a51 : -(h 4) < (-5/43 : ℝ))
    (a57 : h 2 ≤ (2/17 : ℝ))
    (a58 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (1/10 : ℝ) * _ctx.fail1 + (1/10 : ℝ) * a42 + (1/5 : ℝ) * a45 + (2/5 : ℝ) * a51 + (2/5 : ℝ) * a57 + (1/5 : ℝ) * a58 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3276 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a42 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a45 : -(h 1) < (-1/8 : ℝ))
    (a51 : -(h 4) < (-5/43 : ℝ))
    (a53 : -(h 0) < (-5/34 : ℝ))
    (a63 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/16 : ℝ) * _ctx.order3 + (1/32 : ℝ) * _ctx.fail1 + (3/32 : ℝ) * a42 + (3/16 : ℝ) * a45 + (3/8 : ℝ) * a51 + (1/8 : ℝ) * a53 + (3/16 : ℝ) * a63 + (3/16 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3275 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a50 : h 3 ≤ (7/60 : ℝ))
    (a62 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a50 + (1 : ℝ) * a62
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3274 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a42 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a45 : -(h 1) < (-1/8 : ℝ))
    (a51 : -(h 4) < (-5/43 : ℝ))
    (a53 : -(h 0) < (-5/34 : ℝ))
    (a61 : -(h 2) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a45 + (1/3 : ℝ) * a51 + (1/6 : ℝ) * a53 + (1/6 : ℝ) * a61 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3273 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : h 1 ≤ (9/70 : ℝ))
    (a60 : -(h 1) < (-3/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a60
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3272 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a51 : -(h 4) < (-5/43 : ℝ))
    (a59 : -(h 0) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/7 : ℝ) * _ctx.order3 + (1/7 : ℝ) * a25 + (1/7 : ℝ) * a51 + (6/7 : ℝ) * a59
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3271 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a43 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a58 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a43 + (1 : ℝ) * a58
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3270 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a33 : h 1 ≤ (9/70 : ℝ))
    (a42 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a43 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a45 : -(h 1) < (-1/8 : ℝ))
    (a50 : h 3 ≤ (7/60 : ℝ))
    (a51 : -(h 4) < (-5/43 : ℝ))
    (a53 : -(h 0) < (-5/34 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3271 h delta _ctx _hno a43 f0
  by_cases p1 : h 0 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3272 h delta _ctx _hno a25 a51 f1
  by_cases p2 : h 1 ≤ (3/22 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3273 h delta _ctx _hno a33 f2
  by_cases p3 : h 2 ≤ (3/25 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3274 h delta _ctx _hno a42 a45 a51 a53 f3
  by_cases p4 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3275 h delta _ctx _hno a50 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_3276 h delta _ctx _hno a42 a45 a51 a53 f5
  apply _hno 141
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_3269 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : h 1 ≤ (9/70 : ℝ))
    (a56 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a56
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3268 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a47 : h 0 ≤ (4/27 : ℝ))
    (a55 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a47 + (1 : ℝ) * a55
  exact (lt_irrefl (0 : ℝ)) hbad

end RealPinwheel.WeakSevenBandData
