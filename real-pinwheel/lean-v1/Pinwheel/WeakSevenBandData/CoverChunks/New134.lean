import Pinwheel.WeakSevenBandData.CoverChunks.New133

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem new_node_2394 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a39 : -(h 0) < (-3/20 : ℝ))
    (a44 : -(h 3) < (-7/62 : ℝ))
    (a50 : -(h 4) < (-2/19 : ℝ))
    (a53 : -(h 1) < (-5/37 : ℝ))
    (a57 : -(h 2) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a39 + (1/6 : ℝ) * a44 + (1/6 : ℝ) * a50 + (1/6 : ℝ) * a53 + (1/6 : ℝ) * a57 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2393 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a32 : h 1 ≤ (4/29 : ℝ))
    (a56 : -(h 1) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a32 + (1 : ℝ) * a56
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2392 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : h 0 ≤ (5/33 : ℝ))
    (a55 : -(h 0) < (-5/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a25 + (1 : ℝ) * a55
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2391 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a37 : -(h 2) < (-1/8 : ℝ))
    (a39 : -(h 0) < (-3/20 : ℝ))
    (a44 : -(h 3) < (-7/62 : ℝ))
    (a50 : -(h 4) < (-2/19 : ℝ))
    (a53 : -(h 1) < (-5/37 : ℝ))
    (a54 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a39 + (1/6 : ℝ) * a44 + (1/6 : ℝ) * a50 + (1/6 : ℝ) * a53 + (1/6 : ℝ) * a54 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2390 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a37 : -(h 2) < (-1/8 : ℝ))
    (a39 : -(h 0) < (-3/20 : ℝ))
    (a44 : -(h 3) < (-7/62 : ℝ))
    (a56 : -(h 5) < (-3/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order4 + (1/13 : ℝ) * a13 + (2/13 : ℝ) * a23 + (2/13 : ℝ) * a37 + (2/13 : ℝ) * a39 + (2/13 : ℝ) * a44 + (4/13 : ℝ) * a56 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2389 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a37 : -(h 2) < (-1/8 : ℝ))
    (a39 : -(h 0) < (-3/20 : ℝ))
    (a44 : -(h 3) < (-7/62 : ℝ))
    (a53 : h 1 ≤ (5/37 : ℝ))
    (a55 : -(h 4) < (-4/37 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_2410 h delta _ctx _hno a23 a37 a39 a44 a55 f0
  by_cases p1 : h 0 ≤ (5/33 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/33 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_2411 h delta _ctx _hno a13 a23 a37 a44 a55 f1
  by_cases p2 : h 1 ≤ (3/20 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_2412 h delta _ctx _hno a53 f2
  by_cases p3 : h 2 ≤ (3/23 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_2413 h delta _ctx _hno a13 a23 a39 a44 a55 f3
  by_cases p4 : h 3 ≤ (5/44 : ℝ)
  swap
  · have f4 : -(h 3) < (-5/44 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_2414 h delta _ctx _hno a13 a23 a37 a39 a55 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_2415 h delta _ctx _hno a13 a23 a37 a39 a44 f5
  apply _hno 69
  change (((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)) ∧ (h 0 ≤ (5/33 : ℝ)) ∧ (h 1 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (5/44 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_2388 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a39 : -(h 0) < (-3/20 : ℝ))
    (a44 : -(h 3) < (-7/62 : ℝ))
    (a50 : -(h 4) < (-2/19 : ℝ))
    (a54 : -(h 2) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order1 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a39 + (1/6 : ℝ) * a44 + (1/6 : ℝ) * a50 + (1/3 : ℝ) * a54 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2387 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a25 : h 0 ≤ (5/33 : ℝ))
    (a32 : h 1 ≤ (4/29 : ℝ))
    (a37 : -(h 2) < (-1/8 : ℝ))
    (a39 : -(h 0) < (-3/20 : ℝ))
    (a44 : -(h 3) < (-7/62 : ℝ))
    (a50 : -(h 4) < (-2/19 : ℝ))
    (a53 : -(h 1) < (-5/37 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_2391 h delta _ctx _hno a37 a39 a44 a50 a53 f0
  by_cases p1 : h 0 ≤ (5/33 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/33 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_2392 h delta _ctx _hno a25 f1
  by_cases p2 : h 1 ≤ (3/20 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_2393 h delta _ctx _hno a32 f2
  by_cases p3 : h 2 ≤ (3/23 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_2394 h delta _ctx _hno a13 a39 a44 a50 a53 f3
  by_cases p4 : h 3 ≤ (5/44 : ℝ)
  swap
  · have f4 : -(h 3) < (-5/44 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_2395 h delta _ctx _hno a13 a25 a37 a39 a50 a53 p0 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_2396 h delta _ctx _hno a13 a37 a39 a44 a53 f5
  apply _hno 69
  change (((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)) ∧ (h 0 ≤ (5/33 : ℝ)) ∧ (h 1 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (5/44 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_2386 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : h 0 ≤ (5/33 : ℝ))
    (a52 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a25 + (1 : ℝ) * a52
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2385 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a30 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a51 : ((-2 : ℝ) * (delta)) < (-7/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a51
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2384 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a37 : -(h 2) < (-1/8 : ℝ))
    (a39 : -(h 0) < (-3/20 : ℝ))
    (a49 : -(h 3) < (-2/17 : ℝ))
    (a55 : -(h 5) < (-3/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order4 + (1/13 : ℝ) * a13 + (2/13 : ℝ) * a23 + (2/13 : ℝ) * a37 + (2/13 : ℝ) * a39 + (2/13 : ℝ) * a49 + (4/13 : ℝ) * a55 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2383 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a37 : -(h 2) < (-1/8 : ℝ))
    (a39 : -(h 0) < (-3/20 : ℝ))
    (a49 : -(h 3) < (-2/17 : ℝ))
    (a54 : -(h 4) < (-4/37 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a23 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a39 + (1/6 : ℝ) * a49 + (1/6 : ℝ) * a54 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2382 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a33 : -(h 4) < (-3/29 : ℝ))
    (a39 : -(h 0) < (-3/20 : ℝ))
    (a49 : -(h 3) < (-2/17 : ℝ))
    (a53 : -(h 2) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order1 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a39 + (1/6 : ℝ) * a49 + (1/3 : ℝ) * a53 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2381 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a33 : -(h 4) < (-3/29 : ℝ))
    (a37 : -(h 2) < (-1/8 : ℝ))
    (a39 : -(h 0) < (-3/20 : ℝ))
    (a49 : -(h 3) < (-2/17 : ℝ))
    (a52 : -(h 1) < (-5/37 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a39 + (1/6 : ℝ) * a49 + (1/6 : ℝ) * a52 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2380 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : h 0 ≤ (5/33 : ℝ))
    (a51 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a25 + (1 : ℝ) * a51
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2379 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a30 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a50 : ((-2 : ℝ) * (delta)) < (-7/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2378 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a25 : h 0 ≤ (5/33 : ℝ))
    (a30 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a32 : h 1 ≤ (4/29 : ℝ))
    (a37 : -(h 2) < (-1/8 : ℝ))
    (a39 : -(h 0) < (-3/20 : ℝ))
    (a44 : -(h 3) < (-7/62 : ℝ))
    (a50 : -(h 4) < (-2/19 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/33 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/33 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_2385 h delta _ctx _hno a30 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_2386 h delta _ctx _hno a25 f1
  by_cases p2 : h 1 ≤ (5/37 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/37 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_2387 h delta _ctx _hno a13 a25 a32 a37 a39 a44 a50 f2
  by_cases p3 : h 2 ≤ (2/15 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_2388 h delta _ctx _hno a13 a39 a44 a50 f3
  by_cases p4 : h 4 ≤ (4/37 : ℝ)
  swap
  · have f4 : -(h 4) < (-4/37 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_2389 h delta _ctx _hno a13 a23 a37 a39 a44 p2 f4
  by_cases p5 : h 5 ≤ (3/28 : ℝ)
  swap
  · have f5 : -(h 5) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_2390 h delta _ctx _hno a13 a23 a37 a39 a44 f5
  apply _hno 227
  change (((2 : ℝ) * (delta)) ≤ (7/33 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (5/37 : ℝ)) ∧ (h 2 ≤ (2/15 : ℝ)) ∧ (h 4 ≤ (4/37 : ℝ)) ∧ (h 5 ≤ (3/28 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_2377 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a25 : h 0 ≤ (5/33 : ℝ))
    (a30 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a33 : -(h 4) < (-3/29 : ℝ))
    (a37 : -(h 2) < (-1/8 : ℝ))
    (a39 : -(h 0) < (-3/20 : ℝ))
    (a49 : -(h 3) < (-2/17 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/33 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/33 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_2379 h delta _ctx _hno a30 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_2380 h delta _ctx _hno a25 f1
  by_cases p2 : h 1 ≤ (5/37 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/37 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_2381 h delta _ctx _hno a13 a33 a37 a39 a49 f2
  by_cases p3 : h 2 ≤ (2/15 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_2382 h delta _ctx _hno a13 a33 a39 a49 f3
  by_cases p4 : h 4 ≤ (4/37 : ℝ)
  swap
  · have f4 : -(h 4) < (-4/37 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_2383 h delta _ctx _hno a13 a23 a37 a39 a49 f4
  by_cases p5 : h 5 ≤ (3/28 : ℝ)
  swap
  · have f5 : -(h 5) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_2384 h delta _ctx _hno a13 a23 a37 a39 a49 f5
  apply _hno 227
  change (((2 : ℝ) * (delta)) ≤ (7/33 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (5/37 : ℝ)) ∧ (h 2 ≤ (2/15 : ℝ)) ∧ (h 4 ≤ (4/37 : ℝ)) ∧ (h 5 ≤ (3/28 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_2376 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a33 : -(h 4) < (-3/29 : ℝ))
    (a39 : -(h 0) < (-3/20 : ℝ))
    (a44 : -(h 3) < (-7/62 : ℝ))
    (a48 : -(h 2) < (-3/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order1 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a39 + (1/6 : ℝ) * a44 + (1/3 : ℝ) * a48 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2375 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a32 : h 1 ≤ (4/29 : ℝ))
    (a47 : -(h 1) < (-7/50 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a32 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2374 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : h 0 ≤ (5/33 : ℝ))
    (a46 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a25 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2373 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a30 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a45 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2372 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a25 : h 0 ≤ (5/33 : ℝ))
    (a30 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a37 : -(h 2) < (-1/8 : ℝ))
    (a39 : -(h 0) < (-3/20 : ℝ))
    (a45 : -(h 5) < (-2/19 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/33 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/33 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_2416 h delta _ctx _hno a30 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_2417 h delta _ctx _hno a25 f1
  by_cases p2 : h 1 ≤ (5/37 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/37 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_2418 h delta _ctx _hno a13 a17 a37 a39 a45 f2
  by_cases p3 : h 2 ≤ (2/15 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_2419 h delta _ctx _hno a13 a17 a23 a39 a45 f3
  by_cases p4 : h 4 ≤ (4/37 : ℝ)
  swap
  · have f4 : -(h 4) < (-4/37 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_2420 h delta _ctx _hno a13 a17 a23 a37 a39 a45 f4
  by_cases p5 : h 5 ≤ (3/28 : ℝ)
  swap
  · have f5 : -(h 5) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_2421 h delta _ctx _hno a13 a17 a23 a37 a39 f5
  apply _hno 227
  change (((2 : ℝ) * (delta)) ≤ (7/33 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (5/37 : ℝ)) ∧ (h 2 ≤ (2/15 : ℝ)) ∧ (h 4 ≤ (4/37 : ℝ)) ∧ (h 5 ≤ (3/28 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_2371 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a25 : h 0 ≤ (5/33 : ℝ))
    (a30 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a32 : h 1 ≤ (4/29 : ℝ))
    (a33 : -(h 4) < (-3/29 : ℝ))
    (a37 : -(h 2) < (-1/8 : ℝ))
    (a39 : -(h 0) < (-3/20 : ℝ))
    (a44 : -(h 3) < (-7/62 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_2373 h delta _ctx _hno a30 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_2374 h delta _ctx _hno a25 f1
  by_cases p2 : h 1 ≤ (7/50 : ℝ)
  swap
  · have f2 : -(h 1) < (-7/50 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_2375 h delta _ctx _hno a32 f2
  by_cases p3 : h 2 ≤ (3/22 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_2376 h delta _ctx _hno a13 a33 a39 a44 f3
  by_cases p4 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_2377 h delta _ctx _hno a13 a23 a25 a30 a33 a37 a39 f4
  by_cases p5 : h 4 ≤ (2/19 : ℝ)
  swap
  · have f5 : -(h 4) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_2378 h delta _ctx _hno a13 a23 a25 a30 a32 a37 a39 a44 f5
  apply _hno 223
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (7/50 : ℝ)) ∧ (h 2 ≤ (3/22 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_2370 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a33 : -(h 4) < (-3/29 : ℝ))
    (a39 : -(h 0) < (-3/20 : ℝ))
    (a43 : -(h 2) < (-4/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order1 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a17 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a39 + (1/3 : ℝ) * a43 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2369 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a32 : h 1 ≤ (4/29 : ℝ))
    (a42 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a32 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2368 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : h 0 ≤ (5/33 : ℝ))
    (a41 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a25 + (1 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2367 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a30 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a40 : ((-2 : ℝ) * (delta)) < (-11/52 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2366 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a29 : -(h 0) < (-4/27 : ℝ))
    (a30 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a32 : h 1 ≤ (4/29 : ℝ))
    (a37 : -(h 2) < (-1/8 : ℝ))
    (a39 : h 0 ≤ (3/20 : ℝ))
    (a40 : h 2 ≤ (3/23 : ℝ))
    (a41 : -(h 4) < (-5/47 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/33 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/33 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_2446 h delta _ctx _hno a30 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_2447 h delta _ctx _hno a39 f1
  by_cases p2 : h 1 ≤ (5/37 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/37 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_2448 h delta _ctx _hno a13 a17 a29 a30 a32 a37 a39 a40 a41 f2
  by_cases p3 : h 2 ≤ (2/15 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_2449 h delta _ctx _hno a40 f3
  by_cases p4 : h 4 ≤ (4/37 : ℝ)
  swap
  · have f4 : -(h 4) < (-4/37 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_2450 h delta _ctx _hno a13 a23 a29 a30 a37 a39 a40 p2 f4
  by_cases p5 : h 5 ≤ (3/28 : ℝ)
  swap
  · have f5 : -(h 5) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_2451 h delta _ctx _hno a13 a17 a23 a29 a37 f5
  apply _hno 227
  change (((2 : ℝ) * (delta)) ≤ (7/33 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (5/37 : ℝ)) ∧ (h 2 ≤ (2/15 : ℝ)) ∧ (h 4 ≤ (4/37 : ℝ)) ∧ (h 5 ≤ (3/28 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_2365 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a29 : -(h 0) < (-4/27 : ℝ))
    (a30 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a32 : h 1 ≤ (4/29 : ℝ))
    (a33 : -(h 4) < (-3/29 : ℝ))
    (a39 : h 0 ≤ (3/20 : ℝ))
    (a40 : -(h 2) < (-3/23 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/33 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/33 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_2422 h delta _ctx _hno a30 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_2423 h delta _ctx _hno a39 f1
  by_cases p2 : h 1 ≤ (5/37 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/37 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_2424 h delta _ctx _hno a13 a17 a29 a30 a32 a33 a39 a40 f2
  by_cases p3 : h 2 ≤ (2/15 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_2425 h delta _ctx _hno a13 a17 a23 a29 a30 a33 p2 f3
  by_cases p4 : h 4 ≤ (4/37 : ℝ)
  swap
  · have f4 : -(h 4) < (-4/37 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_2426 h delta _ctx _hno a13 a17 a23 a29 a40 f4
  by_cases p5 : h 5 ≤ (3/28 : ℝ)
  swap
  · have f5 : -(h 5) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_2427 h delta _ctx _hno a13 a17 a23 a29 a40 f5
  apply _hno 227
  change (((2 : ℝ) * (delta)) ≤ (7/33 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (5/37 : ℝ)) ∧ (h 2 ≤ (2/15 : ℝ)) ∧ (h 4 ≤ (4/37 : ℝ)) ∧ (h 5 ≤ (3/28 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_2364 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a25 : h 0 ≤ (5/33 : ℝ))
    (a30 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a32 : h 1 ≤ (4/29 : ℝ))
    (a33 : -(h 4) < (-3/29 : ℝ))
    (a37 : -(h 2) < (-1/8 : ℝ))
    (a39 : -(h 0) < (-3/20 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (11/52 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-11/52 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_2367 h delta _ctx _hno a30 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_2368 h delta _ctx _hno a25 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_2369 h delta _ctx _hno a32 f2
  by_cases p3 : h 2 ≤ (4/29 : ℝ)
  swap
  · have f3 : -(h 2) < (-4/29 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_2370 h delta _ctx _hno a13 a17 a33 a39 f3
  by_cases p4 : h 3 ≤ (7/62 : ℝ)
  swap
  · have f4 : -(h 3) < (-7/62 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_2371 h delta _ctx _hno a13 a23 a25 a30 a32 a33 a37 a39 f4
  by_cases p5 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_2372 h delta _ctx _hno a13 a17 a23 a25 a30 a37 a39 f5
  apply _hno 174
  change (((2 : ℝ) * (delta)) ≤ (11/52 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (4/29 : ℝ)) ∧ (h 3 ≤ (7/62 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_2363 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a30 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a38 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a38
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2362 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a25 : h 0 ≤ (5/33 : ℝ))
    (a27 : -(h 2) < (-4/33 : ℝ))
    (a29 : -(h 0) < (-4/27 : ℝ))
    (a30 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a32 : h 1 ≤ (4/29 : ℝ))
    (a37 : h 2 ≤ (1/8 : ℝ))
    (a39 : -(h 4) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/31 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/31 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_2530 h delta _ctx _hno a30 f0
  by_cases p1 : h 0 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_2531 h delta _ctx _hno a13 a23 a25 a27 a30 a32 a37 a39 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_2532 h delta _ctx _hno a32 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_2533 h delta _ctx _hno a37 f3
  by_cases p4 : h 3 ≤ (6/53 : ℝ)
  swap
  · have f4 : -(h 3) < (-6/53 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_2534 h delta _ctx _hno a13 a23 a27 a29 a30 a39 p1 f4
  apply _hno 72
  change (((2 : ℝ) * (delta)) ≤ (7/31 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (6/53 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_2361 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a29 : -(h 0) < (-4/27 : ℝ))
    (a33 : -(h 4) < (-3/29 : ℝ))
    (a38 : -(h 3) < (-7/57 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order2 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a23 + (1/6 : ℝ) * a29 + (1/6 : ℝ) * a33 + (1/3 : ℝ) * a38 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2360 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a25 : h 0 ≤ (5/33 : ℝ))
    (a29 : -(h 0) < (-4/27 : ℝ))
    (a30 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a32 : h 1 ≤ (4/29 : ℝ))
    (a33 : -(h 4) < (-3/29 : ℝ))
    (a37 : -(h 2) < (-1/8 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_2363 h delta _ctx _hno a30 f0
  by_cases p1 : h 0 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_2364 h delta _ctx _hno a13 a17 a23 a25 a30 a32 a33 a37 f1
  by_cases p2 : h 2 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 2) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_2365 h delta _ctx _hno a13 a17 a23 a29 a30 a32 a33 p1 f2
  by_cases p3 : h 4 ≤ (5/47 : ℝ)
  swap
  · have f3 : -(h 4) < (-5/47 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_2366 h delta _ctx _hno a13 a17 a23 a29 a30 a32 a37 p1 p2 f3
  apply _hno 143
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 4 ≤ (5/47 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_2359 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a32 : h 1 ≤ (4/29 : ℝ))
    (a36 : -(h 1) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a32 + (1 : ℝ) * a36
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2358 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : h 0 ≤ (5/33 : ℝ))
    (a35 : -(h 0) < (-5/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a25 + (1 : ℝ) * a35
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2357 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a30 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a34
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2356 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a27 : -(h 2) < (-4/33 : ℝ))
    (a29 : -(h 0) < (-4/27 : ℝ))
    (a32 : -(h 1) < (-4/29 : ℝ))
    (a38 : -(h 4) < (-1/9 : ℝ))
    (a43 : -(h 3) < (-6/53 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a29 + (1/6 : ℝ) * a32 + (1/6 : ℝ) * a38 + (1/6 : ℝ) * a43 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2355 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a29 : -(h 0) < (-4/27 : ℝ))
    (a32 : -(h 1) < (-4/29 : ℝ))
    (a38 : -(h 4) < (-1/9 : ℝ))
    (a42 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a29 + (1/6 : ℝ) * a32 + (1/3 : ℝ) * a38 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2354 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a41 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2353 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a27 : -(h 2) < (-4/33 : ℝ))
    (a32 : -(h 1) < (-4/29 : ℝ))
    (a38 : -(h 4) < (-1/9 : ℝ))
    (a40 : -(h 0) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a32 + (1/3 : ℝ) * a38 + (1/6 : ℝ) * a40 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2352 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a30 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a39 : ((-2 : ℝ) * (delta)) < (-7/31 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2351 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a29 : -(h 0) < (-4/27 : ℝ))
    (a32 : -(h 1) < (-4/29 : ℝ))
    (a36 : -(h 2) < (-1/8 : ℝ))
    (a40 : -(h 4) < (-5/47 : ℝ))
    (a46 : -(h 5) < (-2/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/13 : ℝ) * a13 + (2/13 : ℝ) * a17 + (2/13 : ℝ) * a29 + (2/13 : ℝ) * a32 + (2/13 : ℝ) * a36 + (2/13 : ℝ) * a40 + (2/13 : ℝ) * a46 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2350 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a29 : -(h 0) < (-4/27 : ℝ))
    (a32 : -(h 1) < (-4/29 : ℝ))
    (a36 : -(h 2) < (-1/8 : ℝ))
    (a40 : -(h 4) < (-5/47 : ℝ))
    (a45 : -(h 3) < (-7/62 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a29 + (1/6 : ℝ) * a32 + (1/6 : ℝ) * a36 + (1/6 : ℝ) * a40 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2349 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a39 : h 2 ≤ (3/23 : ℝ))
    (a44 : -(h 2) < (-4/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a39 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2348 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a43 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2347 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a38 : h 0 ≤ (3/20 : ℝ))
    (a42 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a38 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2346 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a30 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-11/52 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2345 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a29 : -(h 0) < (-4/27 : ℝ))
    (a32 : -(h 1) < (-4/29 : ℝ))
    (a39 : -(h 2) < (-3/23 : ℝ))
    (a44 : -(h 4) < (-4/39 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a17 + (1/6 : ℝ) * a29 + (1/6 : ℝ) * a32 + (1/6 : ℝ) * a39 + (1/6 : ℝ) * a44 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2344 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a32 : -(h 1) < (-4/29 : ℝ))
    (a39 : -(h 2) < (-3/23 : ℝ))
    (a43 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/17 : ℝ) * _ctx.min + (1/17 : ℝ) * _ctx.fail2 + (4/17 : ℝ) * a13 + (4/17 : ℝ) * a32 + (4/17 : ℝ) * a39 + (4/17 : ℝ) * a43 + (4/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2343 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a42 : -(h 2) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * _ctx.order1 + (1 : ℝ) * a16 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2342 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a38 : h 0 ≤ (3/20 : ℝ))
    (a41 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a38 + (1 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2341 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a29 : -(h 0) < (-4/27 : ℝ))
    (a32 : -(h 1) < (-4/29 : ℝ))
    (a39 : -(h 2) < (-3/23 : ℝ))
    (a40 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/11 : ℝ) * _ctx.order4 + (4/11 : ℝ) * _ctx.min + (2/11 : ℝ) * a17 + (2/11 : ℝ) * a29 + (2/11 : ℝ) * a32 + (2/11 : ℝ) * a39 + (3/11 : ℝ) * a40 + (2/11 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2340 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a32 : -(h 1) < (-4/29 : ℝ))
    (a36 : -(h 2) < (-1/8 : ℝ))
    (a38 : -(h 0) < (-3/20 : ℝ))
    (a53 : -(h 3) < (-5/44 : ℝ))
    (a59 : -(h 4) < (-2/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a32 + (1/6 : ℝ) * a36 + (1/6 : ℝ) * a38 + (1/6 : ℝ) * a53 + (1/6 : ℝ) * a59 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2339 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a32 : -(h 1) < (-4/29 : ℝ))
    (a36 : -(h 2) < (-1/8 : ℝ))
    (a38 : -(h 0) < (-3/20 : ℝ))
    (a43 : -(h 4) < (-4/39 : ℝ))
    (a58 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a32 + (1/6 : ℝ) * a36 + (1/6 : ℝ) * a38 + (1/6 : ℝ) * a43 + (1/6 : ℝ) * a58 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2338 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a52 : h 2 ≤ (3/23 : ℝ))
    (a57 : -(h 2) < (-3/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a52 + (1 : ℝ) * a57
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2337 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a56 : -(h 1) < (-7/50 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a56
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2336 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : h 0 ≤ (5/33 : ℝ))
    (a55 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a25 + (1 : ℝ) * a55
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2335 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a39 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ))
    (a54 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a39 + (1 : ℝ) * a54
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2334 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a32 : -(h 1) < (-4/29 : ℝ))
    (a36 : -(h 2) < (-1/8 : ℝ))
    (a38 : -(h 0) < (-3/20 : ℝ))
    (a48 : -(h 3) < (-7/62 : ℝ))
    (a54 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a32 + (1/6 : ℝ) * a36 + (1/6 : ℝ) * a38 + (1/6 : ℝ) * a48 + (1/6 : ℝ) * a54 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2333 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a25 : h 0 ≤ (5/33 : ℝ))
    (a32 : -(h 1) < (-4/29 : ℝ))
    (a36 : -(h 2) < (-1/8 : ℝ))
    (a38 : -(h 0) < (-3/20 : ℝ))
    (a39 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ))
    (a43 : -(h 4) < (-4/39 : ℝ))
    (a52 : h 2 ≤ (3/23 : ℝ))
    (a53 : -(h 3) < (-5/44 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_2335 h delta _ctx _hno a39 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_2336 h delta _ctx _hno a25 f1
  by_cases p2 : h 1 ≤ (7/50 : ℝ)
  swap
  · have f2 : -(h 1) < (-7/50 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_2337 h delta _ctx _hno a16 f2
  by_cases p3 : h 2 ≤ (3/22 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_2338 h delta _ctx _hno a52 f3
  by_cases p4 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_2339 h delta _ctx _hno a13 a32 a36 a38 a43 f4
  by_cases p5 : h 4 ≤ (2/19 : ℝ)
  swap
  · have f5 : -(h 4) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_2340 h delta _ctx _hno a13 a32 a36 a38 a53 f5
  apply _hno 223
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (7/50 : ℝ)) ∧ (h 2 ≤ (3/22 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_2332 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a32 : -(h 1) < (-4/29 : ℝ))
    (a38 : -(h 0) < (-3/20 : ℝ))
    (a43 : -(h 4) < (-4/39 : ℝ))
    (a48 : -(h 3) < (-7/62 : ℝ))
    (a52 : -(h 2) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a32 + (1/6 : ℝ) * a38 + (1/6 : ℝ) * a43 + (1/6 : ℝ) * a48 + (1/6 : ℝ) * a52 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2331 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a51 : -(h 1) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a51
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2330 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : h 0 ≤ (5/33 : ℝ))
    (a50 : -(h 0) < (-5/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a25 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2329 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a39 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ))
    (a49 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a39 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2328 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a32 : -(h 1) < (-4/29 : ℝ))
    (a36 : -(h 2) < (-1/8 : ℝ))
    (a38 : -(h 0) < (-3/20 : ℝ))
    (a49 : -(h 5) < (-2/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order4 + (1/13 : ℝ) * a13 + (2/13 : ℝ) * a17 + (2/13 : ℝ) * a32 + (2/13 : ℝ) * a36 + (2/13 : ℝ) * a38 + (4/13 : ℝ) * a49 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2327 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a25 : h 0 ≤ (5/33 : ℝ))
    (a32 : -(h 1) < (-4/29 : ℝ))
    (a36 : -(h 2) < (-1/8 : ℝ))
    (a38 : -(h 0) < (-3/20 : ℝ))
    (a39 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ))
    (a43 : -(h 4) < (-4/39 : ℝ))
    (a48 : -(h 3) < (-7/62 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_2329 h delta _ctx _hno a39 f0
  by_cases p1 : h 0 ≤ (5/33 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/33 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_2330 h delta _ctx _hno a25 f1
  by_cases p2 : h 1 ≤ (3/20 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_2331 h delta _ctx _hno a16 f2
  by_cases p3 : h 2 ≤ (3/23 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_2332 h delta _ctx _hno a13 a32 a38 a43 a48 f3
  by_cases p4 : h 3 ≤ (5/44 : ℝ)
  swap
  · have f4 : -(h 3) < (-5/44 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_2333 h delta _ctx _hno a13 a16 a25 a32 a36 a38 a39 a43 p3 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_2334 h delta _ctx _hno a13 a32 a36 a38 a48 f5
  apply _hno 69
  change (((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)) ∧ (h 0 ≤ (5/33 : ℝ)) ∧ (h 1 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (5/44 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_2326 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a47 : -(h 2) < (-4/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/17 : ℝ) * _ctx.order1 + (4/17 : ℝ) * _ctx.min + (1/17 : ℝ) * _ctx.fail2 + (4/17 : ℝ) * a13 + (4/17 : ℝ) * a17 + (8/17 : ℝ) * a47 + (4/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2325 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a46 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2324 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : h 0 ≤ (5/33 : ℝ))
    (a45 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a25 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2323 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a39 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ))
    (a44 : ((-2 : ℝ) * (delta)) < (-11/52 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a39 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2322 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a32 : -(h 1) < (-4/29 : ℝ))
    (a36 : -(h 2) < (-1/8 : ℝ))
    (a38 : -(h 0) < (-3/20 : ℝ))
    (a39 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ))
    (a45 : -(h 5) < (-2/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order4 + (2/13 : ℝ) * a17 + (2/13 : ℝ) * a32 + (2/13 : ℝ) * a36 + (2/13 : ℝ) * a38 + (1/13 : ℝ) * a39 + (4/13 : ℝ) * a45 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2321 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a32 : -(h 1) < (-4/29 : ℝ))
    (a36 : -(h 2) < (-1/8 : ℝ))
    (a38 : -(h 0) < (-3/20 : ℝ))
    (a39 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ))
    (a44 : -(h 3) < (-7/62 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/11 : ℝ) * _ctx.order4 + (4/11 : ℝ) * _ctx.min + (2/11 : ℝ) * a32 + (2/11 : ℝ) * a36 + (2/11 : ℝ) * a38 + (3/11 : ℝ) * a39 + (2/11 : ℝ) * a44 + (2/11 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2320 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a39 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ))
    (a43 : -(h 2) < (-4/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/17 : ℝ) * _ctx.order1 + (4/17 : ℝ) * _ctx.min + (1/17 : ℝ) * _ctx.fail2 + (4/17 : ℝ) * a17 + (4/17 : ℝ) * a39 + (8/17 : ℝ) * a43 + (4/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2319 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a42 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2318 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : h 0 ≤ (5/33 : ℝ))
    (a41 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a25 + (1 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2317 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a30 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a40 : ((-2 : ℝ) * (delta)) < (-11/52 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2316 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a25 : h 0 ≤ (5/33 : ℝ))
    (a32 : -(h 1) < (-4/29 : ℝ))
    (a36 : -(h 2) < (-1/8 : ℝ))
    (a38 : -(h 0) < (-3/20 : ℝ))
    (a39 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ))
    (a43 : -(h 4) < (-4/39 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (11/52 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-11/52 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_2323 h delta _ctx _hno a39 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_2324 h delta _ctx _hno a25 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_2325 h delta _ctx _hno a16 f2
  by_cases p3 : h 2 ≤ (4/29 : ℝ)
  swap
  · have f3 : -(h 2) < (-4/29 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_2326 h delta _ctx _hno a13 a17 f3
  by_cases p4 : h 3 ≤ (7/62 : ℝ)
  swap
  · have f4 : -(h 3) < (-7/62 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_2327 h delta _ctx _hno a13 a16 a25 a32 a36 a38 a39 a43 f4
  by_cases p5 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_2328 h delta _ctx _hno a13 a17 a32 a36 a38 f5
  apply _hno 174
  change (((2 : ℝ) * (delta)) ≤ (11/52 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (4/29 : ℝ)) ∧ (h 3 ≤ (7/62 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_2315 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a32 : -(h 1) < (-4/29 : ℝ))
    (a36 : -(h 2) < (-1/8 : ℝ))
    (a38 : -(h 0) < (-3/20 : ℝ))
    (a42 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/11 : ℝ) * _ctx.order4 + (4/11 : ℝ) * _ctx.min + (3/11 : ℝ) * a13 + (2/11 : ℝ) * a32 + (2/11 : ℝ) * a36 + (2/11 : ℝ) * a38 + (2/11 : ℝ) * a42 + (2/11 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

end RealPinwheel.WeakSevenBandData
