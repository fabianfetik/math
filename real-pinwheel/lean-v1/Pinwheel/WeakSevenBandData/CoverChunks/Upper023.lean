import Pinwheel.WeakSevenBandData.CoverChunks.Upper022

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem upper_node_2467 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a50 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2466 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a29 : -(h 4) < (-1/9 : ℝ))
    (a30 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a31 : h 0 ≤ (4/27 : ℝ))
    (a45 : h 3 ≤ (3/26 : ℝ))
    (a46 : -(h 5) < (-1/9 : ℝ))
    (a49 : -(h 1) < (-4/31 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2467 h delta _ctx _hno a30 f0
  by_cases p1 : h 0 ≤ (3/19 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/19 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2468 h delta _ctx _hno a31 f1
  by_cases p2 : h 1 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2469 h delta _ctx _hno a23 a25 a29 a46 f2
  by_cases p3 : h 2 ≤ (12/101 : ℝ)
  swap
  · have f3 : -(h 2) < (-12/101 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2470 h delta _ctx _hno a23 a25 a29 a46 a49 f3
  by_cases p4 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2471 h delta _ctx _hno a45 f4
  by_cases p5 : h 4 ≤ (3/26 : ℝ)
  swap
  · have f5 : -(h 4) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_2472 h delta _ctx _hno a25 a46 a49 f5
  apply _hno 117
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 2 ≤ (12/101 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (3/26 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_2465 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : h 0 ≤ (4/27 : ℝ))
    (a48 : -(h 0) < (-3/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2464 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a47 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2463 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a29 : -(h 4) < (-1/9 : ℝ))
    (a30 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a31 : h 0 ≤ (4/27 : ℝ))
    (a41 : -(h 1) < (-9/70 : ℝ))
    (a45 : h 3 ≤ (3/26 : ℝ))
    (a46 : -(h 5) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2464 h delta _ctx _hno a30 f0
  by_cases p1 : h 0 ≤ (3/19 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/19 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2465 h delta _ctx _hno a31 f1
  by_cases p2 : h 1 ≤ (4/31 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/31 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2466 h delta _ctx _hno a23 a25 a29 a30 a31 a45 a46 f2
  by_cases p3 : h 2 ≤ (3/25 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2473 h delta _ctx _hno a23 a25 a29 a41 a46 f3
  by_cases p4 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2474 h delta _ctx _hno a45 f4
  by_cases p5 : h 4 ≤ (3/26 : ℝ)
  swap
  · have f5 : -(h 4) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_2475 h delta _ctx _hno a25 a41 a46 f5
  apply _hno 113
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (4/31 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (3/26 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_2462 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a29 : -(h 4) < (-1/9 : ℝ))
    (a41 : -(h 1) < (-9/70 : ℝ))
    (a45 : -(h 3) < (-3/26 : ℝ))
    (a51 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/25 : ℝ) * _ctx.lower + (1/25 : ℝ) * _ctx.fail1 + (2/75 : ℝ) * a25 + (6/25 : ℝ) * a29 + (6/25 : ℝ) * a41 + (16/75 : ℝ) * a45 + (6/25 : ℝ) * a51 + (6/25 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2461 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a41 : -(h 1) < (-9/70 : ℝ))
    (a45 : -(h 3) < (-3/26 : ℝ))
    (a50 : -(h 4) < (-5/44 : ℝ))
    (a55 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/25 : ℝ) * _ctx.lower + (1/25 : ℝ) * _ctx.fail1 + (2/75 : ℝ) * a25 + (6/25 : ℝ) * a41 + (16/75 : ℝ) * a45 + (6/25 : ℝ) * a50 + (6/25 : ℝ) * a55 + (6/25 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2460 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a35 : -(h 5) < (-2/19 : ℝ))
    (a41 : -(h 1) < (-9/70 : ℝ))
    (a54 : -(h 2) < (-2/17 : ℝ))
    (a60 : -(h 4) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.lower + (1/30 : ℝ) * a25 + (1/5 : ℝ) * a35 + (1/5 : ℝ) * a41 + (1/5 : ℝ) * a54 + (11/30 : ℝ) * a60 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2459 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a35 : -(h 5) < (-2/19 : ℝ))
    (a41 : -(h 1) < (-9/70 : ℝ))
    (a50 : -(h 4) < (-5/44 : ℝ))
    (a59 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/25 : ℝ) * _ctx.lower + (1/25 : ℝ) * _ctx.fail1 + (2/75 : ℝ) * a25 + (6/25 : ℝ) * a35 + (6/25 : ℝ) * a41 + (6/25 : ℝ) * a50 + (16/75 : ℝ) * a59 + (6/25 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2458 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a35 : -(h 5) < (-2/19 : ℝ))
    (a41 : -(h 1) < (-9/70 : ℝ))
    (a45 : -(h 3) < (-3/26 : ℝ))
    (a50 : -(h 4) < (-5/44 : ℝ))
    (a58 : -(h 2) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.lower + (1/30 : ℝ) * a25 + (1/5 : ℝ) * a35 + (1/5 : ℝ) * a41 + (1/6 : ℝ) * a45 + (1/5 : ℝ) * a50 + (1/5 : ℝ) * a58 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2457 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a35 : -(h 5) < (-2/19 : ℝ))
    (a57 : -(h 1) < (-4/31 : ℝ))
    (a63 : -(h 4) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (16/75 : ℝ) * _ctx.order3 + (6/25 : ℝ) * _ctx.lower + (1/25 : ℝ) * _ctx.fail1 + (2/75 : ℝ) * a25 + (6/25 : ℝ) * a35 + (6/25 : ℝ) * a57 + (34/75 : ℝ) * a63 + (6/25 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2456 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a35 : -(h 5) < (-2/19 : ℝ))
    (a50 : -(h 4) < (-5/44 : ℝ))
    (a57 : -(h 1) < (-4/31 : ℝ))
    (a62 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/25 : ℝ) * _ctx.lower + (1/25 : ℝ) * _ctx.fail1 + (2/75 : ℝ) * a25 + (6/25 : ℝ) * a35 + (6/25 : ℝ) * a50 + (6/25 : ℝ) * a57 + (16/75 : ℝ) * a62 + (6/25 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2455 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a35 : -(h 5) < (-2/19 : ℝ))
    (a45 : -(h 3) < (-3/26 : ℝ))
    (a50 : -(h 4) < (-5/44 : ℝ))
    (a57 : -(h 1) < (-4/31 : ℝ))
    (a61 : -(h 2) < (-12/101 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.lower + (1/30 : ℝ) * a25 + (1/5 : ℝ) * a35 + (1/6 : ℝ) * a45 + (1/5 : ℝ) * a50 + (1/5 : ℝ) * a57 + (1/5 : ℝ) * a61 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2454 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a35 : -(h 5) < (-2/19 : ℝ))
    (a45 : -(h 3) < (-3/26 : ℝ))
    (a50 : -(h 4) < (-5/44 : ℝ))
    (a54 : -(h 2) < (-2/17 : ℝ))
    (a60 : -(h 1) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.lower + (1/30 : ℝ) * a25 + (1/5 : ℝ) * a35 + (1/6 : ℝ) * a45 + (1/5 : ℝ) * a50 + (1/5 : ℝ) * a54 + (1/5 : ℝ) * a60 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2453 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : h 0 ≤ (4/27 : ℝ))
    (a59 : -(h 0) < (-3/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a59
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2452 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a45 : -(h 3) < (-3/26 : ℝ))
    (a50 : -(h 4) < (-5/44 : ℝ))
    (a54 : -(h 2) < (-2/17 : ℝ))
    (a57 : -(h 1) < (-4/31 : ℝ))
    (a58 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (1/30 : ℝ) * a25 + (1/6 : ℝ) * a45 + (1/5 : ℝ) * a50 + (1/5 : ℝ) * a54 + (1/5 : ℝ) * a57 + (1/5 : ℝ) * a58 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2451 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a31 : h 0 ≤ (4/27 : ℝ))
    (a35 : -(h 5) < (-2/19 : ℝ))
    (a45 : -(h 3) < (-3/26 : ℝ))
    (a50 : -(h 4) < (-5/44 : ℝ))
    (a54 : -(h 2) < (-2/17 : ℝ))
    (a57 : -(h 1) < (-4/31 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2452 h delta _ctx _hno a25 a45 a50 a54 a57 f0
  by_cases p1 : h 0 ≤ (3/19 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/19 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2453 h delta _ctx _hno a31 f1
  by_cases p2 : h 1 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2454 h delta _ctx _hno a25 a35 a45 a50 a54 f2
  by_cases p3 : h 2 ≤ (12/101 : ℝ)
  swap
  · have f3 : -(h 2) < (-12/101 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2455 h delta _ctx _hno a25 a35 a45 a50 a57 f3
  by_cases p4 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2456 h delta _ctx _hno a25 a35 a50 a57 f4
  by_cases p5 : h 4 ≤ (3/26 : ℝ)
  swap
  · have f5 : -(h 4) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_2457 h delta _ctx _hno a25 a35 a57 f5
  apply _hno 117
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 2 ≤ (12/101 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (3/26 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_2450 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : h 0 ≤ (4/27 : ℝ))
    (a56 : -(h 0) < (-3/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a56
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2449 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a55 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a55
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2448 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a30 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a31 : h 0 ≤ (4/27 : ℝ))
    (a35 : -(h 5) < (-2/19 : ℝ))
    (a41 : -(h 1) < (-9/70 : ℝ))
    (a45 : -(h 3) < (-3/26 : ℝ))
    (a50 : -(h 4) < (-5/44 : ℝ))
    (a54 : -(h 2) < (-2/17 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2449 h delta _ctx _hno a30 f0
  by_cases p1 : h 0 ≤ (3/19 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/19 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2450 h delta _ctx _hno a31 f1
  by_cases p2 : h 1 ≤ (4/31 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/31 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2451 h delta _ctx _hno a25 a31 a35 a45 a50 a54 f2
  by_cases p3 : h 2 ≤ (3/25 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2458 h delta _ctx _hno a25 a35 a41 a45 a50 f3
  by_cases p4 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2459 h delta _ctx _hno a25 a35 a41 a50 f4
  by_cases p5 : h 4 ≤ (3/26 : ℝ)
  swap
  · have f5 : -(h 4) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_2460 h delta _ctx _hno a25 a35 a41 a54 f5
  apply _hno 113
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (4/31 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (3/26 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_2447 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a48 : h 1 ≤ (3/23 : ℝ))
    (a53 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a48 + (1 : ℝ) * a53
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2446 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : h 0 ≤ (4/27 : ℝ))
    (a52 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a52
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2445 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a51 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a51
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2444 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a30 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a31 : h 0 ≤ (4/27 : ℝ))
    (a35 : -(h 5) < (-2/19 : ℝ))
    (a41 : -(h 1) < (-9/70 : ℝ))
    (a45 : -(h 3) < (-3/26 : ℝ))
    (a48 : h 1 ≤ (3/23 : ℝ))
    (a50 : -(h 4) < (-5/44 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2445 h delta _ctx _hno a30 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2446 h delta _ctx _hno a31 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2447 h delta _ctx _hno a48 f2
  by_cases p3 : h 2 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2448 h delta _ctx _hno a25 a30 a31 a35 a41 a45 a50 f3
  by_cases p4 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2461 h delta _ctx _hno a25 a41 a45 a50 f4
  apply _hno 118
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_2443 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a29 : -(h 4) < (-1/9 : ℝ))
    (a41 : -(h 1) < (-9/70 : ℝ))
    (a45 : -(h 3) < (-3/26 : ℝ))
    (a49 : -(h 2) < (-3/25 : ℝ))
    (a56 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.lower + (1/30 : ℝ) * a25 + (1/5 : ℝ) * a29 + (1/5 : ℝ) * a41 + (1/6 : ℝ) * a45 + (1/5 : ℝ) * a49 + (1/5 : ℝ) * a56 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2442 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a35 : -(h 5) < (-2/19 : ℝ))
    (a41 : -(h 1) < (-9/70 : ℝ))
    (a45 : -(h 3) < (-3/26 : ℝ))
    (a49 : -(h 2) < (-3/25 : ℝ))
    (a55 : -(h 4) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.lower + (1/30 : ℝ) * a25 + (1/5 : ℝ) * a35 + (1/5 : ℝ) * a41 + (1/6 : ℝ) * a45 + (1/5 : ℝ) * a49 + (1/5 : ℝ) * a55 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2441 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a29 : -(h 4) < (-1/9 : ℝ))
    (a35 : -(h 5) < (-2/19 : ℝ))
    (a41 : -(h 1) < (-9/70 : ℝ))
    (a49 : -(h 2) < (-3/25 : ℝ))
    (a54 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.lower + (1/30 : ℝ) * a25 + (1/5 : ℝ) * a29 + (1/5 : ℝ) * a35 + (1/5 : ℝ) * a41 + (1/5 : ℝ) * a49 + (1/6 : ℝ) * a54 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2440 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a29 : -(h 4) < (-1/9 : ℝ))
    (a35 : -(h 5) < (-2/19 : ℝ))
    (a41 : -(h 1) < (-9/70 : ℝ))
    (a45 : -(h 3) < (-3/26 : ℝ))
    (a53 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.lower + (1/30 : ℝ) * a25 + (1/5 : ℝ) * a29 + (1/5 : ℝ) * a35 + (1/5 : ℝ) * a41 + (1/6 : ℝ) * a45 + (1/5 : ℝ) * a53 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2439 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a48 : h 1 ≤ (3/23 : ℝ))
    (a52 : -(h 1) < (-5/38 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a48 + (1 : ℝ) * a52
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2438 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : h 0 ≤ (4/27 : ℝ))
    (a51 : -(h 0) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a51
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2437 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a50 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2436 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a29 : -(h 4) < (-1/9 : ℝ))
    (a30 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a31 : h 0 ≤ (4/27 : ℝ))
    (a35 : -(h 5) < (-2/19 : ℝ))
    (a41 : -(h 1) < (-9/70 : ℝ))
    (a45 : -(h 3) < (-3/26 : ℝ))
    (a48 : h 1 ≤ (3/23 : ℝ))
    (a49 : -(h 2) < (-3/25 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2437 h delta _ctx _hno a30 f0
  by_cases p1 : h 0 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2438 h delta _ctx _hno a31 f1
  by_cases p2 : h 1 ≤ (5/38 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/38 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2439 h delta _ctx _hno a48 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2440 h delta _ctx _hno a25 a29 a35 a41 a45 f3
  by_cases p4 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2441 h delta _ctx _hno a25 a29 a35 a41 a49 f4
  by_cases p5 : h 4 ≤ (4/35 : ℝ)
  swap
  · have f5 : -(h 4) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_2442 h delta _ctx _hno a25 a35 a41 a45 a49 f5
  by_cases p6 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f6 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact upper_node_2443 h delta _ctx _hno a25 a29 a41 a45 a49 f6
  apply _hno 134
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 1 ≤ (5/38 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem upper_node_2435 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a29 : -(h 4) < (-1/9 : ℝ))
    (a45 : -(h 3) < (-3/26 : ℝ))
    (a48 : -(h 1) < (-3/23 : ℝ))
    (a53 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/25 : ℝ) * _ctx.lower + (1/25 : ℝ) * _ctx.fail1 + (2/75 : ℝ) * a25 + (6/25 : ℝ) * a29 + (16/75 : ℝ) * a45 + (6/25 : ℝ) * a48 + (6/25 : ℝ) * a53 + (6/25 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2434 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a29 : -(h 4) < (-1/9 : ℝ))
    (a45 : -(h 3) < (-3/26 : ℝ))
    (a48 : -(h 1) < (-3/23 : ℝ))
    (a59 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/25 : ℝ) * _ctx.lower + (1/25 : ℝ) * _ctx.fail1 + (2/75 : ℝ) * a25 + (6/25 : ℝ) * a29 + (16/75 : ℝ) * a45 + (6/25 : ℝ) * a48 + (6/25 : ℝ) * a59 + (6/25 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2433 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a35 : -(h 5) < (-2/19 : ℝ))
    (a45 : -(h 3) < (-3/26 : ℝ))
    (a48 : -(h 1) < (-3/23 : ℝ))
    (a58 : -(h 4) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/25 : ℝ) * _ctx.lower + (1/25 : ℝ) * _ctx.fail1 + (2/75 : ℝ) * a25 + (6/25 : ℝ) * a35 + (16/75 : ℝ) * a45 + (6/25 : ℝ) * a48 + (6/25 : ℝ) * a58 + (6/25 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2432 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a29 : -(h 4) < (-1/9 : ℝ))
    (a48 : -(h 1) < (-3/23 : ℝ))
    (a57 : -(h 3) < (-2/17 : ℝ))
    (a63 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/25 : ℝ) * _ctx.lower + (1/25 : ℝ) * _ctx.fail1 + (2/75 : ℝ) * a25 + (6/25 : ℝ) * a29 + (6/25 : ℝ) * a48 + (16/75 : ℝ) * a57 + (6/25 : ℝ) * a63 + (6/25 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2431 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a35 : -(h 5) < (-2/19 : ℝ))
    (a48 : -(h 1) < (-3/23 : ℝ))
    (a57 : -(h 3) < (-2/17 : ℝ))
    (a62 : -(h 4) < (-5/44 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/25 : ℝ) * _ctx.lower + (1/25 : ℝ) * _ctx.fail1 + (2/75 : ℝ) * a25 + (6/25 : ℝ) * a35 + (6/25 : ℝ) * a48 + (16/75 : ℝ) * a57 + (6/25 : ℝ) * a62 + (6/25 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2430 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a29 : -(h 4) < (-1/9 : ℝ))
    (a35 : -(h 5) < (-2/19 : ℝ))
    (a48 : -(h 1) < (-3/23 : ℝ))
    (a57 : -(h 3) < (-2/17 : ℝ))
    (a61 : -(h 2) < (-5/42 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.lower + (1/30 : ℝ) * a25 + (1/5 : ℝ) * a29 + (1/5 : ℝ) * a35 + (1/5 : ℝ) * a48 + (1/6 : ℝ) * a57 + (1/5 : ℝ) * a61 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2429 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a55 : h 1 ≤ (5/38 : ℝ))
    (a60 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a55 + (1 : ℝ) * a60
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2428 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : h 0 ≤ (4/27 : ℝ))
    (a59 : -(h 0) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a59
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2427 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a29 : -(h 4) < (-1/9 : ℝ))
    (a48 : -(h 1) < (-3/23 : ℝ))
    (a57 : -(h 3) < (-2/17 : ℝ))
    (a58 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/25 : ℝ) * _ctx.min + (1/25 : ℝ) * _ctx.fail1 + (2/75 : ℝ) * a25 + (6/25 : ℝ) * a29 + (6/25 : ℝ) * a48 + (16/75 : ℝ) * a57 + (6/25 : ℝ) * a58 + (6/25 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2426 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a29 : -(h 4) < (-1/9 : ℝ))
    (a31 : h 0 ≤ (4/27 : ℝ))
    (a35 : -(h 5) < (-2/19 : ℝ))
    (a48 : -(h 1) < (-3/23 : ℝ))
    (a55 : h 1 ≤ (5/38 : ℝ))
    (a57 : -(h 3) < (-2/17 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2427 h delta _ctx _hno a25 a29 a48 a57 f0
  by_cases p1 : h 0 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2428 h delta _ctx _hno a31 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2429 h delta _ctx _hno a55 f2
  by_cases p3 : h 2 ≤ (5/42 : ℝ)
  swap
  · have f3 : -(h 2) < (-5/42 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2430 h delta _ctx _hno a25 a29 a35 a48 a57 f3
  by_cases p4 : h 4 ≤ (5/44 : ℝ)
  swap
  · have f4 : -(h 4) < (-5/44 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2431 h delta _ctx _hno a25 a35 a48 a57 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_2432 h delta _ctx _hno a25 a29 a48 a57 f5
  apply _hno 136
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (5/42 : ℝ)) ∧ (h 4 ≤ (5/44 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_2425 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a29 : -(h 4) < (-1/9 : ℝ))
    (a35 : -(h 5) < (-2/19 : ℝ))
    (a45 : -(h 3) < (-3/26 : ℝ))
    (a48 : -(h 1) < (-3/23 : ℝ))
    (a56 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.lower + (1/30 : ℝ) * a25 + (1/5 : ℝ) * a29 + (1/5 : ℝ) * a35 + (1/6 : ℝ) * a45 + (1/5 : ℝ) * a48 + (1/5 : ℝ) * a56 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2424 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a29 : -(h 4) < (-1/9 : ℝ))
    (a45 : -(h 3) < (-3/26 : ℝ))
    (a55 : -(h 1) < (-5/38 : ℝ))
    (a61 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/25 : ℝ) * _ctx.lower + (1/25 : ℝ) * _ctx.fail1 + (2/75 : ℝ) * a25 + (6/25 : ℝ) * a29 + (16/75 : ℝ) * a45 + (6/25 : ℝ) * a55 + (6/25 : ℝ) * a61 + (6/25 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2423 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a29 : -(h 4) < (-1/9 : ℝ))
    (a55 : -(h 1) < (-5/38 : ℝ))
    (a60 : -(h 3) < (-5/43 : ℝ))
    (a66 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/25 : ℝ) * _ctx.lower + (1/25 : ℝ) * _ctx.fail1 + (2/75 : ℝ) * a25 + (6/25 : ℝ) * a29 + (6/25 : ℝ) * a55 + (16/75 : ℝ) * a60 + (6/25 : ℝ) * a66 + (6/25 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2422 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a29 : -(h 4) < (-1/9 : ℝ))
    (a35 : -(h 5) < (-2/19 : ℝ))
    (a55 : -(h 1) < (-5/38 : ℝ))
    (a65 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/25 : ℝ) * _ctx.lower + (1/25 : ℝ) * _ctx.fail1 + (2/75 : ℝ) * a25 + (6/25 : ℝ) * a29 + (6/25 : ℝ) * a35 + (6/25 : ℝ) * a55 + (16/75 : ℝ) * a65 + (6/25 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2421 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a59 : h 2 ≤ (9/76 : ℝ))
    (a64 : -(h 2) < (-5/42 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a59 + (1 : ℝ) * a64
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2420 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a29 : -(h 4) < (-1/9 : ℝ))
    (a35 : -(h 5) < (-2/19 : ℝ))
    (a60 : -(h 3) < (-5/43 : ℝ))
    (a63 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/25 : ℝ) * _ctx.lower + (1/25 : ℝ) * _ctx.fail1 + (2/75 : ℝ) * a25 + (6/25 : ℝ) * a29 + (6/25 : ℝ) * a35 + (16/75 : ℝ) * a60 + (6/25 : ℝ) * a63 + (6/25 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2419 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : h 0 ≤ (4/27 : ℝ))
    (a62 : -(h 0) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a62
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2418 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a61 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a61
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2417 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a29 : -(h 4) < (-1/9 : ℝ))
    (a30 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a31 : h 0 ≤ (4/27 : ℝ))
    (a35 : -(h 5) < (-2/19 : ℝ))
    (a55 : -(h 1) < (-5/38 : ℝ))
    (a59 : h 2 ≤ (9/76 : ℝ))
    (a60 : -(h 3) < (-5/43 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2418 h delta _ctx _hno a30 f0
  by_cases p1 : h 0 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2419 h delta _ctx _hno a31 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2420 h delta _ctx _hno a25 a29 a35 a60 f2
  by_cases p3 : h 2 ≤ (5/42 : ℝ)
  swap
  · have f3 : -(h 2) < (-5/42 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2421 h delta _ctx _hno a59 f3
  by_cases p4 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2422 h delta _ctx _hno a25 a29 a35 a55 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_2423 h delta _ctx _hno a25 a29 a55 a60 f5
  apply _hno 131
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (5/42 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_2416 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a29 : -(h 4) < (-1/9 : ℝ))
    (a35 : -(h 5) < (-2/19 : ℝ))
    (a45 : -(h 3) < (-3/26 : ℝ))
    (a55 : -(h 1) < (-5/38 : ℝ))
    (a59 : -(h 2) < (-9/76 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.lower + (1/30 : ℝ) * a25 + (1/5 : ℝ) * a29 + (1/5 : ℝ) * a35 + (1/6 : ℝ) * a45 + (1/5 : ℝ) * a55 + (1/5 : ℝ) * a59 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2415 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a44 : h 1 ≤ (2/15 : ℝ))
    (a58 : -(h 1) < (-3/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a44 + (1 : ℝ) * a58
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2414 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : h 0 ≤ (4/27 : ℝ))
    (a57 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a57
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2413 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a29 : -(h 4) < (-1/9 : ℝ))
    (a45 : -(h 3) < (-3/26 : ℝ))
    (a52 : -(h 2) < (-2/17 : ℝ))
    (a55 : -(h 1) < (-5/38 : ℝ))
    (a56 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (1/30 : ℝ) * a25 + (1/5 : ℝ) * a29 + (1/6 : ℝ) * a45 + (1/5 : ℝ) * a52 + (1/5 : ℝ) * a55 + (1/5 : ℝ) * a56 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2412 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a29 : -(h 4) < (-1/9 : ℝ))
    (a30 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a31 : h 0 ≤ (4/27 : ℝ))
    (a35 : -(h 5) < (-2/19 : ℝ))
    (a44 : h 1 ≤ (2/15 : ℝ))
    (a45 : -(h 3) < (-3/26 : ℝ))
    (a52 : -(h 2) < (-2/17 : ℝ))
    (a55 : -(h 1) < (-5/38 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2413 h delta _ctx _hno a25 a29 a45 a52 a55 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2414 h delta _ctx _hno a31 f1
  by_cases p2 : h 1 ≤ (3/22 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2415 h delta _ctx _hno a44 f2
  by_cases p3 : h 2 ≤ (9/76 : ℝ)
  swap
  · have f3 : -(h 2) < (-9/76 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2416 h delta _ctx _hno a25 a29 a35 a45 a55 f3
  by_cases p4 : h 3 ≤ (5/43 : ℝ)
  swap
  · have f4 : -(h 3) < (-5/43 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2417 h delta _ctx _hno a25 a29 a30 a31 a35 a55 p3 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_2424 h delta _ctx _hno a25 a29 a45 a55 f5
  apply _hno 121
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 2 ≤ (9/76 : ℝ)) ∧ (h 3 ≤ (5/43 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_2411 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : h 0 ≤ (4/27 : ℝ))
    (a54 : -(h 0) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a54
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2410 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a53 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a53
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2409 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a29 : -(h 4) < (-1/9 : ℝ))
    (a30 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a31 : h 0 ≤ (4/27 : ℝ))
    (a35 : -(h 5) < (-2/19 : ℝ))
    (a44 : h 1 ≤ (2/15 : ℝ))
    (a45 : -(h 3) < (-3/26 : ℝ))
    (a48 : -(h 1) < (-3/23 : ℝ))
    (a52 : -(h 2) < (-2/17 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2410 h delta _ctx _hno a30 f0
  by_cases p1 : h 0 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2411 h delta _ctx _hno a31 f1
  by_cases p2 : h 1 ≤ (5/38 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/38 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2412 h delta _ctx _hno a25 a29 a30 a31 a35 a44 a45 a52 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2425 h delta _ctx _hno a25 a29 a35 a45 a48 f3
  by_cases p4 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2426 h delta _ctx _hno a25 a29 a31 a35 a48 p2 f4
  by_cases p5 : h 4 ≤ (4/35 : ℝ)
  swap
  · have f5 : -(h 4) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_2433 h delta _ctx _hno a25 a35 a45 a48 f5
  by_cases p6 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f6 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact upper_node_2434 h delta _ctx _hno a25 a29 a45 a48 f6
  apply _hno 134
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 1 ≤ (5/38 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem upper_node_2408 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a29 : -(h 4) < (-1/9 : ℝ))
    (a35 : -(h 5) < (-2/19 : ℝ))
    (a45 : -(h 3) < (-3/26 : ℝ))
    (a51 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/25 : ℝ) * _ctx.lower + (1/25 : ℝ) * _ctx.fail1 + (2/75 : ℝ) * a25 + (6/25 : ℝ) * a29 + (6/25 : ℝ) * a35 + (16/75 : ℝ) * a45 + (6/25 : ℝ) * a51 + (6/25 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2407 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : h 0 ≤ (4/27 : ℝ))
    (a50 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2406 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a49 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2405 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a29 : -(h 4) < (-1/9 : ℝ))
    (a30 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a31 : h 0 ≤ (4/27 : ℝ))
    (a35 : -(h 5) < (-2/19 : ℝ))
    (a44 : h 1 ≤ (2/15 : ℝ))
    (a45 : -(h 3) < (-3/26 : ℝ))
    (a48 : -(h 1) < (-3/23 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2406 h delta _ctx _hno a30 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2407 h delta _ctx _hno a31 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2408 h delta _ctx _hno a25 a29 a35 a45 f2
  by_cases p3 : h 2 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2409 h delta _ctx _hno a25 a29 a30 a31 a35 a44 a45 a48 f3
  by_cases p4 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2435 h delta _ctx _hno a25 a29 a45 a48 f4
  apply _hno 118
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_2404 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : h 0 ≤ (4/27 : ℝ))
    (a47 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2403 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a46 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2402 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a29 : -(h 4) < (-1/9 : ℝ))
    (a30 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a31 : h 0 ≤ (4/27 : ℝ))
    (a35 : -(h 5) < (-2/19 : ℝ))
    (a41 : -(h 1) < (-9/70 : ℝ))
    (a44 : h 1 ≤ (2/15 : ℝ))
    (a45 : -(h 3) < (-3/26 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2403 h delta _ctx _hno a30 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2404 h delta _ctx _hno a31 f1
  by_cases p2 : h 1 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2405 h delta _ctx _hno a25 a29 a30 a31 a35 a44 a45 f2
  by_cases p3 : h 2 ≤ (3/25 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2436 h delta _ctx _hno a25 a29 a30 a31 a35 a41 a45 p2 f3
  by_cases p4 : h 4 ≤ (5/44 : ℝ)
  swap
  · have f4 : -(h 4) < (-5/44 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2444 h delta _ctx _hno a25 a30 a31 a35 a41 a45 p2 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_2462 h delta _ctx _hno a25 a29 a41 a45 f5
  apply _hno 125
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 4 ≤ (5/44 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_2401 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a29 : -(h 4) < (-1/9 : ℝ))
    (a44 : -(h 1) < (-2/15 : ℝ))
    (a51 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (18/59 : ℝ) * _ctx.lower + (3/59 : ℝ) * _ctx.fail1 + (2/59 : ℝ) * a23 + (2/59 : ℝ) * a25 + (18/59 : ℝ) * a29 + (18/59 : ℝ) * a44 + (16/59 : ℝ) * a51 + (18/59 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2400 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a35 : -(h 5) < (-2/19 : ℝ))
    (a44 : -(h 1) < (-2/15 : ℝ))
    (a50 : -(h 4) < (-5/44 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (16/75 : ℝ) * _ctx.order3 + (6/25 : ℝ) * _ctx.lower + (1/25 : ℝ) * _ctx.fail1 + (2/75 : ℝ) * a25 + (6/25 : ℝ) * a35 + (6/25 : ℝ) * a44 + (34/75 : ℝ) * a50 + (6/25 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2399 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a29 : -(h 4) < (-1/9 : ℝ))
    (a44 : -(h 1) < (-2/15 : ℝ))
    (a49 : -(h 3) < (-4/35 : ℝ))
    (a55 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/25 : ℝ) * _ctx.lower + (1/25 : ℝ) * _ctx.fail1 + (2/75 : ℝ) * a25 + (6/25 : ℝ) * a29 + (6/25 : ℝ) * a44 + (16/75 : ℝ) * a49 + (6/25 : ℝ) * a55 + (6/25 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2398 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a29 : -(h 4) < (-1/9 : ℝ))
    (a35 : -(h 5) < (-2/19 : ℝ))
    (a44 : -(h 1) < (-2/15 : ℝ))
    (a54 : -(h 3) < (-5/43 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/25 : ℝ) * _ctx.lower + (1/25 : ℝ) * _ctx.fail1 + (2/75 : ℝ) * a25 + (6/25 : ℝ) * a29 + (6/25 : ℝ) * a35 + (6/25 : ℝ) * a44 + (16/75 : ℝ) * a54 + (6/25 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2397 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a29 : -(h 4) < (-1/9 : ℝ))
    (a35 : -(h 5) < (-2/19 : ℝ))
    (a44 : -(h 1) < (-2/15 : ℝ))
    (a49 : -(h 3) < (-4/35 : ℝ))
    (a53 : -(h 2) < (-9/76 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.lower + (1/30 : ℝ) * a25 + (1/5 : ℝ) * a29 + (1/5 : ℝ) * a35 + (1/5 : ℝ) * a44 + (1/6 : ℝ) * a49 + (1/5 : ℝ) * a53 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2396 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a29 : -(h 4) < (-1/9 : ℝ))
    (a35 : -(h 5) < (-2/19 : ℝ))
    (a49 : -(h 3) < (-4/35 : ℝ))
    (a52 : -(h 1) < (-3/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/25 : ℝ) * _ctx.lower + (1/25 : ℝ) * _ctx.fail1 + (2/75 : ℝ) * a25 + (6/25 : ℝ) * a29 + (6/25 : ℝ) * a35 + (16/75 : ℝ) * a49 + (6/25 : ℝ) * a52 + (6/25 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2395 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : h 0 ≤ (4/27 : ℝ))
    (a51 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a51
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2394 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a29 : -(h 4) < (-1/9 : ℝ))
    (a44 : -(h 1) < (-2/15 : ℝ))
    (a49 : -(h 3) < (-4/35 : ℝ))
    (a50 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/25 : ℝ) * _ctx.min + (1/25 : ℝ) * _ctx.fail1 + (2/75 : ℝ) * a25 + (6/25 : ℝ) * a29 + (6/25 : ℝ) * a44 + (16/75 : ℝ) * a49 + (6/25 : ℝ) * a50 + (6/25 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2393 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a29 : -(h 4) < (-1/9 : ℝ))
    (a31 : h 0 ≤ (4/27 : ℝ))
    (a35 : -(h 5) < (-2/19 : ℝ))
    (a44 : -(h 1) < (-2/15 : ℝ))
    (a49 : -(h 3) < (-4/35 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2394 h delta _ctx _hno a25 a29 a44 a49 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2395 h delta _ctx _hno a31 f1
  by_cases p2 : h 1 ≤ (3/22 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2396 h delta _ctx _hno a25 a29 a35 a49 f2
  by_cases p3 : h 2 ≤ (9/76 : ℝ)
  swap
  · have f3 : -(h 2) < (-9/76 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2397 h delta _ctx _hno a25 a29 a35 a44 a49 f3
  by_cases p4 : h 3 ≤ (5/43 : ℝ)
  swap
  · have f4 : -(h 3) < (-5/43 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2398 h delta _ctx _hno a25 a29 a35 a44 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_2399 h delta _ctx _hno a25 a29 a44 a49 f5
  apply _hno 121
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 2 ≤ (9/76 : ℝ)) ∧ (h 3 ≤ (5/43 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_2392 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a29 : -(h 4) < (-1/9 : ℝ))
    (a35 : -(h 5) < (-2/19 : ℝ))
    (a44 : -(h 1) < (-2/15 : ℝ))
    (a48 : -(h 2) < (-5/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/25 : ℝ) * _ctx.lower + (1/40 : ℝ) * a23 + (1/25 : ℝ) * a25 + (6/25 : ℝ) * a29 + (43/200 : ℝ) * a35 + (6/25 : ℝ) * a44 + (6/25 : ℝ) * a48 + (6/25 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2391 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a29 : -(h 4) < (-1/9 : ℝ))
    (a35 : -(h 5) < (-2/19 : ℝ))
    (a47 : -(h 1) < (-3/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (18/59 : ℝ) * _ctx.lower + (3/59 : ℝ) * _ctx.fail1 + (2/59 : ℝ) * a23 + (2/59 : ℝ) * a25 + (18/59 : ℝ) * a29 + (16/59 : ℝ) * a35 + (18/59 : ℝ) * a47 + (18/59 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2390 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : h 0 ≤ (4/27 : ℝ))
    (a46 : -(h 0) < (-11/73 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2389 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a45 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_2388 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a25 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a29 : -(h 4) < (-1/9 : ℝ))
    (a30 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a31 : h 0 ≤ (4/27 : ℝ))
    (a35 : -(h 5) < (-2/19 : ℝ))
    (a44 : -(h 1) < (-2/15 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2389 h delta _ctx _hno a30 f0
  by_cases p1 : h 0 ≤ (11/73 : ℝ)
  swap
  · have f1 : -(h 0) < (-11/73 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_2390 h delta _ctx _hno a31 f1
  by_cases p2 : h 1 ≤ (3/22 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2391 h delta _ctx _hno a23 a25 a29 a35 f2
  by_cases p3 : h 2 ≤ (5/41 : ℝ)
  swap
  · have f3 : -(h 2) < (-5/41 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2392 h delta _ctx _hno a23 a25 a29 a35 a44 f3
  by_cases p4 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2393 h delta _ctx _hno a25 a29 a31 a35 a44 f4
  by_cases p5 : h 4 ≤ (5/44 : ℝ)
  swap
  · have f5 : -(h 4) < (-5/44 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_2400 h delta _ctx _hno a25 a35 a44 f5
  by_cases p6 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f6 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact upper_node_2401 h delta _ctx _hno a23 a25 a29 a44 f6
  apply _hno 122
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (11/73 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 2 ≤ (5/41 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 4 ≤ (5/44 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

end RealPinwheel.WeakSevenBandData
