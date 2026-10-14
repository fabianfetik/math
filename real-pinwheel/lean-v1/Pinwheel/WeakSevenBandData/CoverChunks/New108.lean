import Pinwheel.WeakSevenBandData.CoverChunks.New107

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem new_node_4474 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : -(h 1) < (-5/39 : ℝ))
    (a40 : -(h 5) < (-2/19 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a45 : -(h 4) < (-7/62 : ℝ))
    (a49 : -(h 3) < (-3/26 : ℝ))
    (a51 : -(h 0) < (-13/90 : ℝ))
    (a59 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * a34 + (2/13 : ℝ) * a40 + (1/13 : ℝ) * a41 + (2/13 : ℝ) * a45 + (2/13 : ℝ) * a49 + (2/13 : ℝ) * a51 + (2/13 : ℝ) * a59 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4473 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a40 : -(h 5) < (-2/19 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a44 : h 1 ≤ (3/23 : ℝ))
    (a45 : -(h 4) < (-7/62 : ℝ))
    (a50 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a51 : -(h 0) < (-13/90 : ℝ))
    (a53 : h 0 ≤ (6/41 : ℝ))
    (a55 : -(h 2) < (-5/41 : ℝ))
    (a58 : -(h 1) < (-9/70 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_4476 h delta _ctx _hno a50 f0
  by_cases p1 : h 0 ≤ (5/34 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/34 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_4477 h delta _ctx _hno a53 f1
  by_cases p2 : h 1 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_4478 h delta _ctx _hno a44 f2
  by_cases p3 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_4479 h delta _ctx _hno a40 a41 a45 a51 a55 a58 f3
  apply _hno 109
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (5/34 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_4472 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a53 : h 0 ≤ (6/41 : ℝ))
    (a57 : -(h 0) < (-7/45 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a53 + (1 : ℝ) * a57
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4471 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a50 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a56 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a50 + (1 : ℝ) * a56
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4470 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a31 : -(h 2) < (-4/33 : ℝ))
    (a40 : -(h 5) < (-2/19 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a45 : -(h 4) < (-7/62 : ℝ))
    (a53 : -(h 0) < (-6/41 : ℝ))
    (a56 : -(h 1) < (-9/70 : ℝ))
    (a60 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * a31 + (2/13 : ℝ) * a40 + (1/13 : ℝ) * a41 + (2/13 : ℝ) * a45 + (2/13 : ℝ) * a53 + (2/13 : ℝ) * a56 + (2/13 : ℝ) * a60 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4469 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a31 : -(h 2) < (-4/33 : ℝ))
    (a40 : -(h 5) < (-2/19 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a45 : -(h 4) < (-7/62 : ℝ))
    (a49 : -(h 3) < (-3/26 : ℝ))
    (a53 : -(h 0) < (-6/41 : ℝ))
    (a59 : -(h 1) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * a31 + (2/13 : ℝ) * a40 + (1/13 : ℝ) * a41 + (2/13 : ℝ) * a45 + (2/13 : ℝ) * a49 + (2/13 : ℝ) * a53 + (2/13 : ℝ) * a59 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4468 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a31 : -(h 2) < (-4/33 : ℝ))
    (a40 : -(h 5) < (-2/19 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a45 : -(h 4) < (-7/62 : ℝ))
    (a49 : -(h 3) < (-3/26 : ℝ))
    (a56 : -(h 1) < (-9/70 : ℝ))
    (a58 : -(h 0) < (-5/34 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * a31 + (2/13 : ℝ) * a40 + (1/13 : ℝ) * a41 + (2/13 : ℝ) * a45 + (2/13 : ℝ) * a49 + (2/13 : ℝ) * a56 + (2/13 : ℝ) * a58 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4467 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a50 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a57 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a50 + (1 : ℝ) * a57
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4466 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a31 : -(h 2) < (-4/33 : ℝ))
    (a34 : -(h 1) < (-5/39 : ℝ))
    (a40 : -(h 5) < (-2/19 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a49 : -(h 3) < (-3/26 : ℝ))
    (a53 : -(h 0) < (-6/41 : ℝ))
    (a58 : -(h 4) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * a31 + (2/13 : ℝ) * a34 + (2/13 : ℝ) * a40 + (1/13 : ℝ) * a41 + (2/13 : ℝ) * a49 + (2/13 : ℝ) * a53 + (2/13 : ℝ) * a58 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4465 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : -(h 1) < (-5/39 : ℝ))
    (a40 : -(h 5) < (-2/19 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a45 : -(h 4) < (-7/62 : ℝ))
    (a49 : -(h 3) < (-3/26 : ℝ))
    (a53 : -(h 0) < (-6/41 : ℝ))
    (a57 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * a34 + (2/13 : ℝ) * a40 + (1/13 : ℝ) * a41 + (2/13 : ℝ) * a45 + (2/13 : ℝ) * a49 + (2/13 : ℝ) * a53 + (2/13 : ℝ) * a57 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4464 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a31 : -(h 2) < (-4/33 : ℝ))
    (a40 : -(h 5) < (-2/19 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a45 : -(h 4) < (-7/62 : ℝ))
    (a49 : -(h 3) < (-3/26 : ℝ))
    (a50 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a53 : -(h 0) < (-6/41 : ℝ))
    (a56 : -(h 1) < (-9/70 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_4467 h delta _ctx _hno a50 f0
  by_cases p1 : h 0 ≤ (5/34 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/34 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_4468 h delta _ctx _hno a31 a40 a41 a45 a49 a56 f1
  by_cases p2 : h 1 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_4469 h delta _ctx _hno a31 a40 a41 a45 a49 a53 f2
  by_cases p3 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_4470 h delta _ctx _hno a31 a40 a41 a45 a53 a56 f3
  apply _hno 109
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (5/34 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_4463 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a43 : h 0 ≤ (3/20 : ℝ))
    (a55 : -(h 0) < (-7/45 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a43 + (1 : ℝ) * a55
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4462 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a50 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a54 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a50 + (1 : ℝ) * a54
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4461 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : -(h 1) < (-5/39 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a51 : -(h 0) < (-13/90 : ℝ))
    (a57 : -(h 5) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/16 : ℝ) * _ctx.order3 + (3/8 : ℝ) * _ctx.order4 + (1/32 : ℝ) * _ctx.fail1 + (3/16 : ℝ) * a34 + (3/32 : ℝ) * a41 + (1/8 : ℝ) * a51 + (9/16 : ℝ) * a57 + (3/16 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4460 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a31 : -(h 2) < (-4/33 : ℝ))
    (a34 : -(h 1) < (-5/39 : ℝ))
    (a40 : -(h 5) < (-2/19 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a45 : -(h 4) < (-7/62 : ℝ))
    (a51 : -(h 0) < (-13/90 : ℝ))
    (a56 : -(h 3) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * a31 + (2/13 : ℝ) * a34 + (2/13 : ℝ) * a40 + (1/13 : ℝ) * a41 + (2/13 : ℝ) * a45 + (2/13 : ℝ) * a51 + (2/13 : ℝ) * a56 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4459 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : -(h 1) < (-5/39 : ℝ))
    (a40 : -(h 5) < (-2/19 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a44 : h 1 ≤ (3/23 : ℝ))
    (a45 : -(h 4) < (-7/62 : ℝ))
    (a49 : -(h 3) < (-3/26 : ℝ))
    (a50 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a51 : -(h 0) < (-13/90 : ℝ))
    (a53 : h 0 ≤ (6/41 : ℝ))
    (a55 : -(h 2) < (-5/41 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_4471 h delta _ctx _hno a50 f0
  by_cases p1 : h 0 ≤ (7/45 : ℝ)
  swap
  · have f1 : -(h 0) < (-7/45 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_4472 h delta _ctx _hno a53 f1
  by_cases p2 : h 1 ≤ (9/70 : ℝ)
  swap
  · have f2 : -(h 1) < (-9/70 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_4473 h delta _ctx _hno a40 a41 a44 a45 a50 a51 a53 a55 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_4474 h delta _ctx _hno a34 a40 a41 a45 a49 a51 f3
  by_cases p4 : h 4 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 4) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_4475 h delta _ctx _hno a34 a40 a41 a50 a51 a53 a55 p2 f4
  apply _hno 111
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (7/45 : ℝ)) ∧ (h 1 ≤ (9/70 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (4/35 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_4458 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a44 : h 1 ≤ (3/23 : ℝ))
    (a54 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a44 + (1 : ℝ) * a54
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4457 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a31 : -(h 2) < (-4/33 : ℝ))
    (a34 : -(h 1) < (-5/39 : ℝ))
    (a40 : -(h 5) < (-2/19 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a43 : h 0 ≤ (3/20 : ℝ))
    (a45 : -(h 4) < (-7/62 : ℝ))
    (a49 : -(h 3) < (-3/26 : ℝ))
    (a50 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a53 : -(h 0) < (-6/41 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_4462 h delta _ctx _hno a50 f0
  by_cases p1 : h 0 ≤ (7/45 : ℝ)
  swap
  · have f1 : -(h 0) < (-7/45 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_4463 h delta _ctx _hno a43 f1
  by_cases p2 : h 1 ≤ (9/70 : ℝ)
  swap
  · have f2 : -(h 1) < (-9/70 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_4464 h delta _ctx _hno a31 a40 a41 a45 a49 a50 a53 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_4465 h delta _ctx _hno a34 a40 a41 a45 a49 a53 f3
  by_cases p4 : h 4 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 4) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_4466 h delta _ctx _hno a31 a34 a40 a41 a49 a53 f4
  apply _hno 111
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (7/45 : ℝ)) ∧ (h 1 ≤ (9/70 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (4/35 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_4456 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a50 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a52 : ((-2 : ℝ) * (delta)) < (-9/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a50 + (1 : ℝ) * a52
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4455 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : -(h 0) < (-1/7 : ℝ))
    (a45 : -(h 4) < (-7/62 : ℝ))
    (a50 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a54 : -(h 2) < (-5/41 : ℝ))
    (a58 : -(h 3) < (-2/17 : ℝ))
    (a61 : -(h 1) < (-9/70 : ℝ))
    (a67 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * a27 + (2/13 : ℝ) * a45 + (1/13 : ℝ) * a50 + (2/13 : ℝ) * a54 + (2/13 : ℝ) * a58 + (2/13 : ℝ) * a61 + (2/13 : ℝ) * a67 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4454 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : -(h 0) < (-1/7 : ℝ))
    (a40 : -(h 5) < (-2/19 : ℝ))
    (a50 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a54 : -(h 2) < (-5/41 : ℝ))
    (a61 : -(h 1) < (-9/70 : ℝ))
    (a66 : -(h 4) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order3 + (2/13 : ℝ) * a27 + (2/13 : ℝ) * a40 + (1/13 : ℝ) * a50 + (2/13 : ℝ) * a54 + (2/13 : ℝ) * a61 + (4/13 : ℝ) * a66 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4453 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : -(h 0) < (-1/7 : ℝ))
    (a40 : -(h 5) < (-2/19 : ℝ))
    (a45 : -(h 4) < (-7/62 : ℝ))
    (a50 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a58 : -(h 3) < (-2/17 : ℝ))
    (a61 : -(h 1) < (-9/70 : ℝ))
    (a65 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * a27 + (2/13 : ℝ) * a40 + (2/13 : ℝ) * a45 + (1/13 : ℝ) * a50 + (2/13 : ℝ) * a58 + (2/13 : ℝ) * a61 + (2/13 : ℝ) * a65 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4452 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a44 : h 1 ≤ (3/23 : ℝ))
    (a64 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a44 + (1 : ℝ) * a64
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4451 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a40 : -(h 5) < (-2/19 : ℝ))
    (a45 : -(h 4) < (-7/62 : ℝ))
    (a50 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a54 : -(h 2) < (-5/41 : ℝ))
    (a58 : -(h 3) < (-2/17 : ℝ))
    (a61 : -(h 1) < (-9/70 : ℝ))
    (a63 : -(h 0) < (-9/62 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * a40 + (2/13 : ℝ) * a45 + (1/13 : ℝ) * a50 + (2/13 : ℝ) * a54 + (2/13 : ℝ) * a58 + (2/13 : ℝ) * a61 + (2/13 : ℝ) * a63 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4450 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a62 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a62
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4449 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : -(h 0) < (-1/7 : ℝ))
    (a34 : -(h 1) < (-5/39 : ℝ))
    (a40 : -(h 5) < (-2/19 : ℝ))
    (a50 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a54 : -(h 2) < (-5/41 : ℝ))
    (a58 : -(h 3) < (-2/17 : ℝ))
    (a63 : -(h 4) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * a27 + (2/13 : ℝ) * a34 + (2/13 : ℝ) * a40 + (1/13 : ℝ) * a50 + (2/13 : ℝ) * a54 + (2/13 : ℝ) * a58 + (2/13 : ℝ) * a63 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4448 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : -(h 0) < (-1/7 : ℝ))
    (a34 : -(h 1) < (-5/39 : ℝ))
    (a40 : -(h 5) < (-2/19 : ℝ))
    (a45 : -(h 4) < (-7/62 : ℝ))
    (a50 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a58 : -(h 3) < (-2/17 : ℝ))
    (a62 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * a27 + (2/13 : ℝ) * a34 + (2/13 : ℝ) * a40 + (2/13 : ℝ) * a45 + (1/13 : ℝ) * a50 + (2/13 : ℝ) * a58 + (2/13 : ℝ) * a62 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4447 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : -(h 0) < (-1/7 : ℝ))
    (a40 : -(h 5) < (-2/19 : ℝ))
    (a44 : h 1 ≤ (3/23 : ℝ))
    (a45 : -(h 4) < (-7/62 : ℝ))
    (a50 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a54 : -(h 2) < (-5/41 : ℝ))
    (a58 : -(h 3) < (-2/17 : ℝ))
    (a61 : -(h 1) < (-9/70 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_4450 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (9/62 : ℝ)
  swap
  · have f1 : -(h 0) < (-9/62 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_4451 h delta _ctx _hno a40 a45 a50 a54 a58 a61 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_4452 h delta _ctx _hno a44 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_4453 h delta _ctx _hno a27 a40 a45 a50 a58 a61 f3
  by_cases p4 : h 4 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 4) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_4454 h delta _ctx _hno a27 a40 a50 a54 a61 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_4455 h delta _ctx _hno a27 a45 a50 a54 a58 a61 f5
  apply _hno 148
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (9/62 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_4446 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a52 : h 0 ≤ (6/41 : ℝ))
    (a60 : -(h 0) < (-7/45 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a52 + (1 : ℝ) * a60
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4445 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a59 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a59
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4444 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : -(h 0) < (-1/7 : ℝ))
    (a34 : -(h 1) < (-5/39 : ℝ))
    (a40 : -(h 5) < (-2/19 : ℝ))
    (a44 : h 1 ≤ (3/23 : ℝ))
    (a45 : -(h 4) < (-7/62 : ℝ))
    (a50 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a52 : h 0 ≤ (6/41 : ℝ))
    (a54 : -(h 2) < (-5/41 : ℝ))
    (a58 : -(h 3) < (-2/17 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_4445 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (7/45 : ℝ)
  swap
  · have f1 : -(h 0) < (-7/45 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_4446 h delta _ctx _hno a52 f1
  by_cases p2 : h 1 ≤ (9/70 : ℝ)
  swap
  · have f2 : -(h 1) < (-9/70 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_4447 h delta _ctx _hno a27 a40 a44 a45 a50 a54 a58 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_4448 h delta _ctx _hno a27 a34 a40 a45 a50 a58 f3
  by_cases p4 : h 4 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 4) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_4449 h delta _ctx _hno a27 a34 a40 a50 a54 a58 f4
  apply _hno 111
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (7/45 : ℝ)) ∧ (h 1 ≤ (9/70 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (4/35 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_4443 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a44 : h 1 ≤ (3/23 : ℝ))
    (a57 : -(h 1) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a44 + (1 : ℝ) * a57
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4442 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a52 : h 0 ≤ (6/41 : ℝ))
    (a56 : -(h 0) < (-5/34 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a52 + (1 : ℝ) * a56
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4441 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a55 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a55
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4440 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a31 : -(h 2) < (-4/33 : ℝ))
    (a40 : -(h 5) < (-2/19 : ℝ))
    (a45 : -(h 4) < (-7/62 : ℝ))
    (a50 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a52 : -(h 0) < (-6/41 : ℝ))
    (a55 : -(h 1) < (-9/70 : ℝ))
    (a59 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * a31 + (2/13 : ℝ) * a40 + (2/13 : ℝ) * a45 + (1/13 : ℝ) * a50 + (2/13 : ℝ) * a52 + (2/13 : ℝ) * a55 + (2/13 : ℝ) * a59 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4439 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a31 : -(h 2) < (-4/33 : ℝ))
    (a40 : -(h 5) < (-2/19 : ℝ))
    (a45 : -(h 4) < (-7/62 : ℝ))
    (a49 : -(h 3) < (-3/26 : ℝ))
    (a50 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a52 : -(h 0) < (-6/41 : ℝ))
    (a58 : -(h 1) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * a31 + (2/13 : ℝ) * a40 + (2/13 : ℝ) * a45 + (2/13 : ℝ) * a49 + (1/13 : ℝ) * a50 + (2/13 : ℝ) * a52 + (2/13 : ℝ) * a58 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4438 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a31 : -(h 2) < (-4/33 : ℝ))
    (a40 : -(h 5) < (-2/19 : ℝ))
    (a45 : -(h 4) < (-7/62 : ℝ))
    (a49 : -(h 3) < (-3/26 : ℝ))
    (a50 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a55 : -(h 1) < (-9/70 : ℝ))
    (a57 : -(h 0) < (-5/34 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * a31 + (2/13 : ℝ) * a40 + (2/13 : ℝ) * a45 + (2/13 : ℝ) * a49 + (1/13 : ℝ) * a50 + (2/13 : ℝ) * a55 + (2/13 : ℝ) * a57 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4437 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a56 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a56
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4436 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a31 : -(h 2) < (-4/33 : ℝ))
    (a34 : -(h 1) < (-5/39 : ℝ))
    (a40 : -(h 5) < (-2/19 : ℝ))
    (a49 : -(h 3) < (-3/26 : ℝ))
    (a50 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a52 : -(h 0) < (-6/41 : ℝ))
    (a57 : -(h 4) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * a31 + (2/13 : ℝ) * a34 + (2/13 : ℝ) * a40 + (2/13 : ℝ) * a49 + (1/13 : ℝ) * a50 + (2/13 : ℝ) * a52 + (2/13 : ℝ) * a57 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4435 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : -(h 1) < (-5/39 : ℝ))
    (a40 : -(h 5) < (-2/19 : ℝ))
    (a45 : -(h 4) < (-7/62 : ℝ))
    (a49 : -(h 3) < (-3/26 : ℝ))
    (a50 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a52 : -(h 0) < (-6/41 : ℝ))
    (a56 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * a34 + (2/13 : ℝ) * a40 + (2/13 : ℝ) * a45 + (2/13 : ℝ) * a49 + (1/13 : ℝ) * a50 + (2/13 : ℝ) * a52 + (2/13 : ℝ) * a56 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4434 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a31 : -(h 2) < (-4/33 : ℝ))
    (a40 : -(h 5) < (-2/19 : ℝ))
    (a45 : -(h 4) < (-7/62 : ℝ))
    (a49 : -(h 3) < (-3/26 : ℝ))
    (a50 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a52 : -(h 0) < (-6/41 : ℝ))
    (a55 : -(h 1) < (-9/70 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_4437 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (5/34 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/34 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_4438 h delta _ctx _hno a31 a40 a45 a49 a50 a55 f1
  by_cases p2 : h 1 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_4439 h delta _ctx _hno a31 a40 a45 a49 a50 a52 f2
  by_cases p3 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_4440 h delta _ctx _hno a31 a40 a45 a50 a52 a55 f3
  apply _hno 109
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (5/34 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_4433 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a43 : h 0 ≤ (3/20 : ℝ))
    (a54 : -(h 0) < (-7/45 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a43 + (1 : ℝ) * a54
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4432 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a53 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a53
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4431 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : -(h 0) < (-1/7 : ℝ))
    (a34 : -(h 1) < (-5/39 : ℝ))
    (a50 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a56 : -(h 5) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/16 : ℝ) * _ctx.order3 + (3/8 : ℝ) * _ctx.order4 + (1/32 : ℝ) * _ctx.fail1 + (1/8 : ℝ) * a27 + (3/16 : ℝ) * a34 + (3/32 : ℝ) * a50 + (9/16 : ℝ) * a56 + (3/16 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4430 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : -(h 0) < (-1/7 : ℝ))
    (a31 : -(h 2) < (-4/33 : ℝ))
    (a34 : -(h 1) < (-5/39 : ℝ))
    (a40 : -(h 5) < (-2/19 : ℝ))
    (a45 : -(h 4) < (-7/62 : ℝ))
    (a50 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a55 : -(h 3) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * a27 + (2/13 : ℝ) * a31 + (2/13 : ℝ) * a34 + (2/13 : ℝ) * a40 + (2/13 : ℝ) * a45 + (1/13 : ℝ) * a50 + (2/13 : ℝ) * a55 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4429 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : -(h 0) < (-1/7 : ℝ))
    (a34 : -(h 1) < (-5/39 : ℝ))
    (a40 : -(h 5) < (-2/19 : ℝ))
    (a44 : h 1 ≤ (3/23 : ℝ))
    (a45 : -(h 4) < (-7/62 : ℝ))
    (a50 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a52 : h 0 ≤ (6/41 : ℝ))
    (a54 : -(h 2) < (-5/41 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_4441 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (5/34 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/34 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_4442 h delta _ctx _hno a52 f1
  by_cases p2 : h 1 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_4443 h delta _ctx _hno a44 f2
  by_cases p3 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_4444 h delta _ctx _hno a27 a34 a40 a44 a45 a50 a52 a54 f3
  apply _hno 109
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (5/34 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_4428 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a44 : h 1 ≤ (3/23 : ℝ))
    (a53 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a44 + (1 : ℝ) * a53
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4427 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a31 : -(h 2) < (-4/33 : ℝ))
    (a34 : -(h 1) < (-5/39 : ℝ))
    (a40 : -(h 5) < (-2/19 : ℝ))
    (a43 : h 0 ≤ (3/20 : ℝ))
    (a45 : -(h 4) < (-7/62 : ℝ))
    (a49 : -(h 3) < (-3/26 : ℝ))
    (a50 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a52 : -(h 0) < (-6/41 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_4432 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (7/45 : ℝ)
  swap
  · have f1 : -(h 0) < (-7/45 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_4433 h delta _ctx _hno a43 f1
  by_cases p2 : h 1 ≤ (9/70 : ℝ)
  swap
  · have f2 : -(h 1) < (-9/70 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_4434 h delta _ctx _hno a31 a40 a45 a49 a50 a52 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_4435 h delta _ctx _hno a34 a40 a45 a49 a50 a52 f3
  by_cases p4 : h 4 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 4) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_4436 h delta _ctx _hno a31 a34 a40 a49 a50 a52 f4
  apply _hno 111
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (7/45 : ℝ)) ∧ (h 1 ≤ (9/70 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (4/35 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_4426 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a51 : ((-2 : ℝ) * (delta)) < (-9/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a51
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4425 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : -(h 0) < (-1/7 : ℝ))
    (a34 : -(h 1) < (-5/39 : ℝ))
    (a40 : -(h 5) < (-2/19 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a44 : h 1 ≤ (3/23 : ℝ))
    (a50 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a51 : h 0 ≤ (13/90 : ℝ))
    (a53 : h 3 ≤ (2/17 : ℝ))
    (a54 : -(h 4) < (-3/26 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (9/41 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-9/41 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_4507 h delta _ctx _hno a50 f0
  by_cases p1 : h 0 ≤ (6/41 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/41 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_4508 h delta _ctx _hno a51 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_4509 h delta _ctx _hno a44 f2
  by_cases p3 : h 2 ≤ (5/41 : ℝ)
  swap
  · have f3 : -(h 2) < (-5/41 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_4510 h delta _ctx _hno a27 a34 a40 a41 a50 a51 a54 f3
  by_cases p4 : h 3 ≤ (3/25 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_4511 h delta _ctx _hno a53 f4
  by_cases p5 : h 5 ≤ (2/17 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_4512 h delta _ctx _hno a27 a34 a41 f5
  apply _hno 41
  change (((2 : ℝ) * (delta)) ≤ (9/41 : ℝ)) ∧ (h 0 ≤ (6/41 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (5/41 : ℝ)) ∧ (h 3 ≤ (3/25 : ℝ)) ∧ (h 5 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_4424 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : -(h 0) < (-1/7 : ℝ))
    (a31 : -(h 2) < (-4/33 : ℝ))
    (a34 : -(h 1) < (-5/39 : ℝ))
    (a40 : -(h 5) < (-2/19 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a44 : h 1 ≤ (3/23 : ℝ))
    (a45 : -(h 4) < (-7/62 : ℝ))
    (a50 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a51 : h 0 ≤ (13/90 : ℝ))
    (a53 : -(h 3) < (-2/17 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (9/41 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-9/41 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_4484 h delta _ctx _hno a50 f0
  by_cases p1 : h 0 ≤ (6/41 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/41 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_4485 h delta _ctx _hno a51 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_4486 h delta _ctx _hno a44 f2
  by_cases p3 : h 2 ≤ (5/41 : ℝ)
  swap
  · have f3 : -(h 2) < (-5/41 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_4487 h delta _ctx _hno a27 a34 a40 a41 a44 a45 a50 a51 a53 f3
  by_cases p4 : h 3 ≤ (3/25 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_4488 h delta _ctx _hno a27 a31 a34 a40 a41 a45 f4
  by_cases p5 : h 5 ≤ (2/17 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_4489 h delta _ctx _hno a27 a34 a41 a53 f5
  apply _hno 41
  change (((2 : ℝ) * (delta)) ≤ (9/41 : ℝ)) ∧ (h 0 ≤ (6/41 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (5/41 : ℝ)) ∧ (h 3 ≤ (3/25 : ℝ)) ∧ (h 5 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_4423 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a44 : h 1 ≤ (3/23 : ℝ))
    (a52 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a44 + (1 : ℝ) * a52
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4422 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a31 : -(h 2) < (-4/33 : ℝ))
    (a34 : -(h 1) < (-5/39 : ℝ))
    (a40 : -(h 5) < (-2/19 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a43 : h 0 ≤ (3/20 : ℝ))
    (a44 : h 1 ≤ (3/23 : ℝ))
    (a45 : -(h 4) < (-7/62 : ℝ))
    (a49 : -(h 3) < (-3/26 : ℝ))
    (a50 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a51 : -(h 0) < (-13/90 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (9/41 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-9/41 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_4456 h delta _ctx _hno a50 f0
  by_cases p1 : h 0 ≤ (6/41 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/41 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_4457 h delta _ctx _hno a31 a34 a40 a41 a43 a45 a49 a50 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_4458 h delta _ctx _hno a44 f2
  by_cases p3 : h 2 ≤ (5/41 : ℝ)
  swap
  · have f3 : -(h 2) < (-5/41 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_4459 h delta _ctx _hno a34 a40 a41 a44 a45 a49 a50 a51 p1 f3
  by_cases p4 : h 3 ≤ (3/25 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_4460 h delta _ctx _hno a31 a34 a40 a41 a45 a51 f4
  by_cases p5 : h 5 ≤ (2/17 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_4461 h delta _ctx _hno a34 a41 a51 f5
  apply _hno 41
  change (((2 : ℝ) * (delta)) ≤ (9/41 : ℝ)) ∧ (h 0 ≤ (6/41 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (5/41 : ℝ)) ∧ (h 3 ≤ (3/25 : ℝ)) ∧ (h 5 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_4421 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : -(h 0) < (-1/7 : ℝ))
    (a31 : -(h 2) < (-4/33 : ℝ))
    (a34 : -(h 1) < (-5/39 : ℝ))
    (a40 : -(h 5) < (-2/19 : ℝ))
    (a43 : h 0 ≤ (3/20 : ℝ))
    (a44 : h 1 ≤ (3/23 : ℝ))
    (a45 : -(h 4) < (-7/62 : ℝ))
    (a49 : -(h 3) < (-3/26 : ℝ))
    (a50 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (9/41 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-9/41 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_4426 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (6/41 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/41 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_4427 h delta _ctx _hno a31 a34 a40 a43 a45 a49 a50 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_4428 h delta _ctx _hno a44 f2
  by_cases p3 : h 2 ≤ (5/41 : ℝ)
  swap
  · have f3 : -(h 2) < (-5/41 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_4429 h delta _ctx _hno a27 a34 a40 a44 a45 a50 p1 f3
  by_cases p4 : h 3 ≤ (3/25 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_4430 h delta _ctx _hno a27 a31 a34 a40 a45 a50 f4
  by_cases p5 : h 5 ≤ (2/17 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_4431 h delta _ctx _hno a27 a34 a50 f5
  apply _hno 41
  change (((2 : ℝ) * (delta)) ≤ (9/41 : ℝ)) ∧ (h 0 ≤ (6/41 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (5/41 : ℝ)) ∧ (h 3 ≤ (3/25 : ℝ)) ∧ (h 5 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_4420 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : -(h 0) < (-1/7 : ℝ))
    (a31 : -(h 2) < (-4/33 : ℝ))
    (a34 : -(h 1) < (-5/39 : ℝ))
    (a40 : -(h 5) < (-2/19 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a43 : h 0 ≤ (3/20 : ℝ))
    (a44 : h 1 ≤ (3/23 : ℝ))
    (a45 : -(h 4) < (-7/62 : ℝ))
    (a49 : -(h 3) < (-3/26 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_4421 h delta _ctx _hno a27 a31 a34 a40 a43 a44 a45 a49 f0
  by_cases p1 : h 0 ≤ (13/90 : ℝ)
  swap
  · have f1 : -(h 0) < (-13/90 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_4422 h delta _ctx _hno a31 a34 a40 a41 a43 a44 a45 a49 p0 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_4423 h delta _ctx _hno a44 f2
  by_cases p3 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_4424 h delta _ctx _hno a27 a31 a34 a40 a41 a44 a45 p0 p1 f3
  by_cases p4 : h 4 ≤ (3/26 : ℝ)
  swap
  · have f4 : -(h 4) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_4425 h delta _ctx _hno a27 a34 a40 a41 a44 p0 p1 p3 f4
  apply _hno 211
  change (((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)) ∧ (h 0 ≤ (13/90 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (3/26 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_4419 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a44 : h 1 ≤ (3/23 : ℝ))
    (a48 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a44 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4418 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a31 : -(h 2) < (-4/33 : ℝ))
    (a34 : -(h 1) < (-5/39 : ℝ))
    (a40 : -(h 5) < (-2/19 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a45 : -(h 4) < (-7/62 : ℝ))
    (a47 : -(h 0) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order3 + (2/13 : ℝ) * a31 + (2/13 : ℝ) * a34 + (2/13 : ℝ) * a40 + (1/13 : ℝ) * a41 + (4/13 : ℝ) * a45 + (2/13 : ℝ) * a47 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4417 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a46 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4416 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a27 : -(h 0) < (-1/7 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a44 : -(h 1) < (-3/23 : ℝ))
    (a52 : -(h 3) < (-2/17 : ℝ))
    (a56 : -(h 2) < (-5/41 : ℝ))
    (a62 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * a25 + (2/13 : ℝ) * a27 + (1/13 : ℝ) * a41 + (2/13 : ℝ) * a44 + (2/13 : ℝ) * a52 + (2/13 : ℝ) * a56 + (2/13 : ℝ) * a62 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4415 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : -(h 0) < (-1/7 : ℝ))
    (a40 : -(h 5) < (-2/19 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a44 : -(h 1) < (-3/23 : ℝ))
    (a56 : -(h 2) < (-5/41 : ℝ))
    (a61 : -(h 4) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order3 + (2/13 : ℝ) * a27 + (2/13 : ℝ) * a40 + (1/13 : ℝ) * a41 + (2/13 : ℝ) * a44 + (2/13 : ℝ) * a56 + (4/13 : ℝ) * a61 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4414 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a27 : -(h 0) < (-1/7 : ℝ))
    (a40 : -(h 5) < (-2/19 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a44 : -(h 1) < (-3/23 : ℝ))
    (a52 : -(h 3) < (-2/17 : ℝ))
    (a60 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * a25 + (2/13 : ℝ) * a27 + (2/13 : ℝ) * a40 + (1/13 : ℝ) * a41 + (2/13 : ℝ) * a44 + (2/13 : ℝ) * a52 + (2/13 : ℝ) * a60 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4413 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a37 : h 1 ≤ (5/38 : ℝ))
    (a59 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a37 + (1 : ℝ) * a59
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4412 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a50 : h 0 ≤ (13/90 : ℝ))
    (a58 : -(h 0) < (-9/62 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a50 + (1 : ℝ) * a58
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4411 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a49 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a57 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a49 + (1 : ℝ) * a57
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4410 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : -(h 0) < (-1/7 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a44 : -(h 1) < (-3/23 : ℝ))
    (a52 : -(h 3) < (-2/17 : ℝ))
    (a58 : -(h 5) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/16 : ℝ) * _ctx.order4 + (1/32 : ℝ) * _ctx.fail1 + (1/8 : ℝ) * a27 + (3/32 : ℝ) * a41 + (3/16 : ℝ) * a44 + (3/16 : ℝ) * a52 + (3/8 : ℝ) * a58 + (3/16 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4409 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a27 : -(h 0) < (-1/7 : ℝ))
    (a31 : -(h 2) < (-4/33 : ℝ))
    (a40 : -(h 5) < (-2/19 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a44 : -(h 1) < (-3/23 : ℝ))
    (a57 : -(h 3) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * a25 + (2/13 : ℝ) * a27 + (2/13 : ℝ) * a31 + (2/13 : ℝ) * a40 + (1/13 : ℝ) * a41 + (2/13 : ℝ) * a44 + (2/13 : ℝ) * a57 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4408 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a27 : -(h 0) < (-1/7 : ℝ))
    (a37 : h 1 ≤ (5/38 : ℝ))
    (a40 : -(h 5) < (-2/19 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a44 : -(h 1) < (-3/23 : ℝ))
    (a49 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a50 : h 0 ≤ (13/90 : ℝ))
    (a52 : -(h 3) < (-2/17 : ℝ))
    (a56 : -(h 2) < (-5/41 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_4411 h delta _ctx _hno a49 f0
  by_cases p1 : h 0 ≤ (9/62 : ℝ)
  swap
  · have f1 : -(h 0) < (-9/62 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_4412 h delta _ctx _hno a50 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_4413 h delta _ctx _hno a37 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_4414 h delta _ctx _hno a25 a27 a40 a41 a44 a52 f3
  by_cases p4 : h 4 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 4) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_4415 h delta _ctx _hno a27 a40 a41 a44 a56 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_4416 h delta _ctx _hno a25 a27 a41 a44 a52 a56 f5
  apply _hno 148
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (9/62 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_4407 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a37 : h 1 ≤ (5/38 : ℝ))
    (a55 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a37 + (1 : ℝ) * a55
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4406 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a50 : h 0 ≤ (13/90 : ℝ))
    (a54 : -(h 0) < (-6/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a50 + (1 : ℝ) * a54
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4405 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a49 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a53 : ((-2 : ℝ) * (delta)) < (-9/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a49 + (1 : ℝ) * a53
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4404 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a44 : -(h 1) < (-3/23 : ℝ))
    (a48 : -(h 3) < (-3/26 : ℝ))
    (a50 : -(h 0) < (-13/90 : ℝ))
    (a54 : -(h 2) < (-5/41 : ℝ))
    (a59 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * a25 + (1/13 : ℝ) * a41 + (2/13 : ℝ) * a44 + (2/13 : ℝ) * a48 + (2/13 : ℝ) * a50 + (2/13 : ℝ) * a54 + (2/13 : ℝ) * a59 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4403 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a40 : -(h 5) < (-2/19 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a44 : -(h 1) < (-3/23 : ℝ))
    (a50 : -(h 0) < (-13/90 : ℝ))
    (a54 : -(h 2) < (-5/41 : ℝ))
    (a58 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * a25 + (2/13 : ℝ) * a40 + (1/13 : ℝ) * a41 + (2/13 : ℝ) * a44 + (2/13 : ℝ) * a50 + (2/13 : ℝ) * a54 + (2/13 : ℝ) * a58 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4402 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a37 : h 1 ≤ (5/38 : ℝ))
    (a57 : -(h 1) < (-3/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a37 + (1 : ℝ) * a57
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4401 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a52 : h 0 ≤ (6/41 : ℝ))
    (a56 : -(h 0) < (-4/27 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a52 + (1 : ℝ) * a56
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4400 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a49 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a55 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a49 + (1 : ℝ) * a55
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4399 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a31 : -(h 2) < (-4/33 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a44 : -(h 1) < (-3/23 : ℝ))
    (a48 : -(h 3) < (-3/26 : ℝ))
    (a52 : -(h 0) < (-6/41 : ℝ))
    (a57 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * a25 + (2/13 : ℝ) * a31 + (1/13 : ℝ) * a41 + (2/13 : ℝ) * a44 + (2/13 : ℝ) * a48 + (2/13 : ℝ) * a52 + (2/13 : ℝ) * a57 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4398 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a31 : -(h 2) < (-4/33 : ℝ))
    (a40 : -(h 5) < (-2/19 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a44 : -(h 1) < (-3/23 : ℝ))
    (a52 : -(h 0) < (-6/41 : ℝ))
    (a56 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * a25 + (2/13 : ℝ) * a31 + (2/13 : ℝ) * a40 + (1/13 : ℝ) * a41 + (2/13 : ℝ) * a44 + (2/13 : ℝ) * a52 + (2/13 : ℝ) * a56 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4397 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a37 : h 1 ≤ (5/38 : ℝ))
    (a55 : -(h 1) < (-3/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a37 + (1 : ℝ) * a55
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4396 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 4) < (-1/9 : ℝ))
    (a31 : -(h 2) < (-4/33 : ℝ))
    (a40 : -(h 5) < (-2/19 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a44 : -(h 1) < (-3/23 : ℝ))
    (a48 : -(h 3) < (-3/26 : ℝ))
    (a54 : -(h 0) < (-4/27 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * a25 + (2/13 : ℝ) * a31 + (2/13 : ℝ) * a40 + (1/13 : ℝ) * a41 + (2/13 : ℝ) * a44 + (2/13 : ℝ) * a48 + (2/13 : ℝ) * a54 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_4395 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a49 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a53 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a49 + (1 : ℝ) * a53
  exact (lt_irrefl (0 : ℝ)) hbad

end RealPinwheel.WeakSevenBandData
