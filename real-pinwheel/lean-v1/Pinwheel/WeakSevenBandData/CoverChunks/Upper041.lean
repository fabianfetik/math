import Pinwheel.WeakSevenBandData.CoverChunks.Upper040

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem upper_node_1027 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a51 : -(h 3) < (-5/42 : ℝ))
    (a53 : -(h 0) < (-4/29 : ℝ))
    (a59 : -(h 4) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.min + (1/23 : ℝ) * _ctx.fail1 + (3/46 : ℝ) * a14 + (6/23 : ℝ) * a27 + (6/23 : ℝ) * a51 + (5/46 : ℝ) * a53 + (6/23 : ℝ) * a59 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1026 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a53 : -(h 0) < (-4/29 : ℝ))
    (a58 : -(h 3) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.min + (1/23 : ℝ) * _ctx.fail1 + (3/46 : ℝ) * a14 + (6/23 : ℝ) * a27 + (6/23 : ℝ) * a42 + (5/46 : ℝ) * a53 + (6/23 : ℝ) * a58 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1025 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a50 : h 2 ≤ (4/33 : ℝ))
    (a57 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a50 + (1 : ℝ) * a57
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1024 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a49 : h 1 ≤ (11/87 : ℝ))
    (a56 : -(h 1) < (-7/55 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a49 + (1 : ℝ) * a56
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1023 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a51 : -(h 3) < (-5/42 : ℝ))
    (a55 : -(h 0) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.min + (1/23 : ℝ) * _ctx.fail1 + (3/46 : ℝ) * a14 + (6/23 : ℝ) * a27 + (6/23 : ℝ) * a42 + (6/23 : ℝ) * a51 + (5/46 : ℝ) * a55 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1022 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a47 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ))
    (a54 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a47 + (1 : ℝ) * a54
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1021 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a47 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ))
    (a49 : h 1 ≤ (11/87 : ℝ))
    (a50 : h 2 ≤ (4/33 : ℝ))
    (a51 : -(h 3) < (-5/42 : ℝ))
    (a53 : -(h 0) < (-4/29 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1022 h delta _ctx _hno a47 f0
  by_cases p1 : h 0 ≤ (1/7 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1023 h delta _ctx _hno a14 a27 a42 a51 f1
  by_cases p2 : h 1 ≤ (7/55 : ℝ)
  swap
  · have f2 : -(h 1) < (-7/55 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1024 h delta _ctx _hno a49 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1025 h delta _ctx _hno a50 f3
  by_cases p4 : h 3 ≤ (3/25 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1026 h delta _ctx _hno a14 a27 a42 a53 f4
  by_cases p5 : h 4 ≤ (2/17 : ℝ)
  swap
  · have f5 : -(h 4) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1027 h delta _ctx _hno a14 a27 a51 a53 f5
  apply _hno 101
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (1/7 : ℝ)) ∧ (h 1 ≤ (7/55 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (3/25 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_1020 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a47 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ))
    (a52 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a47 + (1 : ℝ) * a52
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1019 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a47 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ))
    (a49 : h 1 ≤ (11/87 : ℝ))
    (a50 : h 2 ≤ (4/33 : ℝ))
    (a51 : -(h 3) < (-5/42 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1020 h delta _ctx _hno a47 f0
  by_cases p1 : h 0 ≤ (4/29 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/29 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1021 h delta _ctx _hno a14 a27 a42 a47 a49 a50 a51 f1
  by_cases p2 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1028 h delta _ctx _hno a50 f2
  by_cases p3 : h 3 ≤ (5/41 : ℝ)
  swap
  · have f3 : -(h 3) < (-5/41 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1029 h delta _ctx _hno a50 f3
  by_cases p4 : h 4 ≤ (4/33 : ℝ)
  swap
  · have f4 : -(h 4) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1030 h delta _ctx _hno a14 a27 a37 f4
  by_cases p5 : h 5 ≤ (7/64 : ℝ)
  swap
  · have f5 : -(h 5) < (-7/64 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1031 h delta _ctx _hno a14 a27 a37 a42 a51 f5
  apply _hno 98
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (4/29 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (5/41 : ℝ)) ∧ (h 4 ≤ (4/33 : ℝ)) ∧ (h 5 ≤ (7/64 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_1018 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a46 : -(h 3) < (-2/17 : ℝ))
    (a56 : -(h 5) < (-7/64 : ℝ))
    (a62 : -(h 4) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/29 : ℝ) * _ctx.fail1 + (3/116 : ℝ) * a14 + (6/29 : ℝ) * a27 + (13/116 : ℝ) * a37 + (6/29 : ℝ) * a46 + (6/29 : ℝ) * a56 + (6/29 : ℝ) * a62 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1017 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a50 : -(h 2) < (-4/33 : ℝ))
    (a56 : -(h 5) < (-7/64 : ℝ))
    (a61 : -(h 3) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/48 : ℝ) * a14 + (1/6 : ℝ) * a27 + (7/48 : ℝ) * a37 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a50 + (1/6 : ℝ) * a56 + (1/6 : ℝ) * a61 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1016 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a46 : -(h 3) < (-2/17 : ℝ))
    (a56 : -(h 5) < (-7/64 : ℝ))
    (a60 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/48 : ℝ) * a14 + (1/6 : ℝ) * a27 + (7/48 : ℝ) * a37 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a46 + (1/6 : ℝ) * a56 + (1/6 : ℝ) * a60 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1015 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a49 : h 1 ≤ (11/87 : ℝ))
    (a59 : -(h 1) < (-7/55 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a49 + (1 : ℝ) * a59
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1014 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a52 : h 0 ≤ (4/29 : ℝ))
    (a58 : -(h 0) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a52 + (1 : ℝ) * a58
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1013 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a47 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ))
    (a57 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a47 + (1 : ℝ) * a57
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1012 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a46 : -(h 3) < (-2/17 : ℝ))
    (a47 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ))
    (a49 : h 1 ≤ (11/87 : ℝ))
    (a50 : -(h 2) < (-4/33 : ℝ))
    (a52 : h 0 ≤ (4/29 : ℝ))
    (a56 : -(h 5) < (-7/64 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1013 h delta _ctx _hno a47 f0
  by_cases p1 : h 0 ≤ (1/7 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1014 h delta _ctx _hno a52 f1
  by_cases p2 : h 1 ≤ (7/55 : ℝ)
  swap
  · have f2 : -(h 1) < (-7/55 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1015 h delta _ctx _hno a49 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1016 h delta _ctx _hno a14 a27 a37 a42 a46 a56 f3
  by_cases p4 : h 3 ≤ (3/25 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1017 h delta _ctx _hno a14 a27 a37 a42 a50 a56 f4
  by_cases p5 : h 4 ≤ (2/17 : ℝ)
  swap
  · have f5 : -(h 4) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1018 h delta _ctx _hno a14 a27 a37 a46 a56 f5
  apply _hno 101
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (1/7 : ℝ)) ∧ (h 1 ≤ (7/55 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (3/25 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_1011 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a55 : -(h 4) < (-4/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.order3 + (6/23 : ℝ) * _ctx.min + (1/23 : ℝ) * _ctx.fail1 + (3/46 : ℝ) * a14 + (6/23 : ℝ) * a27 + (5/46 : ℝ) * a37 + (12/23 : ℝ) * a55 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1010 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a54 : -(h 3) < (-5/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order2 + (1/5 : ℝ) * _ctx.min + (1/20 : ℝ) * a14 + (1/5 : ℝ) * a27 + (3/20 : ℝ) * a37 + (1/5 : ℝ) * a42 + (2/5 : ℝ) * a54 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1009 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a46 : -(h 3) < (-2/17 : ℝ))
    (a53 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (1/20 : ℝ) * a14 + (1/5 : ℝ) * a27 + (3/20 : ℝ) * a37 + (1/5 : ℝ) * a42 + (1/5 : ℝ) * a46 + (1/5 : ℝ) * a53 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1008 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a46 : -(h 3) < (-2/17 : ℝ))
    (a50 : -(h 2) < (-4/33 : ℝ))
    (a52 : -(h 0) < (-4/29 : ℝ))
    (a59 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/48 : ℝ) * a14 + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a46 + (1/6 : ℝ) * a50 + (7/48 : ℝ) * a52 + (1/6 : ℝ) * a59 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1007 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a46 : -(h 3) < (-2/17 : ℝ))
    (a50 : -(h 2) < (-4/33 : ℝ))
    (a52 : -(h 0) < (-4/29 : ℝ))
    (a58 : -(h 4) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (1/20 : ℝ) * a14 + (1/5 : ℝ) * a27 + (1/5 : ℝ) * a46 + (1/5 : ℝ) * a50 + (3/20 : ℝ) * a52 + (1/5 : ℝ) * a58 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1006 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a50 : -(h 2) < (-4/33 : ℝ))
    (a52 : -(h 0) < (-4/29 : ℝ))
    (a57 : -(h 3) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (1/20 : ℝ) * a14 + (1/5 : ℝ) * a27 + (1/5 : ℝ) * a42 + (1/5 : ℝ) * a50 + (3/20 : ℝ) * a52 + (1/5 : ℝ) * a57 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1005 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a46 : -(h 3) < (-2/17 : ℝ))
    (a52 : -(h 0) < (-4/29 : ℝ))
    (a56 : -(h 2) < (-6/49 : ℝ))
    (a63 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/48 : ℝ) * a14 + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a46 + (7/48 : ℝ) * a52 + (1/6 : ℝ) * a56 + (1/6 : ℝ) * a63 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1004 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a46 : -(h 3) < (-2/17 : ℝ))
    (a52 : -(h 0) < (-4/29 : ℝ))
    (a56 : -(h 2) < (-6/49 : ℝ))
    (a62 : -(h 4) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (1/20 : ℝ) * a14 + (1/5 : ℝ) * a27 + (1/5 : ℝ) * a46 + (3/20 : ℝ) * a52 + (1/5 : ℝ) * a56 + (1/5 : ℝ) * a62 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1003 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a52 : -(h 0) < (-4/29 : ℝ))
    (a56 : -(h 2) < (-6/49 : ℝ))
    (a61 : -(h 3) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (1/20 : ℝ) * a14 + (1/5 : ℝ) * a27 + (1/5 : ℝ) * a42 + (3/20 : ℝ) * a52 + (1/5 : ℝ) * a56 + (1/5 : ℝ) * a61 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1002 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a46 : -(h 3) < (-2/17 : ℝ))
    (a52 : -(h 0) < (-4/29 : ℝ))
    (a60 : -(h 2) < (-7/57 : ℝ))
    (a66 : -(h 4) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (1/20 : ℝ) * a14 + (1/5 : ℝ) * a27 + (1/5 : ℝ) * a46 + (3/20 : ℝ) * a52 + (1/5 : ℝ) * a60 + (1/5 : ℝ) * a66 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1001 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a52 : -(h 0) < (-4/29 : ℝ))
    (a60 : -(h 2) < (-7/57 : ℝ))
    (a65 : -(h 3) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (1/20 : ℝ) * a14 + (1/5 : ℝ) * a27 + (1/5 : ℝ) * a42 + (3/20 : ℝ) * a52 + (1/5 : ℝ) * a60 + (1/5 : ℝ) * a65 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1000 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a46 : -(h 3) < (-2/17 : ℝ))
    (a52 : -(h 0) < (-4/29 : ℝ))
    (a64 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order1 + (1/5 : ℝ) * _ctx.min + (1/20 : ℝ) * a14 + (1/5 : ℝ) * a42 + (1/5 : ℝ) * a46 + (3/20 : ℝ) * a52 + (2/5 : ℝ) * a64 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_999 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a49 : h 1 ≤ (11/87 : ℝ))
    (a63 : -(h 1) < (-7/55 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a49 + (1 : ℝ) * a63
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_998 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a46 : -(h 3) < (-2/17 : ℝ))
    (a60 : -(h 2) < (-7/57 : ℝ))
    (a62 : -(h 0) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (1/20 : ℝ) * a14 + (1/5 : ℝ) * a27 + (1/5 : ℝ) * a42 + (1/5 : ℝ) * a46 + (1/5 : ℝ) * a60 + (3/20 : ℝ) * a62 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_997 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a47 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ))
    (a61 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a47 + (1 : ℝ) * a61
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_996 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a46 : -(h 3) < (-2/17 : ℝ))
    (a47 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ))
    (a49 : h 1 ≤ (11/87 : ℝ))
    (a52 : -(h 0) < (-4/29 : ℝ))
    (a60 : -(h 2) < (-7/57 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_997 h delta _ctx _hno a47 f0
  by_cases p1 : h 0 ≤ (1/7 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_998 h delta _ctx _hno a14 a27 a42 a46 a60 f1
  by_cases p2 : h 1 ≤ (7/55 : ℝ)
  swap
  · have f2 : -(h 1) < (-7/55 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_999 h delta _ctx _hno a49 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1000 h delta _ctx _hno a14 a42 a46 a52 f3
  by_cases p4 : h 3 ≤ (3/25 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1001 h delta _ctx _hno a14 a27 a42 a52 a60 f4
  by_cases p5 : h 4 ≤ (2/17 : ℝ)
  swap
  · have f5 : -(h 4) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1002 h delta _ctx _hno a14 a27 a46 a52 a60 f5
  apply _hno 101
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (1/7 : ℝ)) ∧ (h 1 ≤ (7/55 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (3/25 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_995 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a49 : h 1 ≤ (11/87 : ℝ))
    (a59 : -(h 1) < (-5/39 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a49 + (1 : ℝ) * a59
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_994 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a46 : -(h 3) < (-2/17 : ℝ))
    (a56 : -(h 2) < (-6/49 : ℝ))
    (a58 : -(h 0) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (1/20 : ℝ) * a14 + (1/5 : ℝ) * a27 + (1/5 : ℝ) * a42 + (1/5 : ℝ) * a46 + (1/5 : ℝ) * a56 + (3/20 : ℝ) * a58 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_993 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a47 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ))
    (a57 : ((-2 : ℝ) * (delta)) < (-12/55 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a47 + (1 : ℝ) * a57
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_992 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a46 : -(h 3) < (-2/17 : ℝ))
    (a47 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ))
    (a49 : h 1 ≤ (11/87 : ℝ))
    (a52 : -(h 0) < (-4/29 : ℝ))
    (a56 : -(h 2) < (-6/49 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (12/55 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-12/55 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_993 h delta _ctx _hno a47 f0
  by_cases p1 : h 0 ≤ (1/7 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_994 h delta _ctx _hno a14 a27 a42 a46 a56 f1
  by_cases p2 : h 1 ≤ (5/39 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/39 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_995 h delta _ctx _hno a49 f2
  by_cases p3 : h 2 ≤ (7/57 : ℝ)
  swap
  · have f3 : -(h 2) < (-7/57 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_996 h delta _ctx _hno a14 a27 a42 a46 a47 a49 a52 f3
  by_cases p4 : h 3 ≤ (3/25 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1003 h delta _ctx _hno a14 a27 a42 a52 a56 f4
  by_cases p5 : h 4 ≤ (2/17 : ℝ)
  swap
  · have f5 : -(h 4) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1004 h delta _ctx _hno a14 a27 a46 a52 a56 f5
  by_cases p6 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f6 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact upper_node_1005 h delta _ctx _hno a14 a27 a42 a46 a52 a56 f6
  apply _hno 100
  change (((2 : ℝ) * (delta)) ≤ (12/55 : ℝ)) ∧ (h 0 ≤ (1/7 : ℝ)) ∧ (h 1 ≤ (5/39 : ℝ)) ∧ (h 2 ≤ (7/57 : ℝ)) ∧ (h 3 ≤ (3/25 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem upper_node_991 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a49 : h 1 ≤ (11/87 : ℝ))
    (a55 : -(h 1) < (-11/87 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a49 + (1 : ℝ) * a55
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_990 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a46 : -(h 3) < (-2/17 : ℝ))
    (a50 : -(h 2) < (-4/33 : ℝ))
    (a54 : -(h 0) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (1/20 : ℝ) * a14 + (1/5 : ℝ) * a27 + (1/5 : ℝ) * a42 + (1/5 : ℝ) * a46 + (1/5 : ℝ) * a50 + (3/20 : ℝ) * a54 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_989 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a47 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ))
    (a53 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a47 + (1 : ℝ) * a53
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_988 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a46 : -(h 3) < (-2/17 : ℝ))
    (a47 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ))
    (a49 : h 1 ≤ (11/87 : ℝ))
    (a50 : -(h 2) < (-4/33 : ℝ))
    (a52 : -(h 0) < (-4/29 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_989 h delta _ctx _hno a47 f0
  by_cases p1 : h 0 ≤ (1/7 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_990 h delta _ctx _hno a14 a27 a42 a46 a50 f1
  by_cases p2 : h 1 ≤ (11/87 : ℝ)
  swap
  · have f2 : -(h 1) < (-11/87 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_991 h delta _ctx _hno a49 f2
  by_cases p3 : h 2 ≤ (6/49 : ℝ)
  swap
  · have f3 : -(h 2) < (-6/49 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_992 h delta _ctx _hno a14 a27 a42 a46 a47 a49 a52 f3
  by_cases p4 : h 3 ≤ (3/25 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1006 h delta _ctx _hno a14 a27 a42 a50 a52 f4
  by_cases p5 : h 4 ≤ (2/17 : ℝ)
  swap
  · have f5 : -(h 4) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1007 h delta _ctx _hno a14 a27 a46 a50 a52 f5
  by_cases p6 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f6 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact upper_node_1008 h delta _ctx _hno a14 a27 a42 a46 a50 a52 f6
  apply _hno 99
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (1/7 : ℝ)) ∧ (h 1 ≤ (11/87 : ℝ)) ∧ (h 2 ≤ (6/49 : ℝ)) ∧ (h 3 ≤ (3/25 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem upper_node_987 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a47 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ))
    (a51 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a47 + (1 : ℝ) * a51
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_986 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a46 : -(h 3) < (-2/17 : ℝ))
    (a47 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ))
    (a49 : h 1 ≤ (11/87 : ℝ))
    (a50 : -(h 2) < (-4/33 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_987 h delta _ctx _hno a47 f0
  by_cases p1 : h 0 ≤ (4/29 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/29 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_988 h delta _ctx _hno a14 a27 a42 a46 a47 a49 a50 f1
  by_cases p2 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1009 h delta _ctx _hno a14 a27 a37 a42 a46 f2
  by_cases p3 : h 3 ≤ (5/41 : ℝ)
  swap
  · have f3 : -(h 3) < (-5/41 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1010 h delta _ctx _hno a14 a27 a37 a42 f3
  by_cases p4 : h 4 ≤ (4/33 : ℝ)
  swap
  · have f4 : -(h 4) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1011 h delta _ctx _hno a14 a27 a37 f4
  by_cases p5 : h 5 ≤ (7/64 : ℝ)
  swap
  · have f5 : -(h 5) < (-7/64 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1012 h delta _ctx _hno a14 a27 a37 a42 a46 a47 a49 a50 p1 f5
  apply _hno 98
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (4/29 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (5/41 : ℝ)) ∧ (h 4 ≤ (4/33 : ℝ)) ∧ (h 5 ≤ (7/64 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_985 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a46 : -(h 3) < (-2/17 : ℝ))
    (a49 : -(h 1) < (-11/87 : ℝ))
    (a55 : -(h 5) < (-7/64 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/29 : ℝ) * _ctx.fail1 + (3/116 : ℝ) * a14 + (13/116 : ℝ) * a37 + (6/29 : ℝ) * a42 + (6/29 : ℝ) * a46 + (6/29 : ℝ) * a49 + (6/29 : ℝ) * a55 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_984 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a49 : -(h 1) < (-11/87 : ℝ))
    (a54 : -(h 4) < (-4/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.order3 + (6/23 : ℝ) * _ctx.min + (1/23 : ℝ) * _ctx.fail1 + (3/46 : ℝ) * a14 + (5/46 : ℝ) * a37 + (6/23 : ℝ) * a49 + (12/23 : ℝ) * a54 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_983 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a49 : -(h 1) < (-11/87 : ℝ))
    (a53 : -(h 3) < (-5/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order2 + (1/5 : ℝ) * _ctx.min + (1/20 : ℝ) * a14 + (3/20 : ℝ) * a37 + (1/5 : ℝ) * a42 + (1/5 : ℝ) * a49 + (2/5 : ℝ) * a53 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_982 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a46 : -(h 3) < (-2/17 : ℝ))
    (a49 : -(h 1) < (-11/87 : ℝ))
    (a52 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (1/20 : ℝ) * a14 + (3/20 : ℝ) * a37 + (1/5 : ℝ) * a42 + (1/5 : ℝ) * a46 + (1/5 : ℝ) * a49 + (1/5 : ℝ) * a52 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_981 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a46 : -(h 3) < (-2/17 : ℝ))
    (a49 : -(h 1) < (-11/87 : ℝ))
    (a51 : -(h 0) < (-4/29 : ℝ))
    (a58 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/29 : ℝ) * _ctx.fail1 + (3/116 : ℝ) * a14 + (6/29 : ℝ) * a42 + (6/29 : ℝ) * a46 + (6/29 : ℝ) * a49 + (13/116 : ℝ) * a51 + (6/29 : ℝ) * a58 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_980 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a46 : -(h 3) < (-2/17 : ℝ))
    (a49 : -(h 1) < (-11/87 : ℝ))
    (a51 : -(h 0) < (-4/29 : ℝ))
    (a57 : -(h 4) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.min + (1/23 : ℝ) * _ctx.fail1 + (3/46 : ℝ) * a14 + (6/23 : ℝ) * a46 + (6/23 : ℝ) * a49 + (5/46 : ℝ) * a51 + (6/23 : ℝ) * a57 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_979 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a49 : -(h 1) < (-11/87 : ℝ))
    (a51 : -(h 0) < (-4/29 : ℝ))
    (a56 : -(h 3) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.min + (1/23 : ℝ) * _ctx.fail1 + (3/46 : ℝ) * a14 + (6/23 : ℝ) * a42 + (6/23 : ℝ) * a49 + (5/46 : ℝ) * a51 + (6/23 : ℝ) * a56 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_978 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a46 : -(h 3) < (-2/17 : ℝ))
    (a49 : -(h 1) < (-11/87 : ℝ))
    (a51 : -(h 0) < (-4/29 : ℝ))
    (a55 : -(h 2) < (-7/57 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (1/20 : ℝ) * a14 + (1/5 : ℝ) * a42 + (1/5 : ℝ) * a46 + (1/5 : ℝ) * a49 + (3/20 : ℝ) * a51 + (1/5 : ℝ) * a55 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_977 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a46 : -(h 3) < (-2/17 : ℝ))
    (a51 : -(h 0) < (-4/29 : ℝ))
    (a54 : -(h 1) < (-5/39 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.min + (1/23 : ℝ) * _ctx.fail1 + (3/46 : ℝ) * a14 + (6/23 : ℝ) * a42 + (6/23 : ℝ) * a46 + (5/46 : ℝ) * a51 + (6/23 : ℝ) * a54 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_976 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a46 : -(h 3) < (-2/17 : ℝ))
    (a49 : -(h 1) < (-11/87 : ℝ))
    (a53 : -(h 0) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.min + (1/23 : ℝ) * _ctx.fail1 + (3/46 : ℝ) * a14 + (6/23 : ℝ) * a42 + (6/23 : ℝ) * a46 + (6/23 : ℝ) * a49 + (5/46 : ℝ) * a53 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_975 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a47 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ))
    (a52 : ((-2 : ℝ) * (delta)) < (-12/55 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a47 + (1 : ℝ) * a52
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_974 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a46 : -(h 3) < (-2/17 : ℝ))
    (a47 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ))
    (a49 : -(h 1) < (-11/87 : ℝ))
    (a51 : -(h 0) < (-4/29 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (12/55 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-12/55 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_975 h delta _ctx _hno a47 f0
  by_cases p1 : h 0 ≤ (1/7 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_976 h delta _ctx _hno a14 a42 a46 a49 f1
  by_cases p2 : h 1 ≤ (5/39 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/39 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_977 h delta _ctx _hno a14 a42 a46 a51 f2
  by_cases p3 : h 2 ≤ (7/57 : ℝ)
  swap
  · have f3 : -(h 2) < (-7/57 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_978 h delta _ctx _hno a14 a42 a46 a49 a51 f3
  by_cases p4 : h 3 ≤ (3/25 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_979 h delta _ctx _hno a14 a42 a49 a51 f4
  by_cases p5 : h 4 ≤ (2/17 : ℝ)
  swap
  · have f5 : -(h 4) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_980 h delta _ctx _hno a14 a46 a49 a51 f5
  by_cases p6 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f6 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact upper_node_981 h delta _ctx _hno a14 a42 a46 a49 a51 f6
  apply _hno 100
  change (((2 : ℝ) * (delta)) ≤ (12/55 : ℝ)) ∧ (h 0 ≤ (1/7 : ℝ)) ∧ (h 1 ≤ (5/39 : ℝ)) ∧ (h 2 ≤ (7/57 : ℝ)) ∧ (h 3 ≤ (3/25 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem upper_node_973 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a47 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ))
    (a50 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a47 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_972 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a46 : -(h 3) < (-2/17 : ℝ))
    (a47 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ))
    (a49 : -(h 1) < (-11/87 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_973 h delta _ctx _hno a47 f0
  by_cases p1 : h 0 ≤ (4/29 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/29 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_974 h delta _ctx _hno a14 a42 a46 a47 a49 f1
  by_cases p2 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_982 h delta _ctx _hno a14 a37 a42 a46 a49 f2
  by_cases p3 : h 3 ≤ (5/41 : ℝ)
  swap
  · have f3 : -(h 3) < (-5/41 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_983 h delta _ctx _hno a14 a37 a42 a49 f3
  by_cases p4 : h 4 ≤ (4/33 : ℝ)
  swap
  · have f4 : -(h 4) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_984 h delta _ctx _hno a14 a37 a49 f4
  by_cases p5 : h 5 ≤ (7/64 : ℝ)
  swap
  · have f5 : -(h 5) < (-7/64 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_985 h delta _ctx _hno a14 a37 a42 a46 a49 f5
  apply _hno 98
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (4/29 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (5/41 : ℝ)) ∧ (h 4 ≤ (4/33 : ℝ)) ∧ (h 5 ≤ (7/64 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_971 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : h 0 ≤ (1/7 : ℝ))
    (a48 : -(h 0) < (-8/55 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_970 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a46 : -(h 3) < (-2/17 : ℝ))
    (a47 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    (a53 : -(h 5) < (-7/64 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/32 : ℝ) * _ctx.fail1 + (3/16 : ℝ) * a27 + (1/8 : ℝ) * a37 + (3/16 : ℝ) * a42 + (3/16 : ℝ) * a46 + (3/32 : ℝ) * a47 + (3/16 : ℝ) * a53 + (3/16 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_969 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a52 : -(h 4) < (-4/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.order3 + (6/23 : ℝ) * _ctx.min + (1/23 : ℝ) * _ctx.fail1 + (3/46 : ℝ) * a14 + (6/23 : ℝ) * a27 + (5/46 : ℝ) * a37 + (12/23 : ℝ) * a52 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_968 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a47 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    (a51 : -(h 3) < (-5/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order2 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a47 + (1/3 : ℝ) * a51 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_967 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a46 : -(h 3) < (-2/17 : ℝ))
    (a47 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    (a50 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a46 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * a50 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_966 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a46 : -(h 3) < (-2/17 : ℝ))
    (a47 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    (a49 : -(h 0) < (-4/29 : ℝ))
    (a56 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/32 : ℝ) * _ctx.fail1 + (3/16 : ℝ) * a27 + (3/16 : ℝ) * a42 + (3/16 : ℝ) * a46 + (3/32 : ℝ) * a47 + (1/8 : ℝ) * a49 + (3/16 : ℝ) * a56 + (3/16 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_965 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a47 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    (a49 : -(h 0) < (-4/29 : ℝ))
    (a55 : -(h 4) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.order3 + (6/29 : ℝ) * _ctx.min + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a27 + (6/29 : ℝ) * a47 + (4/29 : ℝ) * a49 + (12/29 : ℝ) * a55 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_964 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a47 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    (a49 : -(h 0) < (-4/29 : ℝ))
    (a54 : -(h 3) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.min + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a27 + (6/29 : ℝ) * a42 + (6/29 : ℝ) * a47 + (4/29 : ℝ) * a49 + (6/29 : ℝ) * a54 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_963 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a46 : -(h 3) < (-2/17 : ℝ))
    (a47 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    (a49 : -(h 0) < (-4/29 : ℝ))
    (a53 : -(h 2) < (-6/49 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a46 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * a49 + (1/6 : ℝ) * a53 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_962 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a46 : -(h 3) < (-2/17 : ℝ))
    (a47 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    (a49 : -(h 0) < (-4/29 : ℝ))
    (a52 : -(h 1) < (-11/87 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.min + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a42 + (6/29 : ℝ) * a46 + (6/29 : ℝ) * a47 + (4/29 : ℝ) * a49 + (6/29 : ℝ) * a52 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_961 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a46 : -(h 3) < (-2/17 : ℝ))
    (a47 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    (a51 : -(h 0) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.min + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a27 + (6/29 : ℝ) * a42 + (6/29 : ℝ) * a46 + (6/29 : ℝ) * a47 + (4/29 : ℝ) * a51 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_960 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : h 3 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a46 : -(h 3) < (-2/17 : ℝ))
    (a50 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * a20 + (1/5 : ℝ) * a46 + (4/5 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_959 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : h 3 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a46 : -(h 3) < (-2/17 : ℝ))
    (a47 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    (a49 : -(h 0) < (-4/29 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_960 h delta _ctx _hno a20 a46 f0
  by_cases p1 : h 0 ≤ (1/7 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_961 h delta _ctx _hno a27 a42 a46 a47 f1
  by_cases p2 : h 1 ≤ (11/87 : ℝ)
  swap
  · have f2 : -(h 1) < (-11/87 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_962 h delta _ctx _hno a42 a46 a47 a49 f2
  by_cases p3 : h 2 ≤ (6/49 : ℝ)
  swap
  · have f3 : -(h 2) < (-6/49 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_963 h delta _ctx _hno a27 a42 a46 a47 a49 f3
  by_cases p4 : h 3 ≤ (3/25 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_964 h delta _ctx _hno a27 a42 a47 a49 f4
  by_cases p5 : h 4 ≤ (2/17 : ℝ)
  swap
  · have f5 : -(h 4) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_965 h delta _ctx _hno a27 a47 a49 f5
  by_cases p6 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f6 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact upper_node_966 h delta _ctx _hno a27 a42 a46 a47 a49 f6
  apply _hno 99
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (1/7 : ℝ)) ∧ (h 1 ≤ (11/87 : ℝ)) ∧ (h 2 ≤ (6/49 : ℝ)) ∧ (h 3 ≤ (3/25 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem upper_node_958 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : h 3 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a46 : -(h 3) < (-2/17 : ℝ))
    (a48 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * a20 + (1/5 : ℝ) * a46 + (4/5 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_957 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a20 : h 3 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a46 : -(h 3) < (-2/17 : ℝ))
    (a47 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_958 h delta _ctx _hno a20 a46 f0
  by_cases p1 : h 0 ≤ (4/29 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/29 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_959 h delta _ctx _hno a20 a27 a42 a46 a47 f1
  by_cases p2 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_967 h delta _ctx _hno a27 a37 a42 a46 a47 f2
  by_cases p3 : h 3 ≤ (5/41 : ℝ)
  swap
  · have f3 : -(h 3) < (-5/41 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_968 h delta _ctx _hno a27 a37 a42 a47 f3
  by_cases p4 : h 4 ≤ (4/33 : ℝ)
  swap
  · have f4 : -(h 4) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_969 h delta _ctx _hno a14 a27 a37 f4
  by_cases p5 : h 5 ≤ (7/64 : ℝ)
  swap
  · have f5 : -(h 5) < (-7/64 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_970 h delta _ctx _hno a27 a37 a42 a46 a47 f5
  apply _hno 98
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (4/29 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (5/41 : ℝ)) ∧ (h 4 ≤ (4/33 : ℝ)) ∧ (h 5 ≤ (7/64 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_956 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a20 : h 3 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a29 : h 0 ≤ (1/7 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a46 : -(h 3) < (-2/17 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_957 h delta _ctx _hno a14 a20 a27 a37 a42 a46 f0
  by_cases p1 : h 0 ≤ (8/55 : ℝ)
  swap
  · have f1 : -(h 0) < (-8/55 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_971 h delta _ctx _hno a29 f1
  by_cases p2 : h 1 ≤ (11/87 : ℝ)
  swap
  · have f2 : -(h 1) < (-11/87 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_972 h delta _ctx _hno a14 a37 a42 a46 p0 f2
  by_cases p3 : h 2 ≤ (4/33 : ℝ)
  swap
  · have f3 : -(h 2) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_986 h delta _ctx _hno a14 a27 a37 a42 a46 p0 p2 f3
  by_cases p4 : h 3 ≤ (5/42 : ℝ)
  swap
  · have f4 : -(h 3) < (-5/42 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1019 h delta _ctx _hno a14 a27 a37 a42 p0 p2 p3 f4
  by_cases p5 : h 4 ≤ (2/17 : ℝ)
  swap
  · have f5 : -(h 4) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1032 h delta _ctx _hno a14 a27 a37 a46 f5
  apply _hno 94
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (8/55 : ℝ)) ∧ (h 1 ≤ (11/87 : ℝ)) ∧ (h 2 ≤ (4/33 : ℝ)) ∧ (h 3 ≤ (5/42 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_955 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a40 : h 1 ≤ (9/70 : ℝ))
    (a45 : -(h 1) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a40 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_954 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : h 0 ≤ (1/7 : ℝ))
    (a44 : -(h 0) < (-5/34 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_953 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : h 3 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * a20 + (1/5 : ℝ) * a42 + (4/5 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_952 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a20 : h 3 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a29 : h 0 ≤ (1/7 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a40 : h 1 ≤ (9/70 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_953 h delta _ctx _hno a20 a42 f0
  by_cases p1 : h 0 ≤ (5/34 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/34 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_954 h delta _ctx _hno a29 f1
  by_cases p2 : h 1 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_955 h delta _ctx _hno a40 f2
  by_cases p3 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_956 h delta _ctx _hno a14 a20 a27 a29 a37 a42 f3
  apply _hno 92
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (5/34 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_951 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a34 : h 2 ≤ (1/8 : ℝ))
    (a41 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_950 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a40 : -(h 1) < (-9/70 : ℝ))
    (a44 : -(h 3) < (-2/17 : ℝ))
    (a48 : -(h 4) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.min + (1/23 : ℝ) * _ctx.fail1 + (3/46 : ℝ) * a14 + (5/46 : ℝ) * a37 + (6/23 : ℝ) * a40 + (6/23 : ℝ) * a44 + (6/23 : ℝ) * a48 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_949 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a40 : -(h 1) < (-9/70 : ℝ))
    (a44 : -(h 3) < (-2/17 : ℝ))
    (a47 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (16/55 : ℝ) * _ctx.min + (3/55 : ℝ) * _ctx.fail2 + (4/55 : ℝ) * a14 + (1/110 : ℝ) * a24 + (16/55 : ℝ) * a40 + (31/110 : ℝ) * a44 + (16/55 : ℝ) * a47 + (16/55 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_948 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a35 : -(h 4) < (-1/9 : ℝ))
    (a40 : -(h 1) < (-9/70 : ℝ))
    (a44 : -(h 3) < (-2/17 : ℝ))
    (a46 : -(h 0) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.min + (1/23 : ℝ) * _ctx.fail1 + (3/46 : ℝ) * a14 + (6/23 : ℝ) * a35 + (6/23 : ℝ) * a40 + (6/23 : ℝ) * a44 + (5/46 : ℝ) * a46 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

end RealPinwheel.WeakSevenBandData
