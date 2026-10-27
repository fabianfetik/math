import Pinwheel.WeakSevenBandData.CoverChunks.New150

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem new_node_1034 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : -(h 4) < (-7/64 : ℝ))
    (a26 : -(h 5) < (-2/19 : ℝ))
    (a28 : -(h 0) < (-4/23 : ℝ))
    (a31 : -(h 1) < (-5/41 : ℝ))
    (a39 : -(h 3) < (-5/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order2 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a19 + (1/6 : ℝ) * a26 + (1/6 : ℝ) * a28 + (1/6 : ℝ) * a31 + (1/3 : ℝ) * a39 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1033 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a19 : -(h 4) < (-7/64 : ℝ))
    (a26 : -(h 5) < (-2/19 : ℝ))
    (a28 : -(h 0) < (-4/23 : ℝ))
    (a35 : -(h 2) < (-1/9 : ℝ))
    (a38 : -(h 1) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order3 + (1/13 : ℝ) * a13 + (4/13 : ℝ) * a19 + (2/13 : ℝ) * a26 + (2/13 : ℝ) * a28 + (2/13 : ℝ) * a35 + (2/13 : ℝ) * a38 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1032 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : h 0 ≤ (3/17 : ℝ))
    (a37 : -(h 0) < (-5/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a24 + (1 : ℝ) * a37
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1031 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a29 : ((2 : ℝ) * (delta)) ≤ (10/49 : ℝ))
    (a36 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a36
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1030 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a19 : -(h 4) < (-7/64 : ℝ))
    (a24 : h 0 ≤ (3/17 : ℝ))
    (a26 : -(h 5) < (-2/19 : ℝ))
    (a28 : -(h 0) < (-4/23 : ℝ))
    (a29 : ((2 : ℝ) * (delta)) ≤ (10/49 : ℝ))
    (a31 : -(h 1) < (-5/41 : ℝ))
    (a35 : -(h 2) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_1031 h delta _ctx _hno a29 f0
  by_cases p1 : h 0 ≤ (5/28 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/28 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_1032 h delta _ctx _hno a24 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_1033 h delta _ctx _hno a13 a19 a26 a28 a35 f2
  by_cases p3 : h 3 ≤ (5/41 : ℝ)
  swap
  · have f3 : -(h 3) < (-5/41 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_1034 h delta _ctx _hno a19 a26 a28 a31 f3
  by_cases p4 : h 5 ≤ (3/28 : ℝ)
  swap
  · have f4 : -(h 5) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_1035 h delta _ctx _hno a13 a19 a28 a31 a35 f4
  apply _hno 85
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (5/28 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (5/41 : ℝ)) ∧ (h 5 ≤ (3/28 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_1029 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a18 : h 1 ≤ (1/8 : ℝ))
    (a34 : -(h 1) < (-4/27 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a18 + (1 : ℝ) * a34
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1028 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : h 0 ≤ (3/17 : ℝ))
    (a33 : -(h 0) < (-5/27 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a24 + (1 : ℝ) * a33
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1027 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a29 : ((2 : ℝ) * (delta)) ≤ (10/49 : ℝ))
    (a32 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a32
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1026 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : -(h 4) < (-7/64 : ℝ))
    (a22 : -(h 1) < (-4/33 : ℝ))
    (a28 : -(h 0) < (-4/23 : ℝ))
    (a29 : ((-2 : ℝ) * (delta)) < (-10/49 : ℝ))
    (a33 : -(h 2) < (-1/9 : ℝ))
    (a38 : -(h 5) < (-3/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order3 + (4/13 : ℝ) * a19 + (2/13 : ℝ) * a22 + (2/13 : ℝ) * a28 + (1/13 : ℝ) * a29 + (2/13 : ℝ) * a33 + (2/13 : ℝ) * a38 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1025 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : -(h 4) < (-7/64 : ℝ))
    (a26 : -(h 5) < (-2/19 : ℝ))
    (a28 : -(h 0) < (-4/23 : ℝ))
    (a29 : ((-2 : ℝ) * (delta)) < (-10/49 : ℝ))
    (a37 : -(h 3) < (-5/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order1 + (4/13 : ℝ) * _ctx.order2 + (2/13 : ℝ) * a19 + (2/13 : ℝ) * a26 + (2/13 : ℝ) * a28 + (1/13 : ℝ) * a29 + (6/13 : ℝ) * a37 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1024 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : -(h 4) < (-7/64 : ℝ))
    (a26 : -(h 5) < (-2/19 : ℝ))
    (a28 : -(h 0) < (-4/23 : ℝ))
    (a29 : ((-2 : ℝ) * (delta)) < (-10/49 : ℝ))
    (a33 : -(h 2) < (-1/9 : ℝ))
    (a36 : -(h 1) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order3 + (4/13 : ℝ) * a19 + (2/13 : ℝ) * a26 + (2/13 : ℝ) * a28 + (1/13 : ℝ) * a29 + (2/13 : ℝ) * a33 + (2/13 : ℝ) * a36 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1023 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : h 0 ≤ (3/17 : ℝ))
    (a35 : -(h 0) < (-5/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a24 + (1 : ℝ) * a35
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1022 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : -(h 4) < (-7/64 : ℝ))
    (a22 : -(h 1) < (-4/33 : ℝ))
    (a26 : -(h 5) < (-2/19 : ℝ))
    (a28 : -(h 0) < (-4/23 : ℝ))
    (a33 : -(h 2) < (-1/9 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order3 + (4/13 : ℝ) * a19 + (2/13 : ℝ) * a22 + (2/13 : ℝ) * a26 + (2/13 : ℝ) * a28 + (2/13 : ℝ) * a33 + (1/13 : ℝ) * a34 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1021 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : -(h 4) < (-7/64 : ℝ))
    (a22 : -(h 1) < (-4/33 : ℝ))
    (a24 : h 0 ≤ (3/17 : ℝ))
    (a26 : -(h 5) < (-2/19 : ℝ))
    (a28 : -(h 0) < (-4/23 : ℝ))
    (a29 : ((-2 : ℝ) * (delta)) < (-10/49 : ℝ))
    (a33 : -(h 2) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_1022 h delta _ctx _hno a19 a22 a26 a28 a33 f0
  by_cases p1 : h 0 ≤ (5/28 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/28 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_1023 h delta _ctx _hno a24 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_1024 h delta _ctx _hno a19 a26 a28 a29 a33 f2
  by_cases p3 : h 3 ≤ (5/41 : ℝ)
  swap
  · have f3 : -(h 3) < (-5/41 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_1025 h delta _ctx _hno a19 a26 a28 a29 f3
  by_cases p4 : h 5 ≤ (3/28 : ℝ)
  swap
  · have f4 : -(h 5) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_1026 h delta _ctx _hno a19 a22 a28 a29 a33 f4
  apply _hno 85
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (5/28 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (5/41 : ℝ)) ∧ (h 5 ≤ (3/28 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_1020 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a18 : h 1 ≤ (1/8 : ℝ))
    (a32 : -(h 1) < (-4/27 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a18 + (1 : ℝ) * a32
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1019 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : h 0 ≤ (3/17 : ℝ))
    (a31 : -(h 0) < (-5/27 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a24 + (1 : ℝ) * a31
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1018 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a30 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a30
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1017 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a18 : h 1 ≤ (1/8 : ℝ))
    (a19 : -(h 4) < (-7/64 : ℝ))
    (a24 : h 0 ≤ (3/17 : ℝ))
    (a26 : -(h 5) < (-2/19 : ℝ))
    (a28 : -(h 0) < (-4/23 : ℝ))
    (a29 : ((2 : ℝ) * (delta)) ≤ (10/49 : ℝ))
    (a31 : -(h 1) < (-5/41 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_1027 h delta _ctx _hno a29 f0
  by_cases p1 : h 0 ≤ (5/27 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/27 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_1028 h delta _ctx _hno a24 f1
  by_cases p2 : h 1 ≤ (4/27 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/27 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_1029 h delta _ctx _hno a18 f2
  by_cases p3 : h 2 ≤ (1/9 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_1030 h delta _ctx _hno a13 a19 a24 a26 a28 a29 a31 f3
  apply _hno 79
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (5/27 : ℝ)) ∧ (h 1 ≤ (4/27 : ℝ)) ∧ (h 2 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_1016 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : h 0 ≤ (3/17 : ℝ))
    (a30 : -(h 0) < (-2/11 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a24 + (1 : ℝ) * a30
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1015 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a18 : h 1 ≤ (1/8 : ℝ))
    (a19 : -(h 4) < (-7/64 : ℝ))
    (a22 : -(h 1) < (-4/33 : ℝ))
    (a24 : h 0 ≤ (3/17 : ℝ))
    (a26 : -(h 5) < (-2/19 : ℝ))
    (a28 : -(h 0) < (-4/23 : ℝ))
    (a29 : ((-2 : ℝ) * (delta)) < (-10/49 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_1018 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (5/27 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/27 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_1019 h delta _ctx _hno a24 f1
  by_cases p2 : h 1 ≤ (4/27 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/27 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_1020 h delta _ctx _hno a18 f2
  by_cases p3 : h 2 ≤ (1/9 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_1021 h delta _ctx _hno a19 a22 a24 a26 a28 a29 f3
  apply _hno 79
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (5/27 : ℝ)) ∧ (h 1 ≤ (4/27 : ℝ)) ∧ (h 2 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_1014 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a15 : -(h 0) < (-1/6 : ℝ))
    (a22 : -(h 1) < (-4/33 : ℝ))
    (a31 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/16 : ℝ) * _ctx.order3 + (3/8 : ℝ) * _ctx.order4 + (1/32 : ℝ) * _ctx.fail1 + (3/32 : ℝ) * a13 + (1/8 : ℝ) * a15 + (3/16 : ℝ) * a22 + (9/16 : ℝ) * a31 + (3/16 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1013 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a15 : -(h 0) < (-1/6 : ℝ))
    (a22 : -(h 1) < (-4/33 : ℝ))
    (a26 : -(h 5) < (-2/19 : ℝ))
    (a28 : h 0 ≤ (4/23 : ℝ))
    (a30 : -(h 4) < (-9/80 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (10/49 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-10/49 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_1036 h delta _ctx _hno a15 a22 a26 a28 a30 f0
  by_cases p1 : h 0 ≤ (2/11 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/11 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_1037 h delta _ctx _hno a28 f1
  by_cases p2 : h 1 ≤ (5/41 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/41 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_1038 h delta _ctx _hno a13 a15 a26 a28 a30 p0 f2
  apply _hno 65
  change (((2 : ℝ) * (delta)) ≤ (10/49 : ℝ)) ∧ (h 0 ≤ (2/11 : ℝ)) ∧ (h 1 ≤ (5/41 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem new_node_1012 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a18 : h 1 ≤ (1/8 : ℝ))
    (a29 : -(h 1) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a18 + (1 : ℝ) * a29
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1011 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a18 : h 1 ≤ (1/8 : ℝ))
    (a19 : -(h 4) < (-7/64 : ℝ))
    (a22 : -(h 1) < (-4/33 : ℝ))
    (a24 : h 0 ≤ (3/17 : ℝ))
    (a26 : -(h 5) < (-2/19 : ℝ))
    (a28 : -(h 0) < (-4/23 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (10/49 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-10/49 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_1015 h delta _ctx _hno a18 a19 a22 a24 a26 a28 f0
  by_cases p1 : h 0 ≤ (2/11 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/11 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_1016 h delta _ctx _hno a24 f1
  by_cases p2 : h 1 ≤ (5/41 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/41 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_1017 h delta _ctx _hno a13 a18 a19 a24 a26 a28 p0 f2
  apply _hno 65
  change (((2 : ℝ) * (delta)) ≤ (10/49 : ℝ)) ∧ (h 0 ≤ (2/11 : ℝ)) ∧ (h 1 ≤ (5/41 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem new_node_1010 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a27
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1009 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a19 : -(h 4) < (-7/64 : ℝ))
    (a24 : -(h 0) < (-3/17 : ℝ))
    (a27 : -(h 1) < (-5/41 : ℝ))
    (a31 : -(h 2) < (-1/9 : ℝ))
    (a36 : -(h 5) < (-3/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order3 + (1/13 : ℝ) * a13 + (4/13 : ℝ) * a19 + (2/13 : ℝ) * a24 + (2/13 : ℝ) * a27 + (2/13 : ℝ) * a31 + (2/13 : ℝ) * a36 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1008 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : -(h 4) < (-7/64 : ℝ))
    (a24 : -(h 0) < (-3/17 : ℝ))
    (a27 : -(h 1) < (-5/41 : ℝ))
    (a35 : -(h 3) < (-5/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order2 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a19 + (1/5 : ℝ) * a24 + (1/5 : ℝ) * a27 + (2/5 : ℝ) * a35 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1007 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a19 : -(h 4) < (-7/64 : ℝ))
    (a24 : -(h 0) < (-3/17 : ℝ))
    (a31 : -(h 2) < (-1/9 : ℝ))
    (a34 : -(h 1) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/3 : ℝ) * a19 + (1/6 : ℝ) * a24 + (1/6 : ℝ) * a31 + (1/6 : ℝ) * a34 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1006 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a19 : -(h 4) < (-7/64 : ℝ))
    (a27 : -(h 1) < (-5/41 : ℝ))
    (a31 : -(h 2) < (-1/9 : ℝ))
    (a33 : -(h 0) < (-5/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/3 : ℝ) * a19 + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a31 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1005 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : ((2 : ℝ) * (delta)) ≤ (10/49 : ℝ))
    (a32 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a25 + (1 : ℝ) * a32
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1004 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a19 : -(h 4) < (-7/64 : ℝ))
    (a24 : -(h 0) < (-3/17 : ℝ))
    (a25 : ((2 : ℝ) * (delta)) ≤ (10/49 : ℝ))
    (a27 : -(h 1) < (-5/41 : ℝ))
    (a31 : -(h 2) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_1005 h delta _ctx _hno a25 f0
  by_cases p1 : h 0 ≤ (5/28 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/28 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_1006 h delta _ctx _hno a13 a19 a27 a31 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_1007 h delta _ctx _hno a13 a19 a24 a31 f2
  by_cases p3 : h 3 ≤ (5/41 : ℝ)
  swap
  · have f3 : -(h 3) < (-5/41 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_1008 h delta _ctx _hno a19 a24 a27 f3
  by_cases p4 : h 5 ≤ (3/28 : ℝ)
  swap
  · have f4 : -(h 5) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_1009 h delta _ctx _hno a13 a19 a24 a27 a31 f4
  apply _hno 85
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (5/28 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (5/41 : ℝ)) ∧ (h 5 ≤ (3/28 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_1003 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a18 : h 1 ≤ (1/8 : ℝ))
    (a30 : -(h 1) < (-4/27 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a18 + (1 : ℝ) * a30
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1002 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a21 : h 0 ≤ (2/11 : ℝ))
    (a29 : -(h 0) < (-5/27 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a21 + (1 : ℝ) * a29
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1001 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : ((2 : ℝ) * (delta)) ≤ (10/49 : ℝ))
    (a28 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a25 + (1 : ℝ) * a28
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1000 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : -(h 4) < (-7/64 : ℝ))
    (a22 : -(h 1) < (-4/33 : ℝ))
    (a24 : -(h 0) < (-3/17 : ℝ))
    (a25 : ((-2 : ℝ) * (delta)) < (-10/49 : ℝ))
    (a29 : -(h 2) < (-1/9 : ℝ))
    (a34 : -(h 5) < (-3/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order3 + (4/13 : ℝ) * a19 + (2/13 : ℝ) * a22 + (2/13 : ℝ) * a24 + (1/13 : ℝ) * a25 + (2/13 : ℝ) * a29 + (2/13 : ℝ) * a34 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_999 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : -(h 4) < (-7/64 : ℝ))
    (a24 : -(h 0) < (-3/17 : ℝ))
    (a25 : ((-2 : ℝ) * (delta)) < (-10/49 : ℝ))
    (a33 : -(h 3) < (-5/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order1 + (1/3 : ℝ) * _ctx.order2 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a19 + (1/6 : ℝ) * a24 + (1/6 : ℝ) * a25 + (1/2 : ℝ) * a33 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_998 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : -(h 4) < (-7/64 : ℝ))
    (a24 : -(h 0) < (-3/17 : ℝ))
    (a25 : ((-2 : ℝ) * (delta)) < (-10/49 : ℝ))
    (a29 : -(h 2) < (-1/9 : ℝ))
    (a32 : -(h 1) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/3 : ℝ) * a19 + (1/6 : ℝ) * a24 + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a29 + (1/6 : ℝ) * a32 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_997 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : -(h 4) < (-7/64 : ℝ))
    (a22 : -(h 1) < (-4/33 : ℝ))
    (a25 : ((-2 : ℝ) * (delta)) < (-10/49 : ℝ))
    (a29 : -(h 2) < (-1/9 : ℝ))
    (a31 : -(h 0) < (-5/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/3 : ℝ) * a19 + (1/6 : ℝ) * a22 + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a29 + (1/6 : ℝ) * a31 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_996 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : -(h 4) < (-7/64 : ℝ))
    (a22 : -(h 1) < (-4/33 : ℝ))
    (a24 : -(h 0) < (-3/17 : ℝ))
    (a29 : -(h 2) < (-1/9 : ℝ))
    (a30 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/3 : ℝ) * a19 + (1/6 : ℝ) * a22 + (1/6 : ℝ) * a24 + (1/6 : ℝ) * a29 + (1/6 : ℝ) * a30 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_995 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : -(h 4) < (-7/64 : ℝ))
    (a22 : -(h 1) < (-4/33 : ℝ))
    (a24 : -(h 0) < (-3/17 : ℝ))
    (a25 : ((-2 : ℝ) * (delta)) < (-10/49 : ℝ))
    (a29 : -(h 2) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_996 h delta _ctx _hno a19 a22 a24 a29 f0
  by_cases p1 : h 0 ≤ (5/28 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/28 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_997 h delta _ctx _hno a19 a22 a25 a29 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_998 h delta _ctx _hno a19 a24 a25 a29 f2
  by_cases p3 : h 3 ≤ (5/41 : ℝ)
  swap
  · have f3 : -(h 3) < (-5/41 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_999 h delta _ctx _hno a19 a24 a25 f3
  by_cases p4 : h 5 ≤ (3/28 : ℝ)
  swap
  · have f4 : -(h 5) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_1000 h delta _ctx _hno a19 a22 a24 a25 a29 f4
  apply _hno 85
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (5/28 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (5/41 : ℝ)) ∧ (h 5 ≤ (3/28 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_994 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a18 : h 1 ≤ (1/8 : ℝ))
    (a28 : -(h 1) < (-4/27 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a18 + (1 : ℝ) * a28
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_993 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a21 : h 0 ≤ (2/11 : ℝ))
    (a27 : -(h 0) < (-5/27 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a21 + (1 : ℝ) * a27
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_992 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a26
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_991 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a18 : h 1 ≤ (1/8 : ℝ))
    (a19 : -(h 4) < (-7/64 : ℝ))
    (a21 : h 0 ≤ (2/11 : ℝ))
    (a24 : -(h 0) < (-3/17 : ℝ))
    (a25 : ((2 : ℝ) * (delta)) ≤ (10/49 : ℝ))
    (a27 : -(h 1) < (-5/41 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_1001 h delta _ctx _hno a25 f0
  by_cases p1 : h 0 ≤ (5/27 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/27 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_1002 h delta _ctx _hno a21 f1
  by_cases p2 : h 1 ≤ (4/27 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/27 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_1003 h delta _ctx _hno a18 f2
  by_cases p3 : h 2 ≤ (1/9 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_1004 h delta _ctx _hno a13 a19 a24 a25 a27 f3
  apply _hno 79
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (5/27 : ℝ)) ∧ (h 1 ≤ (4/27 : ℝ)) ∧ (h 2 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_990 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a19 : -(h 4) < (-7/64 : ℝ))
    (a22 : -(h 1) < (-4/33 : ℝ))
    (a26 : -(h 0) < (-2/11 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order2 + (1/3 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/2 : ℝ) * a19 + (1/6 : ℝ) * a22 + (1/6 : ℝ) * a26 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_989 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a18 : h 1 ≤ (1/8 : ℝ))
    (a19 : -(h 4) < (-7/64 : ℝ))
    (a21 : h 0 ≤ (2/11 : ℝ))
    (a22 : -(h 1) < (-4/33 : ℝ))
    (a24 : -(h 0) < (-3/17 : ℝ))
    (a25 : ((-2 : ℝ) * (delta)) < (-10/49 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_992 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (5/27 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/27 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_993 h delta _ctx _hno a21 f1
  by_cases p2 : h 1 ≤ (4/27 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/27 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_994 h delta _ctx _hno a18 f2
  by_cases p3 : h 2 ≤ (1/9 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_995 h delta _ctx _hno a19 a22 a24 a25 f3
  apply _hno 79
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (5/27 : ℝ)) ∧ (h 1 ≤ (4/27 : ℝ)) ∧ (h 2 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_988 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a15 : -(h 0) < (-1/6 : ℝ))
    (a18 : h 1 ≤ (1/8 : ℝ))
    (a19 : -(h 4) < (-7/64 : ℝ))
    (a22 : -(h 1) < (-4/33 : ℝ))
    (a24 : h 0 ≤ (3/17 : ℝ))
    (a26 : -(h 5) < (-2/19 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_1010 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (4/23 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/23 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_1011 h delta _ctx _hno a13 a18 a19 a22 a24 a26 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_1012 h delta _ctx _hno a18 f2
  by_cases p3 : h 4 ≤ (9/80 : ℝ)
  swap
  · have f3 : -(h 4) < (-9/80 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_1013 h delta _ctx _hno a13 a15 a22 a26 p1 f3
  by_cases p4 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_1014 h delta _ctx _hno a13 a15 a22 f4
  apply _hno 137
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (4/23 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (9/80 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_987 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a18 : h 1 ≤ (1/8 : ℝ))
    (a25 : -(h 1) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a18 + (1 : ℝ) * a25
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_986 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a18 : h 1 ≤ (1/8 : ℝ))
    (a19 : -(h 4) < (-7/64 : ℝ))
    (a21 : h 0 ≤ (2/11 : ℝ))
    (a22 : -(h 1) < (-4/33 : ℝ))
    (a24 : -(h 0) < (-3/17 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (10/49 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-10/49 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_989 h delta _ctx _hno a18 a19 a21 a22 a24 f0
  by_cases p1 : h 0 ≤ (2/11 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/11 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_990 h delta _ctx _hno a13 a19 a22 f1
  by_cases p2 : h 1 ≤ (5/41 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/41 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_991 h delta _ctx _hno a13 a18 a19 a21 a24 p0 f2
  apply _hno 65
  change (((2 : ℝ) * (delta)) ≤ (10/49 : ℝ)) ∧ (h 0 ≤ (2/11 : ℝ)) ∧ (h 1 ≤ (5/41 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem new_node_985 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a23
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_984 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a19 : -(h 4) < (-7/64 : ℝ))
    (a21 : -(h 0) < (-2/11 : ℝ))
    (a24 : -(h 1) < (-2/17 : ℝ))
    (a28 : -(h 2) < (-1/9 : ℝ))
    (a32 : -(h 3) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a19 + (1/6 : ℝ) * a21 + (1/6 : ℝ) * a24 + (1/6 : ℝ) * a28 + (1/6 : ℝ) * a32 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_983 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a18 : h 1 ≤ (1/8 : ℝ))
    (a31 : -(h 1) < (-7/54 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a18 + (1 : ℝ) * a31
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_982 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a19 : -(h 4) < (-7/64 : ℝ))
    (a24 : -(h 1) < (-2/17 : ℝ))
    (a28 : -(h 2) < (-1/9 : ℝ))
    (a30 : -(h 0) < (-5/27 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/3 : ℝ) * a19 + (1/6 : ℝ) * a24 + (1/6 : ℝ) * a28 + (1/6 : ℝ) * a30 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_981 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a29 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a29
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_980 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a18 : h 1 ≤ (1/8 : ℝ))
    (a19 : -(h 4) < (-7/64 : ℝ))
    (a21 : -(h 0) < (-2/11 : ℝ))
    (a24 : -(h 1) < (-2/17 : ℝ))
    (a28 : -(h 2) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_981 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (5/27 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/27 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_982 h delta _ctx _hno a13 a19 a24 a28 f1
  by_cases p2 : h 1 ≤ (7/54 : ℝ)
  swap
  · have f2 : -(h 1) < (-7/54 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_983 h delta _ctx _hno a18 f2
  by_cases p3 : h 3 ≤ (1/9 : ℝ)
  swap
  · have f3 : -(h 3) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_984 h delta _ctx _hno a13 a19 a21 a24 a28 f3
  apply _hno 78
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (5/27 : ℝ)) ∧ (h 1 ≤ (7/54 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_979 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a18 : h 1 ≤ (1/8 : ℝ))
    (a27 : -(h 1) < (-4/27 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a18 + (1 : ℝ) * a27
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_978 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a19 : -(h 4) < (-7/64 : ℝ))
    (a24 : -(h 1) < (-2/17 : ℝ))
    (a26 : -(h 0) < (-5/27 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order2 + (1/3 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/2 : ℝ) * a19 + (1/6 : ℝ) * a24 + (1/6 : ℝ) * a26 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_977 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a25
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_976 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a18 : h 1 ≤ (1/8 : ℝ))
    (a19 : -(h 4) < (-7/64 : ℝ))
    (a21 : -(h 0) < (-2/11 : ℝ))
    (a24 : -(h 1) < (-2/17 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_977 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (5/27 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/27 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_978 h delta _ctx _hno a13 a19 a24 f1
  by_cases p2 : h 1 ≤ (4/27 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/27 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_979 h delta _ctx _hno a18 f2
  by_cases p3 : h 2 ≤ (1/9 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_980 h delta _ctx _hno a13 a18 a19 a21 a24 f3
  apply _hno 79
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (5/27 : ℝ)) ∧ (h 1 ≤ (4/27 : ℝ)) ∧ (h 2 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_975 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : h 0 ≤ (3/16 : ℝ))
    (a23 : -(h 0) < (-4/21 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a23
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_974 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a22 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a22
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_973 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a15 : -(h 0) < (-1/6 : ℝ))
    (a19 : -(h 4) < (-7/64 : ℝ))
    (a22 : h 1 ≤ (4/33 : ℝ))
    (a23 : -(h 2) < (-3/25 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_1049 h delta _ctx _hno a15 a19 a23 f0
  by_cases p1 : h 0 ≤ (3/17 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/17 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_1050 h delta _ctx _hno a13 a19 a23 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_1051 h delta _ctx _hno a22 f2
  by_cases p3 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f3 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_1052 h delta _ctx _hno a15 a19 a22 a23 p1 f3
  apply _hno 86
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (3/17 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_972 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a15 : -(h 0) < (-1/6 : ℝ))
    (a18 : h 1 ≤ (1/8 : ℝ))
    (a19 : -(h 4) < (-7/64 : ℝ))
    (a21 : h 0 ≤ (2/11 : ℝ))
    (a22 : -(h 1) < (-4/33 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_985 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (3/17 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/17 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_986 h delta _ctx _hno a13 a18 a19 a21 a22 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_987 h delta _ctx _hno a18 f2
  by_cases p3 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f3 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_988 h delta _ctx _hno a13 a15 a18 a19 a22 p1 f3
  apply _hno 86
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (3/17 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_971 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a17 : h 0 ≤ (3/16 : ℝ))
    (a18 : h 1 ≤ (1/8 : ℝ))
    (a19 : -(h 4) < (-7/64 : ℝ))
    (a21 : -(h 0) < (-2/11 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_974 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (4/21 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/21 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_975 h delta _ctx _hno a17 f1
  by_cases p2 : h 1 ≤ (2/17 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_976 h delta _ctx _hno a13 a18 a19 a21 f2
  apply _hno 43
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (4/21 : ℝ)) ∧ (h 1 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem new_node_970 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a20 : ((-2 : ℝ) * (delta)) < (-7/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a20
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_969 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a15 : -(h 0) < (-1/6 : ℝ))
    (a18 : -(h 1) < (-1/8 : ℝ))
    (a27 : -(h 3) < (-1/9 : ℝ))
    (a37 : -(h 5) < (-2/19 : ℝ))
    (a45 : -(h 2) < (-2/17 : ℝ))
    (a51 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/13 : ℝ) * a13 + (2/13 : ℝ) * a15 + (2/13 : ℝ) * a18 + (2/13 : ℝ) * a27 + (2/13 : ℝ) * a37 + (2/13 : ℝ) * a45 + (2/13 : ℝ) * a51 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_968 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a15 : -(h 0) < (-1/6 : ℝ))
    (a18 : -(h 1) < (-1/8 : ℝ))
    (a37 : -(h 5) < (-2/19 : ℝ))
    (a45 : -(h 2) < (-2/17 : ℝ))
    (a50 : -(h 3) < (-9/80 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order4 + (1/13 : ℝ) * a13 + (2/13 : ℝ) * a15 + (2/13 : ℝ) * a18 + (4/13 : ℝ) * a37 + (2/13 : ℝ) * a45 + (2/13 : ℝ) * a50 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_967 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a35 : h 2 ≤ (1/8 : ℝ))
    (a49 : -(h 2) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a35 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_966 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : h 1 ≤ (6/47 : ℝ))
    (a48 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_965 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a18 : -(h 1) < (-1/8 : ℝ))
    (a27 : -(h 3) < (-1/9 : ℝ))
    (a37 : -(h 5) < (-2/19 : ℝ))
    (a45 : -(h 2) < (-2/17 : ℝ))
    (a47 : -(h 0) < (-12/71 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order4 + (1/13 : ℝ) * a13 + (2/13 : ℝ) * a18 + (2/13 : ℝ) * a27 + (4/13 : ℝ) * a37 + (2/13 : ℝ) * a45 + (2/13 : ℝ) * a47 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_964 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a42 : ((2 : ℝ) * (delta)) ≤ (7/34 : ℝ))
    (a46 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a42 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_963 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : -(h 0) < (-1/6 : ℝ))
    (a18 : -(h 1) < (-1/8 : ℝ))
    (a27 : -(h 3) < (-1/9 : ℝ))
    (a41 : -(h 2) < (-4/35 : ℝ))
    (a42 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a49 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order4 + (2/13 : ℝ) * a15 + (2/13 : ℝ) * a18 + (2/13 : ℝ) * a27 + (2/13 : ℝ) * a41 + (1/13 : ℝ) * a42 + (4/13 : ℝ) * a49 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_962 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : -(h 0) < (-1/6 : ℝ))
    (a18 : -(h 1) < (-1/8 : ℝ))
    (a37 : -(h 5) < (-2/19 : ℝ))
    (a41 : -(h 2) < (-4/35 : ℝ))
    (a42 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a48 : -(h 4) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order3 + (2/13 : ℝ) * a15 + (2/13 : ℝ) * a18 + (2/13 : ℝ) * a37 + (2/13 : ℝ) * a41 + (1/13 : ℝ) * a42 + (4/13 : ℝ) * a48 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_961 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : -(h 0) < (-1/6 : ℝ))
    (a18 : -(h 1) < (-1/8 : ℝ))
    (a37 : -(h 5) < (-2/19 : ℝ))
    (a42 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a47 : -(h 3) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order2 + (2/13 : ℝ) * _ctx.order4 + (2/13 : ℝ) * a15 + (2/13 : ℝ) * a18 + (4/13 : ℝ) * a37 + (1/13 : ℝ) * a42 + (4/13 : ℝ) * a47 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_960 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : -(h 0) < (-1/6 : ℝ))
    (a18 : -(h 1) < (-1/8 : ℝ))
    (a27 : -(h 3) < (-1/9 : ℝ))
    (a37 : -(h 5) < (-2/19 : ℝ))
    (a42 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a46 : -(h 2) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order4 + (2/13 : ℝ) * a15 + (2/13 : ℝ) * a18 + (2/13 : ℝ) * a27 + (4/13 : ℝ) * a37 + (1/13 : ℝ) * a42 + (2/13 : ℝ) * a46 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_959 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : h 1 ≤ (6/47 : ℝ))
    (a45 : -(h 1) < (-5/37 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_958 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a33 : h 0 ≤ (8/47 : ℝ))
    (a44 : -(h 0) < (-4/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_957 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a28 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a28 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_956 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a15 : -(h 0) < (-1/6 : ℝ))
    (a18 : -(h 1) < (-1/8 : ℝ))
    (a37 : -(h 5) < (-2/19 : ℝ))
    (a41 : -(h 2) < (-4/35 : ℝ))
    (a47 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order3 + (1/13 : ℝ) * a13 + (2/13 : ℝ) * a15 + (2/13 : ℝ) * a18 + (2/13 : ℝ) * a37 + (2/13 : ℝ) * a41 + (4/13 : ℝ) * a47 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_955 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a15 : -(h 0) < (-1/6 : ℝ))
    (a18 : -(h 1) < (-1/8 : ℝ))
    (a37 : -(h 5) < (-2/19 : ℝ))
    (a46 : -(h 3) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order2 + (2/13 : ℝ) * _ctx.order4 + (1/13 : ℝ) * a13 + (2/13 : ℝ) * a15 + (2/13 : ℝ) * a18 + (4/13 : ℝ) * a37 + (4/13 : ℝ) * a46 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

end RealPinwheel.WeakSevenBandData
