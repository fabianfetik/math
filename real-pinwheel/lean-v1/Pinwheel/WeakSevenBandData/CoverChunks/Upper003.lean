import Pinwheel.WeakSevenBandData.CoverChunks.Upper002

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem upper_node_4067 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a29 : h 0 ≤ (4/23 : ℝ))
    (a30 : h 1 ≤ (1/8 : ℝ))
    (a31 : -(h 4) < (-9/80 : ℝ))
    (a32 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a35 : -(h 0) < (-3/19 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/13 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4068 h delta _ctx _hno a32 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4069 h delta _ctx _hno a27 a29 a30 a31 a32 f1
  by_cases p2 : h 1 ≤ (5/42 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/42 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4088 h delta _ctx _hno a13 a27 a30 a31 a32 a35 f2
  apply _hno 34
  change (((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (5/42 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem upper_node_4066 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a32 + (1 : ℝ) * a34
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4065 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a29 : h 0 ≤ (4/23 : ℝ))
    (a30 : h 1 ≤ (1/8 : ℝ))
    (a31 : -(h 4) < (-9/80 : ℝ))
    (a32 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a33 : -(h 0) < (-2/13 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4066 h delta _ctx _hno a32 f0
  by_cases p1 : h 0 ≤ (3/19 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/19 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4067 h delta _ctx _hno a13 a27 a29 a30 a31 a32 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4109 h delta _ctx _hno a13 a27 f2
  by_cases p3 : h 4 ≤ (13/112 : ℝ)
  swap
  · have f3 : -(h 4) < (-13/112 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_4110 h delta _ctx _hno a27 a32 a33 p1 f3
  apply _hno 4
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (13/112 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_4064 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a32 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a40 : -(h 1) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * a13 + (1/2 : ℝ) * a32 + (1/2 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4063 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a34 : h 0 ≤ (1/6 : ℝ))
    (a39 : -(h 0) < (-5/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4062 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a28 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ))
    (a38 : ((-2 : ℝ) * (delta)) < (-3/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a28 + (1 : ℝ) * a38
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4061 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a28 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ))
    (a32 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a34 : h 0 ≤ (1/6 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/13 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4062 h delta _ctx _hno a28 f0
  by_cases p1 : h 0 ≤ (5/26 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/26 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4063 h delta _ctx _hno a34 f1
  by_cases p2 : h 1 ≤ (3/26 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4064 h delta _ctx _hno a13 a32 f2
  apply _hno 1
  change (((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)) ∧ (h 0 ≤ (5/26 : ℝ)) ∧ (h 1 ≤ (3/26 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem upper_node_4060 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : ((3 : ℝ) * (h 2)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a32 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a40 : -(h 4) < (-13/112 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/2 : ℝ) * _ctx.order2 + (1/2 : ℝ) * _ctx.order3 + (1/6 : ℝ) * a14 + (1/2 : ℝ) * a32 + (1/2 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4059 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a32 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a39 : -(h 1) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * a13 + (1/2 : ℝ) * a32 + (1/2 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4058 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a32 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a41 : -(h 1) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * a13 + (1/2 : ℝ) * a32 + (1/2 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4057 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a34 : h 0 ≤ (1/6 : ℝ))
    (a40 : -(h 0) < (-5/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4056 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a28 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ))
    (a39 : ((-2 : ℝ) * (delta)) < (-3/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a28 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4055 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a28 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ))
    (a32 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a34 : h 0 ≤ (1/6 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/13 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4056 h delta _ctx _hno a28 f0
  by_cases p1 : h 0 ≤ (5/26 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/26 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4057 h delta _ctx _hno a34 f1
  by_cases p2 : h 1 ≤ (3/26 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4058 h delta _ctx _hno a13 a32 f2
  apply _hno 1
  change (((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)) ∧ (h 0 ≤ (5/26 : ℝ)) ∧ (h 1 ≤ (3/26 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem upper_node_4054 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a22 : ((3 : ℝ) * (h 3)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a36 : -(h 4) < (-5/44 : ℝ))
    (a37 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/2 : ℝ) * _ctx.order3 + (1/6 : ℝ) * a22 + (1/2 : ℝ) * a36 + (1/2 : ℝ) * a37
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4053 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a14 : ((3 : ℝ) * (h 2)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a22 : ((3 : ℝ) * (h 3)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a28 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ))
    (a32 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a34 : h 0 ≤ (1/6 : ℝ))
    (a36 : -(h 4) < (-5/44 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4054 h delta _ctx _hno a22 a36 f0
  by_cases p1 : h 0 ≤ (3/19 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/19 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4055 h delta _ctx _hno a13 a28 a32 a34
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4059 h delta _ctx _hno a13 a32 f2
  by_cases p3 : h 4 ≤ (13/112 : ℝ)
  swap
  · have f3 : -(h 4) < (-13/112 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_4060 h delta _ctx _hno a14 a32 f3
  apply _hno 4
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (13/112 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_4052 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a32 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a35 : -(h 1) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * a13 + (1/2 : ℝ) * a32 + (1/2 : ℝ) * a35
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4051 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : -(h 4) < (-9/80 : ℝ))
    (a32 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a34 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order1 + (1/3 : ℝ) * _ctx.order2 + (1/2 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (2/3 : ℝ) * a31 + (1/6 : ℝ) * a32 + (1/6 : ℝ) * a34 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4050 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a28 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ))
    (a33 : ((-2 : ℝ) * (delta)) < (-5/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a28 + (1 : ℝ) * a33
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4049 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a14 : ((3 : ℝ) * (h 2)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a22 : ((3 : ℝ) * (h 3)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a28 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ))
    (a31 : -(h 4) < (-9/80 : ℝ))
    (a32 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/22 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/22 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4050 h delta _ctx _hno a28 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4051 h delta _ctx _hno a31 a32 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4052 h delta _ctx _hno a13 a32 f2
  by_cases p3 : h 4 ≤ (5/44 : ℝ)
  swap
  · have f3 : -(h 4) < (-5/44 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_4053 h delta _ctx _hno a13 a14 a22 a28 a32 p1 f3
  by_cases p4 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_4061 h delta _ctx _hno a13 a28 a32 p1
  apply _hno 58
  change (((2 : ℝ) * (delta)) ≤ (5/22 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (5/44 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_4048 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a14 : ((3 : ℝ) * (h 2)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a22 : ((3 : ℝ) * (h 3)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a28 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ))
    (a29 : h 0 ≤ (4/23 : ℝ))
    (a30 : h 1 ≤ (1/8 : ℝ))
    (a31 : -(h 4) < (-9/80 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4049 h delta _ctx _hno a13 a14 a22 a28 a31 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4065 h delta _ctx _hno a13 a27 a29 a30 a31 p0 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4114 h delta _ctx _hno a13 a27 f2
  apply _hno 2
  change (((2 : ℝ) * (delta)) ≤ (7/32 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem upper_node_4047 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a30 : -(h 1) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * a13 + (1/2 : ℝ) * a27 + (1/2 : ℝ) * a30
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4046 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a26 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 4)) < (-1 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a29 : -(h 0) < (-4/23 : ℝ))
    (a35 : -(h 1) + ((-8 : ℝ) * (h 5)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (18/37 : ℝ) * _ctx.order2 + (36/37 : ℝ) * _ctx.order3 + (30/37 : ℝ) * _ctx.order4 + (4/37 : ℝ) * a26 + (9/37 : ℝ) * a27 + (18/37 : ℝ) * a29 + (6/37 : ℝ) * a35 + (18/37 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4045 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : h 1 + ((8 : ℝ) * (h 3)) ≤ (1 : ℝ))
    (a34 : -(h 1) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (8 : ℝ) * _ctx.order3 + (1 : ℝ) * a33 + (1 : ℝ) * a34
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4044 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : h 1 + ((8 : ℝ) * (h 2)) ≤ (1 : ℝ))
    (a33 : -(h 1) + ((-8 : ℝ) * (h 3)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (8 : ℝ) * _ctx.order2 + (1 : ℝ) * a32 + (1 : ℝ) * a33
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4043 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a34 : h 0 ≤ (8/45 : ℝ))
    (a47 : ((-2 : ℝ) * (h 0)) + ((-5 : ℝ) * (h 5)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * _ctx.order1 + (2 : ℝ) * _ctx.order2 + (3 : ℝ) * _ctx.order3 + (4 : ℝ) * _ctx.order4 + (1 : ℝ) * _ctx.lower + (1 : ℝ) * a34 + (1 : ℝ) * a47 + (1 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4042 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a34 : h 0 ≤ (8/45 : ℝ))
    (a46 : ((-2 : ℝ) * (h 0)) + ((-5 : ℝ) * (h 4)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (5/4 : ℝ) * _ctx.order1 + (5/2 : ℝ) * _ctx.order2 + (15/4 : ℝ) * _ctx.order3 + (5/4 : ℝ) * _ctx.min + (5/2 : ℝ) * _ctx.lower + (3/4 : ℝ) * a34 + (1 : ℝ) * a46 + (5/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4041 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a34 : h 0 ≤ (8/45 : ℝ))
    (a45 : ((-2 : ℝ) * (h 0)) + ((-5 : ℝ) * (h 3)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (5/3 : ℝ) * _ctx.order1 + (10/3 : ℝ) * _ctx.order2 + (5/3 : ℝ) * _ctx.order4 + (10/3 : ℝ) * _ctx.min + (5 : ℝ) * _ctx.lower + (1/3 : ℝ) * a34 + (1 : ℝ) * a45 + (5/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4040 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a34 : h 0 ≤ (8/45 : ℝ))
    (a39 : ((5 : ℝ) * (h 2)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a44 : ((-2 : ℝ) * (h 0)) + ((-5 : ℝ) * (h 2)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4 : ℝ) * _ctx.lower + (2 : ℝ) * a34 + (1 : ℝ) * a39 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4039 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a34 : h 0 ≤ (8/45 : ℝ))
    (a38 : ((5 : ℝ) * (h 1)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a43 : ((-2 : ℝ) * (h 0)) + ((-5 : ℝ) * (h 1)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4 : ℝ) * _ctx.lower + (2 : ℝ) * a34 + (1 : ℝ) * a38 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4038 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : -(h 0) < (-4/23 : ℝ))
    (a33 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a42 : ((-5 : ℝ) * (h 5)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/2 : ℝ) * _ctx.order1 + (1 : ℝ) * _ctx.order2 + (3/2 : ℝ) * _ctx.order3 + (2 : ℝ) * _ctx.order4 + (1/2 : ℝ) * a29 + (3/4 : ℝ) * a33 + (1/2 : ℝ) * a42 + (1/2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4037 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : -(h 0) < (-4/23 : ℝ))
    (a33 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a41 : ((-5 : ℝ) * (h 4)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (5/9 : ℝ) * _ctx.order1 + (10/9 : ℝ) * _ctx.order2 + (5/3 : ℝ) * _ctx.order3 + (5/9 : ℝ) * _ctx.min + (5/9 : ℝ) * a29 + (1/3 : ℝ) * a33 + (4/9 : ℝ) * a41 + (5/9 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4036 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a26 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 4)) < (-1 : ℝ))
    (a29 : -(h 0) < (-4/23 : ℝ))
    (a40 : ((-5 : ℝ) * (h 3)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/10 : ℝ) * _ctx.order1 + (9/10 : ℝ) * _ctx.order2 + (3/5 : ℝ) * _ctx.min + (1/10 : ℝ) * a26 + (3/5 : ℝ) * a29 + (3/10 : ℝ) * a40 + (3/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4035 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a26 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 4)) < (-1 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a29 : -(h 0) < (-4/23 : ℝ))
    (a37 : -(h 3) < (-1/9 : ℝ))
    (a39 : ((-5 : ℝ) * (h 2)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (15/86 : ℝ) * _ctx.order1 + (15/43 : ℝ) * _ctx.min + (5/86 : ℝ) * a26 + (6/43 : ℝ) * a27 + (15/43 : ℝ) * a29 + (15/43 : ℝ) * a37 + (9/86 : ℝ) * a39 + (15/43 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4034 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a29 : -(h 0) < (-4/23 : ℝ))
    (a32 : -(h 1) + ((-8 : ℝ) * (h 2)) < (-1 : ℝ))
    (a37 : -(h 3) < (-1/9 : ℝ))
    (a38 : ((-5 : ℝ) * (h 1)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ))
    (a46 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (20/89 : ℝ) * _ctx.order4 + (3/89 : ℝ) * a27 + (20/89 : ℝ) * a29 + (5/178 : ℝ) * a32 + (20/89 : ℝ) * a37 + (7/178 : ℝ) * a38 + (40/89 : ℝ) * a46 + (20/89 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4033 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a26 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 4)) < (-1 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a29 : -(h 0) < (-4/23 : ℝ))
    (a37 : -(h 3) < (-1/9 : ℝ))
    (a38 : ((-5 : ℝ) * (h 1)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ))
    (a45 : -(h 2) < (-5/44 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (15/61 : ℝ) * _ctx.min + (5/122 : ℝ) * a26 + (12/61 : ℝ) * a27 + (15/61 : ℝ) * a29 + (15/61 : ℝ) * a37 + (3/122 : ℝ) * a38 + (15/61 : ℝ) * a45 + (15/61 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4032 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a44 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.lower + (1/3 : ℝ) * a13 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4031 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a26 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 4)) < (-1 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a37 : -(h 3) < (-1/9 : ℝ))
    (a38 : ((-5 : ℝ) * (h 1)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ))
    (a43 : -(h 0) < (-3/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (15/61 : ℝ) * _ctx.order2 + (15/61 : ℝ) * _ctx.min + (5/122 : ℝ) * a26 + (12/61 : ℝ) * a27 + (30/61 : ℝ) * a37 + (3/122 : ℝ) * a38 + (15/61 : ℝ) * a43 + (15/61 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4030 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a42 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4029 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a26 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 4)) < (-1 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a29 : -(h 0) < (-4/23 : ℝ))
    (a32 : -(h 1) + ((-8 : ℝ) * (h 2)) < (-1 : ℝ))
    (a33 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a37 : -(h 3) < (-1/9 : ℝ))
    (a38 : ((-5 : ℝ) * (h 1)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4030 h delta _ctx _hno a33 f0
  by_cases p1 : h 0 ≤ (3/17 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/17 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4031 h delta _ctx _hno a26 a27 a37 a38 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4032 h delta _ctx _hno a13 f2
  by_cases p3 : h 2 ≤ (5/44 : ℝ)
  swap
  · have f3 : -(h 2) < (-5/44 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_4033 h delta _ctx _hno a26 a27 a29 a37 a38 f3
  by_cases p4 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_4034 h delta _ctx _hno a27 a29 a32 a37 a38 f4
  apply _hno 76
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/17 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (5/44 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_4028 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a34 : h 0 ≤ (8/45 : ℝ))
    (a40 : -(h 0) < (-5/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4027 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a39 : ((-2 : ℝ) * (delta)) < (-3/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4026 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a26 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 4)) < (-1 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a29 : -(h 0) < (-4/23 : ℝ))
    (a32 : -(h 1) + ((-8 : ℝ) * (h 2)) < (-1 : ℝ))
    (a33 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a34 : h 0 ≤ (8/45 : ℝ))
    (a37 : -(h 3) < (-1/9 : ℝ))
    (a38 : ((-5 : ℝ) * (h 1)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/13 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4027 h delta _ctx _hno a33 f0
  by_cases p1 : h 0 ≤ (5/26 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/26 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4028 h delta _ctx _hno a34 f1
  by_cases p2 : h 1 ≤ (3/26 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4029 h delta _ctx _hno a13 a26 a27 a29 a32 a33 a37 a38
  apply _hno 1
  change (((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)) ∧ (h 0 ≤ (5/26 : ℝ)) ∧ (h 1 ≤ (3/26 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem upper_node_4025 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a26 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 4)) < (-1 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a29 : -(h 0) < (-4/23 : ℝ))
    (a32 : -(h 1) + ((-8 : ℝ) * (h 2)) < (-1 : ℝ))
    (a33 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a34 : h 0 ≤ (8/45 : ℝ))
    (a37 : -(h 3) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((5 : ℝ) * (h 1)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ)
  swap
  · have f0 : ((-5 : ℝ) * (h 1)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4026 h delta _ctx _hno a13 a26 a27 a29 a32 a33 a34 a37 f0
  by_cases p1 : ((5 : ℝ) * (h 2)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ)
  swap
  · have f1 : ((-5 : ℝ) * (h 2)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4035 h delta _ctx _hno a26 a27 a29 a37 f1
  by_cases p2 : ((5 : ℝ) * (h 3)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ)
  swap
  · have f2 : ((-5 : ℝ) * (h 3)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4036 h delta _ctx _hno a26 a29 f2
  by_cases p3 : ((5 : ℝ) * (h 4)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ)
  swap
  · have f3 : ((-5 : ℝ) * (h 4)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_4037 h delta _ctx _hno a29 a33 f3
  by_cases p4 : ((5 : ℝ) * (h 5)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ)
  swap
  · have f4 : ((-5 : ℝ) * (h 5)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_4038 h delta _ctx _hno a29 a33 f4
  by_cases p5 : ((2 : ℝ) * (h 0)) + ((5 : ℝ) * (h 1)) ≤ (1 : ℝ)
  swap
  · have f5 : ((-2 : ℝ) * (h 0)) + ((-5 : ℝ) * (h 1)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_4039 h delta _ctx _hno a34 p0 f5
  by_cases p6 : ((2 : ℝ) * (h 0)) + ((5 : ℝ) * (h 2)) ≤ (1 : ℝ)
  swap
  · have f6 : ((-2 : ℝ) * (h 0)) + ((-5 : ℝ) * (h 2)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact upper_node_4040 h delta _ctx _hno a34 p1 f6
  by_cases p7 : ((2 : ℝ) * (h 0)) + ((5 : ℝ) * (h 3)) ≤ (1 : ℝ)
  swap
  · have f7 : ((-2 : ℝ) * (h 0)) + ((-5 : ℝ) * (h 3)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p7
      linarith only [hp]
    exact upper_node_4041 h delta _ctx _hno a34 f7
  by_cases p8 : ((2 : ℝ) * (h 0)) + ((5 : ℝ) * (h 4)) ≤ (1 : ℝ)
  swap
  · have f8 : ((-2 : ℝ) * (h 0)) + ((-5 : ℝ) * (h 4)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p8
      linarith only [hp]
    exact upper_node_4042 h delta _ctx _hno a34 f8
  by_cases p9 : ((2 : ℝ) * (h 0)) + ((5 : ℝ) * (h 5)) ≤ (1 : ℝ)
  swap
  · have f9 : ((-2 : ℝ) * (h 0)) + ((-5 : ℝ) * (h 5)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p9
      linarith only [hp]
    exact upper_node_4043 h delta _ctx _hno a34 f9
  apply _hno 152
  change (((5 : ℝ) * (h 1)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ)) ∧ (((5 : ℝ) * (h 2)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ)) ∧ (((5 : ℝ) * (h 3)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ)) ∧ (((5 : ℝ) * (h 4)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ)) ∧ (((5 : ℝ) * (h 5)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ)) ∧ (((2 : ℝ) * (h 0)) + ((5 : ℝ) * (h 1)) ≤ (1 : ℝ)) ∧ (((2 : ℝ) * (h 0)) + ((5 : ℝ) * (h 2)) ≤ (1 : ℝ)) ∧ (((2 : ℝ) * (h 0)) + ((5 : ℝ) * (h 3)) ≤ (1 : ℝ)) ∧ (((2 : ℝ) * (h 0)) + ((5 : ℝ) * (h 4)) ≤ (1 : ℝ)) ∧ (((2 : ℝ) * (h 0)) + ((5 : ℝ) * (h 5)) ≤ (1 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9⟩

theorem upper_node_4024 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : -(h 0) < (-4/23 : ℝ))
    (a36 : -(h 2) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order1 + (1/3 : ℝ) * _ctx.order3 + (2/3 : ℝ) * _ctx.order4 + (1 : ℝ) * _ctx.min + (4/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * a29 + (2/3 : ℝ) * a36 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4023 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a35 : -(h 1) < (-5/38 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.lower + (1/3 : ℝ) * a13 + (1 : ℝ) * a35
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4022 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 3)) < (-1 : ℝ))
    (a26 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 4)) < (-1 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a32 : -(h 1) + ((-8 : ℝ) * (h 2)) < (-1 : ℝ))
    (a34 : -(h 0) < (-8/45 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/61 : ℝ) * _ctx.order4 + (30/61 : ℝ) * _ctx.min + (4/61 : ℝ) * a19 + (3/61 : ℝ) * a26 + (27/61 : ℝ) * a27 + (3/61 : ℝ) * a32 + (24/61 : ℝ) * a34 + (24/61 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4021 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 3)) < (-1 : ℝ))
    (a26 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 4)) < (-1 : ℝ))
    (a29 : -(h 0) < (-4/23 : ℝ))
    (a32 : -(h 1) + ((-8 : ℝ) * (h 2)) < (-1 : ℝ))
    (a33 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a42 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/38 : ℝ) * _ctx.order4 + (1/19 : ℝ) * a19 + (3/76 : ℝ) * a26 + (6/19 : ℝ) * a29 + (3/76 : ℝ) * a32 + (3/19 : ℝ) * a33 + (15/38 : ℝ) * a42 + (6/19 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4020 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 3)) < (-1 : ℝ))
    (a26 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 4)) < (-1 : ℝ))
    (a29 : -(h 0) < (-4/23 : ℝ))
    (a33 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a41 : -(h 2) < (-5/44 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/10 : ℝ) * _ctx.min + (1/20 : ℝ) * a19 + (1/20 : ℝ) * a26 + (3/10 : ℝ) * a29 + (3/10 : ℝ) * a33 + (3/10 : ℝ) * a41 + (3/10 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4019 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a40 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.lower + (1/3 : ℝ) * a13 + (1 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4018 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 3)) < (-1 : ℝ))
    (a26 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 4)) < (-1 : ℝ))
    (a33 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a37 : -(h 2) < (-1/9 : ℝ))
    (a39 : -(h 0) < (-3/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/10 : ℝ) * _ctx.min + (1/20 : ℝ) * a19 + (1/20 : ℝ) * a26 + (3/10 : ℝ) * a33 + (3/10 : ℝ) * a37 + (3/10 : ℝ) * a39 + (3/10 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4017 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a34 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ))
    (a38 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a38
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4016 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a19 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 3)) < (-1 : ℝ))
    (a26 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 4)) < (-1 : ℝ))
    (a29 : -(h 0) < (-4/23 : ℝ))
    (a32 : -(h 1) + ((-8 : ℝ) * (h 2)) < (-1 : ℝ))
    (a33 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a34 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ))
    (a37 : -(h 2) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4017 h delta _ctx _hno a34 f0
  by_cases p1 : h 0 ≤ (3/17 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/17 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4018 h delta _ctx _hno a19 a26 a33 a37 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4019 h delta _ctx _hno a13 f2
  by_cases p3 : h 2 ≤ (5/44 : ℝ)
  swap
  · have f3 : -(h 2) < (-5/44 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_4020 h delta _ctx _hno a19 a26 a29 a33 f3
  by_cases p4 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_4021 h delta _ctx _hno a19 a26 a29 a32 a33 f4
  apply _hno 76
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/17 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (5/44 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_4015 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a36 : -(h 1) < (-5/36 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.lower + (1/3 : ℝ) * a13 + (1 : ℝ) * a36
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4014 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 3)) < (-1 : ℝ))
    (a26 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 4)) < (-1 : ℝ))
    (a32 : -(h 1) + ((-8 : ℝ) * (h 2)) < (-1 : ℝ))
    (a33 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a35 : -(h 0) < (-3/16 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/61 : ℝ) * _ctx.order4 + (30/61 : ℝ) * _ctx.min + (4/61 : ℝ) * a19 + (3/61 : ℝ) * a26 + (3/61 : ℝ) * a32 + (27/61 : ℝ) * a33 + (24/61 : ℝ) * a35 + (24/61 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4013 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 3)) < (-1 : ℝ))
    (a26 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 4)) < (-1 : ℝ))
    (a29 : -(h 0) < (-4/23 : ℝ))
    (a32 : -(h 1) + ((-8 : ℝ) * (h 2)) < (-1 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/61 : ℝ) * _ctx.order4 + (30/61 : ℝ) * _ctx.min + (4/61 : ℝ) * a19 + (3/61 : ℝ) * a26 + (24/61 : ℝ) * a29 + (3/61 : ℝ) * a32 + (27/61 : ℝ) * a34 + (24/61 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4012 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a19 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 3)) < (-1 : ℝ))
    (a26 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 4)) < (-1 : ℝ))
    (a29 : -(h 0) < (-4/23 : ℝ))
    (a32 : -(h 1) + ((-8 : ℝ) * (h 2)) < (-1 : ℝ))
    (a33 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4013 h delta _ctx _hno a19 a26 a29 a32 f0
  by_cases p1 : h 0 ≤ (3/16 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/16 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4014 h delta _ctx _hno a19 a26 a32 a33 f1
  by_cases p2 : h 1 ≤ (5/36 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/36 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4015 h delta _ctx _hno a13 f2
  by_cases p3 : h 2 ≤ (1/9 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_4016 h delta _ctx _hno a13 a19 a26 a29 a32 a33 p0 f3
  apply _hno 61
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (3/16 : ℝ)) ∧ (h 1 ≤ (5/36 : ℝ)) ∧ (h 2 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_4011 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a19 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 3)) < (-1 : ℝ))
    (a26 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 4)) < (-1 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a29 : -(h 0) < (-4/23 : ℝ))
    (a32 : -(h 1) + ((-8 : ℝ) * (h 2)) < (-1 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4012 h delta _ctx _hno a13 a19 a26 a29 a32 f0
  by_cases p1 : h 0 ≤ (8/45 : ℝ)
  swap
  · have f1 : -(h 0) < (-8/45 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4022 h delta _ctx _hno a19 a26 a27 a32 f1
  by_cases p2 : h 1 ≤ (5/38 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/38 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4023 h delta _ctx _hno a13 f2
  by_cases p3 : h 2 ≤ (3/23 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_4024 h delta _ctx _hno a29 f3
  by_cases p4 : h 3 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_4025 h delta _ctx _hno a13 a26 a27 a29 a32 p0 p1 f4
  apply _hno 13
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (8/45 : ℝ)) ∧ (h 1 ≤ (5/38 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_4010 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 3)) < (-1 : ℝ))
    (a31 : ((-4 : ℝ) * (h 0)) + -(h 1) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.order2 + (1 : ℝ) * _ctx.order3 + (3 : ℝ) * _ctx.order4 + (5 : ℝ) * _ctx.min + (7 : ℝ) * _ctx.lower + (1/2 : ℝ) * a19 + (1/2 : ℝ) * a31 + (2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4009 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a26 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 4)) < (-1 : ℝ))
    (a29 : -(h 0) < (-4/23 : ℝ))
    (a30 : -(h 1) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/5 : ℝ) * _ctx.order2 + (6/5 : ℝ) * _ctx.order3 + (6/5 : ℝ) * _ctx.order4 + (9/5 : ℝ) * _ctx.min + (1/10 : ℝ) * a26 + (3/5 : ℝ) * a29 + (3/10 : ℝ) * a30 + (3/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4008 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a19 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 3)) < (-1 : ℝ))
    (a26 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 4)) < (-1 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a29 : -(h 0) < (-4/23 : ℝ))
    : False := by
  by_cases p0 : h 1 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ)
  swap
  · have f0 : -(h 1) + ((-8 : ℝ) * (delta)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4009 h delta _ctx _hno a26 a29 f0
  by_cases p1 : ((4 : ℝ) * (h 0)) + h 1 ≤ (1 : ℝ)
  swap
  · have f1 : ((-4 : ℝ) * (h 0)) + -(h 1) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4010 h delta _ctx _hno a19 f1
  by_cases p2 : h 1 + ((8 : ℝ) * (h 2)) ≤ (1 : ℝ)
  swap
  · have f2 : -(h 1) + ((-8 : ℝ) * (h 2)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4011 h delta _ctx _hno a13 a19 a26 a27 a29 f2
  by_cases p3 : h 1 + ((8 : ℝ) * (h 3)) ≤ (1 : ℝ)
  swap
  · have f3 : -(h 1) + ((-8 : ℝ) * (h 3)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_4044 h delta _ctx _hno p2 f3
  by_cases p4 : h 1 + ((8 : ℝ) * (h 4)) ≤ (1 : ℝ)
  swap
  · have f4 : -(h 1) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_4045 h delta _ctx _hno p3 f4
  by_cases p5 : h 1 + ((8 : ℝ) * (h 5)) ≤ (1 : ℝ)
  swap
  · have f5 : -(h 1) + ((-8 : ℝ) * (h 5)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_4046 h delta _ctx _hno a26 a27 a29 f5
  apply _hno 50
  change (h 1 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ)) ∧ (((4 : ℝ) * (h 0)) + h 1 ≤ (1 : ℝ)) ∧ (h 1 + ((8 : ℝ) * (h 2)) ≤ (1 : ℝ)) ∧ (h 1 + ((8 : ℝ) * (h 3)) ≤ (1 : ℝ)) ∧ (h 1 + ((8 : ℝ) * (h 4)) ≤ (1 : ℝ)) ∧ (h 1 + ((8 : ℝ) * (h 5)) ≤ (1 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_4007 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : ((3 : ℝ) * (h 2)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a26 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 4)) < (-1 : ℝ))
    (a28 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.order3 + (6/23 : ℝ) * _ctx.min + (3/23 : ℝ) * _ctx.fail1 + (4/23 : ℝ) * a14 + (2/23 : ℝ) * a26 + (18/23 : ℝ) * a28 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4006 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a14 : ((3 : ℝ) * (h 2)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a15 : ((3 : ℝ) * (h 5)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a19 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 3)) < (-1 : ℝ))
    (a22 : ((3 : ℝ) * (h 3)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a26 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 4)) < (-1 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4007 h delta _ctx _hno a14 a26 f0
  by_cases p1 : h 0 ≤ (4/23 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/23 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4008 h delta _ctx _hno a13 a19 a26 a27 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4047 h delta _ctx _hno a13 a27 f2
  by_cases p3 : h 4 ≤ (9/80 : ℝ)
  swap
  · have f3 : -(h 4) < (-9/80 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_4048 h delta _ctx _hno a13 a14 a22 a27 p0 p1 p2 f3
  by_cases p4 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_4115 h delta _ctx _hno a13 a15 a27 p0 p1 p3 f4
  apply _hno 52
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (4/23 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (9/80 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_4005 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a14 : ((3 : ℝ) * (h 2)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a15 : ((3 : ℝ) * (h 5)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a19 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 3)) < (-1 : ℝ))
    (a22 : ((3 : ℝ) * (h 3)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a26 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 4)) < (-1 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4006 h delta _ctx _hno a13 a14 a15 a19 a22 a26 f0
  by_cases p1 : h 0 ≤ (4/25 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/25 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4148 h delta _ctx _hno a13 a14 a19 a26 p0 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4297 h delta _ctx _hno a13 f2
  apply _hno 83
  change (((2 : ℝ) * (delta)) ≤ (10/47 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem upper_node_4004 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 3)) < (-1 : ℝ))
    (a25 : ((-3 : ℝ) * (h 0)) + ((-3 : ℝ) * (h 3)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (15/16 : ℝ) * _ctx.order1 + (33/16 : ℝ) * _ctx.order2 + (9/8 : ℝ) * _ctx.order4 + (9/4 : ℝ) * _ctx.min + (27/16 : ℝ) * _ctx.markR + (1/16 : ℝ) * a19 + (15/16 : ℝ) * a25 + (9/8 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4003 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 3)) < (-1 : ℝ))
    (a24 : ((-3 : ℝ) * (h 0)) + ((-3 : ℝ) * (h 2)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/4 : ℝ) * _ctx.order1 + (3/2 : ℝ) * _ctx.order4 + (3 : ℝ) * _ctx.min + (3 : ℝ) * _ctx.lower + (3/4 : ℝ) * _ctx.markR + (1/4 : ℝ) * a19 + (3/4 : ℝ) * a24 + (3/2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4002 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-3 : ℝ) * (h 0)) + ((-3 : ℝ) * (h 1)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3 : ℝ) * _ctx.order2 + (6 : ℝ) * _ctx.order3 + (9 : ℝ) * _ctx.order4 + (12 : ℝ) * _ctx.min + (15 : ℝ) * _ctx.lower + (1 : ℝ) * a23 + (3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4001 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : ((3 : ℝ) * (h 2)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a22 : ((-3 : ℝ) * (h 3)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3 : ℝ) * _ctx.order2 + (1 : ℝ) * a14 + (1 : ℝ) * a22
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4000 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : ((3 : ℝ) * (h 2)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a21 : ((-3 : ℝ) * (h 2)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a14 + (1 : ℝ) * a21
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3999 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a20 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a20
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3998 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a14 : ((3 : ℝ) * (h 2)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a15 : ((3 : ℝ) * (h 5)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a19 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 3)) < (-1 : ℝ))
    : False := by
  by_cases p0 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ)
  swap
  · have f0 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3999 h delta _ctx _hno a13 f0
  by_cases p1 : ((3 : ℝ) * (h 2)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ)
  swap
  · have f1 : ((-3 : ℝ) * (h 2)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4000 h delta _ctx _hno a14 f1
  by_cases p2 : ((3 : ℝ) * (h 3)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ)
  swap
  · have f2 : ((-3 : ℝ) * (h 3)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4001 h delta _ctx _hno a14 f2
  by_cases p3 : ((3 : ℝ) * (h 0)) + ((3 : ℝ) * (h 1)) ≤ (1 : ℝ)
  swap
  · have f3 : ((-3 : ℝ) * (h 0)) + ((-3 : ℝ) * (h 1)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_4002 h delta _ctx _hno f3
  by_cases p4 : ((3 : ℝ) * (h 0)) + ((3 : ℝ) * (h 2)) ≤ (1 : ℝ)
  swap
  · have f4 : ((-3 : ℝ) * (h 0)) + ((-3 : ℝ) * (h 2)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_4003 h delta _ctx _hno a19 f4
  by_cases p5 : ((3 : ℝ) * (h 0)) + ((3 : ℝ) * (h 3)) ≤ (1 : ℝ)
  swap
  · have f5 : ((-3 : ℝ) * (h 0)) + ((-3 : ℝ) * (h 3)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_4004 h delta _ctx _hno a19 f5
  by_cases p6 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (h 4)) ≤ (1 : ℝ)
  swap
  · have f6 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 4)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact upper_node_4005 h delta _ctx _hno a13 a14 a15 a19 p2 f6
  by_cases p7 : ((3 : ℝ) * (h 2)) + ((6 : ℝ) * (h 4)) ≤ (1 : ℝ)
  swap
  · have f7 : ((-3 : ℝ) * (h 2)) + ((-6 : ℝ) * (h 4)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p7
      linarith only [hp]
    exact upper_node_4298 h delta _ctx _hno p6 f7
  by_cases p8 : ((3 : ℝ) * (h 3)) + ((6 : ℝ) * (h 4)) ≤ (1 : ℝ)
  swap
  · have f8 : ((-3 : ℝ) * (h 3)) + ((-6 : ℝ) * (h 4)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p8
      linarith only [hp]
    exact upper_node_4299 h delta _ctx _hno p7 f8
  by_cases p9 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (h 5)) ≤ (1 : ℝ)
  swap
  · have f9 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 5)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p9
      linarith only [hp]
    exact upper_node_4300 h delta _ctx _hno p6 f9
  by_cases p10 : ((3 : ℝ) * (h 2)) + ((6 : ℝ) * (h 5)) ≤ (1 : ℝ)
  swap
  · have f10 : ((-3 : ℝ) * (h 2)) + ((-6 : ℝ) * (h 5)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p10
      linarith only [hp]
    exact upper_node_4301 h delta _ctx _hno p7 f10
  by_cases p11 : ((3 : ℝ) * (h 3)) + ((6 : ℝ) * (h 5)) ≤ (1 : ℝ)
  swap
  · have f11 : ((-3 : ℝ) * (h 3)) + ((-6 : ℝ) * (h 5)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p11
      linarith only [hp]
    exact upper_node_4302 h delta _ctx _hno p7 f11
  apply _hno 151
  change (((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ)) ∧ (((3 : ℝ) * (h 2)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ)) ∧ (((3 : ℝ) * (h 3)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ)) ∧ (((3 : ℝ) * (h 0)) + ((3 : ℝ) * (h 1)) ≤ (1 : ℝ)) ∧ (((3 : ℝ) * (h 0)) + ((3 : ℝ) * (h 2)) ≤ (1 : ℝ)) ∧ (((3 : ℝ) * (h 0)) + ((3 : ℝ) * (h 3)) ≤ (1 : ℝ)) ∧ (((3 : ℝ) * (h 1)) + ((6 : ℝ) * (h 4)) ≤ (1 : ℝ)) ∧ (((3 : ℝ) * (h 2)) + ((6 : ℝ) * (h 4)) ≤ (1 : ℝ)) ∧ (((3 : ℝ) * (h 3)) + ((6 : ℝ) * (h 4)) ≤ (1 : ℝ)) ∧ (((3 : ℝ) * (h 1)) + ((6 : ℝ) * (h 5)) ≤ (1 : ℝ)) ∧ (((3 : ℝ) * (h 2)) + ((6 : ℝ) * (h 5)) ≤ (1 : ℝ)) ∧ (((3 : ℝ) * (h 3)) + ((6 : ℝ) * (h 5)) ≤ (1 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11⟩

theorem upper_node_3997 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : ((-3 : ℝ) * (h 0)) + ((-3 : ℝ) * (h 5)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (9/8 : ℝ) * _ctx.order1 + (9/4 : ℝ) * _ctx.order2 + (27/8 : ℝ) * _ctx.order3 + (9/2 : ℝ) * _ctx.order4 + (21/8 : ℝ) * _ctx.min + (15/8 : ℝ) * _ctx.markR + (1 : ℝ) * a18 + (9/8 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3996 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : ((-3 : ℝ) * (h 0)) + ((-3 : ℝ) * (h 2)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/2 : ℝ) * _ctx.order1 + (3/2 : ℝ) * _ctx.order3 + (3 : ℝ) * _ctx.order4 + (9/2 : ℝ) * _ctx.min + (3 : ℝ) * _ctx.lower + (3/2 : ℝ) * _ctx.markR + (1 : ℝ) * a17 + (3/2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3995 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a16 : ((-3 : ℝ) * (h 0)) + ((-3 : ℝ) * (h 1)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3 : ℝ) * _ctx.order2 + (6 : ℝ) * _ctx.order3 + (9 : ℝ) * _ctx.order4 + (12 : ℝ) * _ctx.min + (15 : ℝ) * _ctx.lower + (1 : ℝ) * a16 + (3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3994 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : ((3 : ℝ) * (h 2)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a15 : ((-3 : ℝ) * (h 5)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/7 : ℝ) * _ctx.order1 + (6/7 : ℝ) * _ctx.order3 + (12/7 : ℝ) * _ctx.order4 + (6/7 : ℝ) * _ctx.min + (3/7 : ℝ) * _ctx.fail1 + (2/7 : ℝ) * a14 + (4/7 : ℝ) * a15 + (6/7 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3993 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a14 : ((-3 : ℝ) * (h 2)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3 : ℝ) * _ctx.order1 + (1 : ℝ) * a13 + (1 : ℝ) * a14
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3992 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : h 0 + ((8 : ℝ) * (h 4)) ≤ (1 : ℝ))
    (a19 : -(h 0) + ((-8 : ℝ) * (h 5)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (8 : ℝ) * _ctx.order4 + (1 : ℝ) * a18 + (1 : ℝ) * a19
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3991 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((8 : ℝ) * (h 3)) + h 5 ≤ (1 : ℝ))
    (a24 : ((-8 : ℝ) * (h 4)) + -(h 5) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (8 : ℝ) * _ctx.order3 + (1 : ℝ) * a23 + (1 : ℝ) * a24
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3990 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a28 : h 3 + ((8 : ℝ) * (h 4)) ≤ (1 : ℝ))
    (a29 : -(h 3) + ((-8 : ℝ) * (h 5)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (8 : ℝ) * _ctx.order4 + (1 : ℝ) * a28 + (1 : ℝ) * a29
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3989 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : h 2 ≤ (1/8 : ℝ))
    (a39 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3988 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a38 : -(h 1) < (-7/51 : ℝ))
    (a42 : -(h 4) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/23 : ℝ) * _ctx.order0 + (6/23 : ℝ) * _ctx.order3 + (6/23 : ℝ) * _ctx.min + (12/23 : ℝ) * _ctx.lower + (1/23 : ℝ) * _ctx.fail1 + (10/23 : ℝ) * a38 + (12/23 : ℝ) * a42 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

end RealPinwheel.WeakSevenBandData
