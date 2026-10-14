import Pinwheel.WeakSevenBandData.CoverChunks.New051

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem new_node_8954 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a66 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a66
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8953 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : -(h 0) < (-1/6 : ℝ))
    (a41 : -(h 2) < (-2/17 : ℝ))
    (a55 : -(h 3) < (-4/35 : ℝ))
    (a58 : -(h 1) < (-508/3957 : ℝ))
    (a64 : -(h 4) < (-2/19 : ℝ))
    (a71 : -(h 5) < (-2/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a19 + (1/6 : ℝ) * a41 + (1/6 : ℝ) * a55 + (1/6 : ℝ) * a58 + (1/6 : ℝ) * a64 + (1/6 : ℝ) * a71 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8952 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : -(h 0) < (-1/6 : ℝ))
    (a41 : -(h 2) < (-2/17 : ℝ))
    (a55 : -(h 3) < (-4/35 : ℝ))
    (a58 : -(h 1) < (-508/3957 : ℝ))
    (a70 : -(h 4) < (-3/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a19 + (1/5 : ℝ) * a41 + (1/5 : ℝ) * a55 + (1/5 : ℝ) * a58 + (1/5 : ℝ) * a70 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8951 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : -(h 0) < (-1/6 : ℝ))
    (a41 : -(h 2) < (-2/17 : ℝ))
    (a58 : -(h 1) < (-508/3957 : ℝ))
    (a64 : -(h 4) < (-2/19 : ℝ))
    (a69 : -(h 3) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a19 + (1/5 : ℝ) * a41 + (1/5 : ℝ) * a58 + (1/5 : ℝ) * a64 + (1/5 : ℝ) * a69 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8950 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a62 : h 2 ≤ (3/25 : ℝ))
    (a68 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a62 + (1 : ℝ) * a68
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8949 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : -(h 0) < (-1/6 : ℝ))
    (a41 : -(h 2) < (-2/17 : ℝ))
    (a55 : -(h 3) < (-4/35 : ℝ))
    (a64 : -(h 4) < (-2/19 : ℝ))
    (a67 : -(h 1) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a19 + (1/5 : ℝ) * a41 + (1/5 : ℝ) * a55 + (1/5 : ℝ) * a64 + (1/5 : ℝ) * a67 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8948 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a47 : h 0 ≤ (12/71 : ℝ))
    (a66 : -(h 0) < (-7/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a47 + (1 : ℝ) * a66
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8947 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a65 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a65
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8946 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : -(h 0) < (-1/6 : ℝ))
    (a55 : -(h 3) < (-4/35 : ℝ))
    (a58 : -(h 1) < (-508/3957 : ℝ))
    (a62 : -(h 2) < (-3/25 : ℝ))
    (a69 : -(h 5) < (-2/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order4 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a19 + (1/6 : ℝ) * a55 + (1/6 : ℝ) * a58 + (1/6 : ℝ) * a62 + (1/3 : ℝ) * a69 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8945 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : -(h 0) < (-1/6 : ℝ))
    (a55 : -(h 3) < (-4/35 : ℝ))
    (a58 : -(h 1) < (-508/3957 : ℝ))
    (a62 : -(h 2) < (-3/25 : ℝ))
    (a68 : -(h 4) < (-3/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a19 + (1/5 : ℝ) * a55 + (1/5 : ℝ) * a58 + (1/5 : ℝ) * a62 + (1/5 : ℝ) * a68 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8944 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : -(h 0) < (-1/6 : ℝ))
    (a45 : -(h 4) < (-3/29 : ℝ))
    (a58 : -(h 1) < (-508/3957 : ℝ))
    (a62 : -(h 2) < (-3/25 : ℝ))
    (a67 : -(h 3) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a19 + (1/5 : ℝ) * a45 + (1/5 : ℝ) * a58 + (1/5 : ℝ) * a62 + (1/5 : ℝ) * a67 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8943 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : -(h 0) < (-1/6 : ℝ))
    (a45 : -(h 4) < (-3/29 : ℝ))
    (a55 : -(h 3) < (-4/35 : ℝ))
    (a58 : -(h 1) < (-508/3957 : ℝ))
    (a66 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a19 + (1/5 : ℝ) * a45 + (1/5 : ℝ) * a55 + (1/5 : ℝ) * a58 + (1/5 : ℝ) * a66 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8942 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : -(h 0) < (-1/6 : ℝ))
    (a45 : -(h 4) < (-3/29 : ℝ))
    (a55 : -(h 3) < (-4/35 : ℝ))
    (a62 : -(h 2) < (-3/25 : ℝ))
    (a65 : -(h 1) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a19 + (1/5 : ℝ) * a45 + (1/5 : ℝ) * a55 + (1/5 : ℝ) * a62 + (1/5 : ℝ) * a65 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8941 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a47 : h 0 ≤ (12/71 : ℝ))
    (a64 : -(h 0) < (-7/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a47 + (1 : ℝ) * a64
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8940 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a63 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a63
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8939 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a19 : -(h 0) < (-1/6 : ℝ))
    (a41 : -(h 2) < (-2/17 : ℝ))
    (a45 : -(h 4) < (-3/29 : ℝ))
    (a47 : h 0 ≤ (12/71 : ℝ))
    (a55 : -(h 3) < (-4/35 : ℝ))
    (a58 : -(h 1) < (-508/3957 : ℝ))
    (a62 : h 2 ≤ (3/25 : ℝ))
    (a64 : h 4 ≤ (2/19 : ℝ))
    (a65 : -(h 5) < (-4/39 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_8954 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (4/23 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/23 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_8955 h delta _ctx _hno a47 f1
  by_cases p2 : h 1 ≤ (14/109 : ℝ)
  swap
  · have f2 : -(h 1) < (-14/109 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_8956 h delta _ctx _hno a13 a19 a41 a45 a47 a55 a62 a64 a65 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_8957 h delta _ctx _hno a62 f3
  by_cases p4 : h 4 ≤ (2/19 : ℝ)
  swap
  · have f4 : -(h 4) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_8958 h delta _ctx _hno a19 a41 a55 a58 a65 f4
  apply _hno 169
  change (((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)) ∧ (h 0 ≤ (4/23 : ℝ)) ∧ (h 1 ≤ (14/109 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_8938 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a19 : -(h 0) < (-1/6 : ℝ))
    (a41 : -(h 2) < (-2/17 : ℝ))
    (a47 : h 0 ≤ (12/71 : ℝ))
    (a55 : -(h 3) < (-4/35 : ℝ))
    (a58 : -(h 1) < (-508/3957 : ℝ))
    (a62 : h 2 ≤ (3/25 : ℝ))
    (a64 : -(h 4) < (-2/19 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_8947 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (7/41 : ℝ)
  swap
  · have f1 : -(h 0) < (-7/41 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_8948 h delta _ctx _hno a47 f1
  by_cases p2 : h 1 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_8949 h delta _ctx _hno a19 a41 a55 a64 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_8950 h delta _ctx _hno a62 f3
  by_cases p4 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_8951 h delta _ctx _hno a19 a41 a58 a64 f4
  by_cases p5 : h 4 ≤ (3/28 : ℝ)
  swap
  · have f5 : -(h 4) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_8952 h delta _ctx _hno a19 a41 a55 a58 f5
  by_cases p6 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f6 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact new_node_8953 h delta _ctx _hno a19 a41 a55 a58 a64 f6
  apply _hno 180
  change (((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)) ∧ (h 0 ≤ (7/41 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 4 ≤ (3/28 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem new_node_8937 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : -(h 0) < (-1/6 : ℝ))
    (a41 : -(h 2) < (-2/17 : ℝ))
    (a45 : -(h 4) < (-3/29 : ℝ))
    (a58 : -(h 1) < (-508/3957 : ℝ))
    (a63 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a19 + (1/5 : ℝ) * a41 + (1/5 : ℝ) * a45 + (1/5 : ℝ) * a58 + (1/5 : ℝ) * a63 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8936 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a19 : -(h 0) < (-1/6 : ℝ))
    (a45 : -(h 4) < (-3/29 : ℝ))
    (a47 : h 0 ≤ (12/71 : ℝ))
    (a55 : -(h 3) < (-4/35 : ℝ))
    (a58 : -(h 1) < (-508/3957 : ℝ))
    (a62 : -(h 2) < (-3/25 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_8940 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (7/41 : ℝ)
  swap
  · have f1 : -(h 0) < (-7/41 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_8941 h delta _ctx _hno a47 f1
  by_cases p2 : h 1 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_8942 h delta _ctx _hno a19 a45 a55 a62 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_8943 h delta _ctx _hno a19 a45 a55 a58 f3
  by_cases p4 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_8944 h delta _ctx _hno a19 a45 a58 a62 f4
  by_cases p5 : h 4 ≤ (3/28 : ℝ)
  swap
  · have f5 : -(h 4) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_8945 h delta _ctx _hno a19 a55 a58 a62 f5
  by_cases p6 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f6 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact new_node_8946 h delta _ctx _hno a19 a55 a58 a62 f6
  apply _hno 180
  change (((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)) ∧ (h 0 ≤ (7/41 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 4 ≤ (3/28 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem new_node_8935 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : -(h 0) < (-1/6 : ℝ))
    (a41 : -(h 2) < (-2/17 : ℝ))
    (a45 : -(h 4) < (-3/29 : ℝ))
    (a55 : -(h 3) < (-4/35 : ℝ))
    (a61 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a19 + (1/5 : ℝ) * a41 + (1/5 : ℝ) * a45 + (1/5 : ℝ) * a55 + (1/5 : ℝ) * a61 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8934 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a47 : h 0 ≤ (12/71 : ℝ))
    (a60 : -(h 0) < (-3/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a47 + (1 : ℝ) * a60
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8933 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a59 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a59
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8932 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : -(h 0) < (-1/6 : ℝ))
    (a37 : -(h 1) < (-6/47 : ℝ))
    (a41 : -(h 2) < (-2/17 : ℝ))
    (a55 : -(h 3) < (-4/35 : ℝ))
    (a61 : -(h 5) < (-2/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order4 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a19 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a41 + (1/6 : ℝ) * a55 + (1/3 : ℝ) * a61 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8931 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : -(h 0) < (-1/6 : ℝ))
    (a37 : -(h 1) < (-6/47 : ℝ))
    (a41 : -(h 2) < (-2/17 : ℝ))
    (a55 : -(h 3) < (-4/35 : ℝ))
    (a60 : -(h 4) < (-3/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a19 + (1/5 : ℝ) * a37 + (1/5 : ℝ) * a41 + (1/5 : ℝ) * a55 + (1/5 : ℝ) * a60 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8930 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : -(h 0) < (-1/6 : ℝ))
    (a37 : -(h 1) < (-6/47 : ℝ))
    (a45 : -(h 4) < (-3/29 : ℝ))
    (a55 : -(h 3) < (-4/35 : ℝ))
    (a59 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a19 + (1/5 : ℝ) * a37 + (1/5 : ℝ) * a45 + (1/5 : ℝ) * a55 + (1/5 : ℝ) * a59 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8929 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a19 : -(h 0) < (-1/6 : ℝ))
    (a41 : -(h 2) < (-2/17 : ℝ))
    (a45 : -(h 4) < (-3/29 : ℝ))
    (a47 : h 0 ≤ (12/71 : ℝ))
    (a55 : -(h 3) < (-4/35 : ℝ))
    (a58 : -(h 1) < (-508/3957 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_8933 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (3/17 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/17 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_8934 h delta _ctx _hno a47 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_8935 h delta _ctx _hno a19 a41 a45 a55 f2
  by_cases p3 : h 2 ≤ (3/25 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_8936 h delta _ctx _hno a13 a19 a45 a47 a55 a58 f3
  by_cases p4 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_8937 h delta _ctx _hno a19 a41 a45 a58 f4
  by_cases p5 : h 4 ≤ (2/19 : ℝ)
  swap
  · have f5 : -(h 4) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_8938 h delta _ctx _hno a13 a19 a41 a47 a55 a58 p3 f5
  by_cases p6 : h 5 ≤ (4/39 : ℝ)
  swap
  · have f6 : -(h 5) < (-4/39 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact new_node_8939 h delta _ctx _hno a13 a19 a41 a45 a47 a55 a58 p3 p5 f6
  apply _hno 165
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (3/17 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (2/19 : ℝ)) ∧ (h 5 ≤ (4/39 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem new_node_8928 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a47 : h 0 ≤ (12/71 : ℝ))
    (a57 : -(h 0) < (-6/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a47 + (1 : ℝ) * a57
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8927 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a56 : ((-2 : ℝ) * (delta)) < (-15/73 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a56
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8926 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a19 : -(h 0) < (-1/6 : ℝ))
    (a37 : -(h 1) < (-6/47 : ℝ))
    (a41 : -(h 2) < (-2/17 : ℝ))
    (a45 : -(h 4) < (-3/29 : ℝ))
    (a47 : h 0 ≤ (12/71 : ℝ))
    (a50 : -(h 3) < (-9/80 : ℝ))
    (a55 : h 3 ≤ (4/35 : ℝ))
    (a56 : -(h 5) < (-3/29 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_8966 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (8/47 : ℝ)
  swap
  · have f1 : -(h 0) < (-8/47 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_8967 h delta _ctx _hno a47 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_8968 h delta _ctx _hno a19 a41 a45 a50 a56 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_8969 h delta _ctx _hno a19 a37 a45 a50 a56 f3
  by_cases p4 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_8970 h delta _ctx _hno a55 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_8971 h delta _ctx _hno a19 a37 a41 a50 a56 f5
  apply _hno 71
  change (((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)) ∧ (h 0 ≤ (8/47 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_8925 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a19 : -(h 0) < (-1/6 : ℝ))
    (a37 : -(h 1) < (-6/47 : ℝ))
    (a41 : -(h 2) < (-2/17 : ℝ))
    (a45 : -(h 4) < (-3/29 : ℝ))
    (a47 : h 0 ≤ (12/71 : ℝ))
    (a55 : -(h 3) < (-4/35 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (15/73 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-15/73 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_8927 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (6/35 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/35 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_8928 h delta _ctx _hno a47 f1
  by_cases p2 : h 1 ≤ (508/3957 : ℝ)
  swap
  · have f2 : -(h 1) < (-508/3957 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_8929 h delta _ctx _hno a13 a19 a41 a45 a47 a55 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_8930 h delta _ctx _hno a19 a37 a45 a55 f3
  by_cases p4 : h 4 ≤ (3/28 : ℝ)
  swap
  · have f4 : -(h 4) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_8931 h delta _ctx _hno a19 a37 a41 a55 f4
  by_cases p5 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_8932 h delta _ctx _hno a19 a37 a41 a55 f5
  apply _hno 217
  change (((2 : ℝ) * (delta)) ≤ (15/73 : ℝ)) ∧ (h 0 ≤ (6/35 : ℝ)) ∧ (h 1 ≤ (508/3957 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (3/28 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_8924 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : -(h 0) < (-1/6 : ℝ))
    (a37 : -(h 1) < (-6/47 : ℝ))
    (a45 : -(h 4) < (-3/29 : ℝ))
    (a50 : -(h 3) < (-9/80 : ℝ))
    (a54 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a19 + (1/5 : ℝ) * a37 + (1/5 : ℝ) * a45 + (1/5 : ℝ) * a50 + (1/5 : ℝ) * a54 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8923 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a48 : h 1 ≤ (2/15 : ℝ))
    (a53 : -(h 1) < (-4/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a48 + (1 : ℝ) * a53
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8922 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a47 : h 0 ≤ (12/71 : ℝ))
    (a52 : -(h 0) < (-5/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a47 + (1 : ℝ) * a52
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8921 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a51 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a51
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8920 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : -(h 0) < (-1/6 : ℝ))
    (a30 : -(h 3) < (-1/9 : ℝ))
    (a41 : -(h 2) < (-2/17 : ℝ))
    (a45 : -(h 4) < (-3/29 : ℝ))
    (a48 : -(h 1) < (-2/15 : ℝ))
    (a54 : -(h 5) < (-3/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a19 + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a41 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a48 + (1/6 : ℝ) * a54 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8919 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : -(h 0) < (-1/6 : ℝ))
    (a41 : -(h 2) < (-2/17 : ℝ))
    (a45 : -(h 4) < (-3/29 : ℝ))
    (a48 : -(h 1) < (-2/15 : ℝ))
    (a53 : -(h 3) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a19 + (1/5 : ℝ) * a41 + (1/5 : ℝ) * a45 + (1/5 : ℝ) * a48 + (1/5 : ℝ) * a53 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8918 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : -(h 0) < (-1/6 : ℝ))
    (a30 : -(h 3) < (-1/9 : ℝ))
    (a45 : -(h 4) < (-3/29 : ℝ))
    (a48 : -(h 1) < (-2/15 : ℝ))
    (a52 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a19 + (1/5 : ℝ) * a30 + (1/5 : ℝ) * a45 + (1/5 : ℝ) * a48 + (1/5 : ℝ) * a52 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8917 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : h 1 ≤ (8/59 : ℝ))
    (a51 : -(h 1) < (-4/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a15 + (1 : ℝ) * a51
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8916 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a47 : h 0 ≤ (12/71 : ℝ))
    (a50 : -(h 0) < (-5/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a47 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8915 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a49 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8914 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a37 : -(h 1) < (-6/47 : ℝ))
    (a41 : -(h 2) < (-2/17 : ℝ))
    (a47 : -(h 0) < (-12/71 : ℝ))
    (a53 : -(h 5) < (-3/29 : ℝ))
    (a59 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a41 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * a53 + (1/3 : ℝ) * a59 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8913 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a37 : -(h 1) < (-6/47 : ℝ))
    (a41 : -(h 2) < (-2/17 : ℝ))
    (a45 : -(h 4) < (-3/29 : ℝ))
    (a47 : -(h 0) < (-12/71 : ℝ))
    (a53 : -(h 5) < (-3/29 : ℝ))
    (a58 : -(h 3) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a41 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * a53 + (1/6 : ℝ) * a58 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8912 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a30 : -(h 3) < (-1/9 : ℝ))
    (a37 : -(h 1) < (-6/47 : ℝ))
    (a45 : -(h 4) < (-3/29 : ℝ))
    (a47 : -(h 0) < (-12/71 : ℝ))
    (a53 : -(h 5) < (-3/29 : ℝ))
    (a57 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * a53 + (1/6 : ℝ) * a57 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8911 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a30 : -(h 3) < (-1/9 : ℝ))
    (a41 : -(h 2) < (-2/17 : ℝ))
    (a45 : -(h 4) < (-3/29 : ℝ))
    (a47 : -(h 0) < (-12/71 : ℝ))
    (a53 : -(h 5) < (-3/29 : ℝ))
    (a56 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a41 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * a53 + (1/6 : ℝ) * a56 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8910 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a30 : -(h 3) < (-1/9 : ℝ))
    (a37 : -(h 1) < (-6/47 : ℝ))
    (a41 : -(h 2) < (-2/17 : ℝ))
    (a45 : -(h 4) < (-3/29 : ℝ))
    (a53 : -(h 5) < (-3/29 : ℝ))
    (a55 : -(h 0) < (-8/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a41 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a53 + (1/6 : ℝ) * a55 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8909 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a54 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a54
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8908 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a41 : -(h 2) < (-2/17 : ℝ))
    (a45 : -(h 4) < (-3/29 : ℝ))
    (a47 : -(h 0) < (-12/71 : ℝ))
    (a52 : -(h 3) < (-4/35 : ℝ))
    (a55 : -(h 1) < (-508/3957 : ℝ))
    (a62 : -(h 5) < (-4/39 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a41 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * a52 + (1/6 : ℝ) * a55 + (1/6 : ℝ) * a62 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8907 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a41 : -(h 2) < (-2/17 : ℝ))
    (a47 : -(h 0) < (-12/71 : ℝ))
    (a52 : -(h 3) < (-4/35 : ℝ))
    (a55 : -(h 1) < (-508/3957 : ℝ))
    (a61 : -(h 4) < (-2/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a41 + (1/5 : ℝ) * a47 + (1/5 : ℝ) * a52 + (1/5 : ℝ) * a55 + (1/5 : ℝ) * a61 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8906 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a41 : -(h 2) < (-2/17 : ℝ))
    (a45 : -(h 4) < (-3/29 : ℝ))
    (a47 : -(h 0) < (-12/71 : ℝ))
    (a55 : -(h 1) < (-508/3957 : ℝ))
    (a60 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a41 + (1/5 : ℝ) * a45 + (1/5 : ℝ) * a47 + (1/5 : ℝ) * a55 + (1/5 : ℝ) * a60 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8905 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a45 : -(h 4) < (-3/29 : ℝ))
    (a47 : -(h 0) < (-12/71 : ℝ))
    (a52 : -(h 3) < (-4/35 : ℝ))
    (a55 : -(h 1) < (-508/3957 : ℝ))
    (a59 : -(h 2) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a45 + (1/5 : ℝ) * a47 + (1/5 : ℝ) * a52 + (1/5 : ℝ) * a55 + (1/5 : ℝ) * a59 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8904 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a41 : -(h 2) < (-2/17 : ℝ))
    (a45 : -(h 4) < (-3/29 : ℝ))
    (a47 : -(h 0) < (-12/71 : ℝ))
    (a52 : -(h 3) < (-4/35 : ℝ))
    (a58 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a41 + (1/5 : ℝ) * a45 + (1/5 : ℝ) * a47 + (1/5 : ℝ) * a52 + (1/5 : ℝ) * a58 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8903 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a36 : h 0 ≤ (8/47 : ℝ))
    (a57 : -(h 0) < (-3/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a36 + (1 : ℝ) * a57
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8902 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a56 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a56
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8901 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a37 : -(h 1) < (-6/47 : ℝ))
    (a41 : -(h 2) < (-2/17 : ℝ))
    (a47 : -(h 0) < (-12/71 : ℝ))
    (a52 : -(h 3) < (-4/35 : ℝ))
    (a58 : -(h 5) < (-2/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order4 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a41 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * a52 + (1/3 : ℝ) * a58 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8900 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a37 : -(h 1) < (-6/47 : ℝ))
    (a41 : -(h 2) < (-2/17 : ℝ))
    (a47 : -(h 0) < (-12/71 : ℝ))
    (a52 : -(h 3) < (-4/35 : ℝ))
    (a57 : -(h 4) < (-3/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a37 + (1/5 : ℝ) * a41 + (1/5 : ℝ) * a47 + (1/5 : ℝ) * a52 + (1/5 : ℝ) * a57 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8899 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a37 : -(h 1) < (-6/47 : ℝ))
    (a45 : -(h 4) < (-3/29 : ℝ))
    (a47 : -(h 0) < (-12/71 : ℝ))
    (a52 : -(h 3) < (-4/35 : ℝ))
    (a56 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a37 + (1/5 : ℝ) * a45 + (1/5 : ℝ) * a47 + (1/5 : ℝ) * a52 + (1/5 : ℝ) * a56 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8898 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a36 : h 0 ≤ (8/47 : ℝ))
    (a41 : -(h 2) < (-2/17 : ℝ))
    (a45 : -(h 4) < (-3/29 : ℝ))
    (a47 : -(h 0) < (-12/71 : ℝ))
    (a52 : -(h 3) < (-4/35 : ℝ))
    (a55 : -(h 1) < (-508/3957 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_8902 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (3/17 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/17 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_8903 h delta _ctx _hno a36 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_8904 h delta _ctx _hno a41 a45 a47 a52 f2
  by_cases p3 : h 2 ≤ (3/25 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_8905 h delta _ctx _hno a45 a47 a52 a55 f3
  by_cases p4 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_8906 h delta _ctx _hno a41 a45 a47 a55 f4
  by_cases p5 : h 4 ≤ (2/19 : ℝ)
  swap
  · have f5 : -(h 4) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_8907 h delta _ctx _hno a41 a47 a52 a55 f5
  by_cases p6 : h 5 ≤ (4/39 : ℝ)
  swap
  · have f6 : -(h 5) < (-4/39 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact new_node_8908 h delta _ctx _hno a41 a45 a47 a52 a55 f6
  apply _hno 165
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (3/17 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (2/19 : ℝ)) ∧ (h 5 ≤ (4/39 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem new_node_8897 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a36 : h 0 ≤ (8/47 : ℝ))
    (a54 : -(h 0) < (-6/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a36 + (1 : ℝ) * a54
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8896 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a53 : ((-2 : ℝ) * (delta)) < (-15/73 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a53
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8895 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a30 : -(h 3) < (-1/9 : ℝ))
    (a37 : -(h 1) < (-6/47 : ℝ))
    (a41 : -(h 2) < (-2/17 : ℝ))
    (a45 : -(h 4) < (-3/29 : ℝ))
    (a47 : -(h 0) < (-12/71 : ℝ))
    (a53 : -(h 5) < (-3/29 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_8909 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (8/47 : ℝ)
  swap
  · have f1 : -(h 0) < (-8/47 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_8910 h delta _ctx _hno a30 a37 a41 a45 a53 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_8911 h delta _ctx _hno a30 a41 a45 a47 a53 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_8912 h delta _ctx _hno a30 a37 a45 a47 a53 f3
  by_cases p4 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_8913 h delta _ctx _hno a37 a41 a45 a47 a53 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_8914 h delta _ctx _hno a37 a41 a47 a53 f5
  apply _hno 71
  change (((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)) ∧ (h 0 ≤ (8/47 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_8894 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a36 : h 0 ≤ (8/47 : ℝ))
    (a37 : -(h 1) < (-6/47 : ℝ))
    (a41 : -(h 2) < (-2/17 : ℝ))
    (a45 : -(h 4) < (-3/29 : ℝ))
    (a47 : -(h 0) < (-12/71 : ℝ))
    (a52 : -(h 3) < (-4/35 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (15/73 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-15/73 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_8896 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (6/35 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/35 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_8897 h delta _ctx _hno a36 f1
  by_cases p2 : h 1 ≤ (508/3957 : ℝ)
  swap
  · have f2 : -(h 1) < (-508/3957 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_8898 h delta _ctx _hno a13 a36 a41 a45 a47 a52 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_8899 h delta _ctx _hno a37 a45 a47 a52 f3
  by_cases p4 : h 4 ≤ (3/28 : ℝ)
  swap
  · have f4 : -(h 4) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_8900 h delta _ctx _hno a37 a41 a47 a52 f4
  by_cases p5 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_8901 h delta _ctx _hno a37 a41 a47 a52 f5
  apply _hno 217
  change (((2 : ℝ) * (delta)) ≤ (15/73 : ℝ)) ∧ (h 0 ≤ (6/35 : ℝ)) ∧ (h 1 ≤ (508/3957 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (3/28 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_8893 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a30 : -(h 3) < (-1/9 : ℝ))
    (a37 : -(h 1) < (-6/47 : ℝ))
    (a45 : -(h 4) < (-3/29 : ℝ))
    (a47 : -(h 0) < (-12/71 : ℝ))
    (a51 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a30 + (1/5 : ℝ) * a37 + (1/5 : ℝ) * a45 + (1/5 : ℝ) * a47 + (1/5 : ℝ) * a51 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8892 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : h 1 ≤ (8/59 : ℝ))
    (a50 : -(h 1) < (-4/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a15 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8891 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a36 : h 0 ≤ (8/47 : ℝ))
    (a49 : -(h 0) < (-5/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a36 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8890 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a48 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8889 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : -(h 0) < (-1/6 : ℝ))
    (a37 : -(h 1) < (-6/47 : ℝ))
    (a41 : -(h 2) < (-2/17 : ℝ))
    (a51 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a19 + (1/5 : ℝ) * a37 + (1/5 : ℝ) * a41 + (2/5 : ℝ) * a51 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8888 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a19 : -(h 0) < (-1/6 : ℝ))
    (a37 : -(h 1) < (-6/47 : ℝ))
    (a41 : -(h 2) < (-2/17 : ℝ))
    (a45 : -(h 4) < (-3/29 : ℝ))
    (a47 : h 0 ≤ (12/71 : ℝ))
    (a48 : h 1 ≤ (2/15 : ℝ))
    (a50 : -(h 3) < (-9/80 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_8921 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (5/29 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/29 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_8922 h delta _ctx _hno a47 f1
  by_cases p2 : h 1 ≤ (4/29 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/29 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_8923 h delta _ctx _hno a48 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_8924 h delta _ctx _hno a19 a37 a45 a50 f3
  by_cases p4 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_8925 h delta _ctx _hno a13 a19 a37 a41 a45 a47 f4
  by_cases p5 : h 5 ≤ (3/29 : ℝ)
  swap
  · have f5 : -(h 5) < (-3/29 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_8926 h delta _ctx _hno a13 a19 a37 a41 a45 a47 a50 p4 f5
  apply _hno 89
  change (((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)) ∧ (h 0 ≤ (5/29 : ℝ)) ∧ (h 1 ≤ (4/29 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (3/29 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_8887 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : -(h 0) < (-1/6 : ℝ))
    (a30 : -(h 3) < (-1/9 : ℝ))
    (a45 : -(h 4) < (-3/29 : ℝ))
    (a49 : -(h 2) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order1 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a19 + (1/5 : ℝ) * a30 + (1/5 : ℝ) * a45 + (2/5 : ℝ) * a49 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8886 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a15 : h 1 ≤ (8/59 : ℝ))
    (a19 : -(h 0) < (-1/6 : ℝ))
    (a30 : -(h 3) < (-1/9 : ℝ))
    (a41 : -(h 2) < (-2/17 : ℝ))
    (a45 : -(h 4) < (-3/29 : ℝ))
    (a47 : h 0 ≤ (12/71 : ℝ))
    (a48 : -(h 1) < (-2/15 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_8915 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (5/29 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/29 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_8916 h delta _ctx _hno a47 f1
  by_cases p2 : h 1 ≤ (4/29 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/29 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_8917 h delta _ctx _hno a15 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_8918 h delta _ctx _hno a19 a30 a45 a48 f3
  by_cases p4 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_8919 h delta _ctx _hno a19 a41 a45 a48 f4
  by_cases p5 : h 5 ≤ (3/29 : ℝ)
  swap
  · have f5 : -(h 5) < (-3/29 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_8920 h delta _ctx _hno a19 a30 a41 a45 a48 f5
  apply _hno 89
  change (((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)) ∧ (h 0 ≤ (5/29 : ℝ)) ∧ (h 1 ≤ (4/29 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (3/29 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_8885 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a15 : h 1 ≤ (8/59 : ℝ))
    (a30 : -(h 3) < (-1/9 : ℝ))
    (a36 : h 0 ≤ (8/47 : ℝ))
    (a37 : -(h 1) < (-6/47 : ℝ))
    (a41 : -(h 2) < (-2/17 : ℝ))
    (a45 : -(h 4) < (-3/29 : ℝ))
    (a47 : -(h 0) < (-12/71 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_8890 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (5/29 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/29 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_8891 h delta _ctx _hno a36 f1
  by_cases p2 : h 1 ≤ (4/29 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/29 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_8892 h delta _ctx _hno a15 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_8893 h delta _ctx _hno a30 a37 a45 a47 f3
  by_cases p4 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_8894 h delta _ctx _hno a13 a36 a37 a41 a45 a47 f4
  by_cases p5 : h 5 ≤ (3/29 : ℝ)
  swap
  · have f5 : -(h 5) < (-3/29 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_8895 h delta _ctx _hno a13 a30 a37 a41 a45 a47 f5
  apply _hno 89
  change (((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)) ∧ (h 0 ≤ (5/29 : ℝ)) ∧ (h 1 ≤ (4/29 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (3/29 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_8884 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a46 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8883 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a15 : h 1 ≤ (8/59 : ℝ))
    (a19 : -(h 0) < (-1/6 : ℝ))
    (a30 : -(h 3) < (-1/9 : ℝ))
    (a36 : h 0 ≤ (8/47 : ℝ))
    (a37 : -(h 1) < (-6/47 : ℝ))
    (a41 : -(h 2) < (-2/17 : ℝ))
    (a45 : -(h 4) < (-3/29 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_8884 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (12/71 : ℝ)
  swap
  · have f1 : -(h 0) < (-12/71 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_8885 h delta _ctx _hno a13 a15 a30 a36 a37 a41 a45 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_8886 h delta _ctx _hno a13 a15 a19 a30 a41 a45 p1 f2
  by_cases p3 : h 2 ≤ (3/23 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_8887 h delta _ctx _hno a19 a30 a45 f3
  by_cases p4 : h 3 ≤ (9/80 : ℝ)
  swap
  · have f4 : -(h 3) < (-9/80 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_8888 h delta _ctx _hno a13 a19 a37 a41 a45 p1 p2 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_8889 h delta _ctx _hno a19 a37 a41 f5
  apply _hno 149
  change (((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)) ∧ (h 0 ≤ (12/71 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (9/80 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_8882 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : h 1 ≤ (8/59 : ℝ))
    (a44 : -(h 1) < (-4/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a15 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8881 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a36 : h 0 ≤ (8/47 : ℝ))
    (a43 : -(h 0) < (-5/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a36 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8880 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a42 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8879 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a19 : -(h 0) < (-1/6 : ℝ))
    (a34 : -(h 2) < (-4/35 : ℝ))
    (a36 : h 0 ≤ (8/47 : ℝ))
    (a37 : -(h 1) < (-6/47 : ℝ))
    (a43 : -(h 4) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_8986 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (4/23 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/23 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_8987 h delta _ctx _hno a36 f1
  by_cases p2 : h 1 ≤ (5/37 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/37 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_8988 h delta _ctx _hno a19 a34 a43 f2
  by_cases p3 : h 2 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_8989 h delta _ctx _hno a19 a37 a43 f3
  by_cases p4 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_8990 h delta _ctx _hno a19 a37 a43 f4
  by_cases p5 : h 4 ≤ (4/35 : ℝ)
  swap
  · have f5 : -(h 4) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_8991 h delta _ctx _hno a19 a34 a37 f5
  by_cases p6 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f6 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact new_node_8992 h delta _ctx _hno a19 a34 a37 a43 f6
  apply _hno 67
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (4/23 : ℝ)) ∧ (h 1 ≤ (5/37 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 4 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem new_node_8878 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a15 : h 1 ≤ (8/59 : ℝ))
    (a19 : -(h 0) < (-1/6 : ℝ))
    (a36 : h 0 ≤ (8/47 : ℝ))
    (a37 : -(h 1) < (-6/47 : ℝ))
    (a41 : h 2 ≤ (2/17 : ℝ))
    (a42 : -(h 3) < (-3/26 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_8972 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (5/29 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/29 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_8973 h delta _ctx _hno a36 f1
  by_cases p2 : h 1 ≤ (4/29 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/29 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_8974 h delta _ctx _hno a15 f2
  by_cases p3 : h 4 ≤ (3/29 : ℝ)
  swap
  · have f3 : -(h 4) < (-3/29 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_8975 h delta _ctx _hno a13 a15 a19 a36 a37 a41 a42
  apply _hno 7
  change (((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)) ∧ (h 0 ≤ (5/29 : ℝ)) ∧ (h 1 ≤ (4/29 : ℝ)) ∧ (h 4 ≤ (3/29 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_8877 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a15 : h 1 ≤ (8/59 : ℝ))
    (a19 : -(h 0) < (-1/6 : ℝ))
    (a30 : -(h 3) < (-1/9 : ℝ))
    (a36 : h 0 ≤ (8/47 : ℝ))
    (a37 : -(h 1) < (-6/47 : ℝ))
    (a41 : -(h 2) < (-2/17 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_8880 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (5/29 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/29 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_8881 h delta _ctx _hno a36 f1
  by_cases p2 : h 1 ≤ (4/29 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/29 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_8882 h delta _ctx _hno a15 f2
  by_cases p3 : h 4 ≤ (3/29 : ℝ)
  swap
  · have f3 : -(h 4) < (-3/29 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_8883 h delta _ctx _hno a13 a15 a19 a30 a36 a37 a41 f3
  apply _hno 7
  change (((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)) ∧ (h 0 ≤ (5/29 : ℝ)) ∧ (h 1 ≤ (4/29 : ℝ)) ∧ (h 4 ≤ (3/29 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_8876 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : h 1 ≤ (8/59 : ℝ))
    (a40 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a15 + (1 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_8875 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a36 : h 0 ≤ (8/47 : ℝ))
    (a39 : -(h 0) < (-4/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a36 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

end RealPinwheel.WeakSevenBandData
