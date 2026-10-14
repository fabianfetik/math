import Pinwheel.WeakSevenBandData.CoverChunks.New085

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem new_node_6234 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a39 : h 0 ≤ (2/13 : ℝ))
    (a50 : -(h 0) < (-5/31 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a39 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6233 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a49 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6232 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 0) < (-3/20 : ℝ))
    (a37 : -(h 1) < (-5/36 : ℝ))
    (a62 : -(h 3) < (-5/43 : ℝ))
    (a68 : -(h 4) < (-2/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a27 + (1/5 : ℝ) * a34 + (1/5 : ℝ) * a37 + (1/5 : ℝ) * a62 + (1/5 : ℝ) * a68 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6231 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 0) < (-3/20 : ℝ))
    (a37 : -(h 1) < (-5/36 : ℝ))
    (a42 : -(h 4) < (-4/39 : ℝ))
    (a67 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a27 + (1/5 : ℝ) * a34 + (1/5 : ℝ) * a37 + (1/5 : ℝ) * a42 + (1/5 : ℝ) * a67 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6230 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a56 : h 2 ≤ (3/23 : ℝ))
    (a66 : -(h 2) < (-3/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a56 + (1 : ℝ) * a66
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6229 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a60 : h 1 ≤ (6/43 : ℝ))
    (a65 : -(h 1) < (-7/50 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a60 + (1 : ℝ) * a65
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6228 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a54 : h 0 ≤ (5/33 : ℝ))
    (a64 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a54 + (1 : ℝ) * a64
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6227 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a63 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a63
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6226 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 0) < (-3/20 : ℝ))
    (a63 : -(h 1) < (-7/50 : ℝ))
    (a67 : -(h 3) < (-4/35 : ℝ))
    (a73 : -(h 4) < (-3/29 : ℝ))
    (a80 : -(h 5) < (-3/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a34 + (1/6 : ℝ) * a63 + (1/6 : ℝ) * a67 + (1/6 : ℝ) * a73 + (1/6 : ℝ) * a80 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6225 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 0) < (-3/20 : ℝ))
    (a63 : -(h 1) < (-7/50 : ℝ))
    (a67 : -(h 3) < (-4/35 : ℝ))
    (a79 : -(h 4) < (-2/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a27 + (1/5 : ℝ) * a34 + (1/5 : ℝ) * a63 + (1/5 : ℝ) * a67 + (1/5 : ℝ) * a79 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6224 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 0) < (-3/20 : ℝ))
    (a63 : -(h 1) < (-7/50 : ℝ))
    (a73 : -(h 4) < (-3/29 : ℝ))
    (a78 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a27 + (1/5 : ℝ) * a34 + (1/5 : ℝ) * a63 + (1/5 : ℝ) * a73 + (1/5 : ℝ) * a78 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6223 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : -(h 0) < (-3/20 : ℝ))
    (a63 : -(h 1) < (-7/50 : ℝ))
    (a67 : -(h 3) < (-4/35 : ℝ))
    (a73 : -(h 4) < (-3/29 : ℝ))
    (a77 : -(h 2) < (-6/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a34 + (1/5 : ℝ) * a63 + (1/5 : ℝ) * a67 + (1/5 : ℝ) * a73 + (1/5 : ℝ) * a77 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6222 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : h 1 ≤ (1/7 : ℝ))
    (a76 : -(h 1) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a23 + (1 : ℝ) * a76
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6221 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a54 : h 0 ≤ (5/33 : ℝ))
    (a75 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a54 + (1 : ℝ) * a75
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6220 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a64 : ((2 : ℝ) * (delta)) ≤ (14/69 : ℝ))
    (a74 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a64 + (1 : ℝ) * a74
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6219 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 0) < (-3/20 : ℝ))
    (a42 : -(h 4) < (-4/39 : ℝ))
    (a63 : -(h 1) < (-7/50 : ℝ))
    (a67 : -(h 3) < (-4/35 : ℝ))
    (a74 : -(h 5) < (-4/39 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a34 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a63 + (1/6 : ℝ) * a67 + (1/6 : ℝ) * a74 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6218 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : h 1 ≤ (1/7 : ℝ))
    (a27 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 0) < (-3/20 : ℝ))
    (a54 : h 0 ≤ (5/33 : ℝ))
    (a63 : -(h 1) < (-7/50 : ℝ))
    (a64 : ((2 : ℝ) * (delta)) ≤ (14/69 : ℝ))
    (a67 : -(h 3) < (-4/35 : ℝ))
    (a73 : -(h 4) < (-3/29 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_6220 h delta _ctx _hno a64 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_6221 h delta _ctx _hno a54 f1
  by_cases p2 : h 1 ≤ (3/20 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_6222 h delta _ctx _hno a23 f2
  by_cases p3 : h 2 ≤ (6/47 : ℝ)
  swap
  · have f3 : -(h 2) < (-6/47 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_6223 h delta _ctx _hno a34 a63 a67 a73 f3
  by_cases p4 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_6224 h delta _ctx _hno a27 a34 a63 a73 f4
  by_cases p5 : h 4 ≤ (2/19 : ℝ)
  swap
  · have f5 : -(h 4) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_6225 h delta _ctx _hno a27 a34 a63 a67 f5
  by_cases p6 : h 5 ≤ (3/29 : ℝ)
  swap
  · have f6 : -(h 5) < (-3/29 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact new_node_6226 h delta _ctx _hno a27 a34 a63 a67 a73 f6
  apply _hno 126
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (6/47 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (2/19 : ℝ)) ∧ (h 5 ≤ (3/29 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem new_node_6217 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 0) < (-3/20 : ℝ))
    (a42 : -(h 4) < (-4/39 : ℝ))
    (a63 : -(h 1) < (-7/50 : ℝ))
    (a72 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a27 + (1/5 : ℝ) * a34 + (1/5 : ℝ) * a42 + (1/5 : ℝ) * a63 + (1/5 : ℝ) * a72 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6216 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a66 : h 2 ≤ (5/39 : ℝ))
    (a71 : -(h 2) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a66 + (1 : ℝ) * a71
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6215 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : h 1 ≤ (1/7 : ℝ))
    (a70 : -(h 1) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a23 + (1 : ℝ) * a70
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6214 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a54 : h 0 ≤ (5/33 : ℝ))
    (a69 : -(h 0) < (-7/45 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a54 + (1 : ℝ) * a69
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6213 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a64 : ((2 : ℝ) * (delta)) ≤ (14/69 : ℝ))
    (a68 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a64 + (1 : ℝ) * a68
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6212 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 0) < (-3/20 : ℝ))
    (a57 : -(h 3) < (-5/44 : ℝ))
    (a63 : -(h 1) < (-7/50 : ℝ))
    (a69 : -(h 5) < (-3/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order4 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a34 + (1/6 : ℝ) * a57 + (1/6 : ℝ) * a63 + (1/3 : ℝ) * a69 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6211 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 0) < (-3/20 : ℝ))
    (a63 : -(h 1) < (-7/50 : ℝ))
    (a68 : -(h 4) < (-9/79 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a27 + (1/5 : ℝ) * a34 + (1/5 : ℝ) * a63 + (2/5 : ℝ) * a68 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6210 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : h 1 ≤ (1/7 : ℝ))
    (a27 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 0) < (-3/20 : ℝ))
    (a42 : -(h 4) < (-4/39 : ℝ))
    (a54 : h 0 ≤ (5/33 : ℝ))
    (a63 : -(h 1) < (-7/50 : ℝ))
    (a64 : ((2 : ℝ) * (delta)) ≤ (14/69 : ℝ))
    (a66 : h 2 ≤ (5/39 : ℝ))
    (a67 : -(h 3) < (-4/35 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_6213 h delta _ctx _hno a64 f0
  by_cases p1 : h 0 ≤ (7/45 : ℝ)
  swap
  · have f1 : -(h 0) < (-7/45 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_6214 h delta _ctx _hno a54 f1
  by_cases p2 : h 1 ≤ (3/20 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_6215 h delta _ctx _hno a23 f2
  by_cases p3 : h 2 ≤ (3/23 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_6216 h delta _ctx _hno a66 f3
  by_cases p4 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_6217 h delta _ctx _hno a27 a34 a42 a63 f4
  by_cases p5 : h 4 ≤ (3/29 : ℝ)
  swap
  · have f5 : -(h 4) < (-3/29 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_6218 h delta _ctx _hno a23 a27 a34 a54 a63 a64 a67 f5
  by_cases p6 : h 5 ≤ (4/39 : ℝ)
  swap
  · have f6 : -(h 5) < (-4/39 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact new_node_6219 h delta _ctx _hno a27 a34 a42 a63 a67 f6
  apply _hno 130
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (7/45 : ℝ)) ∧ (h 1 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (3/29 : ℝ)) ∧ (h 5 ≤ (4/39 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem new_node_6209 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : -(h 0) < (-3/20 : ℝ))
    (a42 : -(h 4) < (-4/39 : ℝ))
    (a57 : -(h 3) < (-5/44 : ℝ))
    (a63 : -(h 1) < (-7/50 : ℝ))
    (a66 : -(h 2) < (-5/39 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a34 + (1/5 : ℝ) * a42 + (1/5 : ℝ) * a57 + (1/5 : ℝ) * a63 + (1/5 : ℝ) * a66 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6208 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a54 : h 0 ≤ (5/33 : ℝ))
    (a65 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a54 + (1 : ℝ) * a65
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6207 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 0) < (-3/20 : ℝ))
    (a42 : -(h 4) < (-4/39 : ℝ))
    (a57 : -(h 3) < (-5/44 : ℝ))
    (a63 : -(h 1) < (-7/50 : ℝ))
    (a64 : ((-2 : ℝ) * (delta)) < (-14/69 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a34 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a57 + (1/6 : ℝ) * a63 + (1/6 : ℝ) * a64 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6206 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 0) < (-3/20 : ℝ))
    (a57 : -(h 3) < (-5/44 : ℝ))
    (a60 : -(h 1) < (-6/43 : ℝ))
    (a66 : -(h 4) < (-2/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a27 + (1/5 : ℝ) * a34 + (1/5 : ℝ) * a57 + (1/5 : ℝ) * a60 + (1/5 : ℝ) * a66 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6205 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 0) < (-3/20 : ℝ))
    (a42 : -(h 4) < (-4/39 : ℝ))
    (a60 : -(h 1) < (-6/43 : ℝ))
    (a65 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a27 + (1/5 : ℝ) * a34 + (1/5 : ℝ) * a42 + (1/5 : ℝ) * a60 + (1/5 : ℝ) * a65 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6204 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a56 : h 2 ≤ (3/23 : ℝ))
    (a64 : -(h 2) < (-3/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a56 + (1 : ℝ) * a64
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6203 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : h 1 ≤ (1/7 : ℝ))
    (a27 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 0) < (-3/20 : ℝ))
    (a42 : -(h 4) < (-4/39 : ℝ))
    (a54 : h 0 ≤ (5/33 : ℝ))
    (a57 : -(h 3) < (-5/44 : ℝ))
    (a63 : -(h 1) < (-7/50 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (14/69 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-14/69 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_6207 h delta _ctx _hno a27 a34 a42 a57 a63 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_6208 h delta _ctx _hno a54 f1
  by_cases p2 : h 2 ≤ (5/39 : ℝ)
  swap
  · have f2 : -(h 2) < (-5/39 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_6209 h delta _ctx _hno a34 a42 a57 a63 f2
  by_cases p3 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f3 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_6210 h delta _ctx _hno a23 a27 a34 a42 a54 a63 p0 p2 f3
  by_cases p4 : h 4 ≤ (9/79 : ℝ)
  swap
  · have f4 : -(h 4) < (-9/79 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_6211 h delta _ctx _hno a27 a34 a63 f4
  by_cases p5 : h 5 ≤ (3/29 : ℝ)
  swap
  · have f5 : -(h 5) < (-3/29 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_6212 h delta _ctx _hno a27 a34 a57 a63 f5
  apply _hno 208
  change (((2 : ℝ) * (delta)) ≤ (14/69 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (5/39 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 4 ≤ (9/79 : ℝ)) ∧ (h 5 ≤ (3/29 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_6202 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a54 : h 0 ≤ (5/33 : ℝ))
    (a62 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a54 + (1 : ℝ) * a62
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6201 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a61 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a61
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6200 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 0) < (-3/20 : ℝ))
    (a37 : -(h 1) < (-5/36 : ℝ))
    (a57 : -(h 3) < (-5/44 : ℝ))
    (a63 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a27 + (1/5 : ℝ) * a34 + (1/5 : ℝ) * a37 + (1/5 : ℝ) * a57 + (1/5 : ℝ) * a63 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6199 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a27 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 0) < (-3/20 : ℝ))
    (a37 : -(h 1) < (-5/36 : ℝ))
    (a42 : -(h 4) < (-4/39 : ℝ))
    (a54 : h 0 ≤ (5/33 : ℝ))
    (a56 : h 2 ≤ (3/23 : ℝ))
    (a60 : h 1 ≤ (6/43 : ℝ))
    (a62 : -(h 3) < (-5/43 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_6227 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_6228 h delta _ctx _hno a54 f1
  by_cases p2 : h 1 ≤ (7/50 : ℝ)
  swap
  · have f2 : -(h 1) < (-7/50 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_6229 h delta _ctx _hno a60 f2
  by_cases p3 : h 2 ≤ (3/22 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_6230 h delta _ctx _hno a56 f3
  by_cases p4 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_6231 h delta _ctx _hno a27 a34 a37 a42 f4
  by_cases p5 : h 4 ≤ (2/19 : ℝ)
  swap
  · have f5 : -(h 4) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_6232 h delta _ctx _hno a27 a34 a37 a62 f5
  apply _hno 223
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (7/50 : ℝ)) ∧ (h 2 ≤ (3/22 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_6198 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a56 : h 2 ≤ (3/23 : ℝ))
    (a61 : -(h 2) < (-3/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a56 + (1 : ℝ) * a61
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6197 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a23 : h 1 ≤ (1/7 : ℝ))
    (a27 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 0) < (-3/20 : ℝ))
    (a42 : -(h 4) < (-4/39 : ℝ))
    (a54 : h 0 ≤ (5/33 : ℝ))
    (a56 : h 2 ≤ (3/23 : ℝ))
    (a57 : -(h 3) < (-5/44 : ℝ))
    (a60 : -(h 1) < (-6/43 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_6201 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_6202 h delta _ctx _hno a54 f1
  by_cases p2 : h 1 ≤ (7/50 : ℝ)
  swap
  · have f2 : -(h 1) < (-7/50 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_6203 h delta _ctx _hno a23 a27 a34 a42 a54 a57 f2
  by_cases p3 : h 2 ≤ (3/22 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_6204 h delta _ctx _hno a56 f3
  by_cases p4 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_6205 h delta _ctx _hno a27 a34 a42 a60 f4
  by_cases p5 : h 4 ≤ (2/19 : ℝ)
  swap
  · have f5 : -(h 4) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_6206 h delta _ctx _hno a27 a34 a57 a60 f5
  apply _hno 223
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (7/50 : ℝ)) ∧ (h 2 ≤ (3/22 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_6196 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a54 : h 0 ≤ (5/33 : ℝ))
    (a59 : -(h 0) < (-5/31 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a54 + (1 : ℝ) * a59
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6195 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a58 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a58
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6194 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : -(h 2) < (-1/8 : ℝ))
    (a52 : -(h 3) < (-7/62 : ℝ))
    (a54 : -(h 0) < (-5/33 : ℝ))
    (a60 : -(h 1) < (-7/50 : ℝ))
    (a66 : -(h 5) < (-3/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order4 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a52 + (1/6 : ℝ) * a54 + (1/6 : ℝ) * a60 + (1/3 : ℝ) * a66 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6193 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : -(h 2) < (-1/8 : ℝ))
    (a54 : -(h 0) < (-5/33 : ℝ))
    (a60 : -(h 1) < (-7/50 : ℝ))
    (a65 : -(h 4) < (-9/79 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a27 + (1/5 : ℝ) * a54 + (1/5 : ℝ) * a60 + (2/5 : ℝ) * a65 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6192 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : -(h 2) < (-1/8 : ℝ))
    (a42 : -(h 4) < (-4/39 : ℝ))
    (a54 : -(h 0) < (-5/33 : ℝ))
    (a60 : -(h 1) < (-7/50 : ℝ))
    (a64 : -(h 3) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a27 + (1/5 : ℝ) * a42 + (1/5 : ℝ) * a54 + (1/5 : ℝ) * a60 + (1/5 : ℝ) * a64 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6191 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a42 : -(h 4) < (-4/39 : ℝ))
    (a52 : -(h 3) < (-7/62 : ℝ))
    (a54 : -(h 0) < (-5/33 : ℝ))
    (a60 : -(h 1) < (-7/50 : ℝ))
    (a63 : -(h 2) < (-5/39 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a42 + (1/5 : ℝ) * a52 + (1/5 : ℝ) * a54 + (1/5 : ℝ) * a60 + (1/5 : ℝ) * a63 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6190 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : -(h 2) < (-1/8 : ℝ))
    (a42 : -(h 4) < (-4/39 : ℝ))
    (a52 : -(h 3) < (-7/62 : ℝ))
    (a60 : -(h 1) < (-7/50 : ℝ))
    (a62 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a27 + (1/5 : ℝ) * a42 + (1/5 : ℝ) * a52 + (1/5 : ℝ) * a60 + (1/5 : ℝ) * a62 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6189 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : -(h 2) < (-1/8 : ℝ))
    (a42 : -(h 4) < (-4/39 : ℝ))
    (a52 : -(h 3) < (-7/62 : ℝ))
    (a54 : -(h 0) < (-5/33 : ℝ))
    (a60 : -(h 1) < (-7/50 : ℝ))
    (a61 : ((-2 : ℝ) * (delta)) < (-14/69 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a52 + (1/6 : ℝ) * a54 + (1/6 : ℝ) * a60 + (1/6 : ℝ) * a61 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6188 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : -(h 2) < (-1/8 : ℝ))
    (a52 : -(h 3) < (-7/62 : ℝ))
    (a54 : -(h 0) < (-5/33 : ℝ))
    (a57 : -(h 1) < (-6/43 : ℝ))
    (a63 : -(h 4) < (-2/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a27 + (1/5 : ℝ) * a52 + (1/5 : ℝ) * a54 + (1/5 : ℝ) * a57 + (1/5 : ℝ) * a63 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6187 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : -(h 2) < (-1/8 : ℝ))
    (a42 : -(h 4) < (-4/39 : ℝ))
    (a54 : -(h 0) < (-5/33 : ℝ))
    (a57 : -(h 1) < (-6/43 : ℝ))
    (a62 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a27 + (1/5 : ℝ) * a42 + (1/5 : ℝ) * a54 + (1/5 : ℝ) * a57 + (1/5 : ℝ) * a62 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6186 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a42 : -(h 4) < (-4/39 : ℝ))
    (a52 : -(h 3) < (-7/62 : ℝ))
    (a54 : -(h 0) < (-5/33 : ℝ))
    (a57 : -(h 1) < (-6/43 : ℝ))
    (a61 : -(h 2) < (-3/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a42 + (1/5 : ℝ) * a52 + (1/5 : ℝ) * a54 + (1/5 : ℝ) * a57 + (1/5 : ℝ) * a61 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6185 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : -(h 2) < (-1/8 : ℝ))
    (a42 : -(h 4) < (-4/39 : ℝ))
    (a52 : -(h 3) < (-7/62 : ℝ))
    (a54 : -(h 0) < (-5/33 : ℝ))
    (a60 : -(h 1) < (-7/50 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (14/69 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-14/69 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_6189 h delta _ctx _hno a27 a42 a52 a54 a60 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_6190 h delta _ctx _hno a27 a42 a52 a60 f1
  by_cases p2 : h 2 ≤ (5/39 : ℝ)
  swap
  · have f2 : -(h 2) < (-5/39 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_6191 h delta _ctx _hno a42 a52 a54 a60 f2
  by_cases p3 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f3 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_6192 h delta _ctx _hno a27 a42 a54 a60 f3
  by_cases p4 : h 4 ≤ (9/79 : ℝ)
  swap
  · have f4 : -(h 4) < (-9/79 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_6193 h delta _ctx _hno a27 a54 a60 f4
  by_cases p5 : h 5 ≤ (3/29 : ℝ)
  swap
  · have f5 : -(h 5) < (-3/29 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_6194 h delta _ctx _hno a27 a52 a54 a60 f5
  apply _hno 208
  change (((2 : ℝ) * (delta)) ≤ (14/69 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (5/39 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 4 ≤ (9/79 : ℝ)) ∧ (h 5 ≤ (3/29 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_6184 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : -(h 2) < (-1/8 : ℝ))
    (a42 : -(h 4) < (-4/39 : ℝ))
    (a52 : -(h 3) < (-7/62 : ℝ))
    (a57 : -(h 1) < (-6/43 : ℝ))
    (a59 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a27 + (1/5 : ℝ) * a42 + (1/5 : ℝ) * a52 + (1/5 : ℝ) * a57 + (1/5 : ℝ) * a59 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6183 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a58 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a58
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6182 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : -(h 2) < (-1/8 : ℝ))
    (a37 : -(h 1) < (-5/36 : ℝ))
    (a52 : -(h 3) < (-7/62 : ℝ))
    (a54 : -(h 0) < (-5/33 : ℝ))
    (a60 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a27 + (1/5 : ℝ) * a37 + (1/5 : ℝ) * a52 + (1/5 : ℝ) * a54 + (1/5 : ℝ) * a60 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6181 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : -(h 2) < (-1/8 : ℝ))
    (a37 : -(h 1) < (-5/36 : ℝ))
    (a42 : -(h 4) < (-4/39 : ℝ))
    (a54 : -(h 0) < (-5/33 : ℝ))
    (a59 : -(h 3) < (-5/43 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a27 + (1/5 : ℝ) * a37 + (1/5 : ℝ) * a42 + (1/5 : ℝ) * a54 + (1/5 : ℝ) * a59 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6180 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a37 : -(h 1) < (-5/36 : ℝ))
    (a42 : -(h 4) < (-4/39 : ℝ))
    (a52 : -(h 3) < (-7/62 : ℝ))
    (a54 : -(h 0) < (-5/33 : ℝ))
    (a58 : -(h 2) < (-3/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a37 + (1/5 : ℝ) * a42 + (1/5 : ℝ) * a52 + (1/5 : ℝ) * a54 + (1/5 : ℝ) * a58 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6179 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a27 : -(h 2) < (-1/8 : ℝ))
    (a42 : -(h 4) < (-4/39 : ℝ))
    (a52 : -(h 3) < (-7/62 : ℝ))
    (a54 : -(h 0) < (-5/33 : ℝ))
    (a57 : -(h 1) < (-6/43 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_6183 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_6184 h delta _ctx _hno a27 a42 a52 a57 f1
  by_cases p2 : h 1 ≤ (7/50 : ℝ)
  swap
  · have f2 : -(h 1) < (-7/50 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_6185 h delta _ctx _hno a27 a42 a52 a54 f2
  by_cases p3 : h 2 ≤ (3/22 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_6186 h delta _ctx _hno a42 a52 a54 a57 f3
  by_cases p4 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_6187 h delta _ctx _hno a27 a42 a54 a57 f4
  by_cases p5 : h 4 ≤ (2/19 : ℝ)
  swap
  · have f5 : -(h 4) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_6188 h delta _ctx _hno a27 a52 a54 a57 f5
  apply _hno 223
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (7/50 : ℝ)) ∧ (h 2 ≤ (3/22 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_6178 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a39 : h 0 ≤ (2/13 : ℝ))
    (a56 : -(h 0) < (-5/31 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a39 + (1 : ℝ) * a56
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6177 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a55 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a55
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6176 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 0) < (-3/20 : ℝ))
    (a37 : -(h 1) < (-5/36 : ℝ))
    (a52 : -(h 3) < (-7/62 : ℝ))
    (a58 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a27 + (1/5 : ℝ) * a34 + (1/5 : ℝ) * a37 + (1/5 : ℝ) * a52 + (1/5 : ℝ) * a58 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6175 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a23 : h 1 ≤ (1/7 : ℝ))
    (a27 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 0) < (-3/20 : ℝ))
    (a37 : -(h 1) < (-5/36 : ℝ))
    (a42 : -(h 4) < (-4/39 : ℝ))
    (a54 : h 0 ≤ (5/33 : ℝ))
    (a56 : h 2 ≤ (3/23 : ℝ))
    (a57 : -(h 3) < (-5/44 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_6195 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (5/31 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/31 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_6196 h delta _ctx _hno a54 f1
  by_cases p2 : h 1 ≤ (6/43 : ℝ)
  swap
  · have f2 : -(h 1) < (-6/43 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_6197 h delta _ctx _hno a13 a23 a27 a34 a42 a54 a56 a57 f2
  by_cases p3 : h 2 ≤ (3/22 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_6198 h delta _ctx _hno a56 f3
  by_cases p4 : h 3 ≤ (5/43 : ℝ)
  swap
  · have f4 : -(h 3) < (-5/43 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_6199 h delta _ctx _hno a13 a27 a34 a37 a42 a54 a56 p2 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_6200 h delta _ctx _hno a27 a34 a37 a57 f5
  apply _hno 228
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (5/31 : ℝ)) ∧ (h 1 ≤ (6/43 : ℝ)) ∧ (h 2 ≤ (3/22 : ℝ)) ∧ (h 3 ≤ (5/43 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_6174 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : -(h 0) < (-3/20 : ℝ))
    (a37 : -(h 1) < (-5/36 : ℝ))
    (a42 : -(h 4) < (-4/39 : ℝ))
    (a52 : -(h 3) < (-7/62 : ℝ))
    (a56 : -(h 2) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a34 + (1/5 : ℝ) * a37 + (1/5 : ℝ) * a42 + (1/5 : ℝ) * a52 + (1/5 : ℝ) * a56 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6173 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : h 1 ≤ (1/7 : ℝ))
    (a55 : -(h 1) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a23 + (1 : ℝ) * a55
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6172 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a27 : -(h 2) < (-1/8 : ℝ))
    (a37 : -(h 1) < (-5/36 : ℝ))
    (a39 : h 0 ≤ (2/13 : ℝ))
    (a42 : -(h 4) < (-4/39 : ℝ))
    (a52 : -(h 3) < (-7/62 : ℝ))
    (a54 : -(h 0) < (-5/33 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_6177 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (5/31 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/31 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_6178 h delta _ctx _hno a39 f1
  by_cases p2 : h 1 ≤ (6/43 : ℝ)
  swap
  · have f2 : -(h 1) < (-6/43 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_6179 h delta _ctx _hno a13 a27 a42 a52 a54 f2
  by_cases p3 : h 2 ≤ (3/22 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_6180 h delta _ctx _hno a37 a42 a52 a54 f3
  by_cases p4 : h 3 ≤ (5/43 : ℝ)
  swap
  · have f4 : -(h 3) < (-5/43 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_6181 h delta _ctx _hno a27 a37 a42 a54 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_6182 h delta _ctx _hno a27 a37 a52 a54 f5
  apply _hno 228
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (5/31 : ℝ)) ∧ (h 1 ≤ (6/43 : ℝ)) ∧ (h 2 ≤ (3/22 : ℝ)) ∧ (h 3 ≤ (5/43 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_6171 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a53 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a53
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6170 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 0) < (-3/20 : ℝ))
    (a37 : -(h 1) < (-5/36 : ℝ))
    (a47 : -(h 3) < (-6/55 : ℝ))
    (a53 : -(h 5) < (-2/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order4 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a34 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a47 + (1/3 : ℝ) * a53 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6169 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a23 : h 1 ≤ (1/7 : ℝ))
    (a27 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 0) < (-3/20 : ℝ))
    (a37 : -(h 1) < (-5/36 : ℝ))
    (a39 : h 0 ≤ (2/13 : ℝ))
    (a42 : -(h 4) < (-4/39 : ℝ))
    (a52 : -(h 3) < (-7/62 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_6171 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (5/33 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/33 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_6172 h delta _ctx _hno a13 a27 a37 a39 a42 a52 f1
  by_cases p2 : h 1 ≤ (3/20 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_6173 h delta _ctx _hno a23 f2
  by_cases p3 : h 2 ≤ (3/23 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_6174 h delta _ctx _hno a34 a37 a42 a52 f3
  by_cases p4 : h 3 ≤ (5/44 : ℝ)
  swap
  · have f4 : -(h 3) < (-5/44 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_6175 h delta _ctx _hno a13 a23 a27 a34 a37 a42 p1 p3 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_6176 h delta _ctx _hno a27 a34 a37 a52 f5
  apply _hno 69
  change (((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)) ∧ (h 0 ≤ (5/33 : ℝ)) ∧ (h 1 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (5/44 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_6168 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : -(h 0) < (-3/20 : ℝ))
    (a37 : -(h 1) < (-5/36 : ℝ))
    (a42 : -(h 4) < (-4/39 : ℝ))
    (a47 : -(h 3) < (-6/55 : ℝ))
    (a51 : -(h 2) < (-4/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a34 + (1/5 : ℝ) * a37 + (1/5 : ℝ) * a42 + (1/5 : ℝ) * a47 + (1/5 : ℝ) * a51 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6167 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : h 1 ≤ (1/7 : ℝ))
    (a50 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a23 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6166 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a39 : h 0 ≤ (2/13 : ℝ))
    (a49 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a39 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6165 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a48 : ((-2 : ℝ) * (delta)) < (-11/52 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6164 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a27 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 0) < (-3/20 : ℝ))
    (a37 : -(h 1) < (-5/36 : ℝ))
    (a39 : h 0 ≤ (2/13 : ℝ))
    (a47 : h 3 ≤ (6/55 : ℝ))
    (a48 : -(h 4) < (-5/46 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_6233 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (5/31 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/31 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_6234 h delta _ctx _hno a39 f1
  by_cases p2 : h 1 ≤ (6/43 : ℝ)
  swap
  · have f2 : -(h 1) < (-6/43 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_6235 h delta _ctx _hno a13 a27 a34 a47 a48 f2
  by_cases p3 : h 2 ≤ (3/22 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_6236 h delta _ctx _hno a34 a37 a48 f3
  by_cases p4 : h 3 ≤ (5/43 : ℝ)
  swap
  · have f4 : -(h 3) < (-5/43 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_6237 h delta _ctx _hno a47 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_6238 h delta _ctx _hno a47 f5
  apply _hno 228
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (5/31 : ℝ)) ∧ (h 1 ≤ (6/43 : ℝ)) ∧ (h 2 ≤ (3/22 : ℝ)) ∧ (h 3 ≤ (5/43 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_6163 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a23 : h 1 ≤ (1/7 : ℝ))
    (a27 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 0) < (-3/20 : ℝ))
    (a37 : -(h 1) < (-5/36 : ℝ))
    (a39 : h 0 ≤ (2/13 : ℝ))
    (a42 : -(h 4) < (-4/39 : ℝ))
    (a47 : -(h 3) < (-6/55 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (11/52 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-11/52 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_6165 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_6166 h delta _ctx _hno a39 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_6167 h delta _ctx _hno a23 f2
  by_cases p3 : h 2 ≤ (4/29 : ℝ)
  swap
  · have f3 : -(h 2) < (-4/29 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_6168 h delta _ctx _hno a34 a37 a42 a47 f3
  by_cases p4 : h 3 ≤ (7/62 : ℝ)
  swap
  · have f4 : -(h 3) < (-7/62 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_6169 h delta _ctx _hno a13 a23 a27 a34 a37 a39 a42 f4
  by_cases p5 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_6170 h delta _ctx _hno a27 a34 a37 a47 f5
  apply _hno 174
  change (((2 : ℝ) * (delta)) ≤ (11/52 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (4/29 : ℝ)) ∧ (h 3 ≤ (7/62 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_6162 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a32 : -(h 3) < (-3/28 : ℝ))
    (a46 : -(h 2) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/13 : ℝ) * _ctx.order1 + (4/13 : ℝ) * _ctx.min + (8/13 : ℝ) * _ctx.lower + (1/13 : ℝ) * _ctx.fail2 + (4/13 : ℝ) * a32 + (8/13 : ℝ) * a46 + (4/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6161 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : h 1 ≤ (1/7 : ℝ))
    (a45 : -(h 1) < (-8/55 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a23 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6160 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a39 : h 0 ≤ (2/13 : ℝ))
    (a44 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a39 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6159 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6158 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : -(h 2) < (-1/8 : ℝ))
    (a34 : -(h 0) < (-3/20 : ℝ))
    (a37 : -(h 1) < (-5/36 : ℝ))
    (a41 : -(h 3) < (-2/17 : ℝ))
    (a47 : -(h 4) < (-4/39 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a27 + (1/5 : ℝ) * a34 + (1/5 : ℝ) * a37 + (1/5 : ℝ) * a41 + (1/5 : ℝ) * a47 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6157 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a37 : -(h 1) < (-5/36 : ℝ))
    (a46 : -(h 3) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/13 : ℝ) * _ctx.order2 + (4/13 : ℝ) * _ctx.min + (8/13 : ℝ) * _ctx.lower + (1/13 : ℝ) * _ctx.fail2 + (4/13 : ℝ) * a37 + (8/13 : ℝ) * a46 + (4/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6156 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a37 : -(h 1) < (-5/36 : ℝ))
    (a41 : -(h 3) < (-2/17 : ℝ))
    (a45 : -(h 2) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/13 : ℝ) * _ctx.min + (8/13 : ℝ) * _ctx.lower + (1/13 : ℝ) * _ctx.fail2 + (4/13 : ℝ) * a37 + (4/13 : ℝ) * a41 + (4/13 : ℝ) * a45 + (4/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_6155 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : -(h 2) < (-1/8 : ℝ))
    (a41 : -(h 3) < (-2/17 : ℝ))
    (a44 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/13 : ℝ) * _ctx.min + (8/13 : ℝ) * _ctx.lower + (1/13 : ℝ) * _ctx.fail2 + (4/13 : ℝ) * a27 + (4/13 : ℝ) * a41 + (4/13 : ℝ) * a44 + (4/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

end RealPinwheel.WeakSevenBandData
