import Pinwheel.WeakSevenBandData.CoverChunks.New089

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem new_node_5914 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : -(h 1) < (-1/7 : ℝ))
    (a26 : h 2 ≤ (1/8 : ℝ))
    (a32 : -(h 0) < (-5/33 : ℝ))
    (a41 : h 3 ≤ (6/55 : ℝ))
    (a42 : -(h 4) < (-5/46 : ℝ))
    (a45 : -(h 2) < (-3/25 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (14/69 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-14/69 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_5916 h delta _ctx _hno a23 a32 a42 a45 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_5917 h delta _ctx _hno a23 a42 a45 f1
  by_cases p2 : h 2 ≤ (5/39 : ℝ)
  swap
  · have f2 : -(h 2) < (-5/39 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_5918 h delta _ctx _hno a26 f2
  by_cases p3 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f3 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_5919 h delta _ctx _hno a41 f3
  by_cases p4 : h 4 ≤ (9/79 : ℝ)
  swap
  · have f4 : -(h 4) < (-9/79 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_5920 h delta _ctx _hno a41 f4
  by_cases p5 : h 5 ≤ (3/29 : ℝ)
  swap
  · have f5 : -(h 5) < (-3/29 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_5921 h delta _ctx _hno a23 a32 a42 a45 f5
  apply _hno 208
  change (((2 : ℝ) * (delta)) ≤ (14/69 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (5/39 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 4 ≤ (9/79 : ℝ)) ∧ (h 5 ≤ (3/29 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_5913 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a38 : h 0 ≤ (2/13 : ℝ))
    (a44 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a38 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5912 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-9/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5911 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : -(h 1) < (-1/7 : ℝ))
    (a32 : -(h 0) < (-5/33 : ℝ))
    (a41 : -(h 3) < (-6/55 : ℝ))
    (a47 : -(h 4) < (-5/46 : ℝ))
    (a50 : -(h 2) < (-3/25 : ℝ))
    (a56 : -(h 5) < (-3/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a23 + (1/6 : ℝ) * a32 + (1/6 : ℝ) * a41 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * a50 + (1/6 : ℝ) * a56 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5910 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : h 3 ≤ (1/9 : ℝ))
    (a55 : -(h 4) < (-9/79 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * _ctx.order3 + (1 : ℝ) * a27 + (1 : ℝ) * a55
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5909 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : h 3 ≤ (1/9 : ℝ))
    (a54 : -(h 3) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a54
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5908 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : h 2 ≤ (1/8 : ℝ))
    (a53 : -(h 2) < (-5/39 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a26 + (1 : ℝ) * a53
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5907 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : -(h 1) < (-1/7 : ℝ))
    (a41 : -(h 3) < (-6/55 : ℝ))
    (a47 : -(h 4) < (-5/46 : ℝ))
    (a50 : -(h 2) < (-3/25 : ℝ))
    (a52 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a23 + (1/5 : ℝ) * a41 + (1/5 : ℝ) * a47 + (1/5 : ℝ) * a50 + (1/5 : ℝ) * a52 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5906 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : -(h 1) < (-1/7 : ℝ))
    (a32 : -(h 0) < (-5/33 : ℝ))
    (a41 : -(h 3) < (-6/55 : ℝ))
    (a47 : -(h 4) < (-5/46 : ℝ))
    (a50 : -(h 2) < (-3/25 : ℝ))
    (a51 : ((-2 : ℝ) * (delta)) < (-14/69 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a23 + (1/6 : ℝ) * a32 + (1/6 : ℝ) * a41 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * a50 + (1/6 : ℝ) * a51 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5905 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : h 3 ≤ (1/9 : ℝ))
    (a51 : -(h 3) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a51
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5904 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : -(h 1) < (-1/7 : ℝ))
    (a26 : h 2 ≤ (1/8 : ℝ))
    (a27 : h 3 ≤ (1/9 : ℝ))
    (a32 : -(h 0) < (-5/33 : ℝ))
    (a41 : -(h 3) < (-6/55 : ℝ))
    (a47 : -(h 4) < (-5/46 : ℝ))
    (a50 : -(h 2) < (-3/25 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (14/69 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-14/69 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_5906 h delta _ctx _hno a23 a32 a41 a47 a50 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_5907 h delta _ctx _hno a23 a41 a47 a50 f1
  by_cases p2 : h 2 ≤ (5/39 : ℝ)
  swap
  · have f2 : -(h 2) < (-5/39 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_5908 h delta _ctx _hno a26 f2
  by_cases p3 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f3 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_5909 h delta _ctx _hno a27 f3
  by_cases p4 : h 4 ≤ (9/79 : ℝ)
  swap
  · have f4 : -(h 4) < (-9/79 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_5910 h delta _ctx _hno a27 f4
  by_cases p5 : h 5 ≤ (3/29 : ℝ)
  swap
  · have f5 : -(h 5) < (-3/29 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_5911 h delta _ctx _hno a23 a32 a41 a47 a50 f5
  apply _hno 208
  change (((2 : ℝ) * (delta)) ≤ (14/69 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (5/39 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 4 ≤ (9/79 : ℝ)) ∧ (h 5 ≤ (3/29 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_5903 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a38 : h 0 ≤ (2/13 : ℝ))
    (a49 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a38 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5902 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a48 : ((-2 : ℝ) * (delta)) < (-9/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5901 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a23 : -(h 1) < (-1/7 : ℝ))
    (a26 : h 2 ≤ (1/8 : ℝ))
    (a27 : h 3 ≤ (1/9 : ℝ))
    (a32 : -(h 0) < (-5/33 : ℝ))
    (a38 : h 0 ≤ (2/13 : ℝ))
    (a41 : -(h 3) < (-6/55 : ℝ))
    (a47 : -(h 4) < (-5/46 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (9/41 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-9/41 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_5902 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_5903 h delta _ctx _hno a38 f1
  by_cases p2 : h 2 ≤ (3/25 : ℝ)
  swap
  · have f2 : -(h 2) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_5904 h delta _ctx _hno a23 a26 a27 a32 a41 a47 f2
  by_cases p3 : h 3 ≤ (1/9 : ℝ)
  swap
  · have f3 : -(h 3) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_5905 h delta _ctx _hno a27 f3
  apply _hno 195
  change (((2 : ℝ) * (delta)) ≤ (9/41 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_5900 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : h 3 ≤ (1/9 : ℝ))
    (a46 : -(h 3) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5899 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : h 2 ≤ (1/8 : ℝ))
    (a45 : -(h 2) < (-6/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a26 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5898 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a39 : h 1 ≤ (8/55 : ℝ))
    (a44 : -(h 1) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a39 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5897 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a38 : h 0 ≤ (2/13 : ℝ))
    (a43 : -(h 0) < (-4/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a38 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5896 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a42 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5895 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a32 : -(h 0) < (-5/33 : ℝ))
    (a36 : -(h 2) < (-2/17 : ℝ))
    (a39 : -(h 1) < (-8/55 : ℝ))
    (a50 : -(h 4) < (-5/46 : ℝ))
    (a54 : -(h 3) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a32 + (1/5 : ℝ) * a36 + (1/5 : ℝ) * a39 + (1/5 : ℝ) * a50 + (1/5 : ℝ) * a54 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5894 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a32 : -(h 0) < (-5/33 : ℝ))
    (a39 : -(h 1) < (-8/55 : ℝ))
    (a50 : -(h 4) < (-5/46 : ℝ))
    (a53 : -(h 2) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a32 + (1/5 : ℝ) * a39 + (2/5 : ℝ) * a50 + (1/5 : ℝ) * a53 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5893 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a36 : -(h 2) < (-2/17 : ℝ))
    (a39 : -(h 1) < (-8/55 : ℝ))
    (a50 : -(h 4) < (-5/46 : ℝ))
    (a52 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a36 + (1/5 : ℝ) * a39 + (2/5 : ℝ) * a50 + (1/5 : ℝ) * a52 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5892 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a51 : ((-2 : ℝ) * (delta)) < (-9/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a51
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5891 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a32 : -(h 0) < (-5/33 : ℝ))
    (a36 : -(h 2) < (-2/17 : ℝ))
    (a39 : -(h 1) < (-8/55 : ℝ))
    (a50 : -(h 4) < (-5/46 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (9/41 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-9/41 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_5892 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_5893 h delta _ctx _hno a36 a39 a50 f1
  by_cases p2 : h 2 ≤ (3/25 : ℝ)
  swap
  · have f2 : -(h 2) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_5894 h delta _ctx _hno a32 a39 a50 f2
  by_cases p3 : h 3 ≤ (1/9 : ℝ)
  swap
  · have f3 : -(h 3) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_5895 h delta _ctx _hno a32 a36 a39 a50 f3
  apply _hno 195
  change (((2 : ℝ) * (delta)) ≤ (9/41 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_5890 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : h 3 ≤ (1/9 : ℝ))
    (a49 : -(h 3) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5889 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : h 2 ≤ (1/8 : ℝ))
    (a48 : -(h 2) < (-6/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a26 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5888 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : h 1 ≤ (4/27 : ℝ))
    (a47 : -(h 1) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a19 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5887 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a38 : h 0 ≤ (2/13 : ℝ))
    (a46 : -(h 0) < (-4/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a38 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5886 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a45 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5885 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a19 : h 1 ≤ (4/27 : ℝ))
    (a26 : h 2 ≤ (1/8 : ℝ))
    (a27 : h 3 ≤ (1/9 : ℝ))
    (a32 : -(h 0) < (-5/33 : ℝ))
    (a36 : -(h 2) < (-2/17 : ℝ))
    (a38 : h 0 ≤ (2/13 : ℝ))
    (a39 : -(h 1) < (-8/55 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_5886 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (4/25 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/25 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_5887 h delta _ctx _hno a38 f1
  by_cases p2 : h 1 ≤ (2/13 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_5888 h delta _ctx _hno a19 f2
  by_cases p3 : h 2 ≤ (6/47 : ℝ)
  swap
  · have f3 : -(h 2) < (-6/47 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_5889 h delta _ctx _hno a26 f3
  by_cases p4 : h 3 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_5890 h delta _ctx _hno a27 f4
  by_cases p5 : h 4 ≤ (5/46 : ℝ)
  swap
  · have f5 : -(h 4) < (-5/46 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_5891 h delta _ctx _hno a13 a32 a36 a39 f5
  apply _hno 157
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (6/47 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ)) ∧ (h 4 ≤ (5/46 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_5884 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a28 : -(h 4) < (-3/28 : ℝ))
    (a32 : -(h 0) < (-5/33 : ℝ))
    (a39 : -(h 1) < (-8/55 : ℝ))
    (a43 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (2/5 : ℝ) * a28 + (1/5 : ℝ) * a32 + (1/5 : ℝ) * a39 + (1/5 : ℝ) * a43 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5883 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : h 1 ≤ (4/27 : ℝ))
    (a42 : -(h 1) < (-4/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a19 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5882 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a38 : h 0 ≤ (2/13 : ℝ))
    (a41 : -(h 0) < (-6/37 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a38 + (1 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5881 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a40 : ((-2 : ℝ) * (delta)) < (-8/37 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5880 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : -(h 1) < (-1/7 : ℝ))
    (a38 : -(h 0) < (-2/13 : ℝ))
    (a49 : -(h 4) < (-5/46 : ℝ))
    (a53 : -(h 2) < (-5/42 : ℝ))
    (a59 : -(h 5) < (-2/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a23 + (1/6 : ℝ) * a38 + (1/3 : ℝ) * a49 + (1/6 : ℝ) * a53 + (1/6 : ℝ) * a59 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5879 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : -(h 1) < (-1/7 : ℝ))
    (a38 : -(h 0) < (-2/13 : ℝ))
    (a49 : -(h 4) < (-5/46 : ℝ))
    (a53 : -(h 2) < (-5/42 : ℝ))
    (a58 : -(h 3) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a23 + (1/5 : ℝ) * a38 + (1/5 : ℝ) * a49 + (1/5 : ℝ) * a53 + (1/5 : ℝ) * a58 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5878 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : -(h 1) < (-1/7 : ℝ))
    (a38 : -(h 0) < (-2/13 : ℝ))
    (a49 : -(h 4) < (-5/46 : ℝ))
    (a57 : -(h 2) < (-5/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a23 + (1/5 : ℝ) * a38 + (2/5 : ℝ) * a49 + (1/5 : ℝ) * a57 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5877 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : h 1 ≤ (4/27 : ℝ))
    (a56 : -(h 1) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a19 + (1 : ℝ) * a56
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5876 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : h 0 ≤ (8/51 : ℝ))
    (a55 : -(h 0) < (-3/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a55
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5875 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a50 : ((2 : ℝ) * (delta)) ≤ (13/64 : ℝ))
    (a54 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a50 + (1 : ℝ) * a54
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5874 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : -(h 1) < (-1/7 : ℝ))
    (a36 : -(h 2) < (-2/17 : ℝ))
    (a38 : -(h 0) < (-2/13 : ℝ))
    (a49 : -(h 4) < (-5/46 : ℝ))
    (a56 : -(h 5) < (-3/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a23 + (1/6 : ℝ) * a36 + (1/6 : ℝ) * a38 + (1/3 : ℝ) * a49 + (1/6 : ℝ) * a56 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5873 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : -(h 1) < (-1/7 : ℝ))
    (a36 : -(h 2) < (-2/17 : ℝ))
    (a38 : -(h 0) < (-2/13 : ℝ))
    (a55 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a23 + (1/5 : ℝ) * a36 + (1/5 : ℝ) * a38 + (2/5 : ℝ) * a55 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5872 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : h 3 ≤ (1/9 : ℝ))
    (a54 : -(h 3) < (-9/79 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a54
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5871 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : h 1 ≤ (4/27 : ℝ))
    (a23 : -(h 1) < (-1/7 : ℝ))
    (a34 : h 0 ≤ (8/51 : ℝ))
    (a38 : -(h 0) < (-2/13 : ℝ))
    (a49 : -(h 4) < (-5/46 : ℝ))
    (a50 : ((2 : ℝ) * (delta)) ≤ (13/64 : ℝ))
    (a53 : -(h 2) < (-5/42 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_5875 h delta _ctx _hno a50 f0
  by_cases p1 : h 0 ≤ (3/19 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/19 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_5876 h delta _ctx _hno a34 f1
  by_cases p2 : h 1 ≤ (2/13 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_5877 h delta _ctx _hno a19 f2
  by_cases p3 : h 2 ≤ (5/41 : ℝ)
  swap
  · have f3 : -(h 2) < (-5/41 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_5878 h delta _ctx _hno a23 a38 a49 f3
  by_cases p4 : h 3 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_5879 h delta _ctx _hno a23 a38 a49 a53 f4
  by_cases p5 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_5880 h delta _ctx _hno a23 a38 a49 a53 f5
  apply _hno 238
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (5/41 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_5870 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : h 1 ≤ (4/27 : ℝ))
    (a52 : -(h 1) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a19 + (1 : ℝ) * a52
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5869 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : h 0 ≤ (8/51 : ℝ))
    (a51 : -(h 0) < (-3/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a51
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5868 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : -(h 1) < (-1/7 : ℝ))
    (a36 : -(h 2) < (-2/17 : ℝ))
    (a38 : -(h 0) < (-2/13 : ℝ))
    (a49 : -(h 4) < (-5/46 : ℝ))
    (a50 : ((-2 : ℝ) * (delta)) < (-13/64 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a23 + (1/6 : ℝ) * a36 + (1/6 : ℝ) * a38 + (1/3 : ℝ) * a49 + (1/6 : ℝ) * a50 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5867 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : h 1 ≤ (4/27 : ℝ))
    (a23 : -(h 1) < (-1/7 : ℝ))
    (a27 : h 3 ≤ (1/9 : ℝ))
    (a34 : h 0 ≤ (8/51 : ℝ))
    (a36 : -(h 2) < (-2/17 : ℝ))
    (a38 : -(h 0) < (-2/13 : ℝ))
    (a49 : -(h 4) < (-5/46 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (13/64 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-13/64 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_5868 h delta _ctx _hno a23 a36 a38 a49 f0
  by_cases p1 : h 0 ≤ (3/19 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/19 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_5869 h delta _ctx _hno a34 f1
  by_cases p2 : h 1 ≤ (2/13 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_5870 h delta _ctx _hno a19 f2
  by_cases p3 : h 2 ≤ (5/42 : ℝ)
  swap
  · have f3 : -(h 2) < (-5/42 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_5871 h delta _ctx _hno a19 a23 a34 a38 a49 p0 f3
  by_cases p4 : h 3 ≤ (9/79 : ℝ)
  swap
  · have f4 : -(h 3) < (-9/79 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_5872 h delta _ctx _hno a27 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_5873 h delta _ctx _hno a23 a36 a38 f5
  by_cases p6 : h 5 ≤ (3/28 : ℝ)
  swap
  · have f6 : -(h 5) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact new_node_5874 h delta _ctx _hno a23 a36 a38 a49 f6
  apply _hno 237
  change (((2 : ℝ) * (delta)) ≤ (13/64 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (5/42 : ℝ)) ∧ (h 3 ≤ (9/79 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ)) ∧ (h 5 ≤ (3/28 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem new_node_5866 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : h 3 ≤ (1/9 : ℝ))
    (a48 : -(h 3) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5865 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : h 2 ≤ (1/8 : ℝ))
    (a47 : -(h 2) < (-6/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a26 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5864 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : h 1 ≤ (4/27 : ℝ))
    (a46 : -(h 1) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a19 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5863 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : h 0 ≤ (8/51 : ℝ))
    (a45 : -(h 0) < (-4/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5862 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a44 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5861 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a19 : h 1 ≤ (4/27 : ℝ))
    (a23 : -(h 1) < (-1/7 : ℝ))
    (a26 : h 2 ≤ (1/8 : ℝ))
    (a27 : h 3 ≤ (1/9 : ℝ))
    (a34 : h 0 ≤ (8/51 : ℝ))
    (a36 : -(h 2) < (-2/17 : ℝ))
    (a38 : -(h 0) < (-2/13 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_5862 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (4/25 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/25 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_5863 h delta _ctx _hno a34 f1
  by_cases p2 : h 1 ≤ (2/13 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_5864 h delta _ctx _hno a19 f2
  by_cases p3 : h 2 ≤ (6/47 : ℝ)
  swap
  · have f3 : -(h 2) < (-6/47 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_5865 h delta _ctx _hno a26 f3
  by_cases p4 : h 3 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_5866 h delta _ctx _hno a27 f4
  by_cases p5 : h 4 ≤ (5/46 : ℝ)
  swap
  · have f5 : -(h 4) < (-5/46 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_5867 h delta _ctx _hno a19 a23 a27 a34 a36 a38 f5
  apply _hno 157
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (6/47 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ)) ∧ (h 4 ≤ (5/46 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_5860 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : -(h 1) < (-1/7 : ℝ))
    (a28 : -(h 4) < (-3/28 : ℝ))
    (a38 : -(h 0) < (-2/13 : ℝ))
    (a42 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a23 + (2/5 : ℝ) * a28 + (1/5 : ℝ) * a38 + (1/5 : ℝ) * a42 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5859 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : h 1 ≤ (4/27 : ℝ))
    (a41 : -(h 1) < (-4/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a19 + (1 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5858 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : h 0 ≤ (8/51 : ℝ))
    (a40 : -(h 0) < (-6/37 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5857 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a39 : ((-2 : ℝ) * (delta)) < (-8/37 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5856 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a23 : -(h 1) < (-1/7 : ℝ))
    (a26 : h 2 ≤ (1/8 : ℝ))
    (a32 : -(h 0) < (-5/33 : ℝ))
    (a38 : h 0 ≤ (2/13 : ℝ))
    (a41 : h 3 ≤ (6/55 : ℝ))
    (a42 : -(h 4) < (-5/46 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (9/41 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-9/41 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_5912 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_5913 h delta _ctx _hno a38 f1
  by_cases p2 : h 2 ≤ (3/25 : ℝ)
  swap
  · have f2 : -(h 2) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_5914 h delta _ctx _hno a23 a26 a32 a41 a42 f2
  by_cases p3 : h 3 ≤ (1/9 : ℝ)
  swap
  · have f3 : -(h 3) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_5915 h delta _ctx _hno a41 f3
  apply _hno 195
  change (((2 : ℝ) * (delta)) ≤ (9/41 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_5855 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a23 : -(h 1) < (-1/7 : ℝ))
    (a26 : h 2 ≤ (1/8 : ℝ))
    (a27 : h 3 ≤ (1/9 : ℝ))
    (a32 : -(h 0) < (-5/33 : ℝ))
    (a38 : h 0 ≤ (2/13 : ℝ))
    (a39 : h 1 ≤ (8/55 : ℝ))
    (a41 : -(h 3) < (-6/55 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_5896 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (4/25 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/25 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_5897 h delta _ctx _hno a38 f1
  by_cases p2 : h 1 ≤ (2/13 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_5898 h delta _ctx _hno a39 f2
  by_cases p3 : h 2 ≤ (6/47 : ℝ)
  swap
  · have f3 : -(h 2) < (-6/47 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_5899 h delta _ctx _hno a26 f3
  by_cases p4 : h 3 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_5900 h delta _ctx _hno a27 f4
  by_cases p5 : h 4 ≤ (5/46 : ℝ)
  swap
  · have f5 : -(h 4) < (-5/46 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_5901 h delta _ctx _hno a13 a23 a26 a27 a32 a38 a41 f5
  apply _hno 157
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (6/47 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ)) ∧ (h 4 ≤ (5/46 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_5854 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : h 2 ≤ (1/8 : ℝ))
    (a40 : -(h 2) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a26 + (1 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5853 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a19 : h 1 ≤ (4/27 : ℝ))
    (a26 : h 2 ≤ (1/8 : ℝ))
    (a27 : h 3 ≤ (1/9 : ℝ))
    (a28 : -(h 4) < (-3/28 : ℝ))
    (a32 : -(h 0) < (-5/33 : ℝ))
    (a36 : -(h 2) < (-2/17 : ℝ))
    (a38 : h 0 ≤ (2/13 : ℝ))
    (a39 : -(h 1) < (-8/55 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (8/37 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-8/37 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_5881 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (6/37 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/37 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_5882 h delta _ctx _hno a38 f1
  by_cases p2 : h 1 ≤ (4/25 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/25 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_5883 h delta _ctx _hno a19 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_5884 h delta _ctx _hno a28 a32 a39 f3
  by_cases p4 : h 3 ≤ (4/37 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/37 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_5885 h delta _ctx _hno a13 a19 a26 a27 a32 a36 a38 a39
  apply _hno 26
  change (((2 : ℝ) * (delta)) ≤ (8/37 : ℝ)) ∧ (h 0 ≤ (6/37 : ℝ)) ∧ (h 1 ≤ (4/25 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (4/37 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_5852 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a19 : h 1 ≤ (4/27 : ℝ))
    (a23 : -(h 1) < (-1/7 : ℝ))
    (a26 : h 2 ≤ (1/8 : ℝ))
    (a27 : h 3 ≤ (1/9 : ℝ))
    (a28 : -(h 4) < (-3/28 : ℝ))
    (a34 : h 0 ≤ (8/51 : ℝ))
    (a36 : -(h 2) < (-2/17 : ℝ))
    (a38 : -(h 0) < (-2/13 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (8/37 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-8/37 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_5857 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (6/37 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/37 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_5858 h delta _ctx _hno a34 f1
  by_cases p2 : h 1 ≤ (4/25 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/25 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_5859 h delta _ctx _hno a19 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_5860 h delta _ctx _hno a23 a28 a38 f3
  by_cases p4 : h 3 ≤ (4/37 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/37 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_5861 h delta _ctx _hno a13 a19 a23 a26 a27 a34 a36 a38
  apply _hno 26
  change (((2 : ℝ) * (delta)) ≤ (8/37 : ℝ)) ∧ (h 0 ≤ (6/37 : ℝ)) ∧ (h 1 ≤ (4/25 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (4/37 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_5851 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a37 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a37
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5850 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : -(h 1) < (-1/7 : ℝ))
    (a34 : -(h 0) < (-8/51 : ℝ))
    (a38 : -(h 3) < (-8/73 : ℝ))
    (a44 : -(h 4) < (-5/46 : ℝ))
    (a49 : -(h 5) < (-2/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.lower + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a23 + (4/29 : ℝ) * a34 + (6/29 : ℝ) * a38 + (6/29 : ℝ) * a44 + (6/29 : ℝ) * a49 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5849 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : -(h 1) < (-1/7 : ℝ))
    (a34 : -(h 0) < (-8/51 : ℝ))
    (a38 : -(h 3) < (-8/73 : ℝ))
    (a44 : -(h 4) < (-5/46 : ℝ))
    (a48 : -(h 2) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a23 + (1/5 : ℝ) * a34 + (1/5 : ℝ) * a38 + (1/5 : ℝ) * a44 + (1/5 : ℝ) * a48 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5848 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : h 1 ≤ (4/27 : ℝ))
    (a47 : -(h 1) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a19 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5847 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : -(h 1) < (-1/7 : ℝ))
    (a38 : -(h 3) < (-8/73 : ℝ))
    (a44 : -(h 4) < (-5/46 : ℝ))
    (a46 : -(h 0) < (-4/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.min + (12/23 : ℝ) * _ctx.lower + (1/23 : ℝ) * _ctx.fail1 + (6/23 : ℝ) * a23 + (6/23 : ℝ) * a38 + (6/23 : ℝ) * a44 + (4/23 : ℝ) * a46 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5846 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : -(h 1) < (-1/7 : ℝ))
    (a34 : -(h 0) < (-8/51 : ℝ))
    (a38 : -(h 3) < (-8/73 : ℝ))
    (a44 : -(h 4) < (-5/46 : ℝ))
    (a45 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.min + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a23 + (4/29 : ℝ) * a34 + (6/29 : ℝ) * a38 + (6/29 : ℝ) * a44 + (6/29 : ℝ) * a45 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5845 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : -(h 1) < (-1/7 : ℝ))
    (a40 : -(h 0) < (-4/25 : ℝ))
    (a46 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.order3 + (6/23 : ℝ) * _ctx.min + (12/23 : ℝ) * _ctx.lower + (1/23 : ℝ) * _ctx.fail1 + (6/23 : ℝ) * a23 + (4/23 : ℝ) * a40 + (12/23 : ℝ) * a46 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5844 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : h 3 ≤ (1/9 : ℝ))
    (a45 : -(h 3) < (-6/53 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5843 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : -(h 1) < (-1/7 : ℝ))
    (a28 : -(h 4) < (-3/28 : ℝ))
    (a38 : -(h 3) < (-8/73 : ℝ))
    (a40 : -(h 0) < (-4/25 : ℝ))
    (a44 : -(h 2) < (-27/236 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a23 + (1/5 : ℝ) * a28 + (1/5 : ℝ) * a38 + (1/5 : ℝ) * a40 + (1/5 : ℝ) * a44 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5842 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a28 : -(h 4) < (-3/28 : ℝ))
    (a38 : -(h 3) < (-8/73 : ℝ))
    (a40 : -(h 0) < (-4/25 : ℝ))
    (a43 : -(h 1) < (-5/34 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.min + (12/23 : ℝ) * _ctx.lower + (1/23 : ℝ) * _ctx.fail1 + (6/23 : ℝ) * a28 + (6/23 : ℝ) * a38 + (4/23 : ℝ) * a40 + (6/23 : ℝ) * a43 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5841 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a36 : h 0 ≤ (7/43 : ℝ))
    (a42 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a36 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5840 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5839 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : h 1 ≤ (4/27 : ℝ))
    (a23 : -(h 1) < (-1/7 : ℝ))
    (a34 : -(h 0) < (-8/51 : ℝ))
    (a38 : -(h 3) < (-8/73 : ℝ))
    (a44 : -(h 4) < (-5/46 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_5846 h delta _ctx _hno a23 a34 a38 a44 f0
  by_cases p1 : h 0 ≤ (4/25 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/25 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_5847 h delta _ctx _hno a23 a38 a44 f1
  by_cases p2 : h 1 ≤ (2/13 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_5848 h delta _ctx _hno a19 f2
  by_cases p3 : h 2 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_5849 h delta _ctx _hno a23 a34 a38 a44 f3
  by_cases p4 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f4 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_5850 h delta _ctx _hno a23 a34 a38 a44 f4
  apply _hno 212
  change (((2 : ℝ) * (delta)) ≤ (12/59 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (2/13 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_5838 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : h 3 ≤ (1/9 : ℝ))
    (a43 : -(h 3) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5837 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a37 : h 2 ≤ (2/17 : ℝ))
    (a42 : -(h 2) < (-6/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a37 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5836 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a19 : h 1 ≤ (4/27 : ℝ))
    (a41 : -(h 1) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a19 + (1 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_5835 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a23 : -(h 1) < (-1/7 : ℝ))
    (a27 : h 3 ≤ (1/9 : ℝ))
    (a28 : -(h 4) < (-3/28 : ℝ))
    (a36 : h 0 ≤ (7/43 : ℝ))
    (a38 : -(h 3) < (-8/73 : ℝ))
    (a40 : -(h 0) < (-4/25 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_5840 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_5841 h delta _ctx _hno a36 f1
  by_cases p2 : h 1 ≤ (5/34 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/34 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_5842 h delta _ctx _hno a28 a38 a40 f2
  by_cases p3 : h 2 ≤ (27/236 : ℝ)
  swap
  · have f3 : -(h 2) < (-27/236 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_5843 h delta _ctx _hno a23 a28 a38 a40 f3
  by_cases p4 : h 3 ≤ (6/53 : ℝ)
  swap
  · have f4 : -(h 3) < (-6/53 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_5844 h delta _ctx _hno a27 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_5845 h delta _ctx _hno a23 a40 f5
  apply _hno 209
  change (((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (5/34 : ℝ)) ∧ (h 2 ≤ (27/236 : ℝ)) ∧ (h 3 ≤ (6/53 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

end RealPinwheel.WeakSevenBandData
