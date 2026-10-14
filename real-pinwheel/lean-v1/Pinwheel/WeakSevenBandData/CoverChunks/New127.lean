import Pinwheel.WeakSevenBandData.CoverChunks.New126

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem new_node_2954 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : -(h 2) < (-1/8 : ℝ))
    (a26 : -(h 0) < (-4/27 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a37 : h 0 ≤ (3/20 : ℝ))
    (a38 : -(h 1) < (-3/23 : ℝ))
    (a43 : h 3 ≤ (5/43 : ℝ))
    (a44 : -(h 4) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_2955 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_2956 h delta _ctx _hno a37 f1
  by_cases p2 : h 1 ≤ (5/38 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/38 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_2957 h delta _ctx _hno a24 a26 a27 a44 f2
  by_cases p3 : h 2 ≤ (3/23 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_2958 h delta _ctx _hno a26 a27 a44 f3
  by_cases p4 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_2959 h delta _ctx _hno a43 f4
  by_cases p5 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_2960 h delta _ctx _hno a24 a26 a27 a38 a44 f5
  apply _hno 30
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (5/38 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_2953 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : -(h 2) < (-1/8 : ℝ))
    (a26 : -(h 0) < (-4/27 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a32 : -(h 4) < (-4/37 : ℝ))
    (a38 : -(h 1) < (-3/23 : ℝ))
    (a43 : -(h 3) < (-5/43 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a24 + (1/6 : ℝ) * a26 + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a32 + (1/6 : ℝ) * a38 + (1/6 : ℝ) * a43 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2952 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : h 1 ≤ (2/15 : ℝ))
    (a42 : -(h 2) < (-3/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * _ctx.order1 + (1 : ℝ) * a23 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2951 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : h 1 ≤ (2/15 : ℝ))
    (a41 : -(h 1) < (-6/43 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a23 + (1 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2950 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a37 : h 0 ≤ (3/20 : ℝ))
    (a40 : -(h 0) < (-5/31 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a37 + (1 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2949 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a39 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2948 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : -(h 2) < (-1/8 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a35 : -(h 1) < (-5/39 : ℝ))
    (a37 : -(h 0) < (-3/20 : ℝ))
    (a42 : -(h 4) < (-1/9 : ℝ))
    (a48 : -(h 5) < (-2/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order3 + (2/13 : ℝ) * a24 + (1/13 : ℝ) * a27 + (2/13 : ℝ) * a35 + (2/13 : ℝ) * a37 + (4/13 : ℝ) * a42 + (2/13 : ℝ) * a48 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2947 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : -(h 2) < (-1/8 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a35 : -(h 1) < (-5/39 : ℝ))
    (a37 : -(h 0) < (-3/20 : ℝ))
    (a42 : -(h 4) < (-1/9 : ℝ))
    (a47 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a24 + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2946 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a37 : -(h 0) < (-3/20 : ℝ))
    (a42 : -(h 4) < (-1/9 : ℝ))
    (a46 : -(h 2) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order1 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a17 + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a42 + (1/3 : ℝ) * a46 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2945 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a40 : h 1 ≤ (7/54 : ℝ))
    (a45 : -(h 1) < (-5/38 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a40 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2944 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a24 : -(h 2) < (-1/8 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a35 : -(h 1) < (-5/39 : ℝ))
    (a42 : -(h 4) < (-1/9 : ℝ))
    (a44 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a17 + (1/6 : ℝ) * a24 + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a44 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2943 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a43 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2942 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : -(h 2) < (-1/8 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a37 : -(h 0) < (-3/20 : ℝ))
    (a40 : -(h 1) < (-7/54 : ℝ))
    (a46 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a24 + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a40 + (1/3 : ℝ) * a46 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2941 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : -(h 2) < (-1/8 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a32 : -(h 4) < (-4/37 : ℝ))
    (a37 : -(h 0) < (-3/20 : ℝ))
    (a40 : -(h 1) < (-7/54 : ℝ))
    (a45 : -(h 3) < (-5/43 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a24 + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a32 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a40 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2940 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : h 1 ≤ (2/15 : ℝ))
    (a44 : -(h 2) < (-3/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * _ctx.order1 + (1 : ℝ) * a23 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2939 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : h 1 ≤ (2/15 : ℝ))
    (a43 : -(h 1) < (-6/43 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a23 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2938 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : h 0 ≤ (2/13 : ℝ))
    (a42 : -(h 0) < (-5/31 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2937 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a41 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2936 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a24 : -(h 2) < (-1/8 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a35 : -(h 1) < (-5/39 : ℝ))
    (a37 : -(h 0) < (-3/20 : ℝ))
    (a40 : h 1 ≤ (7/54 : ℝ))
    (a42 : -(h 4) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_2943 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_2944 h delta _ctx _hno a17 a24 a27 a35 a42 f1
  by_cases p2 : h 1 ≤ (5/38 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/38 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_2945 h delta _ctx _hno a40 f2
  by_cases p3 : h 2 ≤ (3/23 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_2946 h delta _ctx _hno a17 a27 a37 a42 f3
  by_cases p4 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_2947 h delta _ctx _hno a24 a27 a35 a37 a42 f4
  by_cases p5 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_2948 h delta _ctx _hno a24 a27 a35 a37 a42 f5
  apply _hno 30
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (5/38 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_2935 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : -(h 2) < (-1/8 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a32 : -(h 4) < (-4/37 : ℝ))
    (a35 : -(h 1) < (-5/39 : ℝ))
    (a37 : -(h 0) < (-3/20 : ℝ))
    (a41 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a24 + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a32 + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a41 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2934 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : h 1 ≤ (2/15 : ℝ))
    (a24 : -(h 2) < (-1/8 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a32 : -(h 4) < (-4/37 : ℝ))
    (a34 : h 0 ≤ (2/13 : ℝ))
    (a37 : -(h 0) < (-3/20 : ℝ))
    (a40 : -(h 1) < (-7/54 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_2937 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (5/31 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/31 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_2938 h delta _ctx _hno a34 f1
  by_cases p2 : h 1 ≤ (6/43 : ℝ)
  swap
  · have f2 : -(h 1) < (-6/43 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_2939 h delta _ctx _hno a23 f2
  by_cases p3 : h 2 ≤ (3/22 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_2940 h delta _ctx _hno a23 f3
  by_cases p4 : h 3 ≤ (5/43 : ℝ)
  swap
  · have f4 : -(h 3) < (-5/43 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_2941 h delta _ctx _hno a24 a27 a32 a37 a40 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_2942 h delta _ctx _hno a24 a27 a37 a40 f5
  apply _hno 228
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (5/31 : ℝ)) ∧ (h 1 ≤ (6/43 : ℝ)) ∧ (h 2 ≤ (3/22 : ℝ)) ∧ (h 3 ≤ (5/43 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_2933 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : h 0 ≤ (2/13 : ℝ))
    (a39 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2932 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a38 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a38
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2931 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : -(h 2) < (-1/8 : ℝ))
    (a26 : -(h 0) < (-4/27 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a35 : -(h 1) < (-5/39 : ℝ))
    (a39 : -(h 4) < (-7/62 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a24 + (1/6 : ℝ) * a26 + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a35 + (1/3 : ℝ) * a39 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2930 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : h 1 ≤ (2/15 : ℝ))
    (a24 : -(h 2) < (-1/8 : ℝ))
    (a26 : -(h 0) < (-4/27 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a32 : -(h 4) < (-4/37 : ℝ))
    (a37 : h 0 ≤ (3/20 : ℝ))
    (a38 : -(h 1) < (-3/23 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_2949 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (5/31 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/31 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_2950 h delta _ctx _hno a37 f1
  by_cases p2 : h 1 ≤ (6/43 : ℝ)
  swap
  · have f2 : -(h 1) < (-6/43 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_2951 h delta _ctx _hno a23 f2
  by_cases p3 : h 2 ≤ (3/22 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_2952 h delta _ctx _hno a23 f3
  by_cases p4 : h 3 ≤ (5/43 : ℝ)
  swap
  · have f4 : -(h 3) < (-5/43 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_2953 h delta _ctx _hno a24 a26 a27 a32 a38 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_2954 h delta _ctx _hno a24 a26 a27 a37 a38 p4 f5
  apply _hno 228
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (5/31 : ℝ)) ∧ (h 1 ≤ (6/43 : ℝ)) ∧ (h 2 ≤ (3/22 : ℝ)) ∧ (h 3 ≤ (5/43 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_2929 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a23 : h 1 ≤ (2/15 : ℝ))
    (a24 : -(h 2) < (-1/8 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a32 : -(h 4) < (-4/37 : ℝ))
    (a34 : h 0 ≤ (2/13 : ℝ))
    (a35 : -(h 1) < (-5/39 : ℝ))
    (a37 : -(h 0) < (-3/20 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_2932 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_2933 h delta _ctx _hno a34 f1
  by_cases p2 : h 1 ≤ (7/54 : ℝ)
  swap
  · have f2 : -(h 1) < (-7/54 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_2934 h delta _ctx _hno a23 a24 a27 a32 a34 a37 f2
  by_cases p3 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_2935 h delta _ctx _hno a24 a27 a32 a35 a37 f3
  by_cases p4 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_2936 h delta _ctx _hno a17 a24 a27 a35 a37 p2 f4
  apply _hno 80
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (7/54 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_2928 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a36 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a36
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2927 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : -(h 2) < (-1/8 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a34 : -(h 0) < (-2/13 : ℝ))
    (a39 : -(h 4) < (-1/9 : ℝ))
    (a43 : -(h 3) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order1 + (1/6 : ℝ) * _ctx.min + (1/3 : ℝ) * a24 + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a34 + (1/6 : ℝ) * a39 + (1/6 : ℝ) * a43 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2926 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a24 : -(h 2) < (-1/8 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a34 : -(h 0) < (-2/13 : ℝ))
    (a39 : -(h 4) < (-1/9 : ℝ))
    (a42 : -(h 1) < (-4/31 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a17 + (1/6 : ℝ) * a24 + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a34 + (1/6 : ℝ) * a39 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2925 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a24 : -(h 2) < (-1/8 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a39 : -(h 4) < (-1/9 : ℝ))
    (a41 : -(h 0) < (-3/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order1 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a17 + (1/3 : ℝ) * a24 + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a39 + (1/6 : ℝ) * a41 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2924 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a40 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2923 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a24 : -(h 2) < (-1/8 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a34 : -(h 0) < (-2/13 : ℝ))
    (a39 : -(h 4) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_2924 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (3/19 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/19 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_2925 h delta _ctx _hno a17 a24 a27 a39 f1
  by_cases p2 : h 1 ≤ (4/31 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/31 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_2926 h delta _ctx _hno a17 a24 a27 a34 a39 f2
  by_cases p3 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f3 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_2927 h delta _ctx _hno a24 a27 a34 a39 f3
  apply _hno 154
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (4/31 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_2922 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : -(h 2) < (-1/8 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a32 : -(h 4) < (-4/37 : ℝ))
    (a34 : -(h 0) < (-2/13 : ℝ))
    (a38 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order1 + (1/6 : ℝ) * _ctx.min + (1/3 : ℝ) * a24 + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a32 + (1/6 : ℝ) * a34 + (1/6 : ℝ) * a38 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2921 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a24 : -(h 2) < (-1/8 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a32 : -(h 4) < (-4/37 : ℝ))
    (a34 : -(h 0) < (-2/13 : ℝ))
    (a37 : -(h 1) < (-7/54 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a17 + (1/6 : ℝ) * a24 + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a32 + (1/6 : ℝ) * a34 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2920 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a29 : h 0 ≤ (4/25 : ℝ))
    (a36 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a36
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2919 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a35 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a35
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2918 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : -(h 2) < (-1/8 : ℝ))
    (a26 : -(h 0) < (-4/27 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a36 : -(h 4) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order1 + (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/3 : ℝ) * a24 + (1/6 : ℝ) * a26 + (1/6 : ℝ) * a27 + (1/3 : ℝ) * a36 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2917 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a23 : h 1 ≤ (2/15 : ℝ))
    (a24 : -(h 2) < (-1/8 : ℝ))
    (a26 : -(h 0) < (-4/27 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a32 : -(h 4) < (-4/37 : ℝ))
    (a34 : h 0 ≤ (2/13 : ℝ))
    (a35 : -(h 1) < (-5/39 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_2928 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_2929 h delta _ctx _hno a17 a23 a24 a27 a32 a34 a35 f1
  by_cases p2 : h 1 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_2930 h delta _ctx _hno a23 a24 a26 a27 a32 p1 f2
  by_cases p3 : h 4 ≤ (7/62 : ℝ)
  swap
  · have f3 : -(h 4) < (-7/62 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_2931 h delta _ctx _hno a24 a26 a27 a35 f3
  apply _hno 216
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 4 ≤ (7/62 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_2916 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a24 : -(h 2) < (-1/8 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a29 : h 0 ≤ (4/25 : ℝ))
    (a32 : -(h 4) < (-4/37 : ℝ))
    (a34 : -(h 0) < (-2/13 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_2919 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_2920 h delta _ctx _hno a29 f1
  by_cases p2 : h 1 ≤ (7/54 : ℝ)
  swap
  · have f2 : -(h 1) < (-7/54 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_2921 h delta _ctx _hno a17 a24 a27 a32 a34 f2
  by_cases p3 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_2922 h delta _ctx _hno a24 a27 a32 a34 f3
  by_cases p4 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_2923 h delta _ctx _hno a17 a24 a27 a34 f4
  apply _hno 80
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (7/54 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_2915 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a33 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a33
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2914 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a20 : -(h 1) < (-1/8 : ℝ))
    (a24 : -(h 2) < (-1/8 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a29 : -(h 0) < (-4/25 : ℝ))
    (a34 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a17 + (1/6 : ℝ) * a20 + (1/6 : ℝ) * a24 + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a29 + (1/6 : ℝ) * a34 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2913 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : -(h 2) < (-1/8 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a29 : -(h 0) < (-4/25 : ℝ))
    (a33 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/11 : ℝ) * _ctx.order1 + (2/11 : ℝ) * _ctx.order4 + (4/11 : ℝ) * _ctx.min + (4/11 : ℝ) * a24 + (3/11 : ℝ) * a27 + (2/11 : ℝ) * a29 + (2/11 : ℝ) * a33 + (2/11 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2912 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a24 : -(h 2) < (-1/8 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a29 : -(h 0) < (-4/25 : ℝ))
    (a32 : -(h 1) < (-7/54 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/11 : ℝ) * _ctx.order4 + (4/11 : ℝ) * _ctx.min + (2/11 : ℝ) * a17 + (2/11 : ℝ) * a24 + (3/11 : ℝ) * a27 + (2/11 : ℝ) * a29 + (2/11 : ℝ) * a32 + (2/11 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2911 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a24 : -(h 2) < (-1/8 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a31 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/11 : ℝ) * _ctx.order1 + (2/11 : ℝ) * _ctx.order4 + (4/11 : ℝ) * _ctx.min + (2/11 : ℝ) * a17 + (4/11 : ℝ) * a24 + (3/11 : ℝ) * a27 + (2/11 : ℝ) * a31 + (2/11 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2910 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a30 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a30
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2909 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a23 : h 1 ≤ (2/15 : ℝ))
    (a24 : -(h 2) < (-1/8 : ℝ))
    (a26 : -(h 0) < (-4/27 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a29 : h 0 ≤ (4/25 : ℝ))
    (a32 : -(h 4) < (-4/37 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_2915 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_2916 h delta _ctx _hno a17 a24 a27 a29 a32 f1
  by_cases p2 : h 1 ≤ (5/39 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/39 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_2917 h delta _ctx _hno a17 a23 a24 a26 a27 a32 p1 f2
  by_cases p3 : h 4 ≤ (3/26 : ℝ)
  swap
  · have f3 : -(h 4) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_2918 h delta _ctx _hno a24 a26 a27 f3
  apply _hno 134
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (5/39 : ℝ)) ∧ (h 4 ≤ (3/26 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_2908 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a31 : -(h 3) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/17 : ℝ) * _ctx.order1 + (8/17 : ℝ) * _ctx.order2 + (4/17 : ℝ) * _ctx.min + (1/17 : ℝ) * _ctx.fail2 + (4/17 : ℝ) * a27 + (12/17 : ℝ) * a31 + (4/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2907 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : h 1 ≤ (2/15 : ℝ))
    (a30 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a23 + (1 : ℝ) * a30
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2906 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a20 : -(h 1) < (-1/8 : ℝ))
    (a24 : -(h 2) < (-1/8 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a29 : -(h 0) < (-4/25 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_2910 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_2911 h delta _ctx _hno a17 a24 a27 f1
  by_cases p2 : h 1 ≤ (7/54 : ℝ)
  swap
  · have f2 : -(h 1) < (-7/54 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_2912 h delta _ctx _hno a17 a24 a27 a29 f2
  by_cases p3 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_2913 h delta _ctx _hno a24 a27 a29 f3
  by_cases p4 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_2914 h delta _ctx _hno a17 a20 a24 a27 a29 f4
  apply _hno 80
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (7/54 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_2905 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a28 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a28
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2904 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a20 : -(h 1) < (-1/8 : ℝ))
    (a23 : h 1 ≤ (2/15 : ℝ))
    (a24 : -(h 2) < (-1/8 : ℝ))
    (a26 : -(h 0) < (-4/27 : ℝ))
    (a27 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a30 : -(h 4) < (-3/29 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_2961 h delta _ctx _hno a27 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_2962 h delta _ctx _hno a13 a17 a20 a23 a24 a27 a30 f1
  by_cases p2 : h 1 ≤ (5/39 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/39 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_2963 h delta _ctx _hno a13 a17 a23 a24 a26 a27 p1 f2
  by_cases p3 : h 4 ≤ (3/26 : ℝ)
  swap
  · have f3 : -(h 4) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_2964 h delta _ctx _hno a13 a20 a24 a26 a27 p2 f3
  apply _hno 134
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (5/39 : ℝ)) ∧ (h 4 ≤ (3/26 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_2903 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : h 1 ≤ (2/15 : ℝ))
    (a29 : -(h 1) < (-4/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a23 + (1 : ℝ) * a29
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2902 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : h 0 ≤ (1/6 : ℝ))
    (a28 : -(h 0) < (-5/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a15 + (1 : ℝ) * a28
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2901 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a20 : -(h 1) < (-1/8 : ℝ))
    (a23 : h 1 ≤ (2/15 : ℝ))
    (a24 : -(h 2) < (-1/8 : ℝ))
    (a26 : -(h 0) < (-4/27 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_2905 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (4/25 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/25 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_2906 h delta _ctx _hno a17 a20 a24 a27 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_2907 h delta _ctx _hno a23 f2
  by_cases p3 : h 3 ≤ (3/23 : ℝ)
  swap
  · have f3 : -(h 3) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_2908 h delta _ctx _hno a27 f3
  by_cases p4 : h 4 ≤ (4/37 : ℝ)
  swap
  · have f4 : -(h 4) < (-4/37 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_2909 h delta _ctx _hno a17 a23 a24 a26 a27 p1 f4
  apply _hno 24
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (3/23 : ℝ)) ∧ (h 4 ≤ (4/37 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_2900 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a20 : -(h 1) < (-1/8 : ℝ))
    (a23 : h 1 ≤ (2/15 : ℝ))
    (a24 : -(h 2) < (-1/8 : ℝ))
    (a26 : h 0 ≤ (4/27 : ℝ))
    (a27 : h 2 ≤ (7/54 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_3224 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (1/7 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_3225 h delta _ctx _hno a13 a20 a23 a24 a26 a27 a28 f1
  by_cases p2 : h 3 ≤ (5/42 : ℝ)
  swap
  · have f2 : -(h 3) < (-5/42 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_3226 h delta _ctx _hno a13 a20 a23 a24 a27 p1 f2
  apply _hno 42
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (1/7 : ℝ)) ∧ (h 3 ≤ (5/42 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem new_node_2899 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a23 : h 1 ≤ (2/15 : ℝ))
    (a26 : h 0 ≤ (4/27 : ℝ))
    (a27 : -(h 2) < (-7/54 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_3087 h delta _ctx _hno a23 a26 a27 f0
  by_cases p1 : h 0 ≤ (5/29 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/29 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_3088 h delta _ctx _hno a26 f1
  by_cases p2 : h 1 ≤ (4/29 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/29 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_3089 h delta _ctx _hno a23 f2
  by_cases p3 : h 4 ≤ (3/29 : ℝ)
  swap
  · have f3 : -(h 4) < (-3/29 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_3090 h delta _ctx _hno a13 a23 a26 a27 p0
  apply _hno 7
  change (((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)) ∧ (h 0 ≤ (5/29 : ℝ)) ∧ (h 1 ≤ (4/29 : ℝ)) ∧ (h 4 ≤ (3/29 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_2898 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a15 : h 0 ≤ (1/6 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a20 : -(h 1) < (-1/8 : ℝ))
    (a23 : h 1 ≤ (2/15 : ℝ))
    (a24 : -(h 2) < (-1/8 : ℝ))
    (a26 : -(h 0) < (-4/27 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_2901 h delta _ctx _hno a17 a20 a23 a24 a26 f0
  by_cases p1 : h 0 ≤ (5/29 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/29 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_2902 h delta _ctx _hno a15 f1
  by_cases p2 : h 1 ≤ (4/29 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/29 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_2903 h delta _ctx _hno a23 f2
  by_cases p3 : h 4 ≤ (3/29 : ℝ)
  swap
  · have f3 : -(h 4) < (-3/29 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_2904 h delta _ctx _hno a13 a17 a20 a23 a24 a26 p0 f3
  apply _hno 7
  change (((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)) ∧ (h 0 ≤ (5/29 : ℝ)) ∧ (h 1 ≤ (4/29 : ℝ)) ∧ (h 4 ≤ (3/29 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_2897 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a25
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2896 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a28 : -(h 3) < (-3/25 : ℝ))
    (a36 : -(h 4) < (-1/9 : ℝ))
    (a38 : -(h 0) < (-1/7 : ℝ))
    (a44 : -(h 5) < (-2/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order2 + (1/13 : ℝ) * a13 + (2/13 : ℝ) * a23 + (4/13 : ℝ) * a28 + (2/13 : ℝ) * a36 + (2/13 : ℝ) * a38 + (2/13 : ℝ) * a44 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2895 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a28 : -(h 3) < (-3/25 : ℝ))
    (a38 : -(h 0) < (-1/7 : ℝ))
    (a43 : -(h 4) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order2 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a23 + (1/3 : ℝ) * a28 + (1/6 : ℝ) * a38 + (1/6 : ℝ) * a43 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2894 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : h 2 ≤ (4/33 : ℝ))
    (a42 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2893 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a31 : h 1 ≤ (4/29 : ℝ))
    (a41 : -(h 1) < (-6/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2892 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a28 : -(h 3) < (-3/25 : ℝ))
    (a36 : -(h 4) < (-1/9 : ℝ))
    (a40 : -(h 0) < (-4/27 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order2 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a23 + (1/3 : ℝ) * a28 + (1/6 : ℝ) * a36 + (1/6 : ℝ) * a40 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2891 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a29 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a39 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2890 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : h 2 ≤ (4/33 : ℝ))
    (a39 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2889 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a27 : h 2 ≤ (4/33 : ℝ))
    (a28 : -(h 3) < (-3/25 : ℝ))
    (a29 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a31 : h 1 ≤ (4/29 : ℝ))
    (a36 : -(h 4) < (-1/9 : ℝ))
    (a38 : -(h 0) < (-1/7 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_2891 h delta _ctx _hno a29 f0
  by_cases p1 : h 0 ≤ (4/27 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/27 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_2892 h delta _ctx _hno a13 a23 a28 a36 f1
  by_cases p2 : h 1 ≤ (6/41 : ℝ)
  swap
  · have f2 : -(h 1) < (-6/41 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_2893 h delta _ctx _hno a31 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_2894 h delta _ctx _hno a27 f3
  by_cases p4 : h 4 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 4) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_2895 h delta _ctx _hno a13 a23 a28 a38 f4
  by_cases p5 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_2896 h delta _ctx _hno a13 a23 a28 a36 a38 f5
  apply _hno 61
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (4/27 : ℝ)) ∧ (h 1 ≤ (6/41 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_2888 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a29 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a37 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a37
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2887 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a28 : -(h 3) < (-3/25 : ℝ))
    (a36 : -(h 0) < (-3/20 : ℝ))
    (a42 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order2 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a23 + (1/3 : ℝ) * a28 + (1/6 : ℝ) * a36 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2886 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : h 2 ≤ (4/33 : ℝ))
    (a41 : -(h 3) < (-7/57 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * _ctx.order2 + (1 : ℝ) * a27 + (1 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2885 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : h 2 ≤ (4/33 : ℝ))
    (a40 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2884 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a31 : h 1 ≤ (4/29 : ℝ))
    (a39 : -(h 1) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2883 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : h 0 ≤ (5/33 : ℝ))
    (a38 : -(h 0) < (-5/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a25 + (1 : ℝ) * a38
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2882 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a29 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a37 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a37
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2881 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a28 : -(h 3) < (-3/25 : ℝ))
    (a34 : -(h 0) < (-4/27 : ℝ))
    (a38 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order2 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a23 + (1/3 : ℝ) * a28 + (1/6 : ℝ) * a34 + (1/6 : ℝ) * a38 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2880 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : h 2 ≤ (4/33 : ℝ))
    (a37 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a37
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2879 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a25 : h 0 ≤ (5/33 : ℝ))
    (a27 : h 2 ≤ (4/33 : ℝ))
    (a28 : -(h 3) < (-3/25 : ℝ))
    (a29 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a31 : h 1 ≤ (4/29 : ℝ))
    (a36 : -(h 0) < (-3/20 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_2882 h delta _ctx _hno a29 f0
  by_cases p1 : h 0 ≤ (5/33 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/33 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_2883 h delta _ctx _hno a25 f1
  by_cases p2 : h 1 ≤ (3/20 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_2884 h delta _ctx _hno a31 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_2885 h delta _ctx _hno a27 f3
  by_cases p4 : h 3 ≤ (7/57 : ℝ)
  swap
  · have f4 : -(h 3) < (-7/57 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_2886 h delta _ctx _hno a27 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_2887 h delta _ctx _hno a13 a23 a28 a36 f5
  apply _hno 119
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (5/33 : ℝ)) ∧ (h 1 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (7/57 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_2878 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a29 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a35 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a35
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2877 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a27 : h 2 ≤ (4/33 : ℝ))
    (a28 : -(h 3) < (-3/25 : ℝ))
    (a29 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a31 : h 1 ≤ (4/29 : ℝ))
    (a36 : -(h 4) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_2888 h delta _ctx _hno a29 f0
  by_cases p1 : h 0 ≤ (1/7 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_2889 h delta _ctx _hno a13 a23 a27 a28 a29 a31 a36 f1
  by_cases p2 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_2890 h delta _ctx _hno a27 f2
  apply _hno 84
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem new_node_2876 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : h 2 ≤ (4/33 : ℝ))
    (a35 : -(h 2) < (-7/54 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a35
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2875 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a25 : h 0 ≤ (5/33 : ℝ))
    (a27 : h 2 ≤ (4/33 : ℝ))
    (a28 : -(h 3) < (-3/25 : ℝ))
    (a29 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a31 : h 1 ≤ (4/29 : ℝ))
    (a34 : -(h 0) < (-4/27 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_2878 h delta _ctx _hno a29 f0
  by_cases p1 : h 0 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_2879 h delta _ctx _hno a13 a23 a25 a27 a28 a29 a31 f1
  by_cases p2 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_2880 h delta _ctx _hno a27 f2
  by_cases p3 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f3 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_2881 h delta _ctx _hno a13 a23 a28 a34 f3
  apply _hno 136
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

end RealPinwheel.WeakSevenBandData
