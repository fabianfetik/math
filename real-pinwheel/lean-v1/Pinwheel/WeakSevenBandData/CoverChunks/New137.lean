import Pinwheel.WeakSevenBandData.CoverChunks.New136

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem new_node_2154 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a25 : -(h 0) < (-5/33 : ℝ))
    (a33 : -(h 1) < (-3/22 : ℝ))
    (a42 : -(h 4) < (-6/55 : ℝ))
    (a47 : -(h 3) < (-7/62 : ℝ))
    (a51 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * a51 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2153 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a25 : -(h 0) < (-5/33 : ℝ))
    (a37 : -(h 2) < (-3/25 : ℝ))
    (a42 : -(h 4) < (-6/55 : ℝ))
    (a47 : -(h 3) < (-7/62 : ℝ))
    (a50 : -(h 1) < (-4/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * a50 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2152 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a35 : h 0 ≤ (2/13 : ℝ))
    (a49 : -(h 0) < (-5/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a35 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2151 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ))
    (a48 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2150 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a25 : -(h 0) < (-5/33 : ℝ))
    (a33 : -(h 1) < (-3/22 : ℝ))
    (a37 : -(h 2) < (-3/25 : ℝ))
    (a42 : -(h 4) < (-6/55 : ℝ))
    (a48 : -(h 5) < (-2/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/13 : ℝ) * a13 + (2/13 : ℝ) * a17 + (2/13 : ℝ) * a25 + (2/13 : ℝ) * a33 + (2/13 : ℝ) * a37 + (2/13 : ℝ) * a42 + (2/13 : ℝ) * a48 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2149 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a25 : -(h 0) < (-5/33 : ℝ))
    (a33 : -(h 1) < (-3/22 : ℝ))
    (a34 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ))
    (a35 : h 0 ≤ (2/13 : ℝ))
    (a37 : -(h 2) < (-3/25 : ℝ))
    (a42 : -(h 4) < (-6/55 : ℝ))
    (a47 : -(h 3) < (-7/62 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_2151 h delta _ctx _hno a34 f0
  by_cases p1 : h 0 ≤ (5/29 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/29 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_2152 h delta _ctx _hno a35 f1
  by_cases p2 : h 1 ≤ (4/29 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/29 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_2153 h delta _ctx _hno a13 a25 a37 a42 a47 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_2154 h delta _ctx _hno a13 a25 a33 a42 a47 f3
  by_cases p4 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_2155 h delta _ctx _hno a13 a25 a33 a37 a42 f4
  by_cases p5 : h 5 ≤ (3/29 : ℝ)
  swap
  · have f5 : -(h 5) < (-3/29 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_2156 h delta _ctx _hno a13 a25 a33 a37 a42 a47 f5
  apply _hno 89
  change (((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)) ∧ (h 0 ≤ (5/29 : ℝ)) ∧ (h 1 ≤ (4/29 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (3/29 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_2148 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a29 : h 2 ≤ (1/8 : ℝ))
    (a46 : -(h 2) < (-4/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2147 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a45 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2146 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a33 : -(h 1) < (-3/22 : ℝ))
    (a37 : -(h 2) < (-3/25 : ℝ))
    (a42 : -(h 4) < (-6/55 : ℝ))
    (a44 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a17 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a44 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2145 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-11/52 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2144 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a25 : -(h 0) < (-5/33 : ℝ))
    (a30 : -(h 4) < (-3/28 : ℝ))
    (a33 : -(h 1) < (-3/22 : ℝ))
    (a37 : -(h 2) < (-3/25 : ℝ))
    (a43 : -(h 5) < (-3/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/13 : ℝ) * a13 + (2/13 : ℝ) * a17 + (2/13 : ℝ) * a25 + (2/13 : ℝ) * a30 + (2/13 : ℝ) * a33 + (2/13 : ℝ) * a37 + (2/13 : ℝ) * a43 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2143 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a25 : -(h 0) < (-5/33 : ℝ))
    (a29 : h 2 ≤ (1/8 : ℝ))
    (a33 : -(h 1) < (-3/22 : ℝ))
    (a34 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ))
    (a35 : h 0 ≤ (2/13 : ℝ))
    (a37 : -(h 2) < (-3/25 : ℝ))
    (a42 : -(h 4) < (-6/55 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (11/52 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-11/52 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_2145 h delta _ctx _hno a34 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_2146 h delta _ctx _hno a13 a17 a33 a37 a42 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_2147 h delta _ctx _hno a16 f2
  by_cases p3 : h 2 ≤ (4/29 : ℝ)
  swap
  · have f3 : -(h 2) < (-4/29 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_2148 h delta _ctx _hno a29 f3
  by_cases p4 : h 3 ≤ (7/62 : ℝ)
  swap
  · have f4 : -(h 3) < (-7/62 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_2149 h delta _ctx _hno a13 a25 a33 a34 a35 a37 a42 f4
  by_cases p5 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_2150 h delta _ctx _hno a13 a17 a25 a33 a37 a42 f5
  apply _hno 174
  change (((2 : ℝ) * (delta)) ≤ (11/52 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (4/29 : ℝ)) ∧ (h 3 ≤ (7/62 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_2142 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a25 : -(h 0) < (-5/33 : ℝ))
    (a30 : -(h 4) < (-3/28 : ℝ))
    (a33 : -(h 1) < (-3/22 : ℝ))
    (a41 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a17 + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a41 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2141 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a40 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2140 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a35 : h 0 ≤ (2/13 : ℝ))
    (a39 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a35 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2139 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ))
    (a38 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a38
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2138 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a33 : -(h 1) < (-3/22 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a53 : -(h 5) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.order3 + (12/29 : ℝ) * _ctx.order4 + (6/29 : ℝ) * _ctx.lower + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a33 + (4/29 : ℝ) * a35 + (18/29 : ℝ) * a53 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2137 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a46 : h 3 ≤ (4/35 : ℝ))
    (a52 : -(h 3) < (-5/43 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a46 + (1 : ℝ) * a52
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2136 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a39 : h 2 ≤ (5/43 : ℝ))
    (a51 : -(h 2) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a39 + (1 : ℝ) * a51
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2135 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a44 : h 1 ≤ (4/29 : ℝ))
    (a50 : -(h 1) < (-5/32 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a44 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2134 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a33 : -(h 1) < (-3/22 : ℝ))
    (a41 : -(h 4) < (-1/9 : ℝ))
    (a47 : -(h 5) < (-3/29 : ℝ))
    (a49 : -(h 0) < (-8/51 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/16 : ℝ) * _ctx.order3 + (1/32 : ℝ) * _ctx.fail1 + (3/32 : ℝ) * a13 + (3/16 : ℝ) * a33 + (3/8 : ℝ) * a41 + (3/16 : ℝ) * a47 + (1/8 : ℝ) * a49 + (3/16 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2133 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ))
    (a48 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2132 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a44 : -(h 1) < (-4/29 : ℝ))
    (a50 : -(h 5) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.order3 + (12/29 : ℝ) * _ctx.order4 + (6/29 : ℝ) * _ctx.lower + (1/29 : ℝ) * _ctx.fail1 + (4/29 : ℝ) * a35 + (6/29 : ℝ) * a44 + (18/29 : ℝ) * a50 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2131 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a41 : -(h 4) < (-1/9 : ℝ))
    (a44 : -(h 1) < (-4/29 : ℝ))
    (a49 : -(h 3) < (-5/43 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.min + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a13 + (4/29 : ℝ) * a35 + (6/29 : ℝ) * a41 + (6/29 : ℝ) * a44 + (6/29 : ℝ) * a49 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2130 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a39 : h 2 ≤ (5/43 : ℝ))
    (a48 : -(h 2) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a39 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2129 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a47 : -(h 1) < (-5/32 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2128 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a41 : -(h 4) < (-1/9 : ℝ))
    (a44 : -(h 1) < (-4/29 : ℝ))
    (a46 : -(h 0) < (-8/51 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.order3 + (6/29 : ℝ) * _ctx.min + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a13 + (12/29 : ℝ) * a41 + (6/29 : ℝ) * a44 + (4/29 : ℝ) * a46 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2127 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ))
    (a45 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2126 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a33 : -(h 1) < (-3/22 : ℝ))
    (a34 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a39 : h 2 ≤ (5/43 : ℝ))
    (a41 : -(h 4) < (-1/9 : ℝ))
    (a44 : h 1 ≤ (4/29 : ℝ))
    (a46 : h 3 ≤ (4/35 : ℝ))
    (a47 : -(h 5) < (-3/29 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_2133 h delta _ctx _hno a34 f0
  by_cases p1 : h 0 ≤ (8/51 : ℝ)
  swap
  · have f1 : -(h 0) < (-8/51 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_2134 h delta _ctx _hno a13 a33 a41 a47 f1
  by_cases p2 : h 1 ≤ (5/32 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/32 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_2135 h delta _ctx _hno a44 f2
  by_cases p3 : h 2 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_2136 h delta _ctx _hno a39 f3
  by_cases p4 : h 3 ≤ (5/43 : ℝ)
  swap
  · have f4 : -(h 3) < (-5/43 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_2137 h delta _ctx _hno a46 f4
  by_cases p5 : h 5 ≤ (3/26 : ℝ)
  swap
  · have f5 : -(h 5) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_2138 h delta _ctx _hno a33 a35 f5
  apply _hno 226
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (8/51 : ℝ)) ∧ (h 1 ≤ (5/32 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 3 ≤ (5/43 : ℝ)) ∧ (h 5 ≤ (3/26 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_2125 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a33 : -(h 1) < (-3/22 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a41 : -(h 4) < (-1/9 : ℝ))
    (a46 : -(h 3) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.min + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a13 + (6/29 : ℝ) * a33 + (4/29 : ℝ) * a35 + (6/29 : ℝ) * a41 + (6/29 : ℝ) * a46 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2124 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a39 : h 2 ≤ (5/43 : ℝ))
    (a45 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a39 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2123 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a34 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a39 : h 2 ≤ (5/43 : ℝ))
    (a41 : -(h 4) < (-1/9 : ℝ))
    (a44 : -(h 1) < (-4/29 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_2127 h delta _ctx _hno a34 f0
  by_cases p1 : h 0 ≤ (8/51 : ℝ)
  swap
  · have f1 : -(h 0) < (-8/51 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_2128 h delta _ctx _hno a13 a41 a44 f1
  by_cases p2 : h 1 ≤ (5/32 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/32 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_2129 h delta _ctx _hno a16 f2
  by_cases p3 : h 2 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_2130 h delta _ctx _hno a39 f3
  by_cases p4 : h 3 ≤ (5/43 : ℝ)
  swap
  · have f4 : -(h 3) < (-5/43 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_2131 h delta _ctx _hno a13 a35 a41 a44 f4
  by_cases p5 : h 5 ≤ (3/26 : ℝ)
  swap
  · have f5 : -(h 5) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_2132 h delta _ctx _hno a35 a44 f5
  apply _hno 226
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (8/51 : ℝ)) ∧ (h 1 ≤ (5/32 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 3 ≤ (5/43 : ℝ)) ∧ (h 5 ≤ (3/26 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_2122 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : h 0 ≤ (4/25 : ℝ))
    (a43 : -(h 0) < (-5/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2121 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ))
    (a42 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2120 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a33 : -(h 1) < (-3/22 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a40 : -(h 3) < (-3/26 : ℝ))
    (a46 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.min + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a13 + (6/29 : ℝ) * a33 + (4/29 : ℝ) * a35 + (6/29 : ℝ) * a40 + (6/29 : ℝ) * a46 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2119 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a39 : h 2 ≤ (5/43 : ℝ))
    (a45 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * _ctx.order2 + (1 : ℝ) * a39 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2118 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a39 : h 2 ≤ (5/43 : ℝ))
    (a44 : -(h 2) < (-5/42 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a39 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2117 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a43 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2116 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : h 0 ≤ (4/25 : ℝ))
    (a42 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2115 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2114 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a33 : -(h 1) < (-3/22 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a39 : -(h 2) < (-5/43 : ℝ))
    (a45 : -(h 4) < (-1/9 : ℝ))
    (a51 : -(h 5) < (-3/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order3 + (1/13 : ℝ) * a13 + (2/13 : ℝ) * a33 + (2/13 : ℝ) * a35 + (2/13 : ℝ) * a39 + (4/13 : ℝ) * a45 + (2/13 : ℝ) * a51 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2113 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a33 : -(h 1) < (-3/22 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a39 : -(h 2) < (-5/43 : ℝ))
    (a45 : -(h 4) < (-1/9 : ℝ))
    (a50 : -(h 3) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a39 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a50 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2112 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a43 : h 2 ≤ (2/17 : ℝ))
    (a49 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a43 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2111 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a39 : -(h 2) < (-5/43 : ℝ))
    (a45 : -(h 4) < (-1/9 : ℝ))
    (a48 : -(h 1) < (-4/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a39 + (1/3 : ℝ) * a45 + (1/6 : ℝ) * a48 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2110 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : h 0 ≤ (4/25 : ℝ))
    (a47 : -(h 0) < (-5/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2109 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ))
    (a46 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2108 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a33 : -(h 1) < (-3/22 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a39 : -(h 2) < (-5/43 : ℝ))
    (a44 : -(h 3) < (-3/26 : ℝ))
    (a50 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a39 + (1/6 : ℝ) * a44 + (1/6 : ℝ) * a50 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2107 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a30 : -(h 4) < (-3/28 : ℝ))
    (a33 : -(h 1) < (-3/22 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a49 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order2 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a35 + (1/3 : ℝ) * a49 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2106 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a43 : h 2 ≤ (2/17 : ℝ))
    (a48 : -(h 2) < (-5/42 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a43 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2105 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a47 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2104 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : h 0 ≤ (4/25 : ℝ))
    (a46 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2103 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ))
    (a45 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2102 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a33 : -(h 1) < (-3/22 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a49 : -(h 5) < (-3/29 : ℝ))
    (a53 : -(h 2) < (-5/42 : ℝ))
    (a59 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order3 + (1/13 : ℝ) * a13 + (2/13 : ℝ) * a33 + (2/13 : ℝ) * a35 + (2/13 : ℝ) * a49 + (2/13 : ℝ) * a53 + (4/13 : ℝ) * a59 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2101 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a30 : -(h 4) < (-3/28 : ℝ))
    (a33 : -(h 1) < (-3/22 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a49 : -(h 5) < (-3/29 : ℝ))
    (a53 : -(h 2) < (-5/42 : ℝ))
    (a58 : -(h 3) < (-6/53 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/13 : ℝ) * a13 + (2/13 : ℝ) * a30 + (2/13 : ℝ) * a33 + (2/13 : ℝ) * a35 + (2/13 : ℝ) * a49 + (2/13 : ℝ) * a53 + (2/13 : ℝ) * a58 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2100 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a30 : -(h 4) < (-3/28 : ℝ))
    (a33 : -(h 1) < (-3/22 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a49 : -(h 5) < (-3/29 : ℝ))
    (a57 : -(h 2) < (-4/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/13 : ℝ) * a13 + (2/13 : ℝ) * a17 + (2/13 : ℝ) * a30 + (2/13 : ℝ) * a33 + (2/13 : ℝ) * a35 + (2/13 : ℝ) * a49 + (2/13 : ℝ) * a57 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2099 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a46 : h 1 ≤ (4/29 : ℝ))
    (a56 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a46 + (1 : ℝ) * a56
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2098 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a30 : -(h 4) < (-3/28 : ℝ))
    (a33 : -(h 1) < (-3/22 : ℝ))
    (a49 : -(h 5) < (-3/29 : ℝ))
    (a53 : -(h 2) < (-5/42 : ℝ))
    (a55 : -(h 0) < (-5/32 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/13 : ℝ) * a13 + (2/13 : ℝ) * a17 + (2/13 : ℝ) * a30 + (2/13 : ℝ) * a33 + (2/13 : ℝ) * a49 + (2/13 : ℝ) * a53 + (2/13 : ℝ) * a55 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2097 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ))
    (a54 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a54
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2096 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a33 : -(h 1) < (-3/22 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a43 : -(h 2) < (-2/17 : ℝ))
    (a49 : -(h 5) < (-3/29 : ℝ))
    (a55 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order3 + (1/13 : ℝ) * a13 + (2/13 : ℝ) * a33 + (2/13 : ℝ) * a35 + (2/13 : ℝ) * a43 + (2/13 : ℝ) * a49 + (4/13 : ℝ) * a55 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2095 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a48 : h 3 ≤ (4/35 : ℝ))
    (a54 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a48 + (1 : ℝ) * a54
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2094 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a30 : -(h 4) < (-3/28 : ℝ))
    (a33 : -(h 1) < (-3/22 : ℝ))
    (a34 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a46 : h 1 ≤ (4/29 : ℝ))
    (a49 : -(h 5) < (-3/29 : ℝ))
    (a53 : -(h 2) < (-5/42 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_2097 h delta _ctx _hno a34 f0
  by_cases p1 : h 0 ≤ (5/32 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/32 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_2098 h delta _ctx _hno a13 a17 a30 a33 a49 a53 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_2099 h delta _ctx _hno a46 f2
  by_cases p3 : h 2 ≤ (4/33 : ℝ)
  swap
  · have f3 : -(h 2) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_2100 h delta _ctx _hno a13 a17 a30 a33 a35 a49 f3
  by_cases p4 : h 3 ≤ (6/53 : ℝ)
  swap
  · have f4 : -(h 3) < (-6/53 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_2101 h delta _ctx _hno a13 a30 a33 a35 a49 a53 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_2102 h delta _ctx _hno a13 a33 a35 a49 a53 f5
  apply _hno 222
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (5/32 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (4/33 : ℝ)) ∧ (h 3 ≤ (6/53 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_2093 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a46 : h 1 ≤ (4/29 : ℝ))
    (a52 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a46 + (1 : ℝ) * a52
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2092 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : h 0 ≤ (4/25 : ℝ))
    (a51 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a51
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2091 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ))
    (a50 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2090 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a33 : -(h 1) < (-3/22 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a43 : -(h 2) < (-2/17 : ℝ))
    (a53 : -(h 3) < (-7/61 : ℝ))
    (a59 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a43 + (1/6 : ℝ) * a53 + (1/6 : ℝ) * a59 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2089 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a30 : -(h 4) < (-3/28 : ℝ))
    (a33 : -(h 1) < (-3/22 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a43 : -(h 2) < (-2/17 : ℝ))
    (a58 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a43 + (1/6 : ℝ) * a58 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2088 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a30 : -(h 4) < (-3/28 : ℝ))
    (a33 : -(h 1) < (-3/22 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a53 : -(h 3) < (-7/61 : ℝ))
    (a57 : -(h 2) < (-5/42 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a53 + (1/6 : ℝ) * a57 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2087 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a46 : h 1 ≤ (4/29 : ℝ))
    (a56 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a46 + (1 : ℝ) * a56
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2086 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : h 0 ≤ (4/25 : ℝ))
    (a55 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a55
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2085 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ))
    (a54 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a54
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2084 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a33 : -(h 1) < (-3/22 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a43 : -(h 2) < (-2/17 : ℝ))
    (a48 : -(h 3) < (-4/35 : ℝ))
    (a54 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a43 + (1/6 : ℝ) * a48 + (1/6 : ℝ) * a54 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2083 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a27 : h 0 ≤ (4/25 : ℝ))
    (a30 : -(h 4) < (-3/28 : ℝ))
    (a33 : -(h 1) < (-3/22 : ℝ))
    (a34 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a43 : -(h 2) < (-2/17 : ℝ))
    (a46 : h 1 ≤ (4/29 : ℝ))
    (a53 : -(h 3) < (-7/61 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_2085 h delta _ctx _hno a34 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_2086 h delta _ctx _hno a27 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_2087 h delta _ctx _hno a46 f2
  by_cases p3 : h 2 ≤ (5/42 : ℝ)
  swap
  · have f3 : -(h 2) < (-5/42 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_2088 h delta _ctx _hno a13 a30 a33 a35 a53 f3
  by_cases p4 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_2089 h delta _ctx _hno a13 a30 a33 a35 a43 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_2090 h delta _ctx _hno a13 a33 a35 a43 a53 f5
  apply _hno 225
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (5/42 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_2082 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a30 : -(h 4) < (-3/28 : ℝ))
    (a33 : -(h 1) < (-3/22 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a48 : -(h 3) < (-4/35 : ℝ))
    (a52 : -(h 2) < (-22/185 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a48 + (1/6 : ℝ) * a52 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2081 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a46 : h 1 ≤ (4/29 : ℝ))
    (a51 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a46 + (1 : ℝ) * a51
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2080 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : h 0 ≤ (4/25 : ℝ))
    (a50 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2079 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ))
    (a49 : ((-2 : ℝ) * (delta)) < (-13/63 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2078 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a46 : -(h 1) < (-4/29 : ℝ))
    (a50 : -(h 2) < (-22/185 : ℝ))
    (a56 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a46 + (1/6 : ℝ) * a50 + (1/3 : ℝ) * a56 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2077 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a30 : -(h 4) < (-3/28 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a46 : -(h 1) < (-4/29 : ℝ))
    (a50 : -(h 2) < (-22/185 : ℝ))
    (a55 : -(h 3) < (-6/53 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a46 + (1/6 : ℝ) * a50 + (1/6 : ℝ) * a55 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2076 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a30 : -(h 4) < (-3/28 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    (a46 : -(h 1) < (-4/29 : ℝ))
    (a54 : -(h 2) < (-4/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a17 + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a46 + (1/6 : ℝ) * a54 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_2075 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a53 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a53
  exact (lt_irrefl (0 : ℝ)) hbad

end RealPinwheel.WeakSevenBandData
