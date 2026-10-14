import Pinwheel.WeakSevenBandData.CoverChunks.Upper051

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem upper_node_147 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a16 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a20 : -(h 1) < (-1/8 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (9/29 : ℝ) * _ctx.order3 + (18/29 : ℝ) * _ctx.order4 + (26/29 : ℝ) * _ctx.min + (3/58 : ℝ) * _ctx.fail1 + (1/29 : ℝ) * a16 + (9/29 : ℝ) * a20 + (35/58 : ℝ) * a34 + (9/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_146 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a16 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a17 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a20 : -(h 1) < (-1/8 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a33 : -(h 5) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_147 h delta _ctx _hno a16 a20 f0
  by_cases p1 : h 0 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_148 h delta _ctx _hno a17 a20 a24 a28 a33 f1
  by_cases p2 : h 1 ≤ (5/39 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/39 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_149 h delta _ctx _hno a16 a17 a24 a28 a33 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_150 h delta _ctx _hno a16 a17 a24 a28 a33 f3
  by_cases p4 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_151 h delta _ctx _hno a16 a17 a20 a28 a33 f4
  apply _hno 49
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 1 ≤ (5/39 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_145 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a16 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a17 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a20 : -(h 1) < (-1/8 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a32 : -(h 3) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/19 : ℝ) * _ctx.min + (3/76 : ℝ) * _ctx.fail1 + (1/38 : ℝ) * a16 + (17/76 : ℝ) * a17 + (9/38 : ℝ) * a20 + (9/38 : ℝ) * a28 + (9/38 : ℝ) * a32 + (9/38 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_144 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a16 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a17 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a31 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/19 : ℝ) * _ctx.min + (3/76 : ℝ) * _ctx.fail1 + (1/38 : ℝ) * a16 + (17/76 : ℝ) * a17 + (9/38 : ℝ) * a24 + (9/38 : ℝ) * a28 + (9/38 : ℝ) * a31 + (9/38 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_143 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : h 0 ≤ (3/20 : ℝ))
    (a30 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a19 + (1 : ℝ) * a30
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_142 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a16 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a20 : -(h 1) < (-1/8 : ℝ))
    (a29 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (9/29 : ℝ) * _ctx.order3 + (18/29 : ℝ) * _ctx.order4 + (26/29 : ℝ) * _ctx.min + (3/58 : ℝ) * _ctx.fail1 + (1/29 : ℝ) * a16 + (9/29 : ℝ) * a20 + (35/58 : ℝ) * a29 + (9/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_141 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a16 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a17 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a19 : h 0 ≤ (3/20 : ℝ))
    (a20 : -(h 1) < (-1/8 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_142 h delta _ctx _hno a16 a20 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_143 h delta _ctx _hno a19 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_144 h delta _ctx _hno a16 a17 a24 a28 f2
  by_cases p3 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f3 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_145 h delta _ctx _hno a16 a17 a20 a28 f3
  by_cases p4 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_146 h delta _ctx _hno a16 a17 a20 a24 a28 f4
  apply _hno 19
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_140 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a16 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a17 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a27 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (12/55 : ℝ) * _ctx.order1 + (12/55 : ℝ) * _ctx.order4 + (2/5 : ℝ) * _ctx.min + (2/55 : ℝ) * a16 + (17/55 : ℝ) * a17 + (12/55 : ℝ) * a24 + (24/55 : ℝ) * a27 + (12/55 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_139 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : h 0 ≤ (3/20 : ℝ))
    (a26 : -(h 0) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a19 + (1 : ℝ) * a26
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_138 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a16 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a20 : -(h 1) < (-1/8 : ℝ))
    (a25 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (9/29 : ℝ) * _ctx.order3 + (18/29 : ℝ) * _ctx.order4 + (26/29 : ℝ) * _ctx.min + (3/58 : ℝ) * _ctx.fail1 + (1/29 : ℝ) * a16 + (9/29 : ℝ) * a20 + (35/58 : ℝ) * a25 + (9/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_137 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a16 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a17 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a19 : h 0 ≤ (3/20 : ℝ))
    (a20 : -(h 1) < (-1/8 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_138 h delta _ctx _hno a16 a20 f0
  by_cases p1 : h 0 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_139 h delta _ctx _hno a19 f1
  by_cases p2 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_140 h delta _ctx _hno a16 a17 a24 f2
  by_cases p3 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f3 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_141 h delta _ctx _hno a16 a17 a19 a20 a24 f3
  apply _hno 8
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_136 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a16 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a17 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a23 : -(h 1) < (-5/36 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (9/29 : ℝ) * _ctx.order3 + (18/29 : ℝ) * _ctx.order4 + (26/29 : ℝ) * _ctx.min + (3/58 : ℝ) * _ctx.fail1 + (1/29 : ℝ) * a16 + (35/58 : ℝ) * a17 + (9/29 : ℝ) * a23 + (9/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_135 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : h 0 ≤ (3/20 : ℝ))
    (a22 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a19 + (1 : ℝ) * a22
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_134 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a16 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a20 : -(h 1) < (-1/8 : ℝ))
    (a21 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (9/29 : ℝ) * _ctx.order3 + (18/29 : ℝ) * _ctx.order4 + (26/29 : ℝ) * _ctx.min + (3/58 : ℝ) * _ctx.fail1 + (1/29 : ℝ) * a16 + (9/29 : ℝ) * a20 + (35/58 : ℝ) * a21 + (9/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_133 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a16 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a17 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a19 : h 0 ≤ (3/20 : ℝ))
    (a20 : -(h 1) < (-1/8 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_134 h delta _ctx _hno a16 a20 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_135 h delta _ctx _hno a19 f1
  by_cases p2 : h 1 ≤ (5/36 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/36 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_136 h delta _ctx _hno a16 a17 f2
  by_cases p3 : h 3 ≤ (1/9 : ℝ)
  swap
  · have f3 : -(h 3) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_137 h delta _ctx _hno a16 a17 a19 a20 f3
  apply _hno 0
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (5/36 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_132 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a19 : -(h 0) < (-3/20 : ℝ))
    (a26 : -(h 1) < (-13/108 : ℝ))
    (a30 : -(h 4) < (-13/112 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.order3 + (6/29 : ℝ) * _ctx.min + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a17 + (4/29 : ℝ) * a19 + (6/29 : ℝ) * a26 + (12/29 : ℝ) * a30 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_131 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a19 : -(h 0) < (-3/20 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a29 : -(h 1) < (-1/8 : ℝ))
    (a34 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/16 : ℝ) * _ctx.order4 + (1/32 : ℝ) * _ctx.fail1 + (3/32 : ℝ) * a17 + (1/8 : ℝ) * a19 + (3/16 : ℝ) * a23 + (3/16 : ℝ) * a29 + (3/8 : ℝ) * a34 + (3/16 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_130 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a19 : -(h 0) < (-3/20 : ℝ))
    (a29 : -(h 1) < (-1/8 : ℝ))
    (a33 : -(h 3) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/13 : ℝ) * _ctx.order4 + (6/13 : ℝ) * _ctx.min + (1/26 : ℝ) * _ctx.fail1 + (9/26 : ℝ) * a17 + (2/13 : ℝ) * a19 + (3/13 : ℝ) * a29 + (3/13 : ℝ) * a33 + (3/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_129 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a19 : -(h 0) < (-3/20 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a32 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/13 : ℝ) * _ctx.order4 + (6/13 : ℝ) * _ctx.min + (1/26 : ℝ) * _ctx.fail1 + (9/26 : ℝ) * a17 + (2/13 : ℝ) * a19 + (3/13 : ℝ) * a23 + (3/13 : ℝ) * a32 + (3/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_128 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a29 : -(h 1) < (-1/8 : ℝ))
    (a31 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/13 : ℝ) * _ctx.order4 + (6/13 : ℝ) * _ctx.min + (1/26 : ℝ) * _ctx.fail1 + (9/26 : ℝ) * a17 + (3/13 : ℝ) * a23 + (3/13 : ℝ) * a29 + (2/13 : ℝ) * a31 + (3/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_127 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : -(h 0) < (-3/20 : ℝ))
    (a29 : -(h 1) < (-1/8 : ℝ))
    (a30 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.order3 + (12/23 : ℝ) * _ctx.order4 + (18/23 : ℝ) * _ctx.min + (1/23 : ℝ) * _ctx.fail1 + (4/23 : ℝ) * a19 + (6/23 : ℝ) * a29 + (12/23 : ℝ) * a30 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_126 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a19 : -(h 0) < (-3/20 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a29 : -(h 1) < (-1/8 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_127 h delta _ctx _hno a19 a29 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_128 h delta _ctx _hno a17 a23 a29 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_129 h delta _ctx _hno a17 a19 a23 f2
  by_cases p3 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f3 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_130 h delta _ctx _hno a17 a19 a29 f3
  by_cases p4 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_131 h delta _ctx _hno a17 a19 a23 a29 f4
  apply _hno 19
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_125 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : h 0 ≤ (2/13 : ℝ))
    (a28 : -(h 0) < (-3/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a25 + (1 : ℝ) * a28
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_124 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a18 + (1 : ℝ) * a27
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_123 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a18 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ))
    (a19 : -(h 0) < (-3/20 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a25 : h 0 ≤ (2/13 : ℝ))
    (a26 : -(h 1) < (-13/108 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_124 h delta _ctx _hno a18 f0
  by_cases p1 : h 0 ≤ (3/19 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/19 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_125 h delta _ctx _hno a25 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_126 h delta _ctx _hno a17 a19 a23 f2
  by_cases p3 : h 4 ≤ (13/112 : ℝ)
  swap
  · have f3 : -(h 4) < (-13/112 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_132 h delta _ctx _hno a17 a19 a26 f3
  apply _hno 4
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (13/112 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_122 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a25 : -(h 0) < (-2/13 : ℝ))
    (a29 : -(h 4) < (-13/112 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/11 : ℝ) * _ctx.order1 + (3/11 : ℝ) * _ctx.order3 + (3/11 : ℝ) * _ctx.min + (1/11 : ℝ) * _ctx.fail1 + (3/11 : ℝ) * a17 + (1/11 : ℝ) * a25 + (6/11 : ℝ) * a29 + (3/11 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_121 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a25 : -(h 0) < (-2/13 : ℝ))
    (a28 : -(h 1) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/13 : ℝ) * _ctx.order4 + (6/13 : ℝ) * _ctx.min + (1/26 : ℝ) * _ctx.fail1 + (9/26 : ℝ) * a17 + (3/13 : ℝ) * a23 + (2/13 : ℝ) * a25 + (3/13 : ℝ) * a28 + (3/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_120 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a27 : -(h 0) < (-3/19 : ℝ))
    (a30 : -(h 1) < (-5/42 : ℝ))
    (a36 : -(h 4) < (-1/9 : ℝ))
    (a41 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/32 : ℝ) * _ctx.fail1 + (3/32 : ℝ) * a17 + (3/16 : ℝ) * a23 + (1/8 : ℝ) * a27 + (3/16 : ℝ) * a30 + (3/16 : ℝ) * a36 + (3/16 : ℝ) * a41 + (3/16 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_119 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a34 : h 2 ≤ (4/35 : ℝ))
    (a40 : -(h 2) < (-7/60 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_118 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a27 : -(h 0) < (-3/19 : ℝ))
    (a36 : -(h 4) < (-1/9 : ℝ))
    (a39 : -(h 1) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.min + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a17 + (6/29 : ℝ) * a23 + (4/29 : ℝ) * a27 + (6/29 : ℝ) * a36 + (6/29 : ℝ) * a39 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_117 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a30 : -(h 1) < (-5/42 : ℝ))
    (a36 : -(h 4) < (-1/9 : ℝ))
    (a38 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.min + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a17 + (6/29 : ℝ) * a23 + (6/29 : ℝ) * a30 + (6/29 : ℝ) * a36 + (4/29 : ℝ) * a38 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_116 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ))
    (a37 : ((-2 : ℝ) * (delta)) < (-3/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a18 + (1 : ℝ) * a37
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_115 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a18 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a27 : -(h 0) < (-3/19 : ℝ))
    (a30 : -(h 1) < (-5/42 : ℝ))
    (a34 : h 2 ≤ (4/35 : ℝ))
    (a36 : -(h 4) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/13 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_116 h delta _ctx _hno a18 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_117 h delta _ctx _hno a17 a23 a30 a36 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_118 h delta _ctx _hno a17 a23 a27 a36 f2
  by_cases p3 : h 2 ≤ (7/60 : ℝ)
  swap
  · have f3 : -(h 2) < (-7/60 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_119 h delta _ctx _hno a34 f3
  by_cases p4 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_120 h delta _ctx _hno a17 a23 a27 a30 a36 f4
  apply _hno 47
  change (((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 2 ≤ (7/60 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_114 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a27 : -(h 0) < (-3/19 : ℝ))
    (a30 : -(h 1) < (-5/42 : ℝ))
    (a35 : -(h 3) < (-5/44 : ℝ))
    (a40 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/16 : ℝ) * _ctx.order4 + (1/32 : ℝ) * _ctx.fail1 + (3/32 : ℝ) * a17 + (1/8 : ℝ) * a27 + (3/16 : ℝ) * a30 + (3/16 : ℝ) * a35 + (3/8 : ℝ) * a40 + (3/16 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_113 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a34 : h 2 ≤ (4/35 : ℝ))
    (a39 : -(h 2) < (-7/60 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_112 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a27 : -(h 0) < (-3/19 : ℝ))
    (a35 : -(h 3) < (-5/44 : ℝ))
    (a38 : -(h 1) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/13 : ℝ) * _ctx.order4 + (6/13 : ℝ) * _ctx.min + (1/26 : ℝ) * _ctx.fail1 + (9/26 : ℝ) * a17 + (2/13 : ℝ) * a27 + (3/13 : ℝ) * a35 + (3/13 : ℝ) * a38 + (3/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_111 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a30 : -(h 1) < (-5/42 : ℝ))
    (a35 : -(h 3) < (-5/44 : ℝ))
    (a37 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/11 : ℝ) * _ctx.order2 + (2/11 : ℝ) * _ctx.order4 + (4/11 : ℝ) * _ctx.min + (3/11 : ℝ) * a17 + (2/11 : ℝ) * a30 + (4/11 : ℝ) * a35 + (2/11 : ℝ) * a37 + (2/11 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_110 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ))
    (a36 : ((-2 : ℝ) * (delta)) < (-3/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a18 + (1 : ℝ) * a36
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_109 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a18 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ))
    (a27 : -(h 0) < (-3/19 : ℝ))
    (a30 : -(h 1) < (-5/42 : ℝ))
    (a34 : h 2 ≤ (4/35 : ℝ))
    (a35 : -(h 3) < (-5/44 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/13 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_110 h delta _ctx _hno a18 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_111 h delta _ctx _hno a17 a30 a35 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_112 h delta _ctx _hno a17 a27 a35 f2
  by_cases p3 : h 2 ≤ (7/60 : ℝ)
  swap
  · have f3 : -(h 2) < (-7/60 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_113 h delta _ctx _hno a34 f3
  by_cases p4 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_114 h delta _ctx _hno a17 a27 a30 a35 f4
  apply _hno 47
  change (((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 2 ≤ (7/60 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_108 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a27 : -(h 0) < (-3/19 : ℝ))
    (a30 : -(h 1) < (-5/42 : ℝ))
    (a34 : -(h 2) < (-4/35 : ℝ))
    (a39 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order4 + (1/13 : ℝ) * a17 + (2/13 : ℝ) * a23 + (2/13 : ℝ) * a27 + (2/13 : ℝ) * a30 + (2/13 : ℝ) * a34 + (4/13 : ℝ) * a39 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_107 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a27 : -(h 0) < (-3/19 : ℝ))
    (a30 : -(h 1) < (-5/42 : ℝ))
    (a38 : -(h 2) < (-7/60 : ℝ))
    (a43 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a17 + (1/6 : ℝ) * a23 + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a38 + (1/6 : ℝ) * a43 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_106 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a27 : -(h 0) < (-3/19 : ℝ))
    (a30 : -(h 1) < (-5/42 : ℝ))
    (a38 : -(h 2) < (-7/60 : ℝ))
    (a42 : -(h 3) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/11 : ℝ) * _ctx.order4 + (4/11 : ℝ) * _ctx.min + (3/11 : ℝ) * a17 + (2/11 : ℝ) * a27 + (2/11 : ℝ) * a30 + (2/11 : ℝ) * a38 + (2/11 : ℝ) * a42 + (2/11 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_105 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a27 : -(h 0) < (-3/19 : ℝ))
    (a38 : -(h 2) < (-7/60 : ℝ))
    (a41 : -(h 1) < (-4/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/11 : ℝ) * _ctx.order4 + (4/11 : ℝ) * _ctx.min + (3/11 : ℝ) * a17 + (2/11 : ℝ) * a23 + (2/11 : ℝ) * a27 + (2/11 : ℝ) * a38 + (2/11 : ℝ) * a41 + (2/11 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_104 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a30 : -(h 1) < (-5/42 : ℝ))
    (a38 : -(h 2) < (-7/60 : ℝ))
    (a40 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/11 : ℝ) * _ctx.order4 + (4/11 : ℝ) * _ctx.min + (3/11 : ℝ) * a17 + (2/11 : ℝ) * a23 + (2/11 : ℝ) * a30 + (2/11 : ℝ) * a38 + (2/11 : ℝ) * a40 + (2/11 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_103 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : -(h 0) < (-3/19 : ℝ))
    (a30 : -(h 1) < (-5/42 : ℝ))
    (a38 : -(h 2) < (-7/60 : ℝ))
    (a39 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (2/5 : ℝ) * _ctx.order4 + (3/5 : ℝ) * _ctx.min + (1/5 : ℝ) * a27 + (1/5 : ℝ) * a30 + (1/5 : ℝ) * a38 + (2/5 : ℝ) * a39 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_102 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a27 : -(h 0) < (-3/19 : ℝ))
    (a30 : -(h 1) < (-5/42 : ℝ))
    (a38 : -(h 2) < (-7/60 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_103 h delta _ctx _hno a27 a30 a38 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_104 h delta _ctx _hno a17 a23 a30 a38 f1
  by_cases p2 : h 1 ≤ (4/33 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_105 h delta _ctx _hno a17 a23 a27 a38 f2
  by_cases p3 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f3 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_106 h delta _ctx _hno a17 a27 a30 a38 f3
  by_cases p4 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_107 h delta _ctx _hno a17 a23 a27 a30 a38 f4
  apply _hno 48
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (4/33 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_101 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a27 : -(h 0) < (-3/19 : ℝ))
    (a37 : -(h 1) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/13 : ℝ) * _ctx.order4 + (6/13 : ℝ) * _ctx.min + (1/26 : ℝ) * _ctx.fail1 + (9/26 : ℝ) * a17 + (3/13 : ℝ) * a23 + (2/13 : ℝ) * a27 + (3/13 : ℝ) * a37 + (3/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_100 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a30 : -(h 1) < (-5/42 : ℝ))
    (a34 : -(h 2) < (-4/35 : ℝ))
    (a36 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/11 : ℝ) * _ctx.order4 + (4/11 : ℝ) * _ctx.min + (3/11 : ℝ) * a17 + (2/11 : ℝ) * a23 + (2/11 : ℝ) * a30 + (2/11 : ℝ) * a34 + (2/11 : ℝ) * a36 + (2/11 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_99 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ))
    (a35 : ((-2 : ℝ) * (delta)) < (-3/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a18 + (1 : ℝ) * a35
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_98 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a18 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a27 : -(h 0) < (-3/19 : ℝ))
    (a30 : -(h 1) < (-5/42 : ℝ))
    (a34 : -(h 2) < (-4/35 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/13 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_99 h delta _ctx _hno a18 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_100 h delta _ctx _hno a17 a23 a30 a34 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_101 h delta _ctx _hno a17 a23 a27 f2
  by_cases p3 : h 2 ≤ (7/60 : ℝ)
  swap
  · have f3 : -(h 2) < (-7/60 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_102 h delta _ctx _hno a17 a23 a27 a30 f3
  by_cases p4 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_108 h delta _ctx _hno a17 a23 a27 a30 a34 f4
  apply _hno 47
  change (((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 2 ≤ (7/60 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_97 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a27 : -(h 0) < (-3/19 : ℝ))
    (a33 : -(h 1) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/13 : ℝ) * _ctx.order4 + (6/13 : ℝ) * _ctx.min + (1/26 : ℝ) * _ctx.fail1 + (9/26 : ℝ) * a17 + (3/13 : ℝ) * a23 + (2/13 : ℝ) * a27 + (3/13 : ℝ) * a33 + (3/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_96 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a21 : h 0 ≤ (1/6 : ℝ))
    (a32 : -(h 0) < (-3/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a21 + (1 : ℝ) * a32
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_95 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : -(h 0) < (-3/19 : ℝ))
    (a30 : -(h 1) < (-5/42 : ℝ))
    (a31 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.order3 + (12/23 : ℝ) * _ctx.order4 + (18/23 : ℝ) * _ctx.min + (1/23 : ℝ) * _ctx.fail1 + (4/23 : ℝ) * a27 + (6/23 : ℝ) * a30 + (12/23 : ℝ) * a31 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_94 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a18 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ))
    (a21 : h 0 ≤ (1/6 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a27 : -(h 0) < (-3/19 : ℝ))
    (a30 : -(h 1) < (-5/42 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_95 h delta _ctx _hno a27 a30 f0
  by_cases p1 : h 0 ≤ (3/17 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/17 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_96 h delta _ctx _hno a21 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_97 h delta _ctx _hno a17 a23 a27 f2
  by_cases p3 : h 2 ≤ (4/35 : ℝ)
  swap
  · have f3 : -(h 2) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_98 h delta _ctx _hno a17 a18 a23 a27 a30 f3
  by_cases p4 : h 3 ≤ (5/44 : ℝ)
  swap
  · have f4 : -(h 3) < (-5/44 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_109 h delta _ctx _hno a17 a18 a27 a30 p3 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_115 h delta _ctx _hno a17 a18 a23 a27 a30 p3 f5
  apply _hno 46
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/17 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 2 ≤ (4/35 : ℝ)) ∧ (h 3 ≤ (5/44 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_93 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a21 : h 0 ≤ (1/6 : ℝ))
    (a29 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a21 + (1 : ℝ) * a29
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_92 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ))
    (a28 : ((-2 : ℝ) * (delta)) < (-3/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a18 + (1 : ℝ) * a28
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_91 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a18 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ))
    (a21 : h 0 ≤ (1/6 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a27 : -(h 0) < (-3/19 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/13 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_92 h delta _ctx _hno a18 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_93 h delta _ctx _hno a21 f1
  by_cases p2 : h 1 ≤ (5/42 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/42 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_94 h delta _ctx _hno a17 a18 a21 a23 a27 f2
  apply _hno 34
  change (((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (5/42 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem upper_node_90 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ))
    (a26 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a18 + (1 : ℝ) * a26
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_89 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a18 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ))
    (a21 : h 0 ≤ (1/6 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    (a25 : -(h 0) < (-2/13 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_90 h delta _ctx _hno a18 f0
  by_cases p1 : h 0 ≤ (3/19 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/19 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_91 h delta _ctx _hno a17 a18 a21 a23 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_121 h delta _ctx _hno a17 a23 a25 f2
  by_cases p3 : h 4 ≤ (13/112 : ℝ)
  swap
  · have f3 : -(h 4) < (-13/112 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_122 h delta _ctx _hno a17 a25 f3
  apply _hno 4
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (13/112 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_88 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ))
    (a24 : ((-2 : ℝ) * (delta)) < (-5/21 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a18 + (1 : ℝ) * a24
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_87 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a18 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ))
    (a19 : -(h 0) < (-3/20 : ℝ))
    (a21 : h 0 ≤ (1/6 : ℝ))
    (a23 : -(h 3) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/21 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/21 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_88 h delta _ctx _hno a18 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_89 h delta _ctx _hno a17 a18 a21 a23 f1
  by_cases p2 : h 1 ≤ (13/108 : ℝ)
  swap
  · have f2 : -(h 1) < (-13/108 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_123 h delta _ctx _hno a17 a18 a19 a23 p1 f2
  apply _hno 5
  change (((2 : ℝ) * (delta)) ≤ (5/21 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (13/108 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem upper_node_86 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a16 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a17 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a22 : -(h 1) < (-5/36 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (9/29 : ℝ) * _ctx.order3 + (18/29 : ℝ) * _ctx.order4 + (26/29 : ℝ) * _ctx.min + (3/58 : ℝ) * _ctx.fail1 + (1/29 : ℝ) * a16 + (35/58 : ℝ) * a17 + (9/29 : ℝ) * a22 + (9/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_85 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a21 : -(h 0) < (-1/6 : ℝ))
    (a24 : -(h 1) < (-3/26 : ℝ))
    (a30 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.order3 + (6/29 : ℝ) * _ctx.min + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a17 + (4/29 : ℝ) * a21 + (6/29 : ℝ) * a24 + (12/29 : ℝ) * a30 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_84 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a17 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a21 : -(h 0) < (-1/6 : ℝ))
    (a29 : -(h 3) < (-5/44 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.order2 + (6/23 : ℝ) * _ctx.order4 + (12/23 : ℝ) * _ctx.min + (2/23 : ℝ) * a13 + (3/23 : ℝ) * a17 + (6/23 : ℝ) * a21 + (12/23 : ℝ) * a29 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_83 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a21 : -(h 0) < (-1/6 : ℝ))
    (a24 : -(h 1) < (-3/26 : ℝ))
    (a28 : -(h 2) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (2/5 : ℝ) * _ctx.order4 + (3/5 : ℝ) * _ctx.min + (2/5 : ℝ) * a17 + (1/5 : ℝ) * a21 + (1/5 : ℝ) * a24 + (1/5 : ℝ) * a28 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_82 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a21 : -(h 0) < (-1/6 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.order3 + (12/23 : ℝ) * _ctx.order4 + (18/23 : ℝ) * _ctx.min + (1/23 : ℝ) * _ctx.fail1 + (12/23 : ℝ) * a17 + (4/23 : ℝ) * a21 + (6/23 : ℝ) * a27 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_81 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a17 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a26 : -(h 0) < (-3/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/17 : ℝ) * _ctx.order2 + (12/17 : ℝ) * _ctx.order3 + (18/17 : ℝ) * _ctx.order4 + (24/17 : ℝ) * _ctx.min + (2/17 : ℝ) * a13 + (9/17 : ℝ) * a17 + (6/17 : ℝ) * a26 + (6/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_80 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a21 : -(h 0) < (-1/6 : ℝ))
    (a24 : -(h 1) < (-3/26 : ℝ))
    (a25 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.order3 + (12/23 : ℝ) * _ctx.order4 + (18/23 : ℝ) * _ctx.min + (1/23 : ℝ) * _ctx.fail1 + (4/23 : ℝ) * a21 + (6/23 : ℝ) * a24 + (12/23 : ℝ) * a25 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_79 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a17 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a21 : -(h 0) < (-1/6 : ℝ))
    (a24 : -(h 1) < (-3/26 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_80 h delta _ctx _hno a21 a24 f0
  by_cases p1 : h 0 ≤ (3/17 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/17 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_81 h delta _ctx _hno a13 a17 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_82 h delta _ctx _hno a17 a21 f2
  by_cases p3 : h 2 ≤ (4/35 : ℝ)
  swap
  · have f3 : -(h 2) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_83 h delta _ctx _hno a17 a21 a24 f3
  by_cases p4 : h 3 ≤ (5/44 : ℝ)
  swap
  · have f4 : -(h 3) < (-5/44 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_84 h delta _ctx _hno a13 a17 a21 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_85 h delta _ctx _hno a17 a21 a24 f5
  apply _hno 46
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/17 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 2 ≤ (4/35 : ℝ)) ∧ (h 3 ≤ (5/44 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_78 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a17 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a23 : -(h 0) < (-5/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/17 : ℝ) * _ctx.order2 + (12/17 : ℝ) * _ctx.order3 + (18/17 : ℝ) * _ctx.order4 + (24/17 : ℝ) * _ctx.min + (2/17 : ℝ) * a13 + (9/17 : ℝ) * a17 + (6/17 : ℝ) * a23 + (6/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_77 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ))
    (a22 : ((-2 : ℝ) * (delta)) < (-3/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a18 + (1 : ℝ) * a22
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_76 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a17 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a18 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ))
    (a21 : -(h 0) < (-1/6 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/13 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_77 h delta _ctx _hno a18 f0
  by_cases p1 : h 0 ≤ (5/26 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/26 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_78 h delta _ctx _hno a13 a17 f1
  by_cases p2 : h 1 ≤ (3/26 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_79 h delta _ctx _hno a13 a17 a21 f2
  apply _hno 1
  change (((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)) ∧ (h 0 ≤ (5/26 : ℝ)) ∧ (h 1 ≤ (3/26 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem upper_node_75 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ))
    (a20 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a18 + (1 : ℝ) * a20
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_74 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a16 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a17 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    (a18 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ))
    (a19 : -(h 0) < (-3/20 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_75 h delta _ctx _hno a18 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_76 h delta _ctx _hno a13 a17 a18 f1
  by_cases p2 : h 1 ≤ (5/36 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/36 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_86 h delta _ctx _hno a16 a17 f2
  by_cases p3 : h 3 ≤ (1/9 : ℝ)
  swap
  · have f3 : -(h 3) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_87 h delta _ctx _hno a17 a18 a19 p1 f3
  apply _hno 0
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (5/36 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_73 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : h 5 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a18 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/9 : ℝ) * _ctx.min + (2/9 : ℝ) * a15 + (1 : ℝ) * a18
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_72 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a15 : h 5 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a16 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a17 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_73 h delta _ctx _hno a15 f0
  by_cases p1 : h 0 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_74 h delta _ctx _hno a13 a16 a17 p0 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_133 h delta _ctx _hno a16 a17 p1 f2
  apply _hno 3
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem upper_node_71 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a15 : h 5 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a16 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_72 h delta _ctx _hno a13 a15 a16 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_152 h delta _ctx _hno a13 a14 a16 p0 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_577 h delta _ctx _hno a14 a16 p0 p1 f2
  apply _hno 2
  change (((2 : ℝ) * (delta)) ≤ (7/32 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem upper_node_70 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 5) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a19 : -(h 3) < (-4/35 : ℝ))
    (a22 : -(h 1) < (-1/8 : ℝ))
    (a29 : -(h 5) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/11 : ℝ) * _ctx.order4 + (1/22 : ℝ) * _ctx.fail1 + (1/22 : ℝ) * _ctx.fail2 + (3/88 : ℝ) * a15 + (3/11 : ℝ) * a19 + (3/11 : ℝ) * a22 + (29/88 : ℝ) * a29 + (3/11 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_69 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 5) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a22 : -(h 1) < (-1/8 : ℝ))
    (a28 : -(h 4) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (9/26 : ℝ) * _ctx.order3 + (7/26 : ℝ) * _ctx.min + (3/52 : ℝ) * _ctx.fail1 + (3/52 : ℝ) * _ctx.fail2 + (1/13 : ℝ) * a15 + (9/26 : ℝ) * a22 + (6/13 : ℝ) * a28 + (9/26 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_68 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 5) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a22 : -(h 1) < (-1/8 : ℝ))
    (a27 : -(h 3) < (-7/60 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (9/70 : ℝ) * _ctx.order4 + (29/70 : ℝ) * _ctx.min + (9/140 : ℝ) * _ctx.fail1 + (9/140 : ℝ) * _ctx.fail2 + (1/10 : ℝ) * a15 + (27/70 : ℝ) * a22 + (27/70 : ℝ) * a27 + (27/70 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

end RealPinwheel.WeakSevenBandData
