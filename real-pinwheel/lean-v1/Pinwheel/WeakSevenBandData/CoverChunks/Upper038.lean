import Pinwheel.WeakSevenBandData.CoverChunks.Upper037

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem upper_node_1267 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a26 : -(h 0) < (-4/25 : ℝ))
    (a31 : -(h 4) < (-1/9 : ℝ))
    (a39 : -(h 2) < (-7/60 : ℝ))
    (a43 : -(h 3) < (-7/62 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/13 : ℝ) * _ctx.min + (1/13 : ℝ) * a13 + (3/13 : ℝ) * a26 + (3/13 : ℝ) * a31 + (3/13 : ℝ) * a39 + (3/13 : ℝ) * a43 + (3/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1266 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a26 : -(h 0) < (-4/25 : ℝ))
    (a31 : -(h 4) < (-1/9 : ℝ))
    (a39 : -(h 2) < (-7/60 : ℝ))
    (a42 : -(h 1) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a24 + (1/5 : ℝ) * a26 + (1/5 : ℝ) * a31 + (1/5 : ℝ) * a39 + (1/5 : ℝ) * a42 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1265 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a31 : -(h 4) < (-1/9 : ℝ))
    (a39 : -(h 2) < (-7/60 : ℝ))
    (a41 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/13 : ℝ) * _ctx.min + (1/13 : ℝ) * a13 + (3/13 : ℝ) * a24 + (3/13 : ℝ) * a31 + (3/13 : ℝ) * a39 + (3/13 : ℝ) * a41 + (3/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1264 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a26 : -(h 0) < (-4/25 : ℝ))
    (a31 : -(h 4) < (-1/9 : ℝ))
    (a39 : -(h 2) < (-7/60 : ℝ))
    (a45 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (24/131 : ℝ) * _ctx.order3 + (8/131 : ℝ) * a13 + (3/131 : ℝ) * a14 + (27/131 : ℝ) * a26 + (48/131 : ℝ) * a31 + (24/131 : ℝ) * a39 + (24/131 : ℝ) * a45 + (24/131 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1263 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a26 : -(h 0) < (-4/25 : ℝ))
    (a39 : -(h 2) < (-7/60 : ℝ))
    (a44 : -(h 4) < (-9/80 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/13 : ℝ) * _ctx.order3 + (3/13 : ℝ) * _ctx.min + (1/13 : ℝ) * a13 + (3/13 : ℝ) * a26 + (3/13 : ℝ) * a39 + (6/13 : ℝ) * a44 + (3/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1262 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a26 : -(h 0) < (-4/25 : ℝ))
    (a31 : -(h 4) < (-1/9 : ℝ))
    (a39 : -(h 2) < (-7/60 : ℝ))
    (a43 : -(h 1) < (-1/8 : ℝ))
    (a50 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/17 : ℝ) * _ctx.order3 + (1/34 : ℝ) * a13 + (3/17 : ℝ) * a26 + (6/17 : ℝ) * a31 + (3/17 : ℝ) * a39 + (3/34 : ℝ) * a43 + (3/17 : ℝ) * a50 + (3/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1261 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a26 : -(h 0) < (-4/25 : ℝ))
    (a39 : -(h 2) < (-7/60 : ℝ))
    (a49 : -(h 4) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/13 : ℝ) * _ctx.order3 + (3/13 : ℝ) * _ctx.min + (1/13 : ℝ) * a13 + (3/13 : ℝ) * a26 + (3/13 : ℝ) * a39 + (6/13 : ℝ) * a49 + (3/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1260 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a26 : -(h 0) < (-4/25 : ℝ))
    (a31 : -(h 4) < (-1/9 : ℝ))
    (a39 : -(h 2) < (-7/60 : ℝ))
    (a48 : -(h 3) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/13 : ℝ) * _ctx.min + (1/13 : ℝ) * a13 + (3/13 : ℝ) * a26 + (3/13 : ℝ) * a31 + (3/13 : ℝ) * a39 + (3/13 : ℝ) * a48 + (3/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1259 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a26 : -(h 0) < (-4/25 : ℝ))
    (a43 : -(h 1) < (-1/8 : ℝ))
    (a47 : -(h 2) < (-2/17 : ℝ))
    (a53 : -(h 5) < (-5/44 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/17 : ℝ) * _ctx.order3 + (6/17 : ℝ) * _ctx.order4 + (1/34 : ℝ) * a13 + (3/17 : ℝ) * a26 + (3/34 : ℝ) * a43 + (3/17 : ℝ) * a47 + (9/17 : ℝ) * a53 + (3/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1258 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a26 : -(h 0) < (-4/25 : ℝ))
    (a31 : -(h 4) < (-1/9 : ℝ))
    (a47 : -(h 2) < (-2/17 : ℝ))
    (a52 : -(h 3) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/13 : ℝ) * _ctx.min + (1/13 : ℝ) * a13 + (3/13 : ℝ) * a26 + (3/13 : ℝ) * a31 + (3/13 : ℝ) * a47 + (3/13 : ℝ) * a52 + (3/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1257 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a26 : -(h 0) < (-4/25 : ℝ))
    (a31 : -(h 4) < (-1/9 : ℝ))
    (a51 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/13 : ℝ) * _ctx.min + (1/13 : ℝ) * a13 + (3/13 : ℝ) * a24 + (3/13 : ℝ) * a26 + (3/13 : ℝ) * a31 + (3/13 : ℝ) * a51 + (3/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1256 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a26 : -(h 0) < (-4/25 : ℝ))
    (a31 : -(h 4) < (-1/9 : ℝ))
    (a47 : -(h 2) < (-2/17 : ℝ))
    (a50 : -(h 1) < (-6/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a24 + (1/5 : ℝ) * a26 + (1/5 : ℝ) * a31 + (1/5 : ℝ) * a47 + (1/5 : ℝ) * a50 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1255 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a31 : -(h 4) < (-1/9 : ℝ))
    (a47 : -(h 2) < (-2/17 : ℝ))
    (a49 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/13 : ℝ) * _ctx.min + (1/13 : ℝ) * a13 + (3/13 : ℝ) * a24 + (3/13 : ℝ) * a31 + (3/13 : ℝ) * a47 + (3/13 : ℝ) * a49 + (3/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1254 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a26 : -(h 0) < (-4/25 : ℝ))
    (a48 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * a14 + (1/5 : ℝ) * a26 + (4/5 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1253 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a26 : -(h 0) < (-4/25 : ℝ))
    (a31 : -(h 4) < (-1/9 : ℝ))
    (a43 : -(h 1) < (-1/8 : ℝ))
    (a47 : -(h 2) < (-2/17 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1254 h delta _ctx _hno a14 a26 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1255 h delta _ctx _hno a13 a24 a31 a47 f1
  by_cases p2 : h 1 ≤ (6/47 : ℝ)
  swap
  · have f2 : -(h 1) < (-6/47 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1256 h delta _ctx _hno a24 a26 a31 a47 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1257 h delta _ctx _hno a13 a24 a26 a31 f3
  by_cases p4 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1258 h delta _ctx _hno a13 a26 a31 a47 f4
  by_cases p5 : h 5 ≤ (5/44 : ℝ)
  swap
  · have f5 : -(h 5) < (-5/44 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1259 h delta _ctx _hno a13 a26 a43 a47 f5
  apply _hno 104
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (6/47 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (5/44 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_1252 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a26 : -(h 0) < (-4/25 : ℝ))
    (a31 : -(h 4) < (-1/9 : ℝ))
    (a39 : -(h 2) < (-7/60 : ℝ))
    (a46 : -(h 1) < (-4/31 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a24 + (1/5 : ℝ) * a26 + (1/5 : ℝ) * a31 + (1/5 : ℝ) * a39 + (1/5 : ℝ) * a46 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1251 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a22 : h 0 ≤ (1/6 : ℝ))
    (a45 : -(h 0) < (-4/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a22 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1250 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a26 : -(h 0) < (-4/25 : ℝ))
    (a44 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * a14 + (1/5 : ℝ) * a26 + (4/5 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1249 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a22 : h 0 ≤ (1/6 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a26 : -(h 0) < (-4/25 : ℝ))
    (a31 : -(h 4) < (-1/9 : ℝ))
    (a39 : -(h 2) < (-7/60 : ℝ))
    (a43 : -(h 1) < (-1/8 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1250 h delta _ctx _hno a14 a26 f0
  by_cases p1 : h 0 ≤ (4/23 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/23 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1251 h delta _ctx _hno a22 f1
  by_cases p2 : h 1 ≤ (4/31 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/31 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1252 h delta _ctx _hno a24 a26 a31 a39 f2
  by_cases p3 : h 2 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1253 h delta _ctx _hno a13 a14 a24 a26 a31 a43 f3
  by_cases p4 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1260 h delta _ctx _hno a13 a26 a31 a39 f4
  by_cases p5 : h 4 ≤ (4/35 : ℝ)
  swap
  · have f5 : -(h 4) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1261 h delta _ctx _hno a13 a26 a39 f5
  by_cases p6 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f6 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact upper_node_1262 h delta _ctx _hno a13 a26 a31 a39 a43 f6
  apply _hno 80
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (4/23 : ℝ)) ∧ (h 1 ≤ (4/31 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 4 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem upper_node_1248 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a22 : h 0 ≤ (1/6 : ℝ))
    (a42 : -(h 0) < (-4/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a22 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1247 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a26 : -(h 0) < (-4/25 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * a14 + (1/5 : ℝ) * a26 + (4/5 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1246 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a22 : h 0 ≤ (1/6 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a26 : -(h 0) < (-4/25 : ℝ))
    (a31 : -(h 4) < (-1/9 : ℝ))
    (a39 : -(h 2) < (-7/60 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1247 h delta _ctx _hno a14 a26 f0
  by_cases p1 : h 0 ≤ (4/23 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/23 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1248 h delta _ctx _hno a22 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1249 h delta _ctx _hno a13 a14 a22 a24 a26 a31 a39 f2
  by_cases p3 : h 4 ≤ (9/80 : ℝ)
  swap
  · have f3 : -(h 4) < (-9/80 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1263 h delta _ctx _hno a13 a26 a39 f3
  by_cases p4 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1264 h delta _ctx _hno a13 a14 a26 a31 a39 f4
  apply _hno 52
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (4/23 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (9/80 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_1245 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a22 : h 0 ≤ (1/6 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a26 : -(h 0) < (-4/25 : ℝ))
    (a31 : -(h 4) < (-1/9 : ℝ))
    (a39 : -(h 2) < (-7/60 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1246 h delta _ctx _hno a13 a14 a22 a24 a26 a31 a39
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1265 h delta _ctx _hno a13 a24 a31 a39 f1
  by_cases p2 : h 1 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1266 h delta _ctx _hno a24 a26 a31 a39 f2
  by_cases p3 : h 3 ≤ (7/62 : ℝ)
  swap
  · have f3 : -(h 3) < (-7/62 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1267 h delta _ctx _hno a13 a26 a31 a39 f3
  by_cases p4 : h 5 ≤ (4/37 : ℝ)
  swap
  · have f4 : -(h 5) < (-4/37 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1268 h delta _ctx _hno a13 a24 a26 a31 a39 p0 f4
  apply _hno 18
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (7/62 : ℝ)) ∧ (h 5 ≤ (4/37 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_1244 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a26 : -(h 0) < (-4/25 : ℝ))
    (a31 : -(h 4) < (-1/9 : ℝ))
    (a38 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.min + (12/23 : ℝ) * _ctx.lower + (1/23 : ℝ) * _ctx.fail1 + (6/23 : ℝ) * a24 + (4/23 : ℝ) * a26 + (6/23 : ℝ) * a31 + (6/23 : ℝ) * a38 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1243 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a31 : -(h 4) < (-1/9 : ℝ))
    (a35 : -(h 2) < (-5/44 : ℝ))
    (a37 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/13 : ℝ) * _ctx.min + (1/13 : ℝ) * a13 + (3/13 : ℝ) * a24 + (3/13 : ℝ) * a31 + (3/13 : ℝ) * a35 + (3/13 : ℝ) * a37 + (3/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1242 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a26 : -(h 0) < (-4/25 : ℝ))
    (a36 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * a14 + (1/5 : ℝ) * a26 + (4/5 : ℝ) * a36
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1241 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a22 : h 0 ≤ (1/6 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a26 : -(h 0) < (-4/25 : ℝ))
    (a31 : -(h 4) < (-1/9 : ℝ))
    (a35 : -(h 2) < (-5/44 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1242 h delta _ctx _hno a14 a26 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1243 h delta _ctx _hno a13 a24 a31 a35 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1244 h delta _ctx _hno a24 a26 a31 f2
  by_cases p3 : h 2 ≤ (7/60 : ℝ)
  swap
  · have f3 : -(h 2) < (-7/60 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1245 h delta _ctx _hno a13 a14 a22 a24 a26 a31 f3
  by_cases p4 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1269 h delta _ctx _hno a13 a26 a31 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1270 h delta _ctx _hno a13 a14 a24 a26 a31 f5
  apply _hno 54
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (7/60 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_1240 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a26 : -(h 0) < (-4/25 : ℝ))
    (a31 : -(h 4) < (-1/9 : ℝ))
    (a34 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.min + (12/23 : ℝ) * _ctx.lower + (1/23 : ℝ) * _ctx.fail1 + (6/23 : ℝ) * a24 + (4/23 : ℝ) * a26 + (6/23 : ℝ) * a31 + (6/23 : ℝ) * a34 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1239 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a22 : h 0 ≤ (1/6 : ℝ))
    (a33 : -(h 0) < (-3/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a22 + (1 : ℝ) * a33
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1238 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a26 : -(h 0) < (-4/25 : ℝ))
    (a32 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * a14 + (1/5 : ℝ) * a26 + (4/5 : ℝ) * a32
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1237 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a22 : h 0 ≤ (1/6 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a26 : -(h 0) < (-4/25 : ℝ))
    (a31 : -(h 4) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1238 h delta _ctx _hno a14 a26 f0
  by_cases p1 : h 0 ≤ (3/17 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/17 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1239 h delta _ctx _hno a22 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1240 h delta _ctx _hno a24 a26 a31 f2
  by_cases p3 : h 2 ≤ (5/44 : ℝ)
  swap
  · have f3 : -(h 2) < (-5/44 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1241 h delta _ctx _hno a13 a14 a22 a24 a26 a31 f3
  by_cases p4 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1271 h delta _ctx _hno a13 a14 a24 a26 a31 f4
  apply _hno 76
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/17 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (5/44 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_1236 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a26 : -(h 0) < (-4/25 : ℝ))
    (a30 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/10 : ℝ) * _ctx.min + (1/10 : ℝ) * a13 + (3/80 : ℝ) * a18 + (3/10 : ℝ) * a24 + (21/80 : ℝ) * a26 + (3/10 : ℝ) * a30 + (3/10 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1235 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a26 : -(h 0) < (-4/25 : ℝ))
    (a29 : -(h 1) < (-2/15 : ℝ))
    (a34 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.min + (12/23 : ℝ) * _ctx.lower + (1/23 : ℝ) * _ctx.fail1 + (6/23 : ℝ) * a24 + (4/23 : ℝ) * a26 + (6/23 : ℝ) * a29 + (6/23 : ℝ) * a34 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1234 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a26 : -(h 0) < (-4/25 : ℝ))
    (a29 : -(h 1) < (-2/15 : ℝ))
    (a33 : -(h 2) < (-4/35 : ℝ))
    (a39 : -(h 5) < (-2/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order4 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a24 + (1/6 : ℝ) * a26 + (1/6 : ℝ) * a29 + (1/6 : ℝ) * a33 + (1/3 : ℝ) * a39 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1233 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a26 : -(h 0) < (-4/25 : ℝ))
    (a29 : -(h 1) < (-2/15 : ℝ))
    (a33 : -(h 2) < (-4/35 : ℝ))
    (a38 : -(h 4) < (-3/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a24 + (1/5 : ℝ) * a26 + (1/5 : ℝ) * a29 + (1/5 : ℝ) * a33 + (1/5 : ℝ) * a38 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1232 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a26 : -(h 0) < (-4/25 : ℝ))
    (a29 : -(h 1) < (-2/15 : ℝ))
    (a37 : -(h 2) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.min + (1/2 : ℝ) * _ctx.lower + (1/32 : ℝ) * a18 + (1/4 : ℝ) * a24 + (7/32 : ℝ) * a26 + (1/4 : ℝ) * a29 + (1/4 : ℝ) * a37 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1231 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : h 1 ≤ (5/36 : ℝ))
    (a36 : -(h 1) < (-5/31 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a23 + (1 : ℝ) * a36
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1230 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a29 : -(h 1) < (-2/15 : ℝ))
    (a33 : -(h 2) < (-4/35 : ℝ))
    (a35 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.min + (1/2 : ℝ) * _ctx.lower + (1/32 : ℝ) * a18 + (1/4 : ℝ) * a24 + (1/4 : ℝ) * a29 + (1/4 : ℝ) * a33 + (7/32 : ℝ) * a35 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1229 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a26 : -(h 0) < (-4/25 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * a14 + (1/5 : ℝ) * a26 + (4/5 : ℝ) * a34
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1228 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a23 : h 1 ≤ (5/36 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a26 : -(h 0) < (-4/25 : ℝ))
    (a29 : -(h 1) < (-2/15 : ℝ))
    (a33 : -(h 2) < (-4/35 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1229 h delta _ctx _hno a14 a26 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1230 h delta _ctx _hno a18 a24 a29 a33 f1
  by_cases p2 : h 1 ≤ (5/31 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/31 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1231 h delta _ctx _hno a23 f2
  by_cases p3 : h 2 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1232 h delta _ctx _hno a18 a24 a26 a29 f3
  by_cases p4 : h 4 ≤ (3/28 : ℝ)
  swap
  · have f4 : -(h 4) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1233 h delta _ctx _hno a24 a26 a29 a33 f4
  by_cases p5 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1234 h delta _ctx _hno a24 a26 a29 a33 f5
  apply _hno 103
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (5/31 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (3/28 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_1227 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : h 1 ≤ (5/36 : ℝ))
    (a32 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a23 + (1 : ℝ) * a32
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1226 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a22 : h 0 ≤ (1/6 : ℝ))
    (a31 : -(h 0) < (-6/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a22 + (1 : ℝ) * a31
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1225 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a30 : ((-2 : ℝ) * (delta)) < (-8/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a25 + (1 : ℝ) * a30
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1224 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a22 : h 0 ≤ (1/6 : ℝ))
    (a23 : h 1 ≤ (5/36 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a25 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a26 : -(h 0) < (-4/25 : ℝ))
    (a29 : -(h 1) < (-2/15 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (8/35 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-8/35 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1225 h delta _ctx _hno a25 f0
  by_cases p1 : h 0 ≤ (6/35 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/35 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1226 h delta _ctx _hno a22 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1227 h delta _ctx _hno a23 f2
  by_cases p3 : h 2 ≤ (4/35 : ℝ)
  swap
  · have f3 : -(h 2) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1228 h delta _ctx _hno a14 a18 a23 a24 a26 a29 f3
  by_cases p4 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1235 h delta _ctx _hno a24 a26 a29 f4
  apply _hno 51
  change (((2 : ℝ) * (delta)) ≤ (8/35 : ℝ)) ∧ (h 0 ≤ (6/35 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (4/35 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_1223 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a22 : h 0 ≤ (1/6 : ℝ))
    (a28 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a22 + (1 : ℝ) * a28
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1222 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a26 : -(h 0) < (-4/25 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * a14 + (1/5 : ℝ) * a26 + (4/5 : ℝ) * a27
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1221 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a22 : h 0 ≤ (1/6 : ℝ))
    (a23 : h 1 ≤ (5/36 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a25 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a26 : -(h 0) < (-4/25 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1222 h delta _ctx _hno a14 a26 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1223 h delta _ctx _hno a22 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1224 h delta _ctx _hno a14 a18 a22 a23 a24 a25 a26 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1236 h delta _ctx _hno a13 a18 a24 a26 f3
  by_cases p4 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1237 h delta _ctx _hno a13 a14 a22 a24 a26 f4
  apply _hno 57
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_1220 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a25 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a28 : -(h 1) < (-1/8 : ℝ))
    (a33 : -(h 4) < (-4/35 : ℝ))
    (a38 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/14 : ℝ) * _ctx.order3 + (1/28 : ℝ) * _ctx.fail1 + (1/42 : ℝ) * a20 + (3/28 : ℝ) * a25 + (3/14 : ℝ) * a28 + (3/7 : ℝ) * a33 + (4/21 : ℝ) * a38 + (3/14 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1219 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a25 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a28 : -(h 1) < (-1/8 : ℝ))
    (a33 : -(h 4) < (-4/35 : ℝ))
    (a37 : -(h 3) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/19 : ℝ) * _ctx.min + (3/76 : ℝ) * _ctx.fail1 + (1/38 : ℝ) * a20 + (17/76 : ℝ) * a25 + (9/38 : ℝ) * a28 + (9/38 : ℝ) * a33 + (9/38 : ℝ) * a37 + (9/38 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1218 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : h 1 ≤ (9/70 : ℝ))
    (a36 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a36
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1217 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a25 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * a14 + (4/5 : ℝ) * a25 + (1/5 : ℝ) * a35
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1216 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/217 : ℝ) * _ctx.order3 + (6/217 : ℝ) * _ctx.order4 + (1/434 : ℝ) * _ctx.fail1 + (1/217 : ℝ) * a13 + (52/217 : ℝ) * a14 + (9/217 : ℝ) * a20 + (59/62 : ℝ) * a34 + (3/217 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1215 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a25 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a28 : -(h 1) < (-1/8 : ℝ))
    (a31 : h 1 ≤ (9/70 : ℝ))
    (a33 : -(h 4) < (-4/35 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1216 h delta _ctx _hno a13 a14 a20 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1217 h delta _ctx _hno a14 a25 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1218 h delta _ctx _hno a31 f2
  by_cases p3 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f3 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1219 h delta _ctx _hno a20 a25 a28 a33 f3
  by_cases p4 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1220 h delta _ctx _hno a20 a25 a28 a33 f4
  apply _hno 19
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_1214 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a25 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a28 : -(h 1) < (-1/8 : ℝ))
    (a32 : -(h 2) < (-1/8 : ℝ))
    (a37 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (10/61 : ℝ) * _ctx.min + (2/61 : ℝ) * a20 + (12/61 : ℝ) * a24 + (11/61 : ℝ) * a25 + (12/61 : ℝ) * a28 + (12/61 : ℝ) * a32 + (12/61 : ℝ) * a37 + (12/61 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1213 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a25 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a28 : -(h 1) < (-1/8 : ℝ))
    (a32 : -(h 2) < (-1/8 : ℝ))
    (a36 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (82/403 : ℝ) * _ctx.min + (12/403 : ℝ) * a18 + (14/403 : ℝ) * a20 + (89/403 : ℝ) * a25 + (96/403 : ℝ) * a28 + (96/403 : ℝ) * a32 + (96/403 : ℝ) * a36 + (96/403 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1212 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : h 1 ≤ (9/70 : ℝ))
    (a35 : -(h 1) < (-7/54 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a35
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1211 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : h 0 ≤ (2/13 : ℝ))
    (a34 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a34
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1210 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a28 : -(h 1) < (-1/8 : ℝ))
    (a32 : -(h 2) < (-1/8 : ℝ))
    (a33 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/147 : ℝ) * _ctx.order3 + (4/147 : ℝ) * _ctx.order4 + (34/147 : ℝ) * a14 + (2/49 : ℝ) * a20 + (2/147 : ℝ) * a28 + (2/147 : ℝ) * a32 + (137/147 : ℝ) * a33 + (2/147 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1209 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a25 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a27 : h 0 ≤ (2/13 : ℝ))
    (a28 : -(h 1) < (-1/8 : ℝ))
    (a31 : h 1 ≤ (9/70 : ℝ))
    (a32 : -(h 2) < (-1/8 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1210 h delta _ctx _hno a14 a20 a28 a32 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1211 h delta _ctx _hno a27 f1
  by_cases p2 : h 1 ≤ (7/54 : ℝ)
  swap
  · have f2 : -(h 1) < (-7/54 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1212 h delta _ctx _hno a31 f2
  by_cases p3 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1213 h delta _ctx _hno a18 a20 a25 a28 a32 f3
  by_cases p4 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1214 h delta _ctx _hno a20 a24 a25 a28 a32 f4
  apply _hno 14
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (7/54 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_1208 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a25 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a31 : -(h 1) < (-9/70 : ℝ))
    (a35 : -(h 4) < (-1/9 : ℝ))
    (a40 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/28 : ℝ) * _ctx.fail1 + (1/42 : ℝ) * a20 + (3/14 : ℝ) * a24 + (3/28 : ℝ) * a25 + (3/14 : ℝ) * a31 + (3/14 : ℝ) * a35 + (4/21 : ℝ) * a40 + (3/14 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1207 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a25 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a31 : -(h 1) < (-9/70 : ℝ))
    (a35 : -(h 4) < (-1/9 : ℝ))
    (a39 : -(h 3) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/19 : ℝ) * _ctx.min + (3/76 : ℝ) * _ctx.fail1 + (1/38 : ℝ) * a20 + (17/76 : ℝ) * a25 + (9/38 : ℝ) * a31 + (9/38 : ℝ) * a35 + (9/38 : ℝ) * a39 + (9/38 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1206 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a25 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a35 : -(h 4) < (-1/9 : ℝ))
    (a38 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/19 : ℝ) * _ctx.min + (3/76 : ℝ) * _ctx.fail1 + (1/38 : ℝ) * a20 + (9/38 : ℝ) * a24 + (17/76 : ℝ) * a25 + (9/38 : ℝ) * a35 + (9/38 : ℝ) * a38 + (9/38 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1205 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : h 0 ≤ (3/20 : ℝ))
    (a37 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a37
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1204 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a31 : -(h 1) < (-9/70 : ℝ))
    (a36 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/74 : ℝ) * _ctx.order3 + (1/37 : ℝ) * _ctx.order4 + (1/444 : ℝ) * _ctx.fail1 + (26/111 : ℝ) * a14 + (3/74 : ℝ) * a20 + (1/74 : ℝ) * a31 + (419/444 : ℝ) * a36 + (1/74 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1203 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a25 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a31 : -(h 1) < (-9/70 : ℝ))
    (a33 : h 0 ≤ (3/20 : ℝ))
    (a35 : -(h 4) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1204 h delta _ctx _hno a14 a20 a31 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1205 h delta _ctx _hno a33 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1206 h delta _ctx _hno a20 a24 a25 a35 f2
  by_cases p3 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f3 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1207 h delta _ctx _hno a20 a25 a31 a35 f3
  by_cases p4 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1208 h delta _ctx _hno a20 a24 a25 a31 a35 f4
  apply _hno 19
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_1202 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a25 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a31 : -(h 1) < (-9/70 : ℝ))
    (a34 : -(h 2) < (-1/8 : ℝ))
    (a39 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (10/61 : ℝ) * _ctx.min + (2/61 : ℝ) * a20 + (12/61 : ℝ) * a24 + (11/61 : ℝ) * a25 + (12/61 : ℝ) * a31 + (12/61 : ℝ) * a34 + (12/61 : ℝ) * a39 + (12/61 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1201 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a25 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a31 : -(h 1) < (-9/70 : ℝ))
    (a34 : -(h 2) < (-1/8 : ℝ))
    (a38 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (82/403 : ℝ) * _ctx.min + (12/403 : ℝ) * a18 + (14/403 : ℝ) * a20 + (89/403 : ℝ) * a25 + (96/403 : ℝ) * a31 + (96/403 : ℝ) * a34 + (96/403 : ℝ) * a38 + (96/403 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1200 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a25 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a34 : -(h 2) < (-1/8 : ℝ))
    (a37 : -(h 1) < (-7/54 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (82/403 : ℝ) * _ctx.min + (12/403 : ℝ) * a18 + (14/403 : ℝ) * a20 + (96/403 : ℝ) * a24 + (89/403 : ℝ) * a25 + (96/403 : ℝ) * a34 + (96/403 : ℝ) * a37 + (96/403 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1199 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : h 0 ≤ (3/20 : ℝ))
    (a36 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a36
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1198 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a31 : -(h 1) < (-9/70 : ℝ))
    (a34 : -(h 2) < (-1/8 : ℝ))
    (a35 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/99 : ℝ) * _ctx.order4 + (2/9 : ℝ) * a14 + (4/99 : ℝ) * a20 + (2/99 : ℝ) * a24 + (2/99 : ℝ) * a31 + (2/99 : ℝ) * a34 + (89/99 : ℝ) * a35 + (2/99 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1197 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a25 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a31 : -(h 1) < (-9/70 : ℝ))
    (a33 : h 0 ≤ (3/20 : ℝ))
    (a34 : -(h 2) < (-1/8 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1198 h delta _ctx _hno a14 a20 a24 a31 a34 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1199 h delta _ctx _hno a33 f1
  by_cases p2 : h 1 ≤ (7/54 : ℝ)
  swap
  · have f2 : -(h 1) < (-7/54 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1200 h delta _ctx _hno a18 a20 a24 a25 a34 f2
  by_cases p3 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1201 h delta _ctx _hno a18 a20 a25 a31 a34 f3
  by_cases p4 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1202 h delta _ctx _hno a20 a24 a25 a31 a34 f4
  apply _hno 14
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (7/54 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_1196 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a25 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a33 : -(h 0) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * a14 + (4/5 : ℝ) * a25 + (1/5 : ℝ) * a33
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1195 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a31 : -(h 1) < (-9/70 : ℝ))
    (a32 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/74 : ℝ) * _ctx.order3 + (1/37 : ℝ) * _ctx.order4 + (1/444 : ℝ) * _ctx.fail1 + (26/111 : ℝ) * a14 + (3/74 : ℝ) * a20 + (1/74 : ℝ) * a31 + (419/444 : ℝ) * a32 + (1/74 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1194 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a25 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a31 : -(h 1) < (-9/70 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1195 h delta _ctx _hno a14 a20 a31 f0
  by_cases p1 : h 0 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1196 h delta _ctx _hno a14 a25 f1
  by_cases p2 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1197 h delta _ctx _hno a14 a18 a20 a24 a25 a31 p1 f2
  by_cases p3 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f3 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1203 h delta _ctx _hno a14 a20 a24 a25 a31 p1 f3
  apply _hno 8
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_1193 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : h 0 ≤ (2/13 : ℝ))
    (a30 : -(h 0) < (-7/45 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a30
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1192 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a29 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/217 : ℝ) * _ctx.order3 + (6/217 : ℝ) * _ctx.order4 + (1/434 : ℝ) * _ctx.fail1 + (1/217 : ℝ) * a13 + (52/217 : ℝ) * a14 + (9/217 : ℝ) * a20 + (59/62 : ℝ) * a29 + (3/217 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1191 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a25 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a27 : h 0 ≤ (2/13 : ℝ))
    (a28 : -(h 1) < (-1/8 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1192 h delta _ctx _hno a13 a14 a20 f0
  by_cases p1 : h 0 ≤ (7/45 : ℝ)
  swap
  · have f1 : -(h 0) < (-7/45 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1193 h delta _ctx _hno a27 f1
  by_cases p2 : h 1 ≤ (9/70 : ℝ)
  swap
  · have f2 : -(h 1) < (-9/70 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1194 h delta _ctx _hno a14 a18 a20 a24 a25 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1209 h delta _ctx _hno a14 a18 a20 a24 a25 a27 a28 p2 f3
  by_cases p4 : h 4 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 4) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1215 h delta _ctx _hno a13 a14 a20 a25 a28 p2 f4
  apply _hno 55
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (7/45 : ℝ)) ∧ (h 1 ≤ (9/70 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (4/35 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_1190 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a25 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    (a27 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * a14 + (4/5 : ℝ) * a25 + (1/5 : ℝ) * a27
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1189 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a26 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/217 : ℝ) * _ctx.order3 + (6/217 : ℝ) * _ctx.order4 + (1/434 : ℝ) * _ctx.fail1 + (1/217 : ℝ) * a13 + (52/217 : ℝ) * a14 + (9/217 : ℝ) * a20 + (59/62 : ℝ) * a26 + (3/217 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1188 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a25 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1189 h delta _ctx _hno a13 a14 a20 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1190 h delta _ctx _hno a14 a25 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1191 h delta _ctx _hno a13 a14 a18 a20 a24 a25 p1 f2
  apply _hno 2
  change (((2 : ℝ) * (delta)) ≤ (7/32 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ))
  exact ⟨p0, p1, p2⟩

end RealPinwheel.WeakSevenBandData
