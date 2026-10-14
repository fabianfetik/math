import Pinwheel.WeakSevenBandData.CoverChunks.Upper000

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem upper_node_4227 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a38 : h 0 ≤ (4/23 : ℝ))
    (a43 : -(h 0) < (-4/21 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a38 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4226 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a42 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4225 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a33 : -(h 3) < (-1/9 : ℝ))
    (a35 : -(h 0) < (-1/6 : ℝ))
    (a36 : ((-5 : ℝ) * (h 1)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ))
    (a38 : h 0 ≤ (4/23 : ℝ))
    (a41 : -(h 5) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4226 h delta _ctx _hno a27 f0
  by_cases p1 : h 0 ≤ (4/21 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/21 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4227 h delta _ctx _hno a38 f1
  by_cases p2 : h 1 ≤ (2/17 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4228 h delta _ctx _hno a27 a33 a35 a36 a41 f2
  apply _hno 155
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (4/21 : ℝ)) ∧ (h 1 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem upper_node_4224 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a35 : -(h 0) < (-1/6 : ℝ))
    (a36 : ((-5 : ℝ) * (h 1)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ))
    (a40 : -(h 4) < (-9/80 : ℝ))
    (a45 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (5/26 : ℝ) * _ctx.order2 + (5/13 : ℝ) * _ctx.order3 + (1/26 : ℝ) * _ctx.lower + (5/26 : ℝ) * a35 + (1/26 : ℝ) * a36 + (15/26 : ℝ) * a40 + (5/26 : ℝ) * a45 + (5/26 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4223 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a35 : -(h 0) < (-1/6 : ℝ))
    (a36 : ((-5 : ℝ) * (h 1)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ))
    (a40 : -(h 4) < (-9/80 : ℝ))
    (a44 : -(h 2) < (-5/44 : ℝ))
    (a51 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (5/26 : ℝ) * _ctx.order3 + (1/26 : ℝ) * _ctx.lower + (5/26 : ℝ) * a35 + (1/26 : ℝ) * a36 + (5/13 : ℝ) * a40 + (5/26 : ℝ) * a44 + (5/26 : ℝ) * a51 + (5/26 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4222 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a35 : -(h 0) < (-1/6 : ℝ))
    (a36 : ((-5 : ℝ) * (h 1)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ))
    (a50 : -(h 4) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (5/21 : ℝ) * _ctx.order2 + (10/21 : ℝ) * _ctx.order3 + (5/21 : ℝ) * _ctx.min + (2/7 : ℝ) * _ctx.lower + (5/21 : ℝ) * a35 + (1/21 : ℝ) * a36 + (5/7 : ℝ) * a50 + (5/21 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4221 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a35 : -(h 0) < (-1/6 : ℝ))
    (a36 : ((-5 : ℝ) * (h 1)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ))
    (a40 : -(h 4) < (-9/80 : ℝ))
    (a49 : -(h 3) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (5/21 : ℝ) * _ctx.order2 + (5/21 : ℝ) * _ctx.min + (2/7 : ℝ) * _ctx.lower + (5/21 : ℝ) * a35 + (1/21 : ℝ) * a36 + (5/21 : ℝ) * a40 + (10/21 : ℝ) * a49 + (5/21 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4220 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a35 : -(h 0) < (-1/6 : ℝ))
    (a40 : -(h 4) < (-9/80 : ℝ))
    (a48 : -(h 2) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order1 + (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a35 + (2/5 : ℝ) * a40 + (2/5 : ℝ) * a48 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4219 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a39 : h 1 ≤ (1/8 : ℝ))
    (a47 : -(h 1) < (-4/31 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a39 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4218 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a36 : ((-5 : ℝ) * (h 1)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ))
    (a40 : -(h 4) < (-9/80 : ℝ))
    (a44 : -(h 2) < (-5/44 : ℝ))
    (a46 : -(h 0) < (-4/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (5/21 : ℝ) * _ctx.order3 + (5/21 : ℝ) * _ctx.min + (2/7 : ℝ) * _ctx.lower + (1/21 : ℝ) * a36 + (10/21 : ℝ) * a40 + (5/21 : ℝ) * a44 + (5/21 : ℝ) * a46 + (5/21 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4217 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a35 : -(h 0) < (-1/6 : ℝ))
    (a36 : ((-5 : ℝ) * (h 1)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ))
    (a40 : -(h 4) < (-9/80 : ℝ))
    (a44 : -(h 2) < (-5/44 : ℝ))
    (a45 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a54 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (10/53 : ℝ) * _ctx.order3 + (10/53 : ℝ) * a35 + (2/53 : ℝ) * a36 + (20/53 : ℝ) * a40 + (10/53 : ℝ) * a44 + (1/53 : ℝ) * a45 + (10/53 : ℝ) * a54 + (10/53 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4216 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a35 : -(h 0) < (-1/6 : ℝ))
    (a44 : -(h 2) < (-5/44 : ℝ))
    (a45 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a48 : -(h 1) < (-7/60 : ℝ))
    (a53 : -(h 4) < (-5/44 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a44 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a48 + (1/3 : ℝ) * a53 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4215 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a35 : -(h 0) < (-1/6 : ℝ))
    (a40 : -(h 4) < (-9/80 : ℝ))
    (a45 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a52 : -(h 2) < (-4/35 : ℝ))
    (a55 : -(h 1) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a35 + (1/3 : ℝ) * a40 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a52 + (1/6 : ℝ) * a55 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4214 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a38 : h 0 ≤ (4/23 : ℝ))
    (a54 : -(h 0) < (-4/21 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a38 + (1 : ℝ) * a54
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4213 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a53 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a53
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4212 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a35 : -(h 0) < (-1/6 : ℝ))
    (a38 : h 0 ≤ (4/23 : ℝ))
    (a40 : -(h 4) < (-9/80 : ℝ))
    (a45 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a52 : -(h 2) < (-4/35 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4213 h delta _ctx _hno a27 f0
  by_cases p1 : h 0 ≤ (4/21 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/21 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4214 h delta _ctx _hno a38 f1
  by_cases p2 : h 1 ≤ (2/17 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4215 h delta _ctx _hno a35 a40 a45 a52 f2
  apply _hno 155
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (4/21 : ℝ)) ∧ (h 1 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem upper_node_4211 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a35 : -(h 0) < (-1/6 : ℝ))
    (a40 : -(h 4) < (-9/80 : ℝ))
    (a44 : -(h 2) < (-5/44 : ℝ))
    (a45 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a51 : -(h 1) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a35 + (1/3 : ℝ) * a40 + (1/6 : ℝ) * a44 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a51 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4210 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a38 : h 0 ≤ (4/23 : ℝ))
    (a50 : -(h 0) < (-2/11 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a38 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4209 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a49 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4208 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a35 : -(h 0) < (-1/6 : ℝ))
    (a36 : ((-5 : ℝ) * (h 1)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ))
    (a38 : h 0 ≤ (4/23 : ℝ))
    (a40 : -(h 4) < (-9/80 : ℝ))
    (a44 : -(h 2) < (-5/44 : ℝ))
    (a45 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a48 : -(h 1) < (-7/60 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4209 h delta _ctx _hno a27 f0
  by_cases p1 : h 0 ≤ (2/11 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/11 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4210 h delta _ctx _hno a38 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4211 h delta _ctx _hno a35 a40 a44 a45 f2
  by_cases p3 : h 2 ≤ (4/35 : ℝ)
  swap
  · have f3 : -(h 2) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_4212 h delta _ctx _hno a27 a35 a38 a40 a45 f3
  by_cases p4 : h 4 ≤ (5/44 : ℝ)
  swap
  · have f4 : -(h 4) < (-5/44 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_4216 h delta _ctx _hno a35 a44 a45 a48 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_4217 h delta _ctx _hno a35 a36 a40 a44 a45 f5
  apply _hno 63
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (2/11 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 2 ≤ (4/35 : ℝ)) ∧ (h 4 ≤ (5/44 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_4207 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a38 : h 0 ≤ (4/23 : ℝ))
    (a47 : -(h 0) < (-2/11 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a38 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4206 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a46 : ((-2 : ℝ) * (delta)) < (-3/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4205 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a35 : -(h 0) < (-1/6 : ℝ))
    (a36 : ((-5 : ℝ) * (h 1)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ))
    (a38 : h 0 ≤ (4/23 : ℝ))
    (a40 : -(h 4) < (-9/80 : ℝ))
    (a44 : -(h 2) < (-5/44 : ℝ))
    (a45 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/13 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4206 h delta _ctx _hno a27 f0
  by_cases p1 : h 0 ≤ (2/11 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/11 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4207 h delta _ctx _hno a38 f1
  by_cases p2 : h 1 ≤ (7/60 : ℝ)
  swap
  · have f2 : -(h 1) < (-7/60 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4208 h delta _ctx _hno a27 a35 a36 a38 a40 a44 a45 f2
  apply _hno 153
  change (((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)) ∧ (h 0 ≤ (2/11 : ℝ)) ∧ (h 1 ≤ (7/60 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem upper_node_4204 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a35 : -(h 0) < (-1/6 : ℝ))
    (a36 : ((-5 : ℝ) * (h 1)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ))
    (a38 : h 0 ≤ (4/23 : ℝ))
    (a39 : h 1 ≤ (1/8 : ℝ))
    (a40 : -(h 4) < (-9/80 : ℝ))
    (a44 : -(h 2) < (-5/44 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4205 h delta _ctx _hno a27 a35 a36 a38 a40 a44 f0
  by_cases p1 : h 0 ≤ (4/23 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/23 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4218 h delta _ctx _hno a36 a40 a44 f1
  by_cases p2 : h 1 ≤ (4/31 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/31 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4219 h delta _ctx _hno a39 f2
  by_cases p3 : h 2 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_4220 h delta _ctx _hno a35 a40 f3
  by_cases p4 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_4221 h delta _ctx _hno a35 a36 a40 f4
  by_cases p5 : h 4 ≤ (4/35 : ℝ)
  swap
  · have f5 : -(h 4) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_4222 h delta _ctx _hno a35 a36 f5
  by_cases p6 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f6 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact upper_node_4223 h delta _ctx _hno a35 a36 a40 a44 f6
  apply _hno 80
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (4/23 : ℝ)) ∧ (h 1 ≤ (4/31 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 4 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem upper_node_4203 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a39 : h 1 ≤ (1/8 : ℝ))
    (a43 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a39 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4202 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a38 : h 0 ≤ (4/23 : ℝ))
    (a42 : -(h 0) < (-3/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a38 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4201 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4200 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a35 : -(h 0) < (-1/6 : ℝ))
    (a36 : ((-5 : ℝ) * (h 1)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ))
    (a38 : h 0 ≤ (4/23 : ℝ))
    (a39 : h 1 ≤ (1/8 : ℝ))
    (a40 : -(h 4) < (-9/80 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4201 h delta _ctx _hno a27 f0
  by_cases p1 : h 0 ≤ (3/17 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/17 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4202 h delta _ctx _hno a38 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4203 h delta _ctx _hno a39 f2
  by_cases p3 : h 2 ≤ (5/44 : ℝ)
  swap
  · have f3 : -(h 2) < (-5/44 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_4204 h delta _ctx _hno a27 a35 a36 a38 a39 a40 f3
  by_cases p4 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_4224 h delta _ctx _hno a35 a36 a40 f4
  apply _hno 76
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/17 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (5/44 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_4199 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a39 : -(h 1) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.lower + (1/3 : ℝ) * a13 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4198 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : -(h 3) < (-1/9 : ℝ))
    (a36 : ((-5 : ℝ) * (h 1)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ))
    (a38 : -(h 0) < (-4/23 : ℝ))
    (a43 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (5/26 : ℝ) * _ctx.order2 + (5/26 : ℝ) * _ctx.order4 + (1/26 : ℝ) * _ctx.lower + (5/13 : ℝ) * a33 + (1/26 : ℝ) * a36 + (5/26 : ℝ) * a38 + (5/13 : ℝ) * a43 + (5/26 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4197 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : -(h 3) < (-1/9 : ℝ))
    (a36 : ((-5 : ℝ) * (h 1)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ))
    (a38 : -(h 0) < (-4/23 : ℝ))
    (a42 : -(h 2) < (-5/44 : ℝ))
    (a48 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (5/26 : ℝ) * _ctx.order4 + (1/26 : ℝ) * _ctx.lower + (5/26 : ℝ) * a33 + (1/26 : ℝ) * a36 + (5/26 : ℝ) * a38 + (5/26 : ℝ) * a42 + (5/13 : ℝ) * a48 + (5/26 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4196 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a36 : ((-5 : ℝ) * (h 1)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ))
    (a38 : -(h 0) < (-4/23 : ℝ))
    (a42 : -(h 2) < (-5/44 : ℝ))
    (a47 : -(h 4) < (-5/44 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (5/21 : ℝ) * _ctx.order3 + (5/21 : ℝ) * _ctx.min + (2/7 : ℝ) * _ctx.lower + (1/21 : ℝ) * a36 + (5/21 : ℝ) * a38 + (5/21 : ℝ) * a42 + (10/21 : ℝ) * a47 + (5/21 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4195 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a26 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 4)) < (-1 : ℝ))
    (a33 : -(h 3) < (-1/9 : ℝ))
    (a36 : ((-5 : ℝ) * (h 1)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ))
    (a38 : -(h 0) < (-4/23 : ℝ))
    (a46 : -(h 2) < (-4/35 : ℝ))
    (a53 : -(h 5) < (-3/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (9/64 : ℝ) * _ctx.lower + (5/128 : ℝ) * a26 + (15/64 : ℝ) * a33 + (3/128 : ℝ) * a36 + (15/64 : ℝ) * a38 + (15/64 : ℝ) * a46 + (15/64 : ℝ) * a53 + (15/64 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4194 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : -(h 3) < (-1/9 : ℝ))
    (a36 : ((-5 : ℝ) * (h 1)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ))
    (a38 : -(h 0) < (-4/23 : ℝ))
    (a46 : -(h 2) < (-4/35 : ℝ))
    (a52 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (5/21 : ℝ) * _ctx.min + (2/7 : ℝ) * _ctx.lower + (5/21 : ℝ) * a33 + (1/21 : ℝ) * a36 + (5/21 : ℝ) * a38 + (5/21 : ℝ) * a46 + (5/21 : ℝ) * a52 + (5/21 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4193 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a26 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 4)) < (-1 : ℝ))
    (a36 : ((-5 : ℝ) * (h 1)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ))
    (a38 : -(h 0) < (-4/23 : ℝ))
    (a51 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (15/49 : ℝ) * _ctx.order2 + (15/49 : ℝ) * _ctx.min + (24/49 : ℝ) * _ctx.lower + (5/98 : ℝ) * a26 + (3/98 : ℝ) * a36 + (15/49 : ℝ) * a38 + (30/49 : ℝ) * a51 + (15/49 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4192 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a26 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 4)) < (-1 : ℝ))
    (a33 : -(h 3) < (-1/9 : ℝ))
    (a38 : -(h 0) < (-4/23 : ℝ))
    (a50 : -(h 2) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/22 : ℝ) * _ctx.order1 + (3/11 : ℝ) * _ctx.min + (6/11 : ℝ) * _ctx.lower + (1/22 : ℝ) * a26 + (3/11 : ℝ) * a33 + (3/11 : ℝ) * a38 + (9/22 : ℝ) * a50 + (3/11 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4191 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a26 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 4)) < (-1 : ℝ))
    (a33 : -(h 3) < (-1/9 : ℝ))
    (a38 : -(h 0) < (-4/23 : ℝ))
    (a46 : -(h 2) < (-4/35 : ℝ))
    (a49 : -(h 1) < (-4/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/11 : ℝ) * _ctx.min + (6/11 : ℝ) * _ctx.lower + (1/22 : ℝ) * a26 + (3/11 : ℝ) * a33 + (3/11 : ℝ) * a38 + (3/11 : ℝ) * a46 + (3/22 : ℝ) * a49 + (3/11 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4190 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a40 : h 0 ≤ (3/17 : ℝ))
    (a48 : -(h 0) < (-3/16 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a40 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4189 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a47 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4188 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a26 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 4)) < (-1 : ℝ))
    (a27 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a33 : -(h 3) < (-1/9 : ℝ))
    (a36 : ((-5 : ℝ) * (h 1)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ))
    (a38 : -(h 0) < (-4/23 : ℝ))
    (a40 : h 0 ≤ (3/17 : ℝ))
    (a46 : -(h 2) < (-4/35 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4189 h delta _ctx _hno a27 f0
  by_cases p1 : h 0 ≤ (3/16 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/16 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4190 h delta _ctx _hno a40 f1
  by_cases p2 : h 1 ≤ (4/33 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4191 h delta _ctx _hno a26 a33 a38 a46 f2
  by_cases p3 : h 2 ≤ (3/25 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_4192 h delta _ctx _hno a26 a33 a38 f3
  by_cases p4 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_4193 h delta _ctx _hno a26 a36 a38 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_4194 h delta _ctx _hno a33 a36 a38 a46 f5
  by_cases p6 : h 5 ≤ (3/28 : ℝ)
  swap
  · have f6 : -(h 5) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact upper_node_4195 h delta _ctx _hno a26 a33 a36 a38 a46 f6
  apply _hno 154
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (3/16 : ℝ)) ∧ (h 1 ≤ (4/33 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ)) ∧ (h 5 ≤ (3/28 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem upper_node_4187 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a26 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 4)) < (-1 : ℝ))
    (a33 : -(h 3) < (-1/9 : ℝ))
    (a38 : -(h 0) < (-4/23 : ℝ))
    (a42 : -(h 2) < (-5/44 : ℝ))
    (a45 : -(h 1) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/11 : ℝ) * _ctx.min + (6/11 : ℝ) * _ctx.lower + (1/22 : ℝ) * a26 + (3/11 : ℝ) * a33 + (3/11 : ℝ) * a38 + (3/11 : ℝ) * a42 + (3/22 : ℝ) * a45 + (3/11 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4186 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a40 : h 0 ≤ (3/17 : ℝ))
    (a44 : -(h 0) < (-2/11 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a40 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4185 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4184 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a26 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 4)) < (-1 : ℝ))
    (a27 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a33 : -(h 3) < (-1/9 : ℝ))
    (a36 : ((-5 : ℝ) * (h 1)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ))
    (a38 : -(h 0) < (-4/23 : ℝ))
    (a40 : h 0 ≤ (3/17 : ℝ))
    (a42 : -(h 2) < (-5/44 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4185 h delta _ctx _hno a27 f0
  by_cases p1 : h 0 ≤ (2/11 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/11 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4186 h delta _ctx _hno a40 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4187 h delta _ctx _hno a26 a33 a38 a42 f2
  by_cases p3 : h 2 ≤ (4/35 : ℝ)
  swap
  · have f3 : -(h 2) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_4188 h delta _ctx _hno a26 a27 a33 a36 a38 a40 f3
  by_cases p4 : h 4 ≤ (5/44 : ℝ)
  swap
  · have f4 : -(h 4) < (-5/44 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_4196 h delta _ctx _hno a36 a38 a42 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_4197 h delta _ctx _hno a33 a36 a38 a42 f5
  apply _hno 63
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (2/11 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 2 ≤ (4/35 : ℝ)) ∧ (h 4 ≤ (5/44 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_4183 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a41 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.lower + (1/3 : ℝ) * a13 + (1 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4182 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : -(h 3) < (-1/9 : ℝ))
    (a36 : ((-5 : ℝ) * (h 1)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ))
    (a40 : -(h 0) < (-3/17 : ℝ))
    (a46 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (5/26 : ℝ) * _ctx.order2 + (5/26 : ℝ) * _ctx.order4 + (1/26 : ℝ) * _ctx.lower + (5/13 : ℝ) * a33 + (1/26 : ℝ) * a36 + (5/26 : ℝ) * a40 + (5/13 : ℝ) * a46 + (5/26 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4181 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a36 : ((-5 : ℝ) * (h 1)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ))
    (a40 : -(h 0) < (-3/17 : ℝ))
    (a45 : -(h 4) < (-5/44 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (5/21 : ℝ) * _ctx.order2 + (10/21 : ℝ) * _ctx.order3 + (5/21 : ℝ) * _ctx.min + (2/7 : ℝ) * _ctx.lower + (1/21 : ℝ) * a36 + (5/21 : ℝ) * a40 + (5/7 : ℝ) * a45 + (5/21 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4180 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a26 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 4)) < (-1 : ℝ))
    (a33 : -(h 3) < (-1/9 : ℝ))
    (a36 : ((-5 : ℝ) * (h 1)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ))
    (a40 : -(h 0) < (-3/17 : ℝ))
    (a44 : -(h 2) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (15/49 : ℝ) * _ctx.min + (24/49 : ℝ) * _ctx.lower + (5/98 : ℝ) * a26 + (15/49 : ℝ) * a33 + (3/98 : ℝ) * a36 + (15/49 : ℝ) * a40 + (15/49 : ℝ) * a44 + (15/49 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4179 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a26 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 4)) < (-1 : ℝ))
    (a33 : -(h 3) < (-1/9 : ℝ))
    (a40 : -(h 0) < (-3/17 : ℝ))
    (a43 : -(h 1) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/11 : ℝ) * _ctx.order2 + (3/11 : ℝ) * _ctx.min + (6/11 : ℝ) * _ctx.lower + (1/22 : ℝ) * a26 + (6/11 : ℝ) * a33 + (3/11 : ℝ) * a40 + (3/22 : ℝ) * a43 + (3/11 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4178 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : h 0 ≤ (8/45 : ℝ))
    (a42 : -(h 0) < (-2/11 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4177 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4176 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a26 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 4)) < (-1 : ℝ))
    (a27 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a30 : h 0 ≤ (8/45 : ℝ))
    (a33 : -(h 3) < (-1/9 : ℝ))
    (a36 : ((-5 : ℝ) * (h 1)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ))
    (a40 : -(h 0) < (-3/17 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4177 h delta _ctx _hno a27 f0
  by_cases p1 : h 0 ≤ (2/11 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/11 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4178 h delta _ctx _hno a30 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4179 h delta _ctx _hno a26 a33 a40 f2
  by_cases p3 : h 2 ≤ (4/35 : ℝ)
  swap
  · have f3 : -(h 2) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_4180 h delta _ctx _hno a26 a33 a36 a40 f3
  by_cases p4 : h 4 ≤ (5/44 : ℝ)
  swap
  · have f4 : -(h 4) < (-5/44 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_4181 h delta _ctx _hno a36 a40 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_4182 h delta _ctx _hno a33 a36 a40 f5
  apply _hno 63
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (2/11 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 2 ≤ (4/35 : ℝ)) ∧ (h 4 ≤ (5/44 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_4175 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a39 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4174 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a26 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 4)) < (-1 : ℝ))
    (a27 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a30 : h 0 ≤ (8/45 : ℝ))
    (a33 : -(h 3) < (-1/9 : ℝ))
    (a36 : ((-5 : ℝ) * (h 1)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ))
    (a38 : -(h 0) < (-4/23 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4175 h delta _ctx _hno a27 f0
  by_cases p1 : h 0 ≤ (3/17 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/17 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4176 h delta _ctx _hno a26 a27 a30 a33 a36 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4183 h delta _ctx _hno a13 f2
  by_cases p3 : h 2 ≤ (5/44 : ℝ)
  swap
  · have f3 : -(h 2) < (-5/44 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_4184 h delta _ctx _hno a26 a27 a33 a36 a38 p1 f3
  by_cases p4 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_4198 h delta _ctx _hno a33 a36 a38 f4
  apply _hno 76
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/17 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (5/44 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_4173 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a37 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a37
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4172 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a26 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 4)) < (-1 : ℝ))
    (a27 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a30 : h 0 ≤ (8/45 : ℝ))
    (a33 : -(h 3) < (-1/9 : ℝ))
    (a35 : -(h 0) < (-1/6 : ℝ))
    (a36 : ((-5 : ℝ) * (h 1)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4173 h delta _ctx _hno a27 f0
  by_cases p1 : h 0 ≤ (4/23 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/23 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4174 h delta _ctx _hno a13 a26 a27 a30 a33 a36 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4199 h delta _ctx _hno a13 f2
  by_cases p3 : h 4 ≤ (9/80 : ℝ)
  swap
  · have f3 : -(h 4) < (-9/80 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_4200 h delta _ctx _hno a27 a35 a36 p1 p2 f3
  by_cases p4 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_4225 h delta _ctx _hno a27 a33 a35 a36 p1 f4
  apply _hno 52
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (4/23 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (9/80 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_4171 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a26 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 4)) < (-1 : ℝ))
    (a27 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a30 : h 0 ≤ (8/45 : ℝ))
    (a33 : -(h 3) < (-1/9 : ℝ))
    (a35 : -(h 0) < (-1/6 : ℝ))
    : False := by
  by_cases p0 : ((5 : ℝ) * (h 1)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ)
  swap
  · have f0 : ((-5 : ℝ) * (h 1)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4172 h delta _ctx _hno a13 a26 a27 a30 a33 a35 f0
  by_cases p1 : ((5 : ℝ) * (h 2)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ)
  swap
  · have f1 : ((-5 : ℝ) * (h 2)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4234 h delta _ctx _hno p0 f1
  by_cases p2 : ((5 : ℝ) * (h 3)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ)
  swap
  · have f2 : ((-5 : ℝ) * (h 3)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4235 h delta _ctx _hno a26 a35 f2
  by_cases p3 : ((5 : ℝ) * (h 4)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ)
  swap
  · have f3 : ((-5 : ℝ) * (h 4)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_4236 h delta _ctx _hno a27 a35 f3
  by_cases p4 : ((5 : ℝ) * (h 5)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ)
  swap
  · have f4 : ((-5 : ℝ) * (h 5)) + ((-4 : ℝ) * (delta)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_4237 h delta _ctx _hno a27 a35 f4
  by_cases p5 : ((2 : ℝ) * (h 0)) + ((5 : ℝ) * (h 1)) ≤ (1 : ℝ)
  swap
  · have f5 : ((-2 : ℝ) * (h 0)) + ((-5 : ℝ) * (h 1)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_4238 h delta _ctx _hno a30 p0 f5
  by_cases p6 : ((2 : ℝ) * (h 0)) + ((5 : ℝ) * (h 2)) ≤ (1 : ℝ)
  swap
  · have f6 : ((-2 : ℝ) * (h 0)) + ((-5 : ℝ) * (h 2)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact upper_node_4239 h delta _ctx _hno a30 p1 f6
  by_cases p7 : ((2 : ℝ) * (h 0)) + ((5 : ℝ) * (h 3)) ≤ (1 : ℝ)
  swap
  · have f7 : ((-2 : ℝ) * (h 0)) + ((-5 : ℝ) * (h 3)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p7
      linarith only [hp]
    exact upper_node_4240 h delta _ctx _hno a30 f7
  by_cases p8 : ((2 : ℝ) * (h 0)) + ((5 : ℝ) * (h 4)) ≤ (1 : ℝ)
  swap
  · have f8 : ((-2 : ℝ) * (h 0)) + ((-5 : ℝ) * (h 4)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p8
      linarith only [hp]
    exact upper_node_4241 h delta _ctx _hno a30 f8
  by_cases p9 : ((2 : ℝ) * (h 0)) + ((5 : ℝ) * (h 5)) ≤ (1 : ℝ)
  swap
  · have f9 : ((-2 : ℝ) * (h 0)) + ((-5 : ℝ) * (h 5)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p9
      linarith only [hp]
    exact upper_node_4242 h delta _ctx _hno a30 f9
  apply _hno 152
  change (((5 : ℝ) * (h 1)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ)) ∧ (((5 : ℝ) * (h 2)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ)) ∧ (((5 : ℝ) * (h 3)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ)) ∧ (((5 : ℝ) * (h 4)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ)) ∧ (((5 : ℝ) * (h 5)) + ((4 : ℝ) * (delta)) ≤ (1 : ℝ)) ∧ (((2 : ℝ) * (h 0)) + ((5 : ℝ) * (h 1)) ≤ (1 : ℝ)) ∧ (((2 : ℝ) * (h 0)) + ((5 : ℝ) * (h 2)) ≤ (1 : ℝ)) ∧ (((2 : ℝ) * (h 0)) + ((5 : ℝ) * (h 3)) ≤ (1 : ℝ)) ∧ (((2 : ℝ) * (h 0)) + ((5 : ℝ) * (h 4)) ≤ (1 : ℝ)) ∧ (((2 : ℝ) * (h 0)) + ((5 : ℝ) * (h 5)) ≤ (1 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9⟩

theorem upper_node_4170 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a34
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4169 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a26 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 4)) < (-1 : ℝ))
    (a27 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a28 : -(h 0) < (-4/25 : ℝ))
    (a30 : h 0 ≤ (8/45 : ℝ))
    (a33 : -(h 3) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4170 h delta _ctx _hno a27 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4171 h delta _ctx _hno a13 a26 a27 a30 a33 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4243 h delta _ctx _hno a13 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_4244 h delta _ctx _hno a26 a28 a33 f3
  by_cases p4 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_4245 h delta _ctx _hno a13 a27 a28 p1 f4
  apply _hno 57
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_4168 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : ((3 : ℝ) * (h 2)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a32 : -(h 2) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.lower + (1/3 : ℝ) * a14 + (1 : ℝ) * a32
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4167 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a31 : -(h 1) < (-5/38 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.lower + (1/3 : ℝ) * a13 + (1 : ℝ) * a31
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4166 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a26 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 4)) < (-1 : ℝ))
    (a30 : -(h 0) < (-8/45 : ℝ))
    (a36 : -(h 1) + ((-8 : ℝ) * (h 5)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (9/14 : ℝ) * _ctx.order2 + (9/7 : ℝ) * _ctx.order3 + (15/14 : ℝ) * _ctx.order4 + (9/14 : ℝ) * _ctx.lower + (1/7 : ℝ) * a26 + (9/14 : ℝ) * a30 + (3/14 : ℝ) * a36 + (9/14 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4165 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a34 : h 1 + ((8 : ℝ) * (h 3)) ≤ (1 : ℝ))
    (a35 : -(h 1) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (8 : ℝ) * _ctx.order3 + (1 : ℝ) * a34 + (1 : ℝ) * a35
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4164 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : h 1 + ((8 : ℝ) * (h 2)) ≤ (1 : ℝ))
    (a34 : -(h 1) + ((-8 : ℝ) * (h 3)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (8 : ℝ) * _ctx.order2 + (1 : ℝ) * a33 + (1 : ℝ) * a34
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4163 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a26 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 4)) < (-1 : ℝ))
    (a30 : -(h 0) < (-8/45 : ℝ))
    (a33 : -(h 1) + ((-8 : ℝ) * (h 2)) < (-1 : ℝ))
    (a43 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/8 : ℝ) * _ctx.order3 + (3/32 : ℝ) * _ctx.order4 + (3/8 : ℝ) * _ctx.lower + (7/64 : ℝ) * a26 + (3/8 : ℝ) * a30 + (3/64 : ℝ) * a33 + (15/32 : ℝ) * a43 + (3/8 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4162 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a30 : -(h 0) < (-8/45 : ℝ))
    (a42 : -(h 4) < (-5/44 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order1 + (2/5 : ℝ) * _ctx.order2 + (3/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a30 + (4/5 : ℝ) * a42 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4161 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 3)) < (-1 : ℝ))
    (a26 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 4)) < (-1 : ℝ))
    (a30 : -(h 0) < (-8/45 : ℝ))
    (a41 : -(h 2) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/7 : ℝ) * _ctx.min + (6/7 : ℝ) * _ctx.lower + (1/14 : ℝ) * a19 + (1/14 : ℝ) * a26 + (3/7 : ℝ) * a30 + (3/7 : ℝ) * a41 + (3/7 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4160 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a40 : -(h 1) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.lower + (1/3 : ℝ) * a13 + (1 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4159 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 3)) < (-1 : ℝ))
    (a26 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 4)) < (-1 : ℝ))
    (a37 : -(h 2) < (-1/9 : ℝ))
    (a39 : -(h 0) < (-2/11 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/7 : ℝ) * _ctx.min + (6/7 : ℝ) * _ctx.lower + (1/14 : ℝ) * a19 + (1/14 : ℝ) * a26 + (3/7 : ℝ) * a37 + (3/7 : ℝ) * a39 + (3/7 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4158 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a38 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a38
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4157 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a19 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 3)) < (-1 : ℝ))
    (a26 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 4)) < (-1 : ℝ))
    (a27 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a30 : -(h 0) < (-8/45 : ℝ))
    (a33 : -(h 1) + ((-8 : ℝ) * (h 2)) < (-1 : ℝ))
    (a37 : -(h 2) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4158 h delta _ctx _hno a27 f0
  by_cases p1 : h 0 ≤ (2/11 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/11 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4159 h delta _ctx _hno a19 a26 a37 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4160 h delta _ctx _hno a13 f2
  by_cases p3 : h 2 ≤ (4/35 : ℝ)
  swap
  · have f3 : -(h 2) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_4161 h delta _ctx _hno a19 a26 a30 f3
  by_cases p4 : h 4 ≤ (5/44 : ℝ)
  swap
  · have f4 : -(h 4) < (-5/44 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_4162 h delta _ctx _hno a30 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_4163 h delta _ctx _hno a26 a30 a33 f5
  apply _hno 63
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (2/11 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 2 ≤ (4/35 : ℝ)) ∧ (h 4 ≤ (5/44 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_4156 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a36 : -(h 1) < (-5/36 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.lower + (1/3 : ℝ) * a13 + (1 : ℝ) * a36
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4155 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 3)) < (-1 : ℝ))
    (a26 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 4)) < (-1 : ℝ))
    (a33 : -(h 1) + ((-8 : ℝ) * (h 2)) < (-1 : ℝ))
    (a35 : -(h 0) < (-3/16 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/17 : ℝ) * _ctx.order4 + (15/17 : ℝ) * _ctx.min + (27/17 : ℝ) * _ctx.lower + (2/17 : ℝ) * a19 + (3/34 : ℝ) * a26 + (3/34 : ℝ) * a33 + (12/17 : ℝ) * a35 + (12/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4154 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a34
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4153 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a19 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 3)) < (-1 : ℝ))
    (a26 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 4)) < (-1 : ℝ))
    (a27 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a30 : -(h 0) < (-8/45 : ℝ))
    (a33 : -(h 1) + ((-8 : ℝ) * (h 2)) < (-1 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4154 h delta _ctx _hno a27 f0
  by_cases p1 : h 0 ≤ (3/16 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/16 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4155 h delta _ctx _hno a19 a26 a33 f1
  by_cases p2 : h 1 ≤ (5/36 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/36 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4156 h delta _ctx _hno a13 f2
  by_cases p3 : h 2 ≤ (1/9 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_4157 h delta _ctx _hno a13 a19 a26 a27 a30 a33 f3
  apply _hno 61
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (3/16 : ℝ)) ∧ (h 1 ≤ (5/36 : ℝ)) ∧ (h 2 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_4152 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 3)) < (-1 : ℝ))
    (a32 : ((-4 : ℝ) * (h 0)) + -(h 1) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.order2 + (1 : ℝ) * _ctx.order3 + (3 : ℝ) * _ctx.order4 + (5 : ℝ) * _ctx.min + (7 : ℝ) * _ctx.lower + (1/2 : ℝ) * a19 + (1/2 : ℝ) * a32 + (2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4151 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a27 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a31 : -(h 1) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * a13 + (3 : ℝ) * a27 + (1 : ℝ) * a31
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4150 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a19 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 3)) < (-1 : ℝ))
    (a26 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 4)) < (-1 : ℝ))
    (a27 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a30 : -(h 0) < (-8/45 : ℝ))
    : False := by
  by_cases p0 : h 1 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ)
  swap
  · have f0 : -(h 1) + ((-8 : ℝ) * (delta)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4151 h delta _ctx _hno a13 a27 f0
  by_cases p1 : ((4 : ℝ) * (h 0)) + h 1 ≤ (1 : ℝ)
  swap
  · have f1 : ((-4 : ℝ) * (h 0)) + -(h 1) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4152 h delta _ctx _hno a19 f1
  by_cases p2 : h 1 + ((8 : ℝ) * (h 2)) ≤ (1 : ℝ)
  swap
  · have f2 : -(h 1) + ((-8 : ℝ) * (h 2)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4153 h delta _ctx _hno a13 a19 a26 a27 a30 f2
  by_cases p3 : h 1 + ((8 : ℝ) * (h 3)) ≤ (1 : ℝ)
  swap
  · have f3 : -(h 1) + ((-8 : ℝ) * (h 3)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_4164 h delta _ctx _hno p2 f3
  by_cases p4 : h 1 + ((8 : ℝ) * (h 4)) ≤ (1 : ℝ)
  swap
  · have f4 : -(h 1) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_4165 h delta _ctx _hno p3 f4
  by_cases p5 : h 1 + ((8 : ℝ) * (h 5)) ≤ (1 : ℝ)
  swap
  · have f5 : -(h 1) + ((-8 : ℝ) * (h 5)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_4166 h delta _ctx _hno a26 a30 f5
  apply _hno 50
  change (h 1 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ)) ∧ (((4 : ℝ) * (h 0)) + h 1 ≤ (1 : ℝ)) ∧ (h 1 + ((8 : ℝ) * (h 2)) ≤ (1 : ℝ)) ∧ (h 1 + ((8 : ℝ) * (h 3)) ≤ (1 : ℝ)) ∧ (h 1 + ((8 : ℝ) * (h 4)) ≤ (1 : ℝ)) ∧ (h 1 + ((8 : ℝ) * (h 5)) ≤ (1 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_4149 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a29 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a29
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_4148 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a14 : ((3 : ℝ) * (h 2)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a19 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 3)) < (-1 : ℝ))
    (a26 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 4)) < (-1 : ℝ))
    (a27 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a28 : -(h 0) < (-4/25 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4149 h delta _ctx _hno a27 f0
  by_cases p1 : h 0 ≤ (8/45 : ℝ)
  swap
  · have f1 : -(h 0) < (-8/45 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_4150 h delta _ctx _hno a13 a19 a26 a27 f1
  by_cases p2 : h 1 ≤ (5/38 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/38 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_4167 h delta _ctx _hno a13 f2
  by_cases p3 : h 2 ≤ (3/23 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_4168 h delta _ctx _hno a14 f3
  by_cases p4 : h 3 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_4169 h delta _ctx _hno a13 a26 a27 a28 p1 f4
  apply _hno 13
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (8/45 : ℝ)) ∧ (h 1 ≤ (5/38 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

end RealPinwheel.WeakSevenBandData
