import Pinwheel.WeakSevenBandData.CoverChunks.Upper038

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem upper_node_1187 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a22 : h 0 ≤ (1/6 : ℝ))
    (a23 : h 1 ≤ (5/36 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-10/47 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1188 h delta _ctx _hno a13 a14 a18 a20 a24 f0
  by_cases p1 : h 0 ≤ (4/25 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/25 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1221 h delta _ctx _hno a13 a14 a18 a22 a23 a24 p0 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1272 h delta _ctx _hno a13 a14 a18 a20 a23 a24 p0 p1 f2
  apply _hno 83
  change (((2 : ℝ) * (delta)) ≤ (10/47 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem upper_node_1186 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a23 : -(h 1) < (-5/36 : ℝ))
    (a32 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (18/59 : ℝ) * _ctx.order3 + (16/59 : ℝ) * _ctx.min + (34/59 : ℝ) * _ctx.lower + (3/59 : ℝ) * _ctx.fail1 + (2/59 : ℝ) * a20 + (18/59 : ℝ) * a23 + (36/59 : ℝ) * a32 + (18/59 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1185 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a23 : -(h 1) < (-5/36 : ℝ))
    (a28 : -(h 3) < (-3/28 : ℝ))
    (a31 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (41/157 : ℝ) * _ctx.min + (89/157 : ℝ) * _ctx.lower + (6/157 : ℝ) * a18 + (7/157 : ℝ) * a20 + (48/157 : ℝ) * a23 + (48/157 : ℝ) * a28 + (48/157 : ℝ) * a31 + (48/157 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1184 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : -(h 1) < (-5/36 : ℝ))
    (a30 : -(h 0) < (-3/20 : ℝ))
    (a41 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.order3 + (6/23 : ℝ) * _ctx.min + (12/23 : ℝ) * _ctx.lower + (1/23 : ℝ) * _ctx.fail1 + (6/23 : ℝ) * a23 + (4/23 : ℝ) * a30 + (12/23 : ℝ) * a41 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1183 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a23 : -(h 1) < (-5/36 : ℝ))
    (a40 : -(h 3) < (-7/57 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (48/157 : ℝ) * _ctx.order2 + (41/157 : ℝ) * _ctx.min + (89/157 : ℝ) * _ctx.lower + (6/157 : ℝ) * a18 + (7/157 : ℝ) * a20 + (48/157 : ℝ) * a23 + (96/157 : ℝ) * a40 + (48/157 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1182 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a23 : -(h 1) < (-5/36 : ℝ))
    (a35 : -(h 3) < (-1/9 : ℝ))
    (a39 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (41/157 : ℝ) * _ctx.min + (89/157 : ℝ) * _ctx.lower + (6/157 : ℝ) * a18 + (7/157 : ℝ) * a20 + (48/157 : ℝ) * a23 + (48/157 : ℝ) * a35 + (48/157 : ℝ) * a39 + (48/157 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1181 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : h 0 + ((6 : ℝ) * (h 1)) ≤ (1 : ℝ))
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a38 : -(h 1) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/649 : ℝ) * _ctx.order3 + (12/649 : ℝ) * _ctx.order4 + (6/649 : ℝ) * _ctx.lower + (1/649 : ℝ) * _ctx.fail1 + (104/649 : ℝ) * a15 + (18/649 : ℝ) * a20 + (630/649 : ℝ) * a38 + (6/649 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1180 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : -(h 1) < (-5/36 : ℝ))
    (a35 : -(h 3) < (-1/9 : ℝ))
    (a37 : -(h 0) < (-5/33 : ℝ))
    (a49 : -(h 5) < (-3/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.order4 + (6/29 : ℝ) * _ctx.lower + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a23 + (6/29 : ℝ) * a35 + (4/29 : ℝ) * a37 + (12/29 : ℝ) * a49 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1179 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a42 : h 4 ≤ (3/28 : ℝ))
    (a48 : -(h 4) < (-6/55 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a42 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1178 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a41 : h 2 ≤ (2/17 : ℝ))
    (a47 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a41 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1177 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : h 0 + ((6 : ℝ) * (h 1)) ≤ (1 : ℝ))
    (a37 : -(h 0) < (-5/33 : ℝ))
    (a46 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/7 : ℝ) * a15 + (1/7 : ℝ) * a37 + (6/7 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1176 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a23 : -(h 1) < (-5/36 : ℝ))
    (a35 : -(h 3) < (-1/9 : ℝ))
    (a43 : -(h 5) < (-2/19 : ℝ))
    (a45 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.lower + (1/23 : ℝ) * _ctx.fail1 + (3/92 : ℝ) * a18 + (6/23 : ℝ) * a23 + (6/23 : ℝ) * a35 + (6/23 : ℝ) * a43 + (13/92 : ℝ) * a45 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1175 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a38 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a44 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a38 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1174 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : h 0 + ((6 : ℝ) * (h 1)) ≤ (1 : ℝ))
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a23 : -(h 1) < (-5/36 : ℝ))
    (a35 : -(h 3) < (-1/9 : ℝ))
    (a37 : -(h 0) < (-5/33 : ℝ))
    (a38 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a41 : h 2 ≤ (2/17 : ℝ))
    (a42 : h 4 ≤ (3/28 : ℝ))
    (a43 : -(h 5) < (-2/19 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1175 h delta _ctx _hno a38 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1176 h delta _ctx _hno a18 a23 a35 a43 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1177 h delta _ctx _hno a15 a37 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1178 h delta _ctx _hno a41 f3
  by_cases p4 : h 4 ≤ (6/55 : ℝ)
  swap
  · have f4 : -(h 4) < (-6/55 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1179 h delta _ctx _hno a42 f4
  by_cases p5 : h 5 ≤ (3/28 : ℝ)
  swap
  · have f5 : -(h 5) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1180 h delta _ctx _hno a23 a35 a37 f5
  apply _hno 88
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (6/55 : ℝ)) ∧ (h 5 ≤ (3/28 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_1173 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : -(h 1) < (-5/36 : ℝ))
    (a35 : -(h 3) < (-1/9 : ℝ))
    (a37 : -(h 0) < (-5/33 : ℝ))
    (a42 : -(h 4) < (-3/28 : ℝ))
    (a48 : -(h 5) < (-3/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.lower + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a23 + (6/29 : ℝ) * a35 + (4/29 : ℝ) * a37 + (6/29 : ℝ) * a42 + (6/29 : ℝ) * a48 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1172 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : -(h 1) < (-5/36 : ℝ))
    (a35 : -(h 3) < (-1/9 : ℝ))
    (a37 : -(h 0) < (-5/33 : ℝ))
    (a47 : -(h 4) < (-6/55 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.min + (12/23 : ℝ) * _ctx.lower + (1/23 : ℝ) * _ctx.fail1 + (6/23 : ℝ) * a23 + (6/23 : ℝ) * a35 + (4/23 : ℝ) * a37 + (6/23 : ℝ) * a47 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1171 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a41 : h 2 ≤ (2/17 : ℝ))
    (a46 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a41 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1170 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : h 0 + ((6 : ℝ) * (h 1)) ≤ (1 : ℝ))
    (a37 : -(h 0) < (-5/33 : ℝ))
    (a45 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/7 : ℝ) * a15 + (1/7 : ℝ) * a37 + (6/7 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1169 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : -(h 1) < (-5/36 : ℝ))
    (a35 : -(h 3) < (-1/9 : ℝ))
    (a42 : -(h 4) < (-3/28 : ℝ))
    (a44 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.min + (12/23 : ℝ) * _ctx.lower + (1/23 : ℝ) * _ctx.fail1 + (6/23 : ℝ) * a23 + (6/23 : ℝ) * a35 + (6/23 : ℝ) * a42 + (4/23 : ℝ) * a44 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1168 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a38 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a38 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1167 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : h 0 + ((6 : ℝ) * (h 1)) ≤ (1 : ℝ))
    (a23 : -(h 1) < (-5/36 : ℝ))
    (a35 : -(h 3) < (-1/9 : ℝ))
    (a37 : -(h 0) < (-5/33 : ℝ))
    (a38 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a41 : h 2 ≤ (2/17 : ℝ))
    (a42 : -(h 4) < (-3/28 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1168 h delta _ctx _hno a38 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1169 h delta _ctx _hno a23 a35 a42 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1170 h delta _ctx _hno a15 a37 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1171 h delta _ctx _hno a41 f3
  by_cases p4 : h 4 ≤ (6/55 : ℝ)
  swap
  · have f4 : -(h 4) < (-6/55 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1172 h delta _ctx _hno a23 a35 a37 f4
  by_cases p5 : h 5 ≤ (3/28 : ℝ)
  swap
  · have f5 : -(h 5) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1173 h delta _ctx _hno a23 a35 a37 a42 f5
  apply _hno 88
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (6/55 : ℝ)) ∧ (h 5 ≤ (3/28 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_1166 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a23 : -(h 1) < (-5/36 : ℝ))
    (a35 : -(h 3) < (-1/9 : ℝ))
    (a37 : -(h 0) < (-5/33 : ℝ))
    (a41 : -(h 2) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.min + (1/2 : ℝ) * _ctx.lower + (1/32 : ℝ) * a18 + (1/4 : ℝ) * a23 + (1/4 : ℝ) * a35 + (7/32 : ℝ) * a37 + (1/4 : ℝ) * a41 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1165 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : h 0 + ((6 : ℝ) * (h 1)) ≤ (1 : ℝ))
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a40 : -(h 1) < (-5/31 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/649 : ℝ) * _ctx.order3 + (12/649 : ℝ) * _ctx.order4 + (6/649 : ℝ) * _ctx.lower + (1/649 : ℝ) * _ctx.fail1 + (104/649 : ℝ) * a15 + (18/649 : ℝ) * a20 + (630/649 : ℝ) * a40 + (6/649 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1164 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : h 0 ≤ (4/25 : ℝ))
    (a39 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a25 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1163 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a23 : -(h 1) < (-5/36 : ℝ))
    (a35 : -(h 3) < (-1/9 : ℝ))
    (a37 : -(h 0) < (-5/33 : ℝ))
    (a38 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.min + (1/23 : ℝ) * _ctx.fail1 + (3/92 : ℝ) * a18 + (6/23 : ℝ) * a23 + (6/23 : ℝ) * a35 + (13/92 : ℝ) * a37 + (6/23 : ℝ) * a38 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1162 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : h 0 + ((6 : ℝ) * (h 1)) ≤ (1 : ℝ))
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a23 : -(h 1) < (-5/36 : ℝ))
    (a25 : h 0 ≤ (4/25 : ℝ))
    (a35 : -(h 3) < (-1/9 : ℝ))
    (a37 : -(h 0) < (-5/33 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1163 h delta _ctx _hno a18 a23 a35 a37 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1164 h delta _ctx _hno a25 f1
  by_cases p2 : h 1 ≤ (5/31 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/31 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1165 h delta _ctx _hno a15 a20 f2
  by_cases p3 : h 2 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1166 h delta _ctx _hno a18 a23 a35 a37 f3
  by_cases p4 : h 4 ≤ (3/28 : ℝ)
  swap
  · have f4 : -(h 4) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1167 h delta _ctx _hno a15 a23 a35 a37 p0 p3 f4
  by_cases p5 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1174 h delta _ctx _hno a15 a18 a23 a35 a37 p0 p3 p4 f5
  apply _hno 103
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (5/31 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (3/28 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_1161 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a23 : -(h 1) < (-5/36 : ℝ))
    (a36 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/74 : ℝ) * _ctx.order3 + (1/37 : ℝ) * _ctx.order4 + (1/444 : ℝ) * _ctx.fail1 + (26/111 : ℝ) * a14 + (3/74 : ℝ) * a20 + (1/74 : ℝ) * a23 + (419/444 : ℝ) * a36 + (1/74 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1160 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a15 : h 0 + ((6 : ℝ) * (h 1)) ≤ (1 : ℝ))
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a23 : -(h 1) < (-5/36 : ℝ))
    (a25 : h 0 ≤ (4/25 : ℝ))
    (a30 : -(h 0) < (-3/20 : ℝ))
    (a35 : -(h 3) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1161 h delta _ctx _hno a14 a20 a23 f0
  by_cases p1 : h 0 ≤ (5/33 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/33 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1162 h delta _ctx _hno a15 a18 a20 a23 a25 a35 f1
  by_cases p2 : h 1 ≤ (3/20 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1181 h delta _ctx _hno a15 a20 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1182 h delta _ctx _hno a18 a20 a23 a35 f3
  by_cases p4 : h 3 ≤ (7/57 : ℝ)
  swap
  · have f4 : -(h 3) < (-7/57 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1183 h delta _ctx _hno a18 a20 a23 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1184 h delta _ctx _hno a23 a30 f5
  apply _hno 87
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (5/33 : ℝ)) ∧ (h 1 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (7/57 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_1159 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a23 : -(h 1) < (-5/36 : ℝ))
    (a28 : -(h 3) < (-3/28 : ℝ))
    (a30 : -(h 0) < (-3/20 : ℝ))
    (a34 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.min + (1/2 : ℝ) * _ctx.lower + (1/32 : ℝ) * a18 + (1/4 : ℝ) * a23 + (1/4 : ℝ) * a28 + (7/32 : ℝ) * a30 + (1/4 : ℝ) * a34 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1158 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : h 0 + ((6 : ℝ) * (h 1)) ≤ (1 : ℝ))
    (a30 : -(h 0) < (-3/20 : ℝ))
    (a33 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/7 : ℝ) * a15 + (1/7 : ℝ) * a30 + (6/7 : ℝ) * a33
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1157 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : h 0 ≤ (4/25 : ℝ))
    (a32 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a25 + (1 : ℝ) * a32
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1156 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a23 : -(h 1) < (-5/36 : ℝ))
    (a31 : ((-2 : ℝ) * (delta)) < (-11/50 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/74 : ℝ) * _ctx.order3 + (1/37 : ℝ) * _ctx.order4 + (1/444 : ℝ) * _ctx.fail1 + (26/111 : ℝ) * a14 + (3/74 : ℝ) * a20 + (1/74 : ℝ) * a23 + (419/444 : ℝ) * a31 + (1/74 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1155 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a15 : h 0 + ((6 : ℝ) * (h 1)) ≤ (1 : ℝ))
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a23 : -(h 1) < (-5/36 : ℝ))
    (a25 : h 0 ≤ (4/25 : ℝ))
    (a28 : -(h 3) < (-3/28 : ℝ))
    (a30 : -(h 0) < (-3/20 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (11/50 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-11/50 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1156 h delta _ctx _hno a14 a20 a23 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1157 h delta _ctx _hno a25 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1158 h delta _ctx _hno a15 a30 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1159 h delta _ctx _hno a18 a23 a28 a30 f3
  by_cases p4 : h 3 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1160 h delta _ctx _hno a14 a15 a18 a20 a23 a25 a30 f4
  apply _hno 72
  change (((2 : ℝ) * (delta)) ≤ (11/50 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_1154 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a23 : -(h 1) < (-5/36 : ℝ))
    (a29 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/74 : ℝ) * _ctx.order3 + (1/37 : ℝ) * _ctx.order4 + (1/444 : ℝ) * _ctx.fail1 + (26/111 : ℝ) * a14 + (3/74 : ℝ) * a20 + (1/74 : ℝ) * a23 + (419/444 : ℝ) * a29 + (1/74 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1153 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a15 : h 0 + ((6 : ℝ) * (h 1)) ≤ (1 : ℝ))
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a23 : -(h 1) < (-5/36 : ℝ))
    (a25 : h 0 ≤ (4/25 : ℝ))
    (a28 : -(h 3) < (-3/28 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1154 h delta _ctx _hno a14 a20 a23 f0
  by_cases p1 : h 0 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1155 h delta _ctx _hno a14 a15 a18 a20 a23 a25 a28 f1
  by_cases p2 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1185 h delta _ctx _hno a18 a20 a23 a28 f2
  by_cases p3 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f3 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1186 h delta _ctx _hno a20 a23 f3
  apply _hno 8
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_1152 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a27 : -(h 2) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (8/19 : ℝ) * _ctx.order1 + (8/19 : ℝ) * _ctx.order3 + (7/19 : ℝ) * _ctx.min + (15/19 : ℝ) * _ctx.lower + (2/19 : ℝ) * a18 + (1/19 : ℝ) * a20 + (16/19 : ℝ) * a27 + (8/19 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1151 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : h 0 + ((6 : ℝ) * (h 1)) ≤ (1 : ℝ))
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a26 : -(h 1) < (-7/44 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/649 : ℝ) * _ctx.order3 + (12/649 : ℝ) * _ctx.order4 + (6/649 : ℝ) * _ctx.lower + (1/649 : ℝ) * _ctx.fail1 + (104/649 : ℝ) * a15 + (18/649 : ℝ) * a20 + (630/649 : ℝ) * a26 + (6/649 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1150 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : -(h 1) < (-5/36 : ℝ))
    (a25 : -(h 0) < (-4/25 : ℝ))
    (a30 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.order3 + (6/23 : ℝ) * _ctx.min + (12/23 : ℝ) * _ctx.lower + (1/23 : ℝ) * _ctx.fail1 + (6/23 : ℝ) * a23 + (4/23 : ℝ) * a25 + (12/23 : ℝ) * a30 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1149 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a23 : -(h 1) < (-5/36 : ℝ))
    (a25 : -(h 0) < (-4/25 : ℝ))
    (a34 : -(h 3) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/17 : ℝ) * _ctx.min + (12/17 : ℝ) * _ctx.lower + (1/17 : ℝ) * _ctx.fail1 + (3/68 : ℝ) * a18 + (6/17 : ℝ) * a23 + (13/68 : ℝ) * a25 + (6/17 : ℝ) * a34 + (6/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1148 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a23 : -(h 1) < (-5/36 : ℝ))
    (a25 : -(h 0) < (-4/25 : ℝ))
    (a33 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order3 + (1/3 : ℝ) * _ctx.min + (2/3 : ℝ) * _ctx.lower + (1/12 : ℝ) * a18 + (1/3 : ℝ) * a23 + (1/4 : ℝ) * a25 + (1/3 : ℝ) * a33 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1147 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : h 0 + ((6 : ℝ) * (h 1)) ≤ (1 : ℝ))
    (a25 : -(h 0) < (-4/25 : ℝ))
    (a32 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/7 : ℝ) * a15 + (1/7 : ℝ) * a25 + (6/7 : ℝ) * a32
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1146 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a23 : -(h 1) < (-5/36 : ℝ))
    (a29 : -(h 2) < (-4/35 : ℝ))
    (a31 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order3 + (1/3 : ℝ) * _ctx.min + (2/3 : ℝ) * _ctx.lower + (1/12 : ℝ) * a18 + (1/3 : ℝ) * a23 + (1/3 : ℝ) * a29 + (1/4 : ℝ) * a31 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1145 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a25 : -(h 0) < (-4/25 : ℝ))
    (a30 : ((-2 : ℝ) * (delta)) < (-11/50 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * a14 + (1/5 : ℝ) * a25 + (4/5 : ℝ) * a30
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1144 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a15 : h 0 + ((6 : ℝ) * (h 1)) ≤ (1 : ℝ))
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a23 : -(h 1) < (-5/36 : ℝ))
    (a25 : -(h 0) < (-4/25 : ℝ))
    (a29 : -(h 2) < (-4/35 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (11/50 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-11/50 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1145 h delta _ctx _hno a14 a25 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1146 h delta _ctx _hno a18 a23 a29 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1147 h delta _ctx _hno a15 a25 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1148 h delta _ctx _hno a18 a23 a25 f3
  by_cases p4 : h 3 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1149 h delta _ctx _hno a18 a23 a25 f4
  apply _hno 72
  change (((2 : ℝ) * (delta)) ≤ (11/50 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_1143 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : h 0 + ((6 : ℝ) * (h 1)) ≤ (1 : ℝ))
    (a25 : -(h 0) < (-4/25 : ℝ))
    (a28 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/7 : ℝ) * a15 + (1/7 : ℝ) * a25 + (6/7 : ℝ) * a28
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1142 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a22 : h 0 ≤ (1/6 : ℝ))
    (a27 : -(h 0) < (-6/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a22 + (1 : ℝ) * a27
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1141 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a23 : -(h 1) < (-5/36 : ℝ))
    (a26 : ((-2 : ℝ) * (delta)) < (-8/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/74 : ℝ) * _ctx.order3 + (1/37 : ℝ) * _ctx.order4 + (1/444 : ℝ) * _ctx.fail1 + (26/111 : ℝ) * a14 + (3/74 : ℝ) * a20 + (1/74 : ℝ) * a23 + (419/444 : ℝ) * a26 + (1/74 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1140 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a15 : h 0 + ((6 : ℝ) * (h 1)) ≤ (1 : ℝ))
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a22 : h 0 ≤ (1/6 : ℝ))
    (a23 : -(h 1) < (-5/36 : ℝ))
    (a25 : -(h 0) < (-4/25 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (8/35 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-8/35 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1141 h delta _ctx _hno a14 a20 a23 f0
  by_cases p1 : h 0 ≤ (6/35 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/35 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1142 h delta _ctx _hno a22 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1143 h delta _ctx _hno a15 a25 f2
  by_cases p3 : h 2 ≤ (4/35 : ℝ)
  swap
  · have f3 : -(h 2) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1144 h delta _ctx _hno a14 a15 a18 a23 a25 f3
  by_cases p4 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1150 h delta _ctx _hno a23 a25 f4
  apply _hno 51
  change (((2 : ℝ) * (delta)) ≤ (8/35 : ℝ)) ∧ (h 0 ≤ (6/35 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (4/35 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_1139 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a23 : -(h 1) < (-5/36 : ℝ))
    (a24 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/74 : ℝ) * _ctx.order3 + (1/37 : ℝ) * _ctx.order4 + (1/444 : ℝ) * _ctx.fail1 + (26/111 : ℝ) * a14 + (3/74 : ℝ) * a20 + (1/74 : ℝ) * a23 + (419/444 : ℝ) * a24 + (1/74 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1138 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a15 : h 0 + ((6 : ℝ) * (h 1)) ≤ (1 : ℝ))
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a22 : h 0 ≤ (1/6 : ℝ))
    (a23 : -(h 1) < (-5/36 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1139 h delta _ctx _hno a14 a20 a23 f0
  by_cases p1 : h 0 ≤ (4/25 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/25 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1140 h delta _ctx _hno a14 a15 a18 a20 a22 a23 f1
  by_cases p2 : h 1 ≤ (7/44 : ℝ)
  swap
  · have f2 : -(h 1) < (-7/44 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1151 h delta _ctx _hno a15 a20 f2
  by_cases p3 : h 2 ≤ (1/7 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1152 h delta _ctx _hno a18 a20 f3
  by_cases p4 : h 3 ≤ (3/28 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1153 h delta _ctx _hno a14 a15 a18 a20 a23 p1 f4
  apply _hno 10
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (7/44 : ℝ)) ∧ (h 2 ≤ (1/7 : ℝ)) ∧ (h 3 ≤ (3/28 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_1137 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a22 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (8 : ℝ) * _ctx.lower + (1 : ℝ) * a14 + (1 : ℝ) * a22
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1136 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a21 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/217 : ℝ) * _ctx.order3 + (6/217 : ℝ) * _ctx.order4 + (1/434 : ℝ) * _ctx.fail1 + (1/217 : ℝ) * a13 + (52/217 : ℝ) * a14 + (9/217 : ℝ) * a20 + (59/62 : ℝ) * a21 + (3/217 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1135 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a15 : h 0 + ((6 : ℝ) * (h 1)) ≤ (1 : ℝ))
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1136 h delta _ctx _hno a13 a14 a20 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1137 h delta _ctx _hno a14 f1
  by_cases p2 : h 1 ≤ (5/36 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/36 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1138 h delta _ctx _hno a14 a15 a18 a20 p1 f2
  by_cases p3 : h 3 ≤ (1/9 : ℝ)
  swap
  · have f3 : -(h 3) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1187 h delta _ctx _hno a13 a14 a18 a20 p1 p2 f3
  apply _hno 0
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (5/36 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_1134 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a19 : -(h 5) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (192/409 : ℝ) * _ctx.order1 + (192/409 : ℝ) * _ctx.order3 + (76/409 : ℝ) * _ctx.order4 + (64/409 : ℝ) * _ctx.fail1 + (77/409 : ℝ) * _ctx.fail2 + (244/409 : ℝ) * a14 + (268/409 : ℝ) * a19 + (192/409 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1133 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a14 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a15 : h 0 + ((6 : ℝ) * (h 1)) ≤ (1 : ℝ))
    (a18 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    : False := by
  by_cases p0 : h 5 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ)
  swap
  · have f0 : -(h 5) + ((-8 : ℝ) * (delta)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1134 h delta _ctx _hno a14 f0
  by_cases p1 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ)
  swap
  · have f1 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1135 h delta _ctx _hno a13 a14 a15 a18 f1
  by_cases p2 : ((6 : ℝ) * (h 1)) + h 5 ≤ (1 : ℝ)
  swap
  · have f2 : ((-6 : ℝ) * (h 1)) + -(h 5) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_2055 h delta _ctx _hno a15 f2
  by_cases p3 : ((6 : ℝ) * (h 2)) + h 5 ≤ (1 : ℝ)
  swap
  · have f3 : ((-6 : ℝ) * (h 2)) + -(h 5) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_2056 h delta _ctx _hno f3
  by_cases p4 : ((8 : ℝ) * (h 3)) + h 5 ≤ (1 : ℝ)
  swap
  · have f4 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2057 h delta _ctx _hno a13 a14 a15 a18 p1 f4
  by_cases p5 : ((8 : ℝ) * (h 4)) + h 5 ≤ (1 : ℝ)
  swap
  · have f5 : ((-8 : ℝ) * (h 4)) + -(h 5) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_3991 h delta _ctx _hno p4 f5
  apply _hno 32
  change (h 5 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ)) ∧ (((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ)) ∧ (((6 : ℝ) * (h 1)) + h 5 ≤ (1 : ℝ)) ∧ (((6 : ℝ) * (h 2)) + h 5 ≤ (1 : ℝ)) ∧ (((8 : ℝ) * (h 3)) + h 5 ≤ (1 : ℝ)) ∧ (((8 : ℝ) * (h 4)) + h 5 ≤ (1 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_1132 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : -(h 0) + ((-6 : ℝ) * (h 3)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/4 : ℝ) * _ctx.order0 + (5/2 : ℝ) * _ctx.order1 + (17/4 : ℝ) * _ctx.order2 + (7/4 : ℝ) * _ctx.order4 + (7/2 : ℝ) * _ctx.min + (21/4 : ℝ) * _ctx.lower + (1 : ℝ) * a17 + (7/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1131 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a16 : -(h 0) + ((-6 : ℝ) * (h 2)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.order1 + (2 : ℝ) * _ctx.order3 + (8/3 : ℝ) * _ctx.order4 + (14/3 : ℝ) * _ctx.min + (20/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * _ctx.fail2 + (2/3 : ℝ) * a16 + (2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1130 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 0) + ((-6 : ℝ) * (h 1)) < (-1 : ℝ))
    (a26 : -(h 3) + ((-8 : ℝ) * (h 5)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (18/31 : ℝ) * _ctx.order0 + (28/31 : ℝ) * _ctx.order3 + (70/31 : ℝ) * _ctx.order4 + (42/31 : ℝ) * _ctx.lower + (7/31 : ℝ) * _ctx.fail1 + (10/31 : ℝ) * a15 + (14/31 : ℝ) * a26 + (42/31 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1129 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 0) + ((-6 : ℝ) * (h 1)) < (-1 : ℝ))
    (a25 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (54/79 : ℝ) * _ctx.order0 + (98/79 : ℝ) * _ctx.order3 + (126/79 : ℝ) * _ctx.min + (252/79 : ℝ) * _ctx.lower + (21/79 : ℝ) * _ctx.fail1 + (30/79 : ℝ) * a15 + (28/79 : ℝ) * a25 + (126/79 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1128 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a24 : ((-6 : ℝ) * (h 2)) + -(h 3) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.order0 + (4 : ℝ) * _ctx.order1 + (1 : ℝ) * _ctx.order3 + (3 : ℝ) * _ctx.order4 + (5 : ℝ) * _ctx.min + (7 : ℝ) * _ctx.lower + (1 : ℝ) * a24 + (2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1127 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : -(h 3) < (-3/28 : ℝ))
    (a23 : ((-6 : ℝ) * (h 1)) + -(h 3) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/7 : ℝ) * _ctx.order0 + (6/7 : ℝ) * _ctx.order4 + (12/7 : ℝ) * _ctx.min + (18/7 : ℝ) * _ctx.lower + (1/7 : ℝ) * _ctx.fail1 + (13/21 : ℝ) * a20 + (5/21 : ℝ) * a23 + (6/7 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1126 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 0) + ((-6 : ℝ) * (h 1)) < (-1 : ℝ))
    (a22 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a28 : ((-8 : ℝ) * (h 4)) + -(h 5) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (88/63 : ℝ) * _ctx.order3 + (73/63 : ℝ) * _ctx.min + (169/63 : ℝ) * _ctx.lower + (16/63 : ℝ) * _ctx.fail1 + (16/63 : ℝ) * a15 + (8/63 : ℝ) * a22 + (23/63 : ℝ) * a28 + (32/21 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1125 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 0) + ((-6 : ℝ) * (h 1)) < (-1 : ℝ))
    (a22 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a27 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a31 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (85/147 : ℝ) * _ctx.min + (181/147 : ℝ) * _ctx.lower + (16/147 : ℝ) * _ctx.fail1 + (16/147 : ℝ) * a15 + (8/147 : ℝ) * a22 + (11/147 : ℝ) * a27 + (32/49 : ℝ) * a31 + (32/49 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1124 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 0) + ((-6 : ℝ) * (h 1)) < (-1 : ℝ))
    (a22 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a27 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a30 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (288/407 : ℝ) * _ctx.order4 + (545/407 : ℝ) * _ctx.min + (833/407 : ℝ) * _ctx.lower + (48/407 : ℝ) * a15 + (40/407 : ℝ) * a22 + (31/407 : ℝ) * a27 + (288/407 : ℝ) * a30 + (288/407 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1123 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a24 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a29 : -(h 0) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a24 + (1 : ℝ) * a29
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1122 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 0) + ((-6 : ℝ) * (h 1)) < (-1 : ℝ))
    (a22 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a27 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a28 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (192/379 : ℝ) * _ctx.order4 + (362/379 : ℝ) * _ctx.min + (32/379 : ℝ) * _ctx.fail1 + (32/379 : ℝ) * a15 + (16/379 : ℝ) * a22 + (22/379 : ℝ) * a27 + (277/379 : ℝ) * a28 + (192/379 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1121 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 0) + ((-6 : ℝ) * (h 1)) < (-1 : ℝ))
    (a22 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a24 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a27 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1122 h delta _ctx _hno a15 a22 a27 f0
  by_cases p1 : h 0 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1123 h delta _ctx _hno a24 f1
  by_cases p2 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1124 h delta _ctx _hno a15 a22 a27 f2
  by_cases p3 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f3 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1125 h delta _ctx _hno a15 a22 a27 f3
  apply _hno 8
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_1120 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a22 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a26 : ((-6 : ℝ) * (h 2)) + -(h 5) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.order1 + (5/3 : ℝ) * _ctx.order3 + (11/3 : ℝ) * _ctx.order4 + (5 : ℝ) * _ctx.min + (7 : ℝ) * _ctx.lower + (1/3 : ℝ) * a22 + (2/3 : ℝ) * a26 + (2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1119 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : -(h 3) < (-3/28 : ℝ))
    (a25 : ((-6 : ℝ) * (h 1)) + -(h 5) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/13 : ℝ) * _ctx.order0 + (9/13 : ℝ) * _ctx.order4 + (31/26 : ℝ) * _ctx.min + (49/26 : ℝ) * _ctx.lower + (3/26 : ℝ) * _ctx.fail1 + (9/13 : ℝ) * a20 + (5/26 : ℝ) * a25 + (9/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1118 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 0) + ((-6 : ℝ) * (h 1)) < (-1 : ℝ))
    (a24 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (12/29 : ℝ) * _ctx.order3 + (11/29 : ℝ) * _ctx.min + (23/29 : ℝ) * _ctx.lower + (2/29 : ℝ) * _ctx.fail1 + (2/29 : ℝ) * a15 + (1/29 : ℝ) * a24 + (24/29 : ℝ) * a28 + (12/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1117 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 0) + ((-6 : ℝ) * (h 1)) < (-1 : ℝ))
    (a20 : -(h 3) < (-3/28 : ℝ))
    (a24 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a27 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (36/83 : ℝ) * _ctx.order4 + (67/83 : ℝ) * _ctx.min + (103/83 : ℝ) * _ctx.lower + (6/83 : ℝ) * a15 + (36/83 : ℝ) * a20 + (5/83 : ℝ) * a24 + (36/83 : ℝ) * a27 + (36/83 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1116 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 0) + ((-6 : ℝ) * (h 1)) < (-1 : ℝ))
    (a24 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a31 : -(h 3) < (-1/9 : ℝ))
    (a37 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (11/29 : ℝ) * _ctx.min + (23/29 : ℝ) * _ctx.lower + (2/29 : ℝ) * _ctx.fail1 + (2/29 : ℝ) * a15 + (1/29 : ℝ) * a24 + (12/29 : ℝ) * a31 + (12/29 : ℝ) * a37 + (12/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1115 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 0) + ((-6 : ℝ) * (h 1)) < (-1 : ℝ))
    (a24 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a36 : -(h 3) < (-7/57 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (12/17 : ℝ) * _ctx.order4 + (23/17 : ℝ) * _ctx.min + (35/17 : ℝ) * _ctx.lower + (2/17 : ℝ) * _ctx.fail1 + (2/17 : ℝ) * a15 + (1/17 : ℝ) * a24 + (12/17 : ℝ) * a36 + (12/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1114 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 0) + ((-6 : ℝ) * (h 1)) < (-1 : ℝ))
    (a24 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a31 : -(h 3) < (-1/9 : ℝ))
    (a35 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (36/83 : ℝ) * _ctx.order4 + (67/83 : ℝ) * _ctx.min + (103/83 : ℝ) * _ctx.lower + (6/83 : ℝ) * a15 + (5/83 : ℝ) * a24 + (36/83 : ℝ) * a31 + (36/83 : ℝ) * a35 + (36/83 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1113 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : h 1 ≤ (1/7 : ℝ))
    (a34 : -(h 1) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a34
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1112 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 0) + ((-6 : ℝ) * (h 1)) < (-1 : ℝ))
    (a31 : -(h 3) < (-1/9 : ℝ))
    (a33 : -(h 0) < (-5/33 : ℝ))
    (a39 : -(h 5) < (-2/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.order4 + (6/23 : ℝ) * _ctx.lower + (1/23 : ℝ) * _ctx.fail1 + (1/23 : ℝ) * a15 + (6/23 : ℝ) * a31 + (3/23 : ℝ) * a33 + (12/23 : ℝ) * a39 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1111 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 0) + ((-6 : ℝ) * (h 1)) < (-1 : ℝ))
    (a31 : -(h 3) < (-1/9 : ℝ))
    (a33 : -(h 0) < (-5/33 : ℝ))
    (a38 : -(h 4) < (-3/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/17 : ℝ) * _ctx.min + (12/17 : ℝ) * _ctx.lower + (1/17 : ℝ) * _ctx.fail1 + (1/17 : ℝ) * a15 + (6/17 : ℝ) * a31 + (3/17 : ℝ) * a33 + (6/17 : ℝ) * a38 + (6/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1110 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 0) + ((-6 : ℝ) * (h 1)) < (-1 : ℝ))
    (a31 : -(h 3) < (-1/9 : ℝ))
    (a33 : -(h 0) < (-5/33 : ℝ))
    (a37 : -(h 2) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order4 + (2/3 : ℝ) * _ctx.min + (1 : ℝ) * _ctx.lower + (1/18 : ℝ) * a15 + (1/3 : ℝ) * a31 + (5/18 : ℝ) * a33 + (1/3 : ℝ) * a37 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1109 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : h 1 ≤ (1/7 : ℝ))
    (a36 : -(h 1) < (-5/31 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a36
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1108 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : h 0 ≤ (4/25 : ℝ))
    (a35 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a35
  exact (lt_irrefl (0 : ℝ)) hbad

end RealPinwheel.WeakSevenBandData
