import Pinwheel.WeakSevenBandData.CoverChunks.Upper052

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem upper_node_67 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 5) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a19 : -(h 3) < (-4/35 : ℝ))
    (a22 : -(h 1) < (-1/8 : ℝ))
    (a26 : -(h 2) < (-5/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (28/125 : ℝ) * _ctx.min + (9/125 : ℝ) * _ctx.fail2 + (8/125 : ℝ) * a15 + (36/125 : ℝ) * a19 + (36/125 : ℝ) * a22 + (36/125 : ℝ) * a26 + (36/125 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_66 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 5) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a19 : -(h 3) < (-4/35 : ℝ))
    (a25 : -(h 1) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (9/70 : ℝ) * _ctx.order4 + (29/70 : ℝ) * _ctx.min + (9/140 : ℝ) * _ctx.fail1 + (9/140 : ℝ) * _ctx.fail2 + (1/10 : ℝ) * a15 + (27/70 : ℝ) * a19 + (27/70 : ℝ) * a25 + (27/70 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_65 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 5) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a22 : -(h 1) < (-1/8 : ℝ))
    (a24 : -(h 0) < (-9/64 : ℝ))
    (a29 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/19 : ℝ) * _ctx.order4 + (10/19 : ℝ) * _ctx.min + (1/19 : ℝ) * _ctx.fail1 + (2/19 : ℝ) * a15 + (6/19 : ℝ) * a22 + (4/19 : ℝ) * a24 + (6/19 : ℝ) * a29 + (6/19 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_64 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 5) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a19 : -(h 3) < (-4/35 : ℝ))
    (a22 : -(h 1) < (-1/8 : ℝ))
    (a24 : -(h 0) < (-9/64 : ℝ))
    (a28 : -(h 2) < (-5/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/13 : ℝ) * _ctx.order4 + (5/13 : ℝ) * _ctx.min + (1/13 : ℝ) * a15 + (3/13 : ℝ) * a19 + (3/13 : ℝ) * a22 + (3/13 : ℝ) * a24 + (3/13 : ℝ) * a28 + (3/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_63 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 5) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a19 : -(h 3) < (-4/35 : ℝ))
    (a27 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (9/70 : ℝ) * _ctx.order4 + (29/70 : ℝ) * _ctx.min + (9/140 : ℝ) * _ctx.fail1 + (9/140 : ℝ) * _ctx.fail2 + (1/10 : ℝ) * a15 + (27/70 : ℝ) * a19 + (27/70 : ℝ) * a27 + (27/70 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_62 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 5) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a19 : -(h 3) < (-4/35 : ℝ))
    (a22 : -(h 1) < (-1/8 : ℝ))
    (a26 : -(h 0) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/19 : ℝ) * _ctx.order4 + (10/19 : ℝ) * _ctx.min + (1/19 : ℝ) * _ctx.fail1 + (2/19 : ℝ) * a15 + (6/19 : ℝ) * a19 + (6/19 : ℝ) * a22 + (4/19 : ℝ) * a26 + (6/19 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_61 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : -(h 3) < (-4/35 : ℝ))
    (a22 : -(h 1) < (-1/8 : ℝ))
    (a24 : -(h 0) < (-9/64 : ℝ))
    (a25 : ((-2 : ℝ) * (delta)) < (-11/49 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/13 : ℝ) * _ctx.order4 + (6/13 : ℝ) * _ctx.min + (1/26 : ℝ) * _ctx.fail1 + (3/13 : ℝ) * a19 + (3/13 : ℝ) * a22 + (2/13 : ℝ) * a24 + (9/26 : ℝ) * a25 + (3/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_60 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 5) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a19 : -(h 3) < (-4/35 : ℝ))
    (a22 : -(h 1) < (-1/8 : ℝ))
    (a24 : -(h 0) < (-9/64 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (11/49 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-11/49 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_61 h delta _ctx _hno a19 a22 a24 f0
  by_cases p1 : h 0 ≤ (1/7 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_62 h delta _ctx _hno a15 a19 a22 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_63 h delta _ctx _hno a15 a19 f2
  by_cases p3 : h 2 ≤ (5/41 : ℝ)
  swap
  · have f3 : -(h 2) < (-5/41 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_64 h delta _ctx _hno a15 a19 a22 a24 f3
  by_cases p4 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_65 h delta _ctx _hno a15 a22 a24 f4
  apply _hno 45
  change (((2 : ℝ) * (delta)) ≤ (11/49 : ℝ)) ∧ (h 0 ≤ (1/7 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (5/41 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_59 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((2 : ℝ) * (delta)) ≤ (9/40 : ℝ))
    (a23 : ((-2 : ℝ) * (delta)) < (-3/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a20 + (1 : ℝ) * a23
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_58 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 5) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a19 : -(h 3) < (-4/35 : ℝ))
    (a20 : ((2 : ℝ) * (delta)) ≤ (9/40 : ℝ))
    (a22 : -(h 1) < (-1/8 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/13 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_59 h delta _ctx _hno a20 f0
  by_cases p1 : h 0 ≤ (9/64 : ℝ)
  swap
  · have f1 : -(h 0) < (-9/64 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_60 h delta _ctx _hno a15 a19 a22 f1
  by_cases p2 : h 1 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_66 h delta _ctx _hno a15 a19 f2
  by_cases p3 : h 2 ≤ (5/41 : ℝ)
  swap
  · have f3 : -(h 2) < (-5/41 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_67 h delta _ctx _hno a15 a19 a22 f3
  by_cases p4 : h 3 ≤ (7/60 : ℝ)
  swap
  · have f4 : -(h 3) < (-7/60 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_68 h delta _ctx _hno a15 a22 f4
  by_cases p5 : h 4 ≤ (3/26 : ℝ)
  swap
  · have f5 : -(h 4) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_69 h delta _ctx _hno a15 a22 f5
  by_cases p6 : h 5 ≤ (4/35 : ℝ)
  swap
  · have f6 : -(h 5) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact upper_node_70 h delta _ctx _hno a15 a19 a22 f6
  apply _hno 44
  change (((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)) ∧ (h 0 ≤ (9/64 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 2 ≤ (5/41 : ℝ)) ∧ (h 3 ≤ (7/60 : ℝ)) ∧ (h 4 ≤ (3/26 : ℝ)) ∧ (h 5 ≤ (4/35 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem upper_node_57 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : h 0 ≤ (1/7 : ℝ))
    (a21 : -(h 0) < (-4/27 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a21
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_56 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : -(h 3) < (-4/35 : ℝ))
    (a20 : ((-2 : ℝ) * (delta)) < (-9/40 : ℝ))
    (a23 : -(h 1) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/21 : ℝ) * _ctx.order4 + (8/21 : ℝ) * _ctx.min + (1/21 : ℝ) * _ctx.fail1 + (1/21 : ℝ) * _ctx.fail2 + (2/7 : ℝ) * a19 + (1/3 : ℝ) * a20 + (2/7 : ℝ) * a23 + (2/7 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_55 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : h 0 ≤ (1/7 : ℝ))
    (a22 : -(h 0) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a22
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_54 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a21 : ((-2 : ℝ) * (delta)) < (-3/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a21
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_53 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : h 0 ≤ (1/7 : ℝ))
    (a19 : -(h 3) < (-4/35 : ℝ))
    (a20 : ((-2 : ℝ) * (delta)) < (-9/40 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/13 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_54 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (1/7 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_55 h delta _ctx _hno a17 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_56 h delta _ctx _hno a19 a20 f2
  apply _hno 43
  change (((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)) ∧ (h 0 ≤ (1/7 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem upper_node_52 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 5) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a17 : h 0 ≤ (1/7 : ℝ))
    (a19 : -(h 3) < (-4/35 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (9/40 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-9/40 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_53 h delta _ctx _hno a17 a19 f0
  by_cases p1 : h 0 ≤ (4/27 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/27 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_57 h delta _ctx _hno a17 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_58 h delta _ctx _hno a15 a19 p0 f2
  apply _hno 42
  change (((2 : ℝ) * (delta)) ≤ (9/40 : ℝ)) ∧ (h 0 ≤ (4/27 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem upper_node_51 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 5) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a18 : -(h 2) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (12/31 : ℝ) * _ctx.order1 + (12/31 : ℝ) * _ctx.order3 + (12/31 : ℝ) * _ctx.order4 + (20/31 : ℝ) * _ctx.min + (3/31 : ℝ) * _ctx.fail2 + (4/31 : ℝ) * a15 + (24/31 : ℝ) * a18 + (12/31 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_50 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 5) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a17 : -(h 0) < (-1/7 : ℝ))
    (a24 : -(h 3) < (-4/35 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/19 : ℝ) * _ctx.order4 + (10/19 : ℝ) * _ctx.min + (1/19 : ℝ) * _ctx.fail1 + (2/19 : ℝ) * a15 + (4/19 : ℝ) * a17 + (6/19 : ℝ) * a24 + (6/19 : ℝ) * a27 + (6/19 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_49 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 5) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a24 : -(h 3) < (-4/35 : ℝ))
    (a26 : -(h 0) < (-7/48 : ℝ))
    (a29 : -(h 1) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/19 : ℝ) * _ctx.order4 + (10/19 : ℝ) * _ctx.min + (1/19 : ℝ) * _ctx.fail1 + (2/19 : ℝ) * a15 + (6/19 : ℝ) * a24 + (4/19 : ℝ) * a26 + (6/19 : ℝ) * a29 + (6/19 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_48 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 5) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a20 : -(h 1) < (-13/108 : ℝ))
    (a24 : -(h 3) < (-4/35 : ℝ))
    (a28 : -(h 0) < (-4/27 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/19 : ℝ) * _ctx.order4 + (10/19 : ℝ) * _ctx.min + (1/19 : ℝ) * _ctx.fail1 + (2/19 : ℝ) * a15 + (6/19 : ℝ) * a20 + (6/19 : ℝ) * a24 + (4/19 : ℝ) * a28 + (6/19 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_47 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : -(h 1) < (-13/108 : ℝ))
    (a24 : -(h 3) < (-4/35 : ℝ))
    (a26 : -(h 0) < (-7/48 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-9/40 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/13 : ℝ) * _ctx.order4 + (6/13 : ℝ) * _ctx.min + (1/26 : ℝ) * _ctx.fail1 + (3/13 : ℝ) * a20 + (3/13 : ℝ) * a24 + (2/13 : ℝ) * a26 + (9/26 : ℝ) * a27 + (3/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_46 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 5) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a20 : -(h 1) < (-13/108 : ℝ))
    (a24 : -(h 3) < (-4/35 : ℝ))
    (a26 : -(h 0) < (-7/48 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (9/40 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-9/40 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_47 h delta _ctx _hno a20 a24 a26 f0
  by_cases p1 : h 0 ≤ (4/27 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/27 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_48 h delta _ctx _hno a15 a20 a24 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_49 h delta _ctx _hno a15 a24 a26 f2
  apply _hno 42
  change (((2 : ℝ) * (delta)) ≤ (9/40 : ℝ)) ∧ (h 0 ≤ (4/27 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem upper_node_45 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : -(h 0) < (-1/7 : ℝ))
    (a20 : -(h 1) < (-13/108 : ℝ))
    (a24 : -(h 3) < (-4/35 : ℝ))
    (a25 : ((-2 : ℝ) * (delta)) < (-7/31 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/13 : ℝ) * _ctx.order4 + (6/13 : ℝ) * _ctx.min + (1/26 : ℝ) * _ctx.fail1 + (2/13 : ℝ) * a17 + (3/13 : ℝ) * a20 + (3/13 : ℝ) * a24 + (9/26 : ℝ) * a25 + (3/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_44 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 5) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a17 : -(h 0) < (-1/7 : ℝ))
    (a20 : -(h 1) < (-13/108 : ℝ))
    (a24 : -(h 3) < (-4/35 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/31 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/31 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_45 h delta _ctx _hno a17 a20 a24 f0
  by_cases p1 : h 0 ≤ (7/48 : ℝ)
  swap
  · have f1 : -(h 0) < (-7/48 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_46 h delta _ctx _hno a15 a20 a24 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_50 h delta _ctx _hno a15 a17 a24 f2
  apply _hno 41
  change (((2 : ℝ) * (delta)) ≤ (7/31 : ℝ)) ∧ (h 0 ≤ (7/48 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem upper_node_43 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 5) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a17 : -(h 0) < (-1/7 : ℝ))
    (a23 : -(h 1) < (-1/8 : ℝ))
    (a29 : -(h 5) < (-6/53 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.order3 + (12/29 : ℝ) * _ctx.order4 + (1/29 : ℝ) * _ctx.fail1 + (3/116 : ℝ) * a15 + (4/29 : ℝ) * a17 + (6/29 : ℝ) * a23 + (69/116 : ℝ) * a29 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_42 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 5) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a17 : -(h 0) < (-1/7 : ℝ))
    (a23 : -(h 1) < (-1/8 : ℝ))
    (a28 : -(h 3) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/19 : ℝ) * _ctx.order4 + (10/19 : ℝ) * _ctx.min + (1/19 : ℝ) * _ctx.fail1 + (2/19 : ℝ) * a15 + (4/19 : ℝ) * a17 + (6/19 : ℝ) * a23 + (6/19 : ℝ) * a28 + (6/19 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_41 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 5) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a17 : -(h 0) < (-1/7 : ℝ))
    (a23 : -(h 1) < (-1/8 : ℝ))
    (a27 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (9/31 : ℝ) * _ctx.order3 + (18/31 : ℝ) * _ctx.order4 + (23/31 : ℝ) * _ctx.min + (4/31 : ℝ) * a15 + (9/31 : ℝ) * a17 + (9/31 : ℝ) * a23 + (9/31 : ℝ) * a27 + (9/31 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_40 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 5) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a26 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (27/46 : ℝ) * _ctx.order3 + (18/23 : ℝ) * _ctx.order4 + (53/46 : ℝ) * _ctx.min + (9/92 : ℝ) * _ctx.fail1 + (9/92 : ℝ) * _ctx.fail2 + (5/23 : ℝ) * a15 + (27/46 : ℝ) * a26 + (27/46 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_39 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 5) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a23 : -(h 1) < (-1/8 : ℝ))
    (a25 : -(h 0) < (-8/55 : ℝ))
    (a30 : -(h 3) < (-5/44 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/19 : ℝ) * _ctx.order4 + (10/19 : ℝ) * _ctx.min + (1/19 : ℝ) * _ctx.fail1 + (2/19 : ℝ) * a15 + (6/19 : ℝ) * a23 + (4/19 : ℝ) * a25 + (6/19 : ℝ) * a30 + (6/19 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_38 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 5) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a23 : -(h 1) < (-1/8 : ℝ))
    (a25 : -(h 0) < (-8/55 : ℝ))
    (a29 : -(h 2) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (9/31 : ℝ) * _ctx.order3 + (18/31 : ℝ) * _ctx.order4 + (23/31 : ℝ) * _ctx.min + (4/31 : ℝ) * a15 + (9/31 : ℝ) * a23 + (9/31 : ℝ) * a25 + (9/31 : ℝ) * a29 + (9/31 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_37 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 5) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a28 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (27/46 : ℝ) * _ctx.order3 + (18/23 : ℝ) * _ctx.order4 + (53/46 : ℝ) * _ctx.min + (9/92 : ℝ) * _ctx.fail1 + (9/92 : ℝ) * _ctx.fail2 + (5/23 : ℝ) * a15 + (27/46 : ℝ) * a28 + (27/46 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_36 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 5) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a23 : -(h 1) < (-1/8 : ℝ))
    (a27 : -(h 0) < (-5/34 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (18/41 : ℝ) * _ctx.order3 + (36/41 : ℝ) * _ctx.order4 + (46/41 : ℝ) * _ctx.min + (3/41 : ℝ) * _ctx.fail1 + (8/41 : ℝ) * a15 + (18/41 : ℝ) * a23 + (12/41 : ℝ) * a27 + (18/41 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_35 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : -(h 1) < (-1/8 : ℝ))
    (a25 : -(h 0) < (-8/55 : ℝ))
    (a26 : ((-2 : ℝ) * (delta)) < (-16/71 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.order3 + (12/23 : ℝ) * _ctx.order4 + (18/23 : ℝ) * _ctx.min + (1/23 : ℝ) * _ctx.fail1 + (6/23 : ℝ) * a23 + (4/23 : ℝ) * a25 + (12/23 : ℝ) * a26 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_34 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 5) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a23 : -(h 1) < (-1/8 : ℝ))
    (a25 : -(h 0) < (-8/55 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (16/71 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-16/71 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_35 h delta _ctx _hno a23 a25 f0
  by_cases p1 : h 0 ≤ (5/34 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/34 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_36 h delta _ctx _hno a15 a23 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_37 h delta _ctx _hno a15 f2
  by_cases p3 : h 2 ≤ (3/25 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_38 h delta _ctx _hno a15 a23 a25 f3
  by_cases p4 : h 3 ≤ (5/44 : ℝ)
  swap
  · have f4 : -(h 3) < (-5/44 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_39 h delta _ctx _hno a15 a23 a25 f4
  apply _hno 40
  change (((2 : ℝ) * (delta)) ≤ (16/71 : ℝ)) ∧ (h 0 ≤ (5/34 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (5/44 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_33 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a17 : -(h 0) < (-1/7 : ℝ))
    (a23 : -(h 1) < (-1/8 : ℝ))
    (a24 : ((-2 : ℝ) * (delta)) < (-7/31 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.order3 + (12/23 : ℝ) * _ctx.order4 + (18/23 : ℝ) * _ctx.min + (1/23 : ℝ) * _ctx.fail1 + (4/23 : ℝ) * a17 + (6/23 : ℝ) * a23 + (12/23 : ℝ) * a24 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_32 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 5) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a17 : -(h 0) < (-1/7 : ℝ))
    (a23 : -(h 1) < (-1/8 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/31 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/31 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_33 h delta _ctx _hno a17 a23 f0
  by_cases p1 : h 0 ≤ (8/55 : ℝ)
  swap
  · have f1 : -(h 0) < (-8/55 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_34 h delta _ctx _hno a15 a23 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_40 h delta _ctx _hno a15 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_41 h delta _ctx _hno a15 a17 a23 f3
  by_cases p4 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_42 h delta _ctx _hno a15 a17 a23 f4
  by_cases p5 : h 5 ≤ (6/53 : ℝ)
  swap
  · have f5 : -(h 5) < (-6/53 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_43 h delta _ctx _hno a15 a17 a23 f5
  apply _hno 39
  change (((2 : ℝ) * (delta)) ≤ (7/31 : ℝ)) ∧ (h 0 ≤ (8/55 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (6/53 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_31 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 5) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a20 : -(h 1) < (-13/108 : ℝ))
    (a22 : -(h 0) < (-3/20 : ℝ))
    (a26 : -(h 2) < (-2/17 : ℝ))
    (a31 : -(h 3) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/13 : ℝ) * _ctx.order4 + (5/13 : ℝ) * _ctx.min + (1/13 : ℝ) * a15 + (3/13 : ℝ) * a20 + (3/13 : ℝ) * a22 + (3/13 : ℝ) * a26 + (3/13 : ℝ) * a31 + (3/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_30 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 5) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a22 : -(h 0) < (-3/20 : ℝ))
    (a30 : -(h 2) < (-7/58 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (9/31 : ℝ) * _ctx.order1 + (9/31 : ℝ) * _ctx.order3 + (18/31 : ℝ) * _ctx.order4 + (23/31 : ℝ) * _ctx.min + (4/31 : ℝ) * a15 + (9/31 : ℝ) * a22 + (18/31 : ℝ) * a30 + (9/31 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_29 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 5) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a22 : -(h 0) < (-3/20 : ℝ))
    (a26 : -(h 2) < (-2/17 : ℝ))
    (a29 : -(h 1) < (-5/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (9/31 : ℝ) * _ctx.order3 + (18/31 : ℝ) * _ctx.order4 + (23/31 : ℝ) * _ctx.min + (4/31 : ℝ) * a15 + (9/31 : ℝ) * a22 + (9/31 : ℝ) * a26 + (9/31 : ℝ) * a29 + (9/31 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_28 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 5) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a20 : -(h 1) < (-13/108 : ℝ))
    (a26 : -(h 2) < (-2/17 : ℝ))
    (a28 : -(h 0) < (-7/46 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (9/31 : ℝ) * _ctx.order3 + (18/31 : ℝ) * _ctx.order4 + (23/31 : ℝ) * _ctx.min + (4/31 : ℝ) * a15 + (9/31 : ℝ) * a20 + (9/31 : ℝ) * a26 + (9/31 : ℝ) * a28 + (9/31 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_27 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : -(h 1) < (-13/108 : ℝ))
    (a22 : -(h 0) < (-3/20 : ℝ))
    (a27 : ((-2 : ℝ) * (delta)) < (-5/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.order3 + (12/23 : ℝ) * _ctx.order4 + (18/23 : ℝ) * _ctx.min + (1/23 : ℝ) * _ctx.fail1 + (6/23 : ℝ) * a20 + (4/23 : ℝ) * a22 + (12/23 : ℝ) * a27 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_26 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 5) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a20 : -(h 1) < (-13/108 : ℝ))
    (a22 : -(h 0) < (-3/20 : ℝ))
    (a26 : -(h 2) < (-2/17 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/22 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/22 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_27 h delta _ctx _hno a20 a22 f0
  by_cases p1 : h 0 ≤ (7/46 : ℝ)
  swap
  · have f1 : -(h 0) < (-7/46 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_28 h delta _ctx _hno a15 a20 a26 f1
  by_cases p2 : h 1 ≤ (5/41 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/41 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_29 h delta _ctx _hno a15 a22 a26 f2
  by_cases p3 : h 2 ≤ (7/58 : ℝ)
  swap
  · have f3 : -(h 2) < (-7/58 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_30 h delta _ctx _hno a15 a22 f3
  by_cases p4 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_31 h delta _ctx _hno a15 a20 a22 a26 f4
  apply _hno 38
  change (((2 : ℝ) * (delta)) ≤ (5/22 : ℝ)) ∧ (h 0 ≤ (7/46 : ℝ)) ∧ (h 1 ≤ (5/41 : ℝ)) ∧ (h 2 ≤ (7/58 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_25 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 5) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a22 : -(h 0) < (-3/20 : ℝ))
    (a25 : -(h 1) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (18/41 : ℝ) * _ctx.order3 + (36/41 : ℝ) * _ctx.order4 + (46/41 : ℝ) * _ctx.min + (3/41 : ℝ) * _ctx.fail1 + (8/41 : ℝ) * a15 + (12/41 : ℝ) * a22 + (18/41 : ℝ) * a25 + (18/41 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_24 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 5) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a20 : -(h 1) < (-13/108 : ℝ))
    (a24 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (18/41 : ℝ) * _ctx.order3 + (36/41 : ℝ) * _ctx.order4 + (46/41 : ℝ) * _ctx.min + (3/41 : ℝ) * _ctx.fail1 + (8/41 : ℝ) * a15 + (18/41 : ℝ) * a20 + (12/41 : ℝ) * a24 + (18/41 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_23 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : ((-2 : ℝ) * (delta)) < (-4/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a23
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_22 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 5) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a20 : -(h 1) < (-13/108 : ℝ))
    (a22 : -(h 0) < (-3/20 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/17 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/17 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_23 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_24 h delta _ctx _hno a15 a20 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_25 h delta _ctx _hno a15 a22 f2
  by_cases p3 : h 2 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_26 h delta _ctx _hno a15 a20 a22 f3
  apply _hno 37
  change (((2 : ℝ) * (delta)) ≤ (4/17 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_21 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a21 : ((-2 : ℝ) * (delta)) < (-1/4 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a21
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_20 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 5) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a17 : -(h 0) < (-1/7 : ℝ))
    (a20 : -(h 1) < (-13/108 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (1/4 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-1/4 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_21 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_22 h delta _ctx _hno a15 a20 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_32 h delta _ctx _hno a15 a17 f2
  by_cases p3 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f3 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_44 h delta _ctx _hno a15 a17 a20 f3
  apply _hno 36
  change (((2 : ℝ) * (delta)) ≤ (1/4 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_19 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 5) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a19 : -(h 0) < (-2/13 : ℝ))
    (a25 : -(h 1) < (-5/42 : ℝ))
    (a31 : -(h 5) < (-5/44 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.order3 + (12/29 : ℝ) * _ctx.order4 + (1/29 : ℝ) * _ctx.fail1 + (3/116 : ℝ) * a15 + (4/29 : ℝ) * a19 + (6/29 : ℝ) * a25 + (69/116 : ℝ) * a31 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_18 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 5) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a19 : -(h 0) < (-2/13 : ℝ))
    (a25 : -(h 1) < (-5/42 : ℝ))
    (a30 : -(h 4) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (18/73 : ℝ) * _ctx.order3 + (14/73 : ℝ) * _ctx.min + (3/73 : ℝ) * _ctx.fail1 + (4/73 : ℝ) * a15 + (12/73 : ℝ) * a19 + (18/73 : ℝ) * a25 + (36/73 : ℝ) * a30 + (18/73 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_17 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 5) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a19 : -(h 0) < (-2/13 : ℝ))
    (a25 : -(h 1) < (-5/42 : ℝ))
    (a29 : -(h 2) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (9/31 : ℝ) * _ctx.order3 + (18/31 : ℝ) * _ctx.order4 + (23/31 : ℝ) * _ctx.min + (4/31 : ℝ) * a15 + (9/31 : ℝ) * a19 + (9/31 : ℝ) * a25 + (9/31 : ℝ) * a29 + (9/31 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_16 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 5) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a19 : -(h 0) < (-2/13 : ℝ))
    (a28 : -(h 1) < (-17/141 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (18/41 : ℝ) * _ctx.order3 + (36/41 : ℝ) * _ctx.order4 + (46/41 : ℝ) * _ctx.min + (3/41 : ℝ) * _ctx.fail1 + (8/41 : ℝ) * a15 + (12/41 : ℝ) * a19 + (18/41 : ℝ) * a28 + (18/41 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_15 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 5) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a25 : -(h 1) < (-5/42 : ℝ))
    (a27 : -(h 0) < (-3/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (18/41 : ℝ) * _ctx.order3 + (36/41 : ℝ) * _ctx.order4 + (46/41 : ℝ) * _ctx.min + (3/41 : ℝ) * _ctx.fail1 + (8/41 : ℝ) * a15 + (18/41 : ℝ) * a25 + (12/41 : ℝ) * a27 + (18/41 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_14 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : -(h 0) < (-2/13 : ℝ))
    (a25 : -(h 1) < (-5/42 : ℝ))
    (a26 : ((-2 : ℝ) * (delta)) < (-5/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.order3 + (12/23 : ℝ) * _ctx.order4 + (18/23 : ℝ) * _ctx.min + (1/23 : ℝ) * _ctx.fail1 + (4/23 : ℝ) * a19 + (6/23 : ℝ) * a25 + (12/23 : ℝ) * a26 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_13 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 5) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a19 : -(h 0) < (-2/13 : ℝ))
    (a25 : -(h 1) < (-5/42 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/22 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/22 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_14 h delta _ctx _hno a19 a25 f0
  by_cases p1 : h 0 ≤ (3/19 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/19 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_15 h delta _ctx _hno a15 a25 f1
  by_cases p2 : h 1 ≤ (17/141 : ℝ)
  swap
  · have f2 : -(h 1) < (-17/141 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_16 h delta _ctx _hno a15 a19 f2
  by_cases p3 : h 2 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_17 h delta _ctx _hno a15 a19 a25 f3
  by_cases p4 : h 4 ≤ (3/26 : ℝ)
  swap
  · have f4 : -(h 4) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_18 h delta _ctx _hno a15 a19 a25 f4
  by_cases p5 : h 5 ≤ (5/44 : ℝ)
  swap
  · have f5 : -(h 5) < (-5/44 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_19 h delta _ctx _hno a15 a19 a25 f5
  apply _hno 35
  change (((2 : ℝ) * (delta)) ≤ (5/22 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (17/141 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (3/26 : ℝ)) ∧ (h 5 ≤ (5/44 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_12 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 5) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a22 : -(h 1) < (-3/26 : ℝ))
    (a24 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (18/41 : ℝ) * _ctx.order3 + (36/41 : ℝ) * _ctx.order4 + (46/41 : ℝ) * _ctx.min + (3/41 : ℝ) * _ctx.fail1 + (8/41 : ℝ) * a15 + (18/41 : ℝ) * a22 + (12/41 : ℝ) * a24 + (18/41 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_11 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : -(h 0) < (-2/13 : ℝ))
    (a23 : ((-2 : ℝ) * (delta)) < (-3/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/8 : ℝ) * _ctx.order1 + (3/8 : ℝ) * _ctx.order3 + (3/4 : ℝ) * _ctx.order4 + (9/8 : ℝ) * _ctx.min + (1/8 : ℝ) * _ctx.fail1 + (1/8 : ℝ) * a19 + (3/4 : ℝ) * a23 + (3/8 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_10 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : -(h 5) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a19 : -(h 0) < (-2/13 : ℝ))
    (a22 : -(h 1) < (-3/26 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/13 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_11 h delta _ctx _hno a19 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_12 h delta _ctx _hno a15 a22 f1
  by_cases p2 : h 1 ≤ (5/42 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/42 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_13 h delta _ctx _hno a15 a19 f2
  apply _hno 34
  change (((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (5/42 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem upper_node_9 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a15 : -(h 5) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a21 : -(h 0) < (-5/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/5 : ℝ) * _ctx.order2 + (6/5 : ℝ) * _ctx.order3 + (9/5 : ℝ) * _ctx.order4 + (11/5 : ℝ) * _ctx.min + (1/5 : ℝ) * a13 + (1/5 : ℝ) * a15 + (3/5 : ℝ) * a21 + (3/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_8 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : -(h 0) < (-2/13 : ℝ))
    (a20 : ((-2 : ℝ) * (delta)) < (-3/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/8 : ℝ) * _ctx.order1 + (3/8 : ℝ) * _ctx.order3 + (3/4 : ℝ) * _ctx.order4 + (9/8 : ℝ) * _ctx.min + (1/8 : ℝ) * _ctx.fail1 + (1/8 : ℝ) * a19 + (3/4 : ℝ) * a20 + (3/8 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_7 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a15 : -(h 5) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a19 : -(h 0) < (-2/13 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/13 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_8 h delta _ctx _hno a19 f0
  by_cases p1 : h 0 ≤ (5/26 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/26 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_9 h delta _ctx _hno a13 a15 f1
  by_cases p2 : h 1 ≤ (3/26 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_10 h delta _ctx _hno a15 a19 f2
  apply _hno 1
  change (((2 : ℝ) * (delta)) ≤ (3/13 : ℝ)) ∧ (h 0 ≤ (5/26 : ℝ)) ∧ (h 1 ≤ (3/26 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem upper_node_6 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a18 : ((-2 : ℝ) * (delta)) < (-5/21 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a18
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_5 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a15 : -(h 5) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a17 : -(h 0) < (-1/7 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/21 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/21 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_6 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_7 h delta _ctx _hno a13 a15 f1
  by_cases p2 : h 1 ≤ (13/108 : ℝ)
  swap
  · have f2 : -(h 1) < (-13/108 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_20 h delta _ctx _hno a15 a17 f2
  apply _hno 5
  change (((2 : ℝ) * (delta)) ≤ (5/21 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (13/108 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem upper_node_4 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a16 : ((-2 : ℝ) * (delta)) < (-8/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a16
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_3 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a15 : -(h 5) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (8/35 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-8/35 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_4 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (1/7 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_5 h delta _ctx _hno a13 a15 f1
  by_cases p2 : h 2 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 2) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_51 h delta _ctx _hno a15 f2
  by_cases p3 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f3 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_52 h delta _ctx _hno a15 p1 f3
  apply _hno 33
  change (((2 : ℝ) * (delta)) ≤ (8/35 : ℝ)) ∧ (h 0 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_2 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    : False := by
  by_cases p0 : h 5 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ)
  swap
  · have f0 : -(h 5) + ((-8 : ℝ) * (delta)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_3 h delta _ctx _hno a13 f0
  by_cases p1 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ)
  swap
  · have f1 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_71 h delta _ctx _hno a13 a14 p0 f1
  by_cases p2 : ((6 : ℝ) * (h 1)) + h 5 ≤ (1 : ℝ)
  swap
  · have f2 : ((-6 : ℝ) * (h 1)) + -(h 5) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_722 h delta _ctx _hno a14 f2
  by_cases p3 : ((6 : ℝ) * (h 2)) + h 5 ≤ (1 : ℝ)
  swap
  · have f3 : ((-6 : ℝ) * (h 2)) + -(h 5) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_723 h delta _ctx _hno f3
  by_cases p4 : ((8 : ℝ) * (h 3)) + h 5 ≤ (1 : ℝ)
  swap
  · have f4 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_724 h delta _ctx _hno a14 p0 p1 f4
  by_cases p5 : ((8 : ℝ) * (h 4)) + h 5 ≤ (1 : ℝ)
  swap
  · have f5 : ((-8 : ℝ) * (h 4)) + -(h 5) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1036 h delta _ctx _hno p4 f5
  apply _hno 32
  change (h 5 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ)) ∧ (((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ)) ∧ (((6 : ℝ) * (h 1)) + h 5 ≤ (1 : ℝ)) ∧ (((6 : ℝ) * (h 2)) + h 5 ≤ (1 : ℝ)) ∧ (((8 : ℝ) * (h 3)) + h 5 ≤ (1 : ℝ)) ∧ (((8 : ℝ) * (h 4)) + h 5 ≤ (1 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_1 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    : False := by
  by_cases p0 : h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ)
  swap
  · have f0 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_2 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 + ((6 : ℝ) * (h 1)) ≤ (1 : ℝ)
  swap
  · have f1 : -(h 0) + ((-6 : ℝ) * (h 1)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1037 h delta _ctx _hno p0 f1
  by_cases p2 : h 0 + ((6 : ℝ) * (h 2)) ≤ (1 : ℝ)
  swap
  · have f2 : -(h 0) + ((-6 : ℝ) * (h 2)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1131 h delta _ctx _hno f2
  by_cases p3 : h 0 + ((6 : ℝ) * (h 3)) ≤ (1 : ℝ)
  swap
  · have f3 : -(h 0) + ((-6 : ℝ) * (h 3)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1132 h delta _ctx _hno f3
  by_cases p4 : h 0 + ((8 : ℝ) * (h 4)) ≤ (1 : ℝ)
  swap
  · have f4 : -(h 0) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1133 h delta _ctx _hno a13 p0 p1 f4
  by_cases p5 : h 0 + ((8 : ℝ) * (h 5)) ≤ (1 : ℝ)
  swap
  · have f5 : -(h 0) + ((-8 : ℝ) * (h 5)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_3992 h delta _ctx _hno p4 f5
  apply _hno 31
  change (h 0 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ)) ∧ (h 0 + ((6 : ℝ) * (h 1)) ≤ (1 : ℝ)) ∧ (h 0 + ((6 : ℝ) * (h 2)) ≤ (1 : ℝ)) ∧ (h 0 + ((6 : ℝ) * (h 3)) ≤ (1 : ℝ)) ∧ (h 0 + ((8 : ℝ) * (h 4)) ≤ (1 : ℝ)) ∧ (h 0 + ((8 : ℝ) * (h 5)) ≤ (1 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_0 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    : False := by
  by_cases p0 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ)
  swap
  · have f0 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1 h delta _ctx _hno f0
  by_cases p1 : ((3 : ℝ) * (h 2)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ)
  swap
  · have f1 : ((-3 : ℝ) * (h 2)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_3993 h delta _ctx _hno p0 f1
  by_cases p2 : ((3 : ℝ) * (h 5)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ)
  swap
  · have f2 : ((-3 : ℝ) * (h 5)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_3994 h delta _ctx _hno p1 f2
  by_cases p3 : ((3 : ℝ) * (h 0)) + ((3 : ℝ) * (h 1)) ≤ (1 : ℝ)
  swap
  · have f3 : ((-3 : ℝ) * (h 0)) + ((-3 : ℝ) * (h 1)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_3995 h delta _ctx _hno f3
  by_cases p4 : ((3 : ℝ) * (h 0)) + ((3 : ℝ) * (h 2)) ≤ (1 : ℝ)
  swap
  · have f4 : ((-3 : ℝ) * (h 0)) + ((-3 : ℝ) * (h 2)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_3996 h delta _ctx _hno f4
  by_cases p5 : ((3 : ℝ) * (h 0)) + ((3 : ℝ) * (h 5)) ≤ (1 : ℝ)
  swap
  · have f5 : ((-3 : ℝ) * (h 0)) + ((-3 : ℝ) * (h 5)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_3997 h delta _ctx _hno f5
  by_cases p6 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (h 3)) ≤ (1 : ℝ)
  swap
  · have f6 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 3)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact upper_node_3998 h delta _ctx _hno p0 p1 p2 f6
  by_cases p7 : ((3 : ℝ) * (h 2)) + ((6 : ℝ) * (h 3)) ≤ (1 : ℝ)
  swap
  · have f7 : ((-3 : ℝ) * (h 2)) + ((-6 : ℝ) * (h 3)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p7
      linarith only [hp]
    exact upper_node_4303 h delta _ctx _hno p6 f7
  by_cases p8 : ((6 : ℝ) * (h 3)) + ((3 : ℝ) * (h 5)) ≤ (1 : ℝ)
  swap
  · have f8 : ((-6 : ℝ) * (h 3)) + ((-3 : ℝ) * (h 5)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p8
      linarith only [hp]
    exact upper_node_4304 h delta _ctx _hno p7 f8
  by_cases p9 : ((3 : ℝ) * (h 1)) + ((6 : ℝ) * (h 4)) ≤ (1 : ℝ)
  swap
  · have f9 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (h 4)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p9
      linarith only [hp]
    exact upper_node_4305 h delta _ctx _hno p6 f9
  by_cases p10 : ((3 : ℝ) * (h 2)) + ((6 : ℝ) * (h 4)) ≤ (1 : ℝ)
  swap
  · have f10 : ((-3 : ℝ) * (h 2)) + ((-6 : ℝ) * (h 4)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p10
      linarith only [hp]
    exact upper_node_4306 h delta _ctx _hno p7 f10
  by_cases p11 : ((6 : ℝ) * (h 4)) + ((3 : ℝ) * (h 5)) ≤ (1 : ℝ)
  swap
  · have f11 : ((-6 : ℝ) * (h 4)) + ((-3 : ℝ) * (h 5)) < (-1 : ℝ) := by
      have hp := lt_of_not_ge p11
      linarith only [hp]
    exact upper_node_4307 h delta _ctx _hno p10 f11
  apply _hno 30
  change (((3 : ℝ) * (h 1)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ)) ∧ (((3 : ℝ) * (h 2)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ)) ∧ (((3 : ℝ) * (h 5)) + ((6 : ℝ) * (delta)) ≤ (1 : ℝ)) ∧ (((3 : ℝ) * (h 0)) + ((3 : ℝ) * (h 1)) ≤ (1 : ℝ)) ∧ (((3 : ℝ) * (h 0)) + ((3 : ℝ) * (h 2)) ≤ (1 : ℝ)) ∧ (((3 : ℝ) * (h 0)) + ((3 : ℝ) * (h 5)) ≤ (1 : ℝ)) ∧ (((3 : ℝ) * (h 1)) + ((6 : ℝ) * (h 3)) ≤ (1 : ℝ)) ∧ (((3 : ℝ) * (h 2)) + ((6 : ℝ) * (h 3)) ≤ (1 : ℝ)) ∧ (((6 : ℝ) * (h 3)) + ((3 : ℝ) * (h 5)) ≤ (1 : ℝ)) ∧ (((3 : ℝ) * (h 1)) + ((6 : ℝ) * (h 4)) ≤ (1 : ℝ)) ∧ (((3 : ℝ) * (h 2)) + ((6 : ℝ) * (h 4)) ≤ (1 : ℝ)) ∧ (((6 : ℝ) * (h 4)) + ((3 : ℝ) * (h 5)) ≤ (1 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11⟩

end RealPinwheel.WeakSevenBandData
