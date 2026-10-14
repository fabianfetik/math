import Pinwheel.WeakSevenBandData.CoverChunks.Upper041

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem upper_node_947 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a40 : -(h 1) < (-9/70 : ℝ))
    (a44 : -(h 3) < (-2/17 : ℝ))
    (a45 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/21 : ℝ) * _ctx.order4 + (8/21 : ℝ) * _ctx.min + (1/21 : ℝ) * _ctx.fail1 + (1/21 : ℝ) * _ctx.fail2 + (2/7 : ℝ) * a40 + (2/7 : ℝ) * a44 + (1/3 : ℝ) * a45 + (2/7 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_946 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a35 : -(h 4) < (-1/9 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a40 : -(h 1) < (-9/70 : ℝ))
    (a44 : -(h 3) < (-2/17 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_947 h delta _ctx _hno a40 a44 f0
  by_cases p1 : h 0 ≤ (1/7 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_948 h delta _ctx _hno a14 a35 a40 a44 f1
  by_cases p2 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_949 h delta _ctx _hno a14 a24 a40 a44 f2
  by_cases p3 : h 4 ≤ (4/35 : ℝ)
  swap
  · have f3 : -(h 4) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_950 h delta _ctx _hno a14 a37 a40 a44 f3
  apply _hno 97
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (4/35 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_945 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a31 : -(h 3) < (-4/35 : ℝ))
    (a35 : -(h 4) < (-1/9 : ℝ))
    (a43 : -(h 1) < (-3/23 : ℝ))
    (a48 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (16/373 : ℝ) * _ctx.fail1 + (13/373 : ℝ) * _ctx.fail2 + (12/373 : ℝ) * a14 + (96/373 : ℝ) * a31 + (44/373 : ℝ) * a35 + (96/373 : ℝ) * a43 + (96/373 : ℝ) * a48 + (96/373 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_944 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a35 : -(h 4) < (-1/9 : ℝ))
    (a43 : -(h 1) < (-3/23 : ℝ))
    (a52 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (48/149 : ℝ) * _ctx.min + (8/149 : ℝ) * _ctx.fail1 + (5/149 : ℝ) * _ctx.fail2 + (12/149 : ℝ) * a14 + (28/149 : ℝ) * a35 + (48/149 : ℝ) * a43 + (48/149 : ℝ) * a52 + (48/149 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_943 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a43 : -(h 1) < (-3/23 : ℝ))
    (a47 : -(h 3) < (-3/26 : ℝ))
    (a51 : -(h 2) < (-5/41 : ℝ))
    (a55 : -(h 4) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (1/20 : ℝ) * a14 + (3/20 : ℝ) * a37 + (1/5 : ℝ) * a43 + (1/5 : ℝ) * a47 + (1/5 : ℝ) * a51 + (1/5 : ℝ) * a55 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_942 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a43 : -(h 1) < (-3/23 : ℝ))
    (a47 : -(h 3) < (-3/26 : ℝ))
    (a54 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (16/55 : ℝ) * _ctx.min + (3/55 : ℝ) * _ctx.fail2 + (4/55 : ℝ) * a14 + (1/110 : ℝ) * a24 + (16/55 : ℝ) * a43 + (31/110 : ℝ) * a47 + (16/55 : ℝ) * a54 + (16/55 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_941 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a43 : -(h 1) < (-3/23 : ℝ))
    (a47 : -(h 3) < (-3/26 : ℝ))
    (a51 : -(h 2) < (-5/41 : ℝ))
    (a53 : -(h 0) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.min + (1/16 : ℝ) * a14 + (1/32 : ℝ) * a24 + (1/4 : ℝ) * a43 + (7/32 : ℝ) * a47 + (1/4 : ℝ) * a51 + (3/16 : ℝ) * a53 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_940 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a43 : -(h 1) < (-3/23 : ℝ))
    (a47 : -(h 3) < (-3/26 : ℝ))
    (a51 : -(h 2) < (-5/41 : ℝ))
    (a52 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/17 : ℝ) * _ctx.min + (1/17 : ℝ) * _ctx.fail2 + (4/17 : ℝ) * a43 + (4/17 : ℝ) * a47 + (4/17 : ℝ) * a51 + (4/17 : ℝ) * a52 + (4/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_939 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a43 : -(h 1) < (-3/23 : ℝ))
    (a47 : -(h 3) < (-3/26 : ℝ))
    (a51 : -(h 2) < (-5/41 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_940 h delta _ctx _hno a43 a47 a51 f0
  by_cases p1 : h 0 ≤ (1/7 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_941 h delta _ctx _hno a14 a24 a43 a47 a51 f1
  by_cases p2 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_942 h delta _ctx _hno a14 a24 a43 a47 f2
  by_cases p3 : h 4 ≤ (4/35 : ℝ)
  swap
  · have f3 : -(h 4) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_943 h delta _ctx _hno a14 a37 a43 a47 a51 f3
  apply _hno 97
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (4/35 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_938 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a35 : -(h 4) < (-1/9 : ℝ))
    (a47 : -(h 3) < (-3/26 : ℝ))
    (a50 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (48/149 : ℝ) * _ctx.min + (8/149 : ℝ) * _ctx.fail1 + (5/149 : ℝ) * _ctx.fail2 + (12/149 : ℝ) * a14 + (28/149 : ℝ) * a35 + (48/149 : ℝ) * a47 + (48/149 : ℝ) * a50 + (48/149 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_937 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : h 0 ≤ (1/7 : ℝ))
    (a49 : -(h 0) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_936 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : h 3 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a47 : -(h 3) < (-3/26 : ℝ))
    (a48 : ((-2 : ℝ) * (delta)) < (-11/49 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * a20 + (1/5 : ℝ) * a47 + (4/5 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_935 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a20 : h 3 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a29 : h 0 ≤ (1/7 : ℝ))
    (a35 : -(h 4) < (-1/9 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a43 : -(h 1) < (-3/23 : ℝ))
    (a47 : -(h 3) < (-3/26 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (11/49 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-11/49 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_936 h delta _ctx _hno a20 a47 f0
  by_cases p1 : h 0 ≤ (1/7 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_937 h delta _ctx _hno a29 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_938 h delta _ctx _hno a14 a35 a47 f2
  by_cases p3 : h 2 ≤ (5/41 : ℝ)
  swap
  · have f3 : -(h 2) < (-5/41 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_939 h delta _ctx _hno a14 a24 a37 a43 a47 f3
  by_cases p4 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_944 h delta _ctx _hno a14 a35 a43 f4
  apply _hno 45
  change (((2 : ℝ) * (delta)) ≤ (11/49 : ℝ)) ∧ (h 0 ≤ (1/7 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (5/41 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_934 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a31 : -(h 3) < (-4/35 : ℝ))
    (a46 : -(h 1) < (-2/15 : ℝ))
    (a53 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (16/329 : ℝ) * _ctx.fail1 + (13/329 : ℝ) * _ctx.fail2 + (12/329 : ℝ) * a14 + (11/658 : ℝ) * a24 + (181/658 : ℝ) * a31 + (96/329 : ℝ) * a46 + (96/329 : ℝ) * a53 + (96/329 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_933 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a46 : -(h 1) < (-2/15 : ℝ))
    (a52 : -(h 4) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.order3 + (6/23 : ℝ) * _ctx.min + (1/23 : ℝ) * _ctx.fail1 + (3/46 : ℝ) * a14 + (5/46 : ℝ) * a37 + (6/23 : ℝ) * a46 + (12/23 : ℝ) * a52 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_932 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a35 : -(h 4) < (-1/9 : ℝ))
    (a46 : -(h 1) < (-2/15 : ℝ))
    (a51 : -(h 3) < (-15/131 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (48/149 : ℝ) * _ctx.min + (8/149 : ℝ) * _ctx.fail1 + (5/149 : ℝ) * _ctx.fail2 + (12/149 : ℝ) * a14 + (28/149 : ℝ) * a35 + (48/149 : ℝ) * a46 + (48/149 : ℝ) * a51 + (48/149 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_931 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a34 : h 2 ≤ (1/8 : ℝ))
    (a50 : -(h 2) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_930 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a31 : -(h 3) < (-4/35 : ℝ))
    (a49 : -(h 1) < (-5/37 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (48/121 : ℝ) * _ctx.min + (8/121 : ℝ) * _ctx.fail1 + (5/121 : ℝ) * _ctx.fail2 + (12/121 : ℝ) * a14 + (7/242 : ℝ) * a24 + (89/242 : ℝ) * a31 + (48/121 : ℝ) * a49 + (48/121 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_929 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : h 0 ≤ (1/7 : ℝ))
    (a48 : -(h 0) < (-13/90 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_928 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a31 : -(h 3) < (-4/35 : ℝ))
    (a46 : -(h 1) < (-2/15 : ℝ))
    (a47 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/10 : ℝ) * _ctx.min + (1/20 : ℝ) * _ctx.fail1 + (1/20 : ℝ) * _ctx.fail2 + (1/80 : ℝ) * a24 + (23/80 : ℝ) * a31 + (3/10 : ℝ) * a46 + (3/10 : ℝ) * a47 + (3/10 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_927 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a29 : h 0 ≤ (1/7 : ℝ))
    (a31 : -(h 3) < (-4/35 : ℝ))
    (a34 : h 2 ≤ (1/8 : ℝ))
    (a35 : -(h 4) < (-1/9 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a46 : -(h 1) < (-2/15 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_928 h delta _ctx _hno a24 a31 a46 f0
  by_cases p1 : h 0 ≤ (13/90 : ℝ)
  swap
  · have f1 : -(h 0) < (-13/90 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_929 h delta _ctx _hno a29 f1
  by_cases p2 : h 1 ≤ (5/37 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/37 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_930 h delta _ctx _hno a14 a24 a31 f2
  by_cases p3 : h 2 ≤ (3/23 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_931 h delta _ctx _hno a34 f3
  by_cases p4 : h 3 ≤ (15/131 : ℝ)
  swap
  · have f4 : -(h 3) < (-15/131 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_932 h delta _ctx _hno a14 a35 a46 f4
  by_cases p5 : h 4 ≤ (4/35 : ℝ)
  swap
  · have f5 : -(h 4) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_933 h delta _ctx _hno a14 a37 a46 f5
  by_cases p6 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f6 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact upper_node_934 h delta _ctx _hno a14 a24 a31 a46 f6
  apply _hno 28
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (13/90 : ℝ)) ∧ (h 1 ≤ (5/37 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (15/131 : ℝ)) ∧ (h 4 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem upper_node_926 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : h 0 ≤ (1/7 : ℝ))
    (a45 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_925 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a31 : -(h 3) < (-4/35 : ℝ))
    (a43 : -(h 1) < (-3/23 : ℝ))
    (a44 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/10 : ℝ) * _ctx.min + (1/20 : ℝ) * _ctx.fail1 + (1/20 : ℝ) * _ctx.fail2 + (1/80 : ℝ) * a24 + (23/80 : ℝ) * a31 + (3/10 : ℝ) * a43 + (3/10 : ℝ) * a44 + (3/10 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_924 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a20 : h 3 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a29 : h 0 ≤ (1/7 : ℝ))
    (a31 : -(h 3) < (-4/35 : ℝ))
    (a34 : h 2 ≤ (1/8 : ℝ))
    (a35 : -(h 4) < (-1/9 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a43 : -(h 1) < (-3/23 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_925 h delta _ctx _hno a24 a31 a43 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_926 h delta _ctx _hno a29 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_927 h delta _ctx _hno a14 a24 a29 a31 a34 a35 a37 f2
  by_cases p3 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f3 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_935 h delta _ctx _hno a14 a20 a24 a29 a35 a37 a43 f3
  by_cases p4 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_945 h delta _ctx _hno a14 a31 a35 a43 f4
  apply _hno 19
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_923 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : h 0 ≤ (1/7 : ℝ))
    (a42 : -(h 0) < (-5/34 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_922 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : h 3 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a31 : -(h 3) < (-4/35 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * a20 + (1/5 : ℝ) * a31 + (4/5 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_921 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a20 : h 3 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a29 : h 0 ≤ (1/7 : ℝ))
    (a31 : -(h 3) < (-4/35 : ℝ))
    (a34 : h 2 ≤ (1/8 : ℝ))
    (a35 : -(h 4) < (-1/9 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    (a40 : -(h 1) < (-9/70 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_922 h delta _ctx _hno a20 a31 f0
  by_cases p1 : h 0 ≤ (5/34 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/34 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_923 h delta _ctx _hno a29 f1
  by_cases p2 : h 1 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_924 h delta _ctx _hno a14 a20 a24 a29 a31 a34 a35 a37 f2
  by_cases p3 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_946 h delta _ctx _hno a14 a24 a35 a37 a40 f3
  apply _hno 92
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (5/34 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_920 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : h 0 ≤ (1/7 : ℝ))
    (a39 : -(h 0) < (-7/45 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_919 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : h 3 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a31 : -(h 3) < (-4/35 : ℝ))
    (a38 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * a20 + (1/5 : ℝ) * a31 + (4/5 : ℝ) * a38
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_918 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a20 : h 3 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a29 : h 0 ≤ (1/7 : ℝ))
    (a31 : -(h 3) < (-4/35 : ℝ))
    (a34 : h 2 ≤ (1/8 : ℝ))
    (a35 : -(h 4) < (-1/9 : ℝ))
    (a37 : -(h 0) < (-11/80 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_919 h delta _ctx _hno a20 a31 f0
  by_cases p1 : h 0 ≤ (7/45 : ℝ)
  swap
  · have f1 : -(h 0) < (-7/45 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_920 h delta _ctx _hno a29 f1
  by_cases p2 : h 1 ≤ (9/70 : ℝ)
  swap
  · have f2 : -(h 1) < (-9/70 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_921 h delta _ctx _hno a14 a20 a24 a29 a31 a34 a35 a37 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_951 h delta _ctx _hno a34 f3
  by_cases p4 : h 4 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 4) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_952 h delta _ctx _hno a14 a20 a27 a29 a37 p2 f4
  apply _hno 55
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (7/45 : ℝ)) ∧ (h 1 ≤ (9/70 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (4/35 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_917 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : h 3 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a31 : -(h 3) < (-4/35 : ℝ))
    (a36 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * a20 + (1/5 : ℝ) * a31 + (4/5 : ℝ) * a36
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_916 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a20 : h 3 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a29 : h 0 ≤ (1/7 : ℝ))
    (a31 : -(h 3) < (-4/35 : ℝ))
    (a34 : h 2 ≤ (1/8 : ℝ))
    (a35 : -(h 4) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_917 h delta _ctx _hno a20 a31 f0
  by_cases p1 : h 0 ≤ (11/80 : ℝ)
  swap
  · have f1 : -(h 0) < (-11/80 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_918 h delta _ctx _hno a14 a20 a24 a27 a29 a31 a34 a35 f1
  by_cases p2 : h 1 ≤ (7/51 : ℝ)
  swap
  · have f2 : -(h 1) < (-7/51 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1033 h delta _ctx _hno a14 a31 p1 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1034 h delta _ctx _hno a34 f3
  apply _hno 6
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (11/80 : ℝ)) ∧ (h 1 ≤ (7/51 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_915 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a34 : -(h 2) < (-1/8 : ℝ))
    (a38 : -(h 3) < (-2/17 : ℝ))
    (a44 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/143 : ℝ) * _ctx.order4 + (7/143 : ℝ) * _ctx.fail2 + (4/143 : ℝ) * a14 + (32/143 : ℝ) * a27 + (32/143 : ℝ) * a34 + (32/143 : ℝ) * a38 + (36/143 : ℝ) * a44 + (32/143 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_914 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a34 : -(h 2) < (-1/8 : ℝ))
    (a38 : -(h 3) < (-2/17 : ℝ))
    (a43 : -(h 4) < (-5/44 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (16/59 : ℝ) * _ctx.min + (3/59 : ℝ) * _ctx.fail2 + (4/59 : ℝ) * a14 + (16/59 : ℝ) * a27 + (16/59 : ℝ) * a34 + (16/59 : ℝ) * a38 + (4/59 : ℝ) * a43 + (16/59 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_913 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a34 : -(h 2) < (-1/8 : ℝ))
    (a42 : -(h 3) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (16/55 : ℝ) * _ctx.min + (3/55 : ℝ) * _ctx.fail2 + (4/55 : ℝ) * a14 + (1/110 : ℝ) * a24 + (16/55 : ℝ) * a27 + (16/55 : ℝ) * a34 + (31/110 : ℝ) * a42 + (16/55 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_912 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a34 : -(h 2) < (-1/8 : ℝ))
    (a38 : -(h 3) < (-2/17 : ℝ))
    (a41 : -(h 1) < (-9/71 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (16/55 : ℝ) * _ctx.min + (3/55 : ℝ) * _ctx.fail2 + (4/55 : ℝ) * a14 + (1/110 : ℝ) * a24 + (16/55 : ℝ) * a34 + (31/110 : ℝ) * a38 + (16/55 : ℝ) * a41 + (16/55 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_911 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a34 : -(h 2) < (-1/8 : ℝ))
    (a38 : -(h 3) < (-2/17 : ℝ))
    (a40 : -(h 0) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.min + (1/16 : ℝ) * a14 + (1/32 : ℝ) * a24 + (1/4 : ℝ) * a27 + (1/4 : ℝ) * a34 + (7/32 : ℝ) * a38 + (3/16 : ℝ) * a40 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_910 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a34 : -(h 2) < (-1/8 : ℝ))
    (a38 : -(h 3) < (-2/17 : ℝ))
    (a39 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/17 : ℝ) * _ctx.min + (1/17 : ℝ) * _ctx.fail2 + (4/17 : ℝ) * a27 + (4/17 : ℝ) * a34 + (4/17 : ℝ) * a38 + (4/17 : ℝ) * a39 + (4/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_909 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a34 : -(h 2) < (-1/8 : ℝ))
    (a38 : -(h 3) < (-2/17 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_910 h delta _ctx _hno a27 a34 a38 f0
  by_cases p1 : h 0 ≤ (1/7 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_911 h delta _ctx _hno a14 a24 a27 a34 a38 f1
  by_cases p2 : h 1 ≤ (9/71 : ℝ)
  swap
  · have f2 : -(h 1) < (-9/71 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_912 h delta _ctx _hno a14 a24 a34 a38 f2
  by_cases p3 : h 3 ≤ (3/25 : ℝ)
  swap
  · have f3 : -(h 3) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_913 h delta _ctx _hno a14 a24 a27 a34 f3
  by_cases p4 : h 4 ≤ (5/44 : ℝ)
  swap
  · have f4 : -(h 4) < (-5/44 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_914 h delta _ctx _hno a14 a27 a34 a38 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_915 h delta _ctx _hno a14 a27 a34 a38 f5
  apply _hno 96
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (1/7 : ℝ)) ∧ (h 1 ≤ (9/71 : ℝ)) ∧ (h 3 ≤ (3/25 : ℝ)) ∧ (h 4 ≤ (5/44 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_908 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a31 : -(h 3) < (-4/35 : ℝ))
    (a34 : -(h 2) < (-1/8 : ℝ))
    (a37 : -(h 1) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (16/55 : ℝ) * _ctx.min + (3/55 : ℝ) * _ctx.fail2 + (4/55 : ℝ) * a14 + (1/110 : ℝ) * a24 + (31/110 : ℝ) * a31 + (16/55 : ℝ) * a34 + (16/55 : ℝ) * a37 + (16/55 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_907 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : h 0 ≤ (1/7 : ℝ))
    (a36 : -(h 0) < (-5/34 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a36
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_906 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a31 : -(h 3) < (-4/35 : ℝ))
    (a34 : -(h 2) < (-1/8 : ℝ))
    (a35 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/17 : ℝ) * _ctx.min + (1/17 : ℝ) * _ctx.fail2 + (4/17 : ℝ) * a27 + (4/17 : ℝ) * a31 + (4/17 : ℝ) * a34 + (4/17 : ℝ) * a35 + (4/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_905 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a29 : h 0 ≤ (1/7 : ℝ))
    (a31 : -(h 3) < (-4/35 : ℝ))
    (a34 : -(h 2) < (-1/8 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_906 h delta _ctx _hno a27 a31 a34 f0
  by_cases p1 : h 0 ≤ (5/34 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/34 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_907 h delta _ctx _hno a29 f1
  by_cases p2 : h 1 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_908 h delta _ctx _hno a14 a24 a31 a34 f2
  by_cases p3 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_909 h delta _ctx _hno a14 a24 a27 a34 f3
  apply _hno 92
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (5/34 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_904 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : h 0 ≤ (1/7 : ℝ))
    (a33 : -(h 0) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a33
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_903 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : h 3 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a31 : -(h 3) < (-4/35 : ℝ))
    (a32 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * a20 + (1/5 : ℝ) * a31 + (4/5 : ℝ) * a32
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_902 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a20 : h 3 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a29 : h 0 ≤ (1/7 : ℝ))
    (a31 : -(h 3) < (-4/35 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_903 h delta _ctx _hno a20 a31 f0
  by_cases p1 : h 0 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_904 h delta _ctx _hno a29 f1
  by_cases p2 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_905 h delta _ctx _hno a14 a24 a27 a29 a31 f2
  by_cases p3 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f3 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_916 h delta _ctx _hno a14 a20 a24 a27 a29 a31 p2 f3
  apply _hno 8
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_901 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a30 : -(h 2) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2044/5267 : ℝ) * _ctx.order1 + (1796/5267 : ℝ) * _ctx.min + (17/229 : ℝ) * _ctx.fail2 + (480/5267 : ℝ) * a14 + (248/5267 : ℝ) * a19 + (60/5267 : ℝ) * a24 + (4088/5267 : ℝ) * a30 + (2044/5267 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_900 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a29 : -(h 0) < (-1/7 : ℝ))
    (a34 : -(h 5) < (-1/9 : ℝ))
    (a39 : -(h 4) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.order3 + (1/29 : ℝ) * _ctx.fail1 + (3/116 : ℝ) * a14 + (6/29 : ℝ) * a27 + (13/116 : ℝ) * a29 + (6/29 : ℝ) * a34 + (12/29 : ℝ) * a39 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_899 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a29 : -(h 0) < (-1/7 : ℝ))
    (a34 : -(h 5) < (-1/9 : ℝ))
    (a38 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/33 : ℝ) * a14 + (7/264 : ℝ) * a19 + (1/33 : ℝ) * a24 + (8/33 : ℝ) * a27 + (7/33 : ℝ) * a29 + (19/88 : ℝ) * a34 + (8/33 : ℝ) * a38 + (8/33 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_898 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : h 3 ≤ (3/26 : ℝ))
    (a41 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_897 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a29 : -(h 0) < (-1/7 : ℝ))
    (a40 : -(h 1) < (-3/23 : ℝ))
    (a46 : -(h 5) < (-6/53 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.order3 + (12/29 : ℝ) * _ctx.order4 + (1/29 : ℝ) * _ctx.fail1 + (3/116 : ℝ) * a14 + (13/116 : ℝ) * a29 + (6/29 : ℝ) * a40 + (18/29 : ℝ) * a46 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_896 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a29 : -(h 0) < (-1/7 : ℝ))
    (a34 : -(h 5) < (-1/9 : ℝ))
    (a40 : -(h 1) < (-3/23 : ℝ))
    (a45 : -(h 3) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/23 : ℝ) * _ctx.fail1 + (3/92 : ℝ) * a14 + (3/92 : ℝ) * a24 + (13/92 : ℝ) * a29 + (6/23 : ℝ) * a34 + (6/23 : ℝ) * a40 + (21/92 : ℝ) * a45 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_895 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a29 : -(h 0) < (-1/7 : ℝ))
    (a34 : -(h 5) < (-1/9 : ℝ))
    (a40 : -(h 1) < (-3/23 : ℝ))
    (a44 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/33 : ℝ) * a14 + (7/264 : ℝ) * a19 + (1/33 : ℝ) * a24 + (7/33 : ℝ) * a29 + (19/88 : ℝ) * a34 + (8/33 : ℝ) * a40 + (8/33 : ℝ) * a44 + (8/33 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_894 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a32 : h 1 ≤ (2/15 : ℝ))
    (a43 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a32 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_893 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a34 : -(h 5) < (-1/9 : ℝ))
    (a40 : -(h 1) < (-3/23 : ℝ))
    (a42 : -(h 0) < (-8/55 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/71 : ℝ) * _ctx.fail1 + (3/71 : ℝ) * a14 + (21/568 : ℝ) * a19 + (3/71 : ℝ) * a24 + (171/568 : ℝ) * a34 + (24/71 : ℝ) * a40 + (13/71 : ℝ) * a42 + (24/71 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_892 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-7/31 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a25 + (1 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_891 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a25 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ))
    (a29 : -(h 0) < (-1/7 : ℝ))
    (a32 : h 1 ≤ (2/15 : ℝ))
    (a34 : -(h 5) < (-1/9 : ℝ))
    (a40 : -(h 1) < (-3/23 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/31 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/31 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_892 h delta _ctx _hno a25 f0
  by_cases p1 : h 0 ≤ (8/55 : ℝ)
  swap
  · have f1 : -(h 0) < (-8/55 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_893 h delta _ctx _hno a14 a19 a24 a34 a40 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_894 h delta _ctx _hno a32 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_895 h delta _ctx _hno a14 a19 a24 a29 a34 a40 f3
  by_cases p4 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_896 h delta _ctx _hno a14 a24 a29 a34 a40 f4
  by_cases p5 : h 5 ≤ (6/53 : ℝ)
  swap
  · have f5 : -(h 5) < (-6/53 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_897 h delta _ctx _hno a14 a29 a40 f5
  apply _hno 39
  change (((2 : ℝ) * (delta)) ≤ (7/31 : ℝ)) ∧ (h 0 ≤ (8/55 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (6/53 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_890 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a34 : -(h 5) < (-1/9 : ℝ))
    (a37 : -(h 1) < (-9/70 : ℝ))
    (a39 : -(h 0) < (-5/34 : ℝ))
    (a44 : -(h 3) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/23 : ℝ) * _ctx.fail1 + (3/92 : ℝ) * a14 + (3/92 : ℝ) * a24 + (6/23 : ℝ) * a34 + (6/23 : ℝ) * a37 + (13/92 : ℝ) * a39 + (21/92 : ℝ) * a44 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_889 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a34 : -(h 5) < (-1/9 : ℝ))
    (a37 : -(h 1) < (-9/70 : ℝ))
    (a39 : -(h 0) < (-5/34 : ℝ))
    (a43 : -(h 2) < (-6/49 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/33 : ℝ) * a14 + (7/264 : ℝ) * a19 + (1/33 : ℝ) * a24 + (19/88 : ℝ) * a34 + (8/33 : ℝ) * a37 + (7/33 : ℝ) * a39 + (8/33 : ℝ) * a43 + (8/33 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_888 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a34 : -(h 5) < (-1/9 : ℝ))
    (a39 : -(h 0) < (-5/34 : ℝ))
    (a42 : -(h 1) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/71 : ℝ) * _ctx.fail1 + (3/71 : ℝ) * a14 + (21/568 : ℝ) * a19 + (3/71 : ℝ) * a24 + (171/568 : ℝ) * a34 + (13/71 : ℝ) * a39 + (24/71 : ℝ) * a42 + (24/71 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_887 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a16 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a21 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a41 : -(h 0) < (-7/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/55 : ℝ) * a16 + (1/55 : ℝ) * a19 + (8/55 : ℝ) * a21 + (54/55 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_886 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a37 : -(h 1) < (-9/70 : ℝ))
    (a39 : -(h 0) < (-5/34 : ℝ))
    (a40 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (342/1157 : ℝ) * _ctx.min + (64/1157 : ℝ) * _ctx.fail1 + (42/1157 : ℝ) * a19 + (48/1157 : ℝ) * a24 + (384/1157 : ℝ) * a37 + (256/1157 : ℝ) * a39 + (363/1157 : ℝ) * a40 + (384/1157 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_885 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a16 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a21 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a34 : -(h 5) < (-1/9 : ℝ))
    (a37 : -(h 1) < (-9/70 : ℝ))
    (a39 : -(h 0) < (-5/34 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_886 h delta _ctx _hno a19 a24 a37 a39 f0
  by_cases p1 : h 0 ≤ (7/47 : ℝ)
  swap
  · have f1 : -(h 0) < (-7/47 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_887 h delta _ctx _hno a16 a19 a21 f1
  by_cases p2 : h 1 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_888 h delta _ctx _hno a14 a19 a24 a34 a39 f2
  by_cases p3 : h 2 ≤ (6/49 : ℝ)
  swap
  · have f3 : -(h 2) < (-6/49 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_889 h delta _ctx _hno a14 a19 a24 a34 a37 a39 f3
  by_cases p4 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_890 h delta _ctx _hno a14 a24 a34 a37 a39 f4
  apply _hno 95
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (7/47 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 2 ≤ (6/49 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_884 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a29 : -(h 0) < (-1/7 : ℝ))
    (a37 : -(h 1) < (-9/70 : ℝ))
    (a38 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (342/1157 : ℝ) * _ctx.min + (64/1157 : ℝ) * _ctx.fail1 + (42/1157 : ℝ) * a19 + (48/1157 : ℝ) * a24 + (256/1157 : ℝ) * a29 + (384/1157 : ℝ) * a37 + (363/1157 : ℝ) * a38 + (384/1157 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_883 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a16 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a21 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a25 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ))
    (a29 : -(h 0) < (-1/7 : ℝ))
    (a32 : h 1 ≤ (2/15 : ℝ))
    (a33 : h 3 ≤ (3/26 : ℝ))
    (a34 : -(h 5) < (-1/9 : ℝ))
    (a37 : -(h 1) < (-9/70 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_884 h delta _ctx _hno a19 a24 a29 a37 f0
  by_cases p1 : h 0 ≤ (5/34 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/34 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_885 h delta _ctx _hno a14 a16 a19 a21 a24 a34 a37 f1
  by_cases p2 : h 1 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_891 h delta _ctx _hno a14 a19 a24 a25 a29 a32 a34 f2
  by_cases p3 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_898 h delta _ctx _hno a33 f3
  apply _hno 92
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (5/34 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_882 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a16 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a21 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a36 : -(h 0) < (-7/45 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/55 : ℝ) * a16 + (1/55 : ℝ) * a19 + (8/55 : ℝ) * a21 + (54/55 : ℝ) * a36
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_881 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ))
    (a35 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a25 + (1 : ℝ) * a35
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_880 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a16 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a21 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a25 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a29 : -(h 0) < (-1/7 : ℝ))
    (a32 : h 1 ≤ (2/15 : ℝ))
    (a33 : h 3 ≤ (3/26 : ℝ))
    (a34 : -(h 5) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_881 h delta _ctx _hno a25 f0
  by_cases p1 : h 0 ≤ (7/45 : ℝ)
  swap
  · have f1 : -(h 0) < (-7/45 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_882 h delta _ctx _hno a16 a19 a21 f1
  by_cases p2 : h 1 ≤ (9/70 : ℝ)
  swap
  · have f2 : -(h 1) < (-9/70 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_883 h delta _ctx _hno a14 a16 a19 a21 a24 a25 a29 a32 a33 a34 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_899 h delta _ctx _hno a14 a19 a24 a27 a29 a34 f3
  by_cases p4 : h 4 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 4) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_900 h delta _ctx _hno a14 a27 a29 a34 f4
  apply _hno 55
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (7/45 : ℝ)) ∧ (h 1 ≤ (9/70 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (4/35 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_879 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a29 : -(h 0) < (-1/7 : ℝ))
    (a46 : -(h 3) < (-2/17 : ℝ))
    (a52 : -(h 4) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.min + (1/23 : ℝ) * _ctx.fail1 + (3/46 : ℝ) * a14 + (6/23 : ℝ) * a27 + (5/46 : ℝ) * a29 + (6/23 : ℝ) * a46 + (6/23 : ℝ) * a52 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_878 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a29 : -(h 0) < (-1/7 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a51 : -(h 3) < (-5/42 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.min + (1/23 : ℝ) * _ctx.fail1 + (3/46 : ℝ) * a14 + (6/23 : ℝ) * a27 + (5/46 : ℝ) * a29 + (6/23 : ℝ) * a42 + (6/23 : ℝ) * a51 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_877 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a29 : -(h 0) < (-1/7 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a46 : -(h 3) < (-2/17 : ℝ))
    (a50 : -(h 2) < (-4/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (1/20 : ℝ) * a14 + (1/5 : ℝ) * a27 + (3/20 : ℝ) * a29 + (1/5 : ℝ) * a42 + (1/5 : ℝ) * a46 + (1/5 : ℝ) * a50 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_876 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a29 : -(h 0) < (-1/7 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a46 : -(h 3) < (-2/17 : ℝ))
    (a49 : -(h 1) < (-11/87 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.min + (1/23 : ℝ) * _ctx.fail1 + (3/46 : ℝ) * a14 + (5/46 : ℝ) * a29 + (6/23 : ℝ) * a42 + (6/23 : ℝ) * a46 + (6/23 : ℝ) * a49 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_875 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a46 : -(h 3) < (-2/17 : ℝ))
    (a48 : -(h 0) < (-8/55 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.min + (1/23 : ℝ) * _ctx.fail1 + (3/46 : ℝ) * a14 + (6/23 : ℝ) * a27 + (6/23 : ℝ) * a42 + (6/23 : ℝ) * a46 + (5/46 : ℝ) * a48 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_874 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a29 : -(h 0) < (-1/7 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a46 : -(h 3) < (-2/17 : ℝ))
    (a47 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.min + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a27 + (4/29 : ℝ) * a29 + (6/29 : ℝ) * a42 + (6/29 : ℝ) * a46 + (6/29 : ℝ) * a47 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_873 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a29 : -(h 0) < (-1/7 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a46 : -(h 3) < (-2/17 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_874 h delta _ctx _hno a27 a29 a42 a46 f0
  by_cases p1 : h 0 ≤ (8/55 : ℝ)
  swap
  · have f1 : -(h 0) < (-8/55 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_875 h delta _ctx _hno a14 a27 a42 a46 f1
  by_cases p2 : h 1 ≤ (11/87 : ℝ)
  swap
  · have f2 : -(h 1) < (-11/87 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_876 h delta _ctx _hno a14 a29 a42 a46 f2
  by_cases p3 : h 2 ≤ (4/33 : ℝ)
  swap
  · have f3 : -(h 2) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_877 h delta _ctx _hno a14 a27 a29 a42 a46 f3
  by_cases p4 : h 3 ≤ (5/42 : ℝ)
  swap
  · have f4 : -(h 3) < (-5/42 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_878 h delta _ctx _hno a14 a27 a29 a42 f4
  by_cases p5 : h 4 ≤ (2/17 : ℝ)
  swap
  · have f5 : -(h 4) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_879 h delta _ctx _hno a14 a27 a29 a46 f5
  apply _hno 94
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (8/55 : ℝ)) ∧ (h 1 ≤ (11/87 : ℝ)) ∧ (h 2 ≤ (4/33 : ℝ)) ∧ (h 3 ≤ (5/42 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_872 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a40 : h 1 ≤ (9/70 : ℝ))
    (a45 : -(h 1) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a40 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_871 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a33 : -(h 3) < (-3/26 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a44 : -(h 0) < (-5/34 : ℝ))
    (a50 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/29 : ℝ) * _ctx.fail1 + (3/116 : ℝ) * a14 + (6/29 : ℝ) * a27 + (6/29 : ℝ) * a33 + (6/29 : ℝ) * a42 + (13/116 : ℝ) * a44 + (6/29 : ℝ) * a50 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_870 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a44 : -(h 0) < (-5/34 : ℝ))
    (a49 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.min + (1/23 : ℝ) * _ctx.fail1 + (3/46 : ℝ) * a14 + (6/23 : ℝ) * a27 + (6/23 : ℝ) * a42 + (5/46 : ℝ) * a44 + (6/23 : ℝ) * a49 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_869 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a33 : -(h 3) < (-3/26 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a44 : -(h 0) < (-5/34 : ℝ))
    (a48 : -(h 2) < (-33/278 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (1/20 : ℝ) * a14 + (1/5 : ℝ) * a27 + (1/5 : ℝ) * a33 + (1/5 : ℝ) * a42 + (3/20 : ℝ) * a44 + (1/5 : ℝ) * a48 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_868 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a40 : h 1 ≤ (9/70 : ℝ))
    (a47 : -(h 1) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a40 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

end RealPinwheel.WeakSevenBandData
