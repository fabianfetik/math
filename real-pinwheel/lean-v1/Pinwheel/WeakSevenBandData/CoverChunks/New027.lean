import Pinwheel.WeakSevenBandData.CoverChunks.New026

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem new_node_10954 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : h 1 ≤ (2/15 : ℝ))
    (a41 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a24 + (1 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10953 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a31 : h 0 ≤ (5/33 : ℝ))
    (a40 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10952 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a39 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10951 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a24 : h 1 ≤ (2/15 : ℝ))
    (a25 : h 2 ≤ (1/8 : ℝ))
    (a26 : -(h 4) < (-1/9 : ℝ))
    (a33 : -(h 2) < (-4/33 : ℝ))
    (a36 : -(h 1) < (-5/38 : ℝ))
    (a38 : h 0 ≤ (3/20 : ℝ))
    (a40 : -(h 3) < (-3/26 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_10977 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (7/48 : ℝ)
  swap
  · have f1 : -(h 0) < (-7/48 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_10978 h delta _ctx _hno a13 a24 a25 a26 a33 a36 a38 a40 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_10979 h delta _ctx _hno a24 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_10980 h delta _ctx _hno a25 f3
  apply _hno 230
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (7/48 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_10950 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : h 1 ≤ (2/15 : ℝ))
    (a39 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a24 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10949 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a24 : h 1 ≤ (2/15 : ℝ))
    (a25 : h 2 ≤ (1/8 : ℝ))
    (a26 : -(h 4) < (-1/9 : ℝ))
    (a31 : h 0 ≤ (5/33 : ℝ))
    (a33 : -(h 2) < (-4/33 : ℝ))
    (a36 : -(h 1) < (-5/38 : ℝ))
    (a38 : -(h 0) < (-3/20 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_10952 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_10953 h delta _ctx _hno a31 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_10954 h delta _ctx _hno a24 f2
  by_cases p3 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f3 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_10955 h delta _ctx _hno a13 a24 a25 a26 a31 a33 a36 a38 f3
  by_cases p4 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_10956 h delta _ctx _hno a26 a33 a36 a38 f4
  apply _hno 70
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_10948 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a37 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a37
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10947 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a25 : h 2 ≤ (1/8 : ℝ))
    (a26 : -(h 4) < (-1/9 : ℝ))
    (a31 : h 0 ≤ (5/33 : ℝ))
    (a33 : -(h 2) < (-4/33 : ℝ))
    (a36 : h 1 ≤ (5/38 : ℝ))
    (a39 : -(h 5) < (-2/19 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_11064 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (1/7 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_11065 h delta _ctx _hno a13 a25 a26 a31 a33 a36 a39
  by_cases p2 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_11066 h delta _ctx _hno a25 f2
  apply _hno 84
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem new_node_10946 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : h 2 ≤ (1/8 : ℝ))
    (a38 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * _ctx.order2 + (1 : ℝ) * a25 + (1 : ℝ) * a38
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10945 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : h 2 ≤ (1/8 : ℝ))
    (a37 : -(h 2) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a25 + (1 : ℝ) * a37
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10944 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a24 : h 1 ≤ (2/15 : ℝ))
    (a25 : h 2 ≤ (1/8 : ℝ))
    (a26 : -(h 4) < (-1/9 : ℝ))
    (a31 : h 0 ≤ (5/33 : ℝ))
    (a33 : -(h 2) < (-4/33 : ℝ))
    (a36 : -(h 1) < (-5/38 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_10948 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_10949 h delta _ctx _hno a13 a24 a25 a26 a31 a33 a36 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_10950 h delta _ctx _hno a24 f2
  by_cases p3 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f3 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_10951 h delta _ctx _hno a13 a24 a25 a26 a33 a36 p1 f3
  apply _hno 68
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_10943 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a31 : h 0 ≤ (5/33 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a35
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10942 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a34
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10941 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a29 : -(h 1) < (-1/8 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    (a44 : -(h 0) < (-2/13 : ℝ))
    (a54 : -(h 4) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order2 + (1/3 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a29 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a44 + (1/2 : ℝ) * a54 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10940 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a35 : h 2 ≤ (2/17 : ℝ))
    (a53 : -(h 3) < (-4/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * _ctx.order2 + (1 : ℝ) * a35 + (1 : ℝ) * a53
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10939 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a36 : -(h 3) < (-5/43 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    (a44 : -(h 0) < (-2/13 : ℝ))
    (a49 : -(h 4) < (-4/35 : ℝ))
    (a52 : -(h 1) < (-6/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order2 + (1/6 : ℝ) * _ctx.lower + (1/3 : ℝ) * a36 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a44 + (1/6 : ℝ) * a49 + (1/6 : ℝ) * a52 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10938 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a46 : h 0 ≤ (7/45 : ℝ))
    (a51 : -(h 0) < (-4/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a46 + (1 : ℝ) * a51
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10937 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a50 : ((-2 : ℝ) * (delta)) < (-10/49 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10936 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a29 : -(h 1) < (-1/8 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    (a46 : -(h 0) < (-7/45 : ℝ))
    (a51 : -(h 4) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order2 + (1/3 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a29 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a46 + (1/2 : ℝ) * a51 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10935 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a35 : h 2 ≤ (2/17 : ℝ))
    (a50 : -(h 3) < (-4/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * _ctx.order2 + (1 : ℝ) * a35 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10934 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a39 : h 1 ≤ (6/47 : ℝ))
    (a49 : -(h 1) < (-6/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a39 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10933 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a33 : h 0 ≤ (8/51 : ℝ))
    (a48 : -(h 0) < (-4/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10932 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a47 : ((-2 : ℝ) * (delta)) < (-10/49 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10931 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a29 : -(h 1) < (-1/8 : ℝ))
    (a35 : h 2 ≤ (2/17 : ℝ))
    (a36 : -(h 3) < (-5/43 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    (a44 : -(h 0) < (-2/13 : ℝ))
    (a46 : h 0 ≤ (7/45 : ℝ))
    (a49 : -(h 4) < (-4/35 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (10/49 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-10/49 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_10937 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (4/25 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/25 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_10938 h delta _ctx _hno a46 f1
  by_cases p2 : h 1 ≤ (6/47 : ℝ)
  swap
  · have f2 : -(h 1) < (-6/47 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_10939 h delta _ctx _hno a36 a42 a44 a49 f2
  by_cases p3 : h 3 ≤ (4/33 : ℝ)
  swap
  · have f3 : -(h 3) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_10940 h delta _ctx _hno a35 f3
  by_cases p4 : h 4 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 4) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_10941 h delta _ctx _hno a29 a42 a44 f4
  apply _hno 156
  change (((2 : ℝ) * (delta)) ≤ (10/49 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (6/47 : ℝ)) ∧ (h 3 ≤ (4/33 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_10930 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a35 : h 2 ≤ (2/17 : ℝ))
    (a48 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a35 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10929 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a39 : h 1 ≤ (6/47 : ℝ))
    (a47 : -(h 1) < (-9/70 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a39 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10928 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a29 : -(h 1) < (-1/8 : ℝ))
    (a33 : h 0 ≤ (8/51 : ℝ))
    (a35 : h 2 ≤ (2/17 : ℝ))
    (a39 : h 1 ≤ (6/47 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    (a46 : -(h 0) < (-7/45 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (10/49 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-10/49 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_10932 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (4/25 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/25 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_10933 h delta _ctx _hno a33 f1
  by_cases p2 : h 1 ≤ (6/47 : ℝ)
  swap
  · have f2 : -(h 1) < (-6/47 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_10934 h delta _ctx _hno a39 f2
  by_cases p3 : h 3 ≤ (4/33 : ℝ)
  swap
  · have f3 : -(h 3) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_10935 h delta _ctx _hno a35 f3
  by_cases p4 : h 4 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 4) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_10936 h delta _ctx _hno a29 a42 a46 f4
  apply _hno 156
  change (((2 : ℝ) * (delta)) ≤ (10/49 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (6/47 : ℝ)) ∧ (h 3 ≤ (4/33 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_10927 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a45 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10926 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a35 : h 2 ≤ (2/17 : ℝ))
    (a46 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a35 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10925 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a39 : h 1 ≤ (6/47 : ℝ))
    (a45 : -(h 1) < (-5/39 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a39 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10924 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a29 : -(h 1) < (-1/8 : ℝ))
    (a33 : h 0 ≤ (8/51 : ℝ))
    (a35 : h 2 ≤ (2/17 : ℝ))
    (a36 : -(h 3) < (-5/43 : ℝ))
    (a39 : h 1 ≤ (6/47 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    (a44 : -(h 0) < (-2/13 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_10927 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (7/45 : ℝ)
  swap
  · have f1 : -(h 0) < (-7/45 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_10928 h delta _ctx _hno a13 a29 a33 a35 a39 a42 f1
  by_cases p2 : h 1 ≤ (9/70 : ℝ)
  swap
  · have f2 : -(h 1) < (-9/70 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_10929 h delta _ctx _hno a39 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_10930 h delta _ctx _hno a35 f3
  by_cases p4 : h 4 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 4) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_10931 h delta _ctx _hno a13 a29 a35 a36 a42 a44 p1 f4
  apply _hno 111
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (7/45 : ℝ)) ∧ (h 1 ≤ (9/70 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (4/35 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_10923 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10922 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a36 : -(h 3) < (-5/43 : ℝ))
    (a39 : -(h 1) < (-6/47 : ℝ))
    (a47 : -(h 0) < (-2/13 : ℝ))
    (a57 : -(h 5) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.order4 + (6/29 : ℝ) * _ctx.lower + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a36 + (6/29 : ℝ) * a39 + (4/29 : ℝ) * a47 + (12/29 : ℝ) * a57 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10921 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a36 : -(h 3) < (-5/43 : ℝ))
    (a39 : -(h 1) < (-6/47 : ℝ))
    (a45 : -(h 5) < (-5/48 : ℝ))
    (a47 : -(h 0) < (-2/13 : ℝ))
    (a52 : -(h 4) < (-4/35 : ℝ))
    (a56 : -(h 2) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a36 + (1/6 : ℝ) * a39 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * a52 + (1/6 : ℝ) * a56 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10920 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a50 : h 1 ≤ (9/70 : ℝ))
    (a55 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a50 + (1 : ℝ) * a55
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10919 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a49 : h 0 ≤ (7/45 : ℝ))
    (a54 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a49 + (1 : ℝ) * a54
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10918 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a53 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a53
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10917 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a36 : -(h 3) < (-5/43 : ℝ))
    (a47 : -(h 0) < (-2/13 : ℝ))
    (a50 : -(h 1) < (-9/70 : ℝ))
    (a55 : -(h 5) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.order4 + (6/29 : ℝ) * _ctx.lower + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a36 + (4/29 : ℝ) * a47 + (6/29 : ℝ) * a50 + (12/29 : ℝ) * a55 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10916 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a35 : h 2 ≤ (2/17 : ℝ))
    (a54 : -(h 2) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a35 + (1 : ℝ) * a54
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10915 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a42 : h 1 ≤ (3/23 : ℝ))
    (a53 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a42 + (1 : ℝ) * a53
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10914 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a49 : h 0 ≤ (7/45 : ℝ))
    (a52 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a49 + (1 : ℝ) * a52
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10913 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a51 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a51
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10912 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a36 : -(h 3) < (-5/43 : ℝ))
    (a39 : -(h 1) < (-6/47 : ℝ))
    (a49 : -(h 0) < (-7/45 : ℝ))
    (a54 : -(h 5) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.order4 + (6/29 : ℝ) * _ctx.lower + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a36 + (6/29 : ℝ) * a39 + (4/29 : ℝ) * a49 + (12/29 : ℝ) * a54 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10911 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a35 : h 2 ≤ (2/17 : ℝ))
    (a53 : -(h 2) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a35 + (1 : ℝ) * a53
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10910 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a42 : h 1 ≤ (3/23 : ℝ))
    (a52 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a42 + (1 : ℝ) * a52
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10909 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a33 : h 0 ≤ (8/51 : ℝ))
    (a51 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a51
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10908 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a50 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10907 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a36 : -(h 3) < (-5/43 : ℝ))
    (a39 : -(h 1) < (-6/47 : ℝ))
    (a45 : -(h 5) < (-5/48 : ℝ))
    (a47 : -(h 0) < (-2/13 : ℝ))
    (a49 : h 0 ≤ (7/45 : ℝ))
    (a50 : h 1 ≤ (9/70 : ℝ))
    (a52 : -(h 4) < (-4/35 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_10918 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_10919 h delta _ctx _hno a49 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_10920 h delta _ctx _hno a50 f2
  by_cases p3 : h 2 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_10921 h delta _ctx _hno a36 a39 a45 a47 a52 f3
  by_cases p4 : h 5 ≤ (3/26 : ℝ)
  swap
  · have f4 : -(h 5) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_10922 h delta _ctx _hno a36 a39 a47 f4
  apply _hno 15
  change (((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (3/26 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_10906 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a35 : h 2 ≤ (2/17 : ℝ))
    (a51 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a35 + (1 : ℝ) * a51
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10905 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a35 : h 2 ≤ (2/17 : ℝ))
    (a36 : -(h 3) < (-5/43 : ℝ))
    (a42 : h 1 ≤ (3/23 : ℝ))
    (a47 : -(h 0) < (-2/13 : ℝ))
    (a49 : h 0 ≤ (7/45 : ℝ))
    (a50 : -(h 1) < (-9/70 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_10913 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_10914 h delta _ctx _hno a49 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_10915 h delta _ctx _hno a42 f2
  by_cases p3 : h 2 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_10916 h delta _ctx _hno a35 f3
  by_cases p4 : h 5 ≤ (3/26 : ℝ)
  swap
  · have f4 : -(h 5) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_10917 h delta _ctx _hno a36 a47 a50 f4
  apply _hno 15
  change (((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (3/26 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_10904 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a33 : h 0 ≤ (8/51 : ℝ))
    (a35 : h 2 ≤ (2/17 : ℝ))
    (a36 : -(h 3) < (-5/43 : ℝ))
    (a39 : -(h 1) < (-6/47 : ℝ))
    (a42 : h 1 ≤ (3/23 : ℝ))
    (a49 : -(h 0) < (-7/45 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_10908 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_10909 h delta _ctx _hno a33 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_10910 h delta _ctx _hno a42 f2
  by_cases p3 : h 2 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_10911 h delta _ctx _hno a35 f3
  by_cases p4 : h 5 ≤ (3/26 : ℝ)
  swap
  · have f4 : -(h 5) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_10912 h delta _ctx _hno a36 a39 a49 f4
  apply _hno 15
  change (((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (3/26 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_10903 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a48 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10902 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a35 : h 2 ≤ (2/17 : ℝ))
    (a49 : -(h 2) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a35 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10901 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a42 : h 1 ≤ (3/23 : ℝ))
    (a48 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a42 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10900 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a33 : h 0 ≤ (8/51 : ℝ))
    (a35 : h 2 ≤ (2/17 : ℝ))
    (a36 : -(h 3) < (-5/43 : ℝ))
    (a39 : -(h 1) < (-6/47 : ℝ))
    (a42 : h 1 ≤ (3/23 : ℝ))
    (a45 : -(h 5) < (-5/48 : ℝ))
    (a47 : -(h 0) < (-2/13 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_10903 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (7/45 : ℝ)
  swap
  · have f1 : -(h 0) < (-7/45 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_10904 h delta _ctx _hno a13 a33 a35 a36 a39 a42 f1
  by_cases p2 : h 1 ≤ (9/70 : ℝ)
  swap
  · have f2 : -(h 1) < (-9/70 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_10905 h delta _ctx _hno a13 a35 a36 a42 a47 p1 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_10906 h delta _ctx _hno a35 f3
  by_cases p4 : h 4 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 4) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_10907 h delta _ctx _hno a13 a36 a39 a45 a47 p1 p2 f4
  apply _hno 111
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (7/45 : ℝ)) ∧ (h 1 ≤ (9/70 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (4/35 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_10899 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a46 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10898 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a36 : -(h 3) < (-5/43 : ℝ))
    (a42 : -(h 1) < (-3/23 : ℝ))
    (a44 : -(h 0) < (-2/13 : ℝ))
    (a49 : -(h 5) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.order4 + (6/29 : ℝ) * _ctx.lower + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a36 + (6/29 : ℝ) * a42 + (4/29 : ℝ) * a44 + (12/29 : ℝ) * a49 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10897 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a35 : h 2 ≤ (2/17 : ℝ))
    (a48 : -(h 2) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a35 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10896 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : h 1 ≤ (2/15 : ℝ))
    (a47 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a24 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10895 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a33 : h 0 ≤ (8/51 : ℝ))
    (a46 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10894 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a45 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10893 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a35 : h 2 ≤ (2/17 : ℝ))
    (a46 : -(h 2) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a35 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10892 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : h 1 ≤ (2/15 : ℝ))
    (a45 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a24 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10891 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a24 : h 1 ≤ (2/15 : ℝ))
    (a33 : h 0 ≤ (8/51 : ℝ))
    (a35 : h 2 ≤ (2/17 : ℝ))
    (a36 : -(h 3) < (-5/43 : ℝ))
    (a42 : -(h 1) < (-3/23 : ℝ))
    (a44 : -(h 0) < (-2/13 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_10894 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_10895 h delta _ctx _hno a33 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_10896 h delta _ctx _hno a24 f2
  by_cases p3 : h 2 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_10897 h delta _ctx _hno a35 f3
  by_cases p4 : h 5 ≤ (3/26 : ℝ)
  swap
  · have f4 : -(h 5) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_10898 h delta _ctx _hno a36 a42 a44 f4
  apply _hno 15
  change (((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (3/26 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_10890 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10889 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a33 : h 0 ≤ (8/51 : ℝ))
    (a35 : h 2 ≤ (2/17 : ℝ))
    (a36 : -(h 3) < (-5/43 : ℝ))
    (a39 : -(h 1) < (-6/47 : ℝ))
    (a42 : h 1 ≤ (3/23 : ℝ))
    (a45 : -(h 5) < (-5/48 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_10899 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_10900 h delta _ctx _hno a13 a33 a35 a36 a39 a42 a45 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_10901 h delta _ctx _hno a42 f2
  by_cases p3 : h 2 ≤ (3/25 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_10902 h delta _ctx _hno a35 f3
  apply _hno 198
  change (((2 : ℝ) * (delta)) ≤ (8/39 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_10888 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a35 : h 2 ≤ (2/17 : ℝ))
    (a44 : -(h 4) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * _ctx.order2 + (1 : ℝ) * _ctx.order3 + (1 : ℝ) * a35 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10887 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a35 : h 2 ≤ (2/17 : ℝ))
    (a43 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * _ctx.order2 + (1 : ℝ) * a35 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10886 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a24 : h 1 ≤ (2/15 : ℝ))
    (a33 : h 0 ≤ (8/51 : ℝ))
    (a35 : h 2 ≤ (2/17 : ℝ))
    (a36 : -(h 3) < (-5/43 : ℝ))
    (a42 : -(h 1) < (-3/23 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_10890 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_10891 h delta _ctx _hno a13 a24 a33 a35 a36 a42 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_10892 h delta _ctx _hno a24 f2
  by_cases p3 : h 2 ≤ (3/25 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_10893 h delta _ctx _hno a35 f3
  apply _hno 198
  change (((2 : ℝ) * (delta)) ≤ (8/39 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_10885 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a33 : h 0 ≤ (8/51 : ℝ))
    (a41 : -(h 0) < (-5/31 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10884 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a40 : ((-2 : ℝ) * (delta)) < (-9/44 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10883 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a29 : -(h 1) < (-1/8 : ℝ))
    (a33 : h 0 ≤ (8/51 : ℝ))
    (a35 : h 2 ≤ (2/17 : ℝ))
    (a36 : -(h 3) < (-5/43 : ℝ))
    (a39 : h 1 ≤ (6/47 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_10923 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_10924 h delta _ctx _hno a13 a29 a33 a35 a36 a39 a42 f1
  by_cases p2 : h 1 ≤ (5/39 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/39 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_10925 h delta _ctx _hno a39 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_10926 h delta _ctx _hno a35 f3
  apply _hno 32
  change (((2 : ℝ) * (delta)) ≤ (8/39 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (5/39 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_10882 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a35 : h 2 ≤ (2/17 : ℝ))
    (a41 : -(h 4) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * _ctx.order2 + (1 : ℝ) * _ctx.order3 + (1 : ℝ) * a35 + (1 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10881 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a35 : h 2 ≤ (2/17 : ℝ))
    (a40 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a35 + (1 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10880 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a24 : h 1 ≤ (2/15 : ℝ))
    (a33 : h 0 ≤ (8/51 : ℝ))
    (a35 : h 2 ≤ (2/17 : ℝ))
    (a36 : -(h 3) < (-5/43 : ℝ))
    (a39 : -(h 1) < (-6/47 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (9/44 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-9/44 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_10884 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (5/31 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/31 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_10885 h delta _ctx _hno a33 f1
  by_cases p2 : h 1 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_10886 h delta _ctx _hno a13 a24 a33 a35 a36 f2
  by_cases p3 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_10887 h delta _ctx _hno a35 f3
  by_cases p4 : h 4 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 4) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_10888 h delta _ctx _hno a35 f4
  by_cases p5 : h 5 ≤ (5/48 : ℝ)
  swap
  · have f5 : -(h 5) < (-5/48 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_10889 h delta _ctx _hno a13 a33 a35 a36 a39 p2 f5
  apply _hno 155
  change (((2 : ℝ) * (delta)) ≤ (9/44 : ℝ)) ∧ (h 0 ≤ (5/31 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (5/48 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_10879 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a33 : h 0 ≤ (8/51 : ℝ))
    (a38 : -(h 0) < (-8/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a33 + (1 : ℝ) * a38
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10878 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a37 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a37
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10877 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a31 : -(h 0) < (-5/33 : ℝ))
    (a40 : -(h 4) < (-4/35 : ℝ))
    (a43 : -(h 1) < (-5/39 : ℝ))
    (a49 : -(h 5) < (-2/19 : ℝ))
    (a53 : -(h 2) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a31 + (1/3 : ℝ) * a40 + (1/6 : ℝ) * a43 + (1/6 : ℝ) * a49 + (1/6 : ℝ) * a53 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10876 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a38 : h 1 ≤ (9/70 : ℝ))
    (a52 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a38 + (1 : ℝ) * a52
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10875 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a35 : -(h 2) < (-2/17 : ℝ))
    (a40 : -(h 4) < (-4/35 : ℝ))
    (a43 : -(h 1) < (-5/39 : ℝ))
    (a49 : -(h 5) < (-2/19 : ℝ))
    (a51 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a35 + (1/3 : ℝ) * a40 + (1/6 : ℝ) * a43 + (1/6 : ℝ) * a49 + (1/6 : ℝ) * a51 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

end RealPinwheel.WeakSevenBandData
