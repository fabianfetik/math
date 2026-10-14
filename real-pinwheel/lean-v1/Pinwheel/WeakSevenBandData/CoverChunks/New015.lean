import Pinwheel.WeakSevenBandData.CoverChunks.New014

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem new_node_11914 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a44 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11913 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a20 : -(h 0) < (-1/6 : ℝ))
    (a31 : -(h 3) < (-1/9 : ℝ))
    (a38 : -(h 1) < (-6/47 : ℝ))
    (a44 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.order4 + (6/29 : ℝ) * _ctx.lower + (1/29 : ℝ) * _ctx.fail1 + (4/29 : ℝ) * a20 + (6/29 : ℝ) * a31 + (6/29 : ℝ) * a38 + (12/29 : ℝ) * a44 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11912 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a20 : -(h 0) < (-1/6 : ℝ))
    (a30 : h 1 ≤ (7/54 : ℝ))
    (a34 : h 2 ≤ (2/17 : ℝ))
    (a35 : -(h 5) < (-6/59 : ℝ))
    (a37 : h 0 ≤ (8/47 : ℝ))
    (a38 : -(h 1) < (-6/47 : ℝ))
    (a43 : -(h 3) < (-4/35 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_11914 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (5/29 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/29 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_11915 h delta _ctx _hno a37 f1
  by_cases p2 : h 1 ≤ (4/29 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/29 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_11916 h delta _ctx _hno a30 f2
  by_cases p3 : h 4 ≤ (3/29 : ℝ)
  swap
  · have f3 : -(h 4) < (-3/29 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_11917 h delta _ctx _hno a17 a20 a30 a34 a35 a37 a38 a43 f3
  apply _hno 7
  change (((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)) ∧ (h 0 ≤ (5/29 : ℝ)) ∧ (h 1 ≤ (4/29 : ℝ)) ∧ (h 4 ≤ (3/29 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_11911 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : h 2 ≤ (2/17 : ℝ))
    (a42 : -(h 2) < (-3/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11910 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a30 : h 1 ≤ (7/54 : ℝ))
    (a41 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11909 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a37 : h 0 ≤ (8/47 : ℝ))
    (a40 : -(h 0) < (-6/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a37 + (1 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11908 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a39 : ((-2 : ℝ) * (delta)) < (-1/5 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11907 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : -(h 1) < (-5/41 : ℝ))
    (a27 : -(h 2) < (-1/9 : ℝ))
    (a31 : -(h 3) < (-1/9 : ℝ))
    (a41 : -(h 4) < (-7/64 : ℝ))
    (a49 : -(h 0) < (-4/23 : ℝ))
    (a54 : -(h 5) < (-3/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a23 + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a31 + (1/6 : ℝ) * a41 + (1/6 : ℝ) * a49 + (1/6 : ℝ) * a54 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11906 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : h 2 ≤ (2/17 : ℝ))
    (a53 : -(h 3) < (-5/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * _ctx.order2 + (1 : ℝ) * a34 + (1 : ℝ) * a53
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11905 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : -(h 2) < (-1/9 : ℝ))
    (a31 : -(h 3) < (-1/9 : ℝ))
    (a41 : -(h 4) < (-7/64 : ℝ))
    (a45 : -(h 5) < (-2/19 : ℝ))
    (a49 : -(h 0) < (-4/23 : ℝ))
    (a52 : -(h 1) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a31 + (1/6 : ℝ) * a41 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a49 + (1/6 : ℝ) * a52 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11904 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a43 : h 0 ≤ (3/17 : ℝ))
    (a51 : -(h 0) < (-5/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a43 + (1 : ℝ) * a51
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11903 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a50 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11902 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : -(h 1) < (-5/41 : ℝ))
    (a27 : -(h 2) < (-1/9 : ℝ))
    (a31 : -(h 3) < (-1/9 : ℝ))
    (a47 : -(h 0) < (-6/35 : ℝ))
    (a52 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order4 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a23 + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a31 + (1/6 : ℝ) * a47 + (1/3 : ℝ) * a52 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11901 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : -(h 1) < (-5/41 : ℝ))
    (a45 : -(h 5) < (-2/19 : ℝ))
    (a47 : -(h 0) < (-6/35 : ℝ))
    (a51 : -(h 4) < (-9/80 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order2 + (1/3 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a23 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a47 + (1/2 : ℝ) * a51 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11900 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a40 : h 1 ≤ (1/8 : ℝ))
    (a50 : -(h 1) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a40 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11899 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a23 : -(h 1) < (-5/41 : ℝ))
    (a27 : -(h 2) < (-1/9 : ℝ))
    (a31 : -(h 3) < (-1/9 : ℝ))
    (a34 : h 2 ≤ (2/17 : ℝ))
    (a41 : -(h 4) < (-7/64 : ℝ))
    (a43 : h 0 ≤ (3/17 : ℝ))
    (a45 : -(h 5) < (-2/19 : ℝ))
    (a49 : -(h 0) < (-4/23 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_11903 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (5/28 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/28 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_11904 h delta _ctx _hno a43 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_11905 h delta _ctx _hno a27 a31 a41 a45 a49 f2
  by_cases p3 : h 3 ≤ (5/41 : ℝ)
  swap
  · have f3 : -(h 3) < (-5/41 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_11906 h delta _ctx _hno a34 f3
  by_cases p4 : h 5 ≤ (3/28 : ℝ)
  swap
  · have f4 : -(h 5) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_11907 h delta _ctx _hno a23 a27 a31 a41 a49 f4
  apply _hno 85
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (5/28 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (5/41 : ℝ)) ∧ (h 5 ≤ (3/28 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_11898 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a48 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11897 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : -(h 1) < (-5/41 : ℝ))
    (a27 : -(h 2) < (-1/9 : ℝ))
    (a31 : -(h 3) < (-1/9 : ℝ))
    (a37 : -(h 0) < (-8/47 : ℝ))
    (a51 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order4 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a23 + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a31 + (1/6 : ℝ) * a37 + (1/3 : ℝ) * a51 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11896 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : -(h 1) < (-5/41 : ℝ))
    (a37 : -(h 0) < (-8/47 : ℝ))
    (a41 : -(h 4) < (-7/64 : ℝ))
    (a45 : -(h 5) < (-2/19 : ℝ))
    (a50 : -(h 3) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order2 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a23 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a41 + (1/6 : ℝ) * a45 + (1/3 : ℝ) * a50 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11895 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : h 2 ≤ (2/17 : ℝ))
    (a49 : -(h 2) < (-3/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11894 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a40 : h 1 ≤ (1/8 : ℝ))
    (a48 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a40 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11893 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a23 : -(h 1) < (-5/41 : ℝ))
    (a27 : -(h 2) < (-1/9 : ℝ))
    (a31 : -(h 3) < (-1/9 : ℝ))
    (a34 : h 2 ≤ (2/17 : ℝ))
    (a40 : h 1 ≤ (1/8 : ℝ))
    (a41 : -(h 4) < (-7/64 : ℝ))
    (a43 : h 0 ≤ (3/17 : ℝ))
    (a45 : -(h 5) < (-2/19 : ℝ))
    (a47 : -(h 0) < (-6/35 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_11898 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (4/23 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/23 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_11899 h delta _ctx _hno a17 a23 a27 a31 a34 a41 a43 a45 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_11900 h delta _ctx _hno a40 f2
  by_cases p3 : h 4 ≤ (9/80 : ℝ)
  swap
  · have f3 : -(h 4) < (-9/80 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_11901 h delta _ctx _hno a23 a45 a47 f3
  by_cases p4 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_11902 h delta _ctx _hno a23 a27 a31 a47 f4
  apply _hno 137
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (4/23 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (9/80 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_11892 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a46 : ((-2 : ℝ) * (delta)) < (-1/5 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11891 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : -(h 1) < (-5/41 : ℝ))
    (a27 : -(h 2) < (-1/9 : ℝ))
    (a31 : -(h 3) < (-1/9 : ℝ))
    (a41 : -(h 4) < (-7/64 : ℝ))
    (a43 : -(h 0) < (-3/17 : ℝ))
    (a48 : -(h 5) < (-3/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a23 + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a31 + (1/6 : ℝ) * a41 + (1/6 : ℝ) * a43 + (1/6 : ℝ) * a48 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11890 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : h 2 ≤ (2/17 : ℝ))
    (a47 : -(h 3) < (-5/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * _ctx.order2 + (1 : ℝ) * a34 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11889 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : -(h 2) < (-1/9 : ℝ))
    (a31 : -(h 3) < (-1/9 : ℝ))
    (a35 : -(h 5) < (-6/59 : ℝ))
    (a41 : -(h 4) < (-7/64 : ℝ))
    (a43 : -(h 0) < (-3/17 : ℝ))
    (a46 : -(h 1) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a31 + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a41 + (1/6 : ℝ) * a43 + (1/6 : ℝ) * a46 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11888 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a23 : -(h 1) < (-5/41 : ℝ))
    (a27 : -(h 2) < (-1/9 : ℝ))
    (a31 : -(h 3) < (-1/9 : ℝ))
    (a35 : -(h 5) < (-6/59 : ℝ))
    (a41 : -(h 4) < (-7/64 : ℝ))
    (a45 : -(h 0) < (-5/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a23 + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a31 + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a41 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11887 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a44 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11886 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a23 : -(h 1) < (-5/41 : ℝ))
    (a27 : -(h 2) < (-1/9 : ℝ))
    (a31 : -(h 3) < (-1/9 : ℝ))
    (a34 : h 2 ≤ (2/17 : ℝ))
    (a37 : -(h 0) < (-8/47 : ℝ))
    (a40 : h 1 ≤ (1/8 : ℝ))
    (a41 : -(h 4) < (-7/64 : ℝ))
    (a43 : h 0 ≤ (3/17 : ℝ))
    (a45 : -(h 5) < (-2/19 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-1/5 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_11892 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (6/35 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/35 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_11893 h delta _ctx _hno a17 a23 a27 a31 a34 a40 a41 a43 a45 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_11894 h delta _ctx _hno a40 f2
  by_cases p3 : h 2 ≤ (3/22 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_11895 h delta _ctx _hno a34 f3
  by_cases p4 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_11896 h delta _ctx _hno a23 a37 a41 a45 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_11897 h delta _ctx _hno a23 a27 a31 a37 f5
  apply _hno 17
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 0 ≤ (6/35 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (3/22 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_11885 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a40 : h 1 ≤ (1/8 : ℝ))
    (a44 : -(h 1) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a40 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11884 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a23 : -(h 1) < (-5/41 : ℝ))
    (a27 : -(h 2) < (-1/9 : ℝ))
    (a31 : -(h 3) < (-1/9 : ℝ))
    (a34 : h 2 ≤ (2/17 : ℝ))
    (a35 : -(h 5) < (-6/59 : ℝ))
    (a41 : -(h 4) < (-7/64 : ℝ))
    (a43 : -(h 0) < (-3/17 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_11887 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (5/28 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/28 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_11888 h delta _ctx _hno a23 a27 a31 a35 a41 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_11889 h delta _ctx _hno a27 a31 a35 a41 a43 f2
  by_cases p3 : h 3 ≤ (5/41 : ℝ)
  swap
  · have f3 : -(h 3) < (-5/41 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_11890 h delta _ctx _hno a34 f3
  by_cases p4 : h 5 ≤ (3/28 : ℝ)
  swap
  · have f4 : -(h 5) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_11891 h delta _ctx _hno a23 a27 a31 a41 a43 f4
  apply _hno 85
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (5/28 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (5/41 : ℝ)) ∧ (h 5 ≤ (3/28 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_11883 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a42 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11882 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : -(h 2) < (-1/9 : ℝ))
    (a31 : -(h 3) < (-1/9 : ℝ))
    (a40 : -(h 1) < (-1/8 : ℝ))
    (a45 : -(h 4) < (-1/9 : ℝ))
    (a47 : -(h 0) < (-6/35 : ℝ))
    (a54 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a31 + (1/6 : ℝ) * a40 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * a54 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11881 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a35 : -(h 5) < (-6/59 : ℝ))
    (a40 : -(h 1) < (-1/8 : ℝ))
    (a47 : -(h 0) < (-6/35 : ℝ))
    (a53 : -(h 4) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order2 + (1/3 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a40 + (1/6 : ℝ) * a47 + (1/2 : ℝ) * a53 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11880 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a44 : h 2 ≤ (5/44 : ℝ))
    (a52 : -(h 3) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * _ctx.order2 + (1 : ℝ) * a44 + (1 : ℝ) * a52
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11879 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a44 : h 2 ≤ (5/44 : ℝ))
    (a51 : -(h 2) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a44 + (1 : ℝ) * a51
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11878 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a30 : h 1 ≤ (7/54 : ℝ))
    (a50 : -(h 1) < (-5/37 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11877 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : -(h 2) < (-1/9 : ℝ))
    (a31 : -(h 3) < (-1/9 : ℝ))
    (a35 : -(h 5) < (-6/59 : ℝ))
    (a40 : -(h 1) < (-1/8 : ℝ))
    (a45 : -(h 4) < (-1/9 : ℝ))
    (a49 : -(h 0) < (-4/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a27 + (1/6 : ℝ) * a31 + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a40 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a49 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11876 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a48 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11875 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a31 : -(h 3) < (-1/9 : ℝ))
    (a37 : -(h 0) < (-8/47 : ℝ))
    (a40 : -(h 1) < (-1/8 : ℝ))
    (a45 : -(h 4) < (-1/9 : ℝ))
    (a51 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.lower + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a31 + (4/29 : ℝ) * a37 + (6/29 : ℝ) * a40 + (6/29 : ℝ) * a45 + (6/29 : ℝ) * a51 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11874 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a44 : h 2 ≤ (5/44 : ℝ))
    (a50 : -(h 3) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * _ctx.order2 + (1 : ℝ) * a44 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11873 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a44 : h 2 ≤ (5/44 : ℝ))
    (a49 : -(h 2) < (-3/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a44 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11872 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a30 : h 1 ≤ (7/54 : ℝ))
    (a48 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11871 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a27 : -(h 2) < (-1/9 : ℝ))
    (a30 : h 1 ≤ (7/54 : ℝ))
    (a31 : -(h 3) < (-1/9 : ℝ))
    (a35 : -(h 5) < (-6/59 : ℝ))
    (a40 : -(h 1) < (-1/8 : ℝ))
    (a44 : h 2 ≤ (5/44 : ℝ))
    (a45 : -(h 4) < (-1/9 : ℝ))
    (a47 : -(h 0) < (-6/35 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_11876 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (4/23 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/23 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_11877 h delta _ctx _hno a27 a31 a35 a40 a45 f1
  by_cases p2 : h 1 ≤ (5/37 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/37 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_11878 h delta _ctx _hno a30 f2
  by_cases p3 : h 2 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_11879 h delta _ctx _hno a44 f3
  by_cases p4 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_11880 h delta _ctx _hno a44 f4
  by_cases p5 : h 4 ≤ (4/35 : ℝ)
  swap
  · have f5 : -(h 4) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_11881 h delta _ctx _hno a35 a40 a47 f5
  by_cases p6 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f6 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact new_node_11882 h delta _ctx _hno a27 a31 a40 a45 a47 f6
  apply _hno 67
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (4/23 : ℝ)) ∧ (h 1 ≤ (5/37 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 4 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem new_node_11870 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a46 : ((-2 : ℝ) * (delta)) < (-1/5 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11869 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a31 : -(h 3) < (-1/9 : ℝ))
    (a37 : -(h 0) < (-8/47 : ℝ))
    (a40 : -(h 1) < (-1/8 : ℝ))
    (a44 : -(h 2) < (-5/44 : ℝ))
    (a54 : -(h 4) < (-1/9 : ℝ))
    (a60 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a31 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a40 + (1/6 : ℝ) * a44 + (1/6 : ℝ) * a54 + (1/6 : ℝ) * a60 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11868 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a35 : -(h 5) < (-6/59 : ℝ))
    (a37 : -(h 0) < (-8/47 : ℝ))
    (a40 : -(h 1) < (-1/8 : ℝ))
    (a54 : -(h 4) < (-1/9 : ℝ))
    (a59 : -(h 3) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order2 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a40 + (1/6 : ℝ) * a54 + (1/3 : ℝ) * a59 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11867 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : h 2 ≤ (2/17 : ℝ))
    (a58 : -(h 2) < (-3/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a58
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11866 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a30 : h 1 ≤ (7/54 : ℝ))
    (a57 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a57
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11865 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a31 : -(h 3) < (-1/9 : ℝ))
    (a35 : -(h 5) < (-6/59 : ℝ))
    (a40 : -(h 1) < (-1/8 : ℝ))
    (a44 : -(h 2) < (-5/44 : ℝ))
    (a54 : -(h 4) < (-1/9 : ℝ))
    (a56 : -(h 0) < (-6/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a31 + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a40 + (1/6 : ℝ) * a44 + (1/6 : ℝ) * a54 + (1/6 : ℝ) * a56 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11864 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a55 : ((-2 : ℝ) * (delta)) < (-1/5 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a55
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11863 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a59 : h 4 ≤ (2/19 : ℝ))
    (a65 : -(h 4) < (-3/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a59 + (1 : ℝ) * a65
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11862 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a37 : -(h 0) < (-8/47 : ℝ))
    (a40 : -(h 1) < (-1/8 : ℝ))
    (a48 : -(h 4) < (-3/29 : ℝ))
    (a53 : -(h 3) < (-3/26 : ℝ))
    (a60 : -(h 5) < (-3/29 : ℝ))
    (a64 : -(h 2) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a40 + (1/6 : ℝ) * a48 + (1/6 : ℝ) * a53 + (1/6 : ℝ) * a60 + (1/6 : ℝ) * a64 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11861 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a30 : h 1 ≤ (7/54 : ℝ))
    (a63 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a63
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11860 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a46 : h 0 ≤ (5/29 : ℝ))
    (a62 : -(h 0) < (-5/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a46 + (1 : ℝ) * a62
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11859 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a61 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a61
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11858 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a35 : -(h 5) < (-6/59 : ℝ))
    (a37 : -(h 0) < (-8/47 : ℝ))
    (a40 : -(h 1) < (-1/8 : ℝ))
    (a53 : -(h 3) < (-3/26 : ℝ))
    (a64 : -(h 4) < (-3/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order2 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a40 + (1/3 : ℝ) * a53 + (1/6 : ℝ) * a64 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11857 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a35 : -(h 5) < (-6/59 : ℝ))
    (a37 : -(h 0) < (-8/47 : ℝ))
    (a40 : -(h 1) < (-1/8 : ℝ))
    (a53 : -(h 3) < (-3/26 : ℝ))
    (a59 : -(h 4) < (-2/19 : ℝ))
    (a63 : -(h 2) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a40 + (1/6 : ℝ) * a53 + (1/6 : ℝ) * a59 + (1/6 : ℝ) * a63 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11856 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a30 : h 1 ≤ (7/54 : ℝ))
    (a62 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a62
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11855 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a46 : h 0 ≤ (5/29 : ℝ))
    (a61 : -(h 0) < (-5/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a46 + (1 : ℝ) * a61
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11854 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a60 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a60
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11853 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a30 : h 1 ≤ (7/54 : ℝ))
    (a37 : -(h 0) < (-8/47 : ℝ))
    (a40 : -(h 1) < (-1/8 : ℝ))
    (a46 : h 0 ≤ (5/29 : ℝ))
    (a48 : -(h 4) < (-3/29 : ℝ))
    (a53 : -(h 3) < (-3/26 : ℝ))
    (a59 : h 4 ≤ (2/19 : ℝ))
    (a60 : -(h 5) < (-3/29 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_11859 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (5/28 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/28 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_11860 h delta _ctx _hno a46 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_11861 h delta _ctx _hno a30 f2
  by_cases p3 : h 2 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_11862 h delta _ctx _hno a37 a40 a48 a53 a60 f3
  by_cases p4 : h 4 ≤ (3/28 : ℝ)
  swap
  · have f4 : -(h 4) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_11863 h delta _ctx _hno a59 f4
  apply _hno 83
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (5/28 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (3/28 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_11852 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a30 : h 1 ≤ (7/54 : ℝ))
    (a35 : -(h 5) < (-6/59 : ℝ))
    (a37 : -(h 0) < (-8/47 : ℝ))
    (a40 : -(h 1) < (-1/8 : ℝ))
    (a46 : h 0 ≤ (5/29 : ℝ))
    (a53 : -(h 3) < (-3/26 : ℝ))
    (a59 : -(h 4) < (-2/19 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_11854 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (5/28 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/28 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_11855 h delta _ctx _hno a46 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_11856 h delta _ctx _hno a30 f2
  by_cases p3 : h 2 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_11857 h delta _ctx _hno a35 a37 a40 a53 a59 f3
  by_cases p4 : h 4 ≤ (3/28 : ℝ)
  swap
  · have f4 : -(h 4) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_11858 h delta _ctx _hno a35 a37 a40 a53 f4
  apply _hno 83
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (5/28 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (3/28 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_11851 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : h 2 ≤ (2/17 : ℝ))
    (a58 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * _ctx.order2 + (1 : ℝ) * a34 + (1 : ℝ) * a58
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11850 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : h 2 ≤ (2/17 : ℝ))
    (a57 : -(h 2) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a57
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11849 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a30 : h 1 ≤ (7/54 : ℝ))
    (a56 : -(h 1) < (-5/38 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a56
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11848 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a46 : h 0 ≤ (5/29 : ℝ))
    (a55 : -(h 0) < (-2/11 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a46 + (1 : ℝ) * a55
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11847 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a54 : ((-2 : ℝ) * (delta)) < (-1/5 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a54
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11846 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a30 : h 1 ≤ (7/54 : ℝ))
    (a31 : -(h 3) < (-1/9 : ℝ))
    (a34 : h 2 ≤ (2/17 : ℝ))
    (a35 : -(h 5) < (-6/59 : ℝ))
    (a37 : -(h 0) < (-8/47 : ℝ))
    (a40 : -(h 1) < (-1/8 : ℝ))
    (a44 : -(h 2) < (-5/44 : ℝ))
    (a54 : -(h 4) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-1/5 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_11864 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (6/35 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/35 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_11865 h delta _ctx _hno a31 a35 a40 a44 a54 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_11866 h delta _ctx _hno a30 f2
  by_cases p3 : h 2 ≤ (3/22 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_11867 h delta _ctx _hno a34 f3
  by_cases p4 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_11868 h delta _ctx _hno a35 a37 a40 a54 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_11869 h delta _ctx _hno a31 a37 a40 a44 a54 f5
  apply _hno 17
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 0 ≤ (6/35 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (3/22 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_11845 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a30 : h 1 ≤ (7/54 : ℝ))
    (a34 : h 2 ≤ (2/17 : ℝ))
    (a35 : -(h 5) < (-6/59 : ℝ))
    (a37 : -(h 0) < (-8/47 : ℝ))
    (a40 : -(h 1) < (-1/8 : ℝ))
    (a46 : h 0 ≤ (5/29 : ℝ))
    (a48 : -(h 4) < (-3/29 : ℝ))
    (a53 : -(h 3) < (-3/26 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-1/5 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_11847 h delta _ctx _hno a17 f0
  by_cases p1 : h 0 ≤ (2/11 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/11 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_11848 h delta _ctx _hno a46 f1
  by_cases p2 : h 1 ≤ (5/38 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/38 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_11849 h delta _ctx _hno a30 f2
  by_cases p3 : h 2 ≤ (3/23 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_11850 h delta _ctx _hno a34 f3
  by_cases p4 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_11851 h delta _ctx _hno a34 f4
  by_cases p5 : h 4 ≤ (2/19 : ℝ)
  swap
  · have f5 : -(h 4) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_11852 h delta _ctx _hno a17 a30 a35 a37 a40 a46 a53 f5
  by_cases p6 : h 5 ≤ (3/29 : ℝ)
  swap
  · have f6 : -(h 5) < (-3/29 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact new_node_11853 h delta _ctx _hno a17 a30 a37 a40 a46 a48 a53 p5 f6
  apply _hno 27
  change (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 0 ≤ (2/11 : ℝ)) ∧ (h 1 ≤ (5/38 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (2/19 : ℝ)) ∧ (h 5 ≤ (3/29 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem new_node_11844 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : h 2 ≤ (2/17 : ℝ))
    (a52 : -(h 2) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a52
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11843 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a30 : h 1 ≤ (7/54 : ℝ))
    (a51 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a51
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11842 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a46 : h 0 ≤ (5/29 : ℝ))
    (a50 : -(h 0) < (-4/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a46 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11841 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ))
    (a49 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a17 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11840 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a40 : -(h 1) < (-1/8 : ℝ))
    (a46 : -(h 0) < (-5/29 : ℝ))
    (a51 : -(h 3) < (-3/26 : ℝ))
    (a58 : -(h 5) < (-3/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order2 + (1/6 : ℝ) * _ctx.order4 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a40 + (1/6 : ℝ) * a46 + (1/3 : ℝ) * a51 + (1/3 : ℝ) * a58 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11839 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a35 : -(h 5) < (-6/59 : ℝ))
    (a40 : -(h 1) < (-1/8 : ℝ))
    (a46 : -(h 0) < (-5/29 : ℝ))
    (a51 : -(h 3) < (-3/26 : ℝ))
    (a57 : -(h 4) < (-2/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order2 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a40 + (1/6 : ℝ) * a46 + (1/3 : ℝ) * a51 + (1/6 : ℝ) * a57 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11838 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : h 2 ≤ (2/17 : ℝ))
    (a56 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * _ctx.order2 + (1 : ℝ) * a34 + (1 : ℝ) * a56
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11837 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : h 2 ≤ (2/17 : ℝ))
    (a55 : -(h 2) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a55
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11836 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a30 : h 1 ≤ (7/54 : ℝ))
    (a54 : -(h 1) < (-5/38 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a54
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_11835 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a48 : h 0 ≤ (4/23 : ℝ))
    (a53 : -(h 0) < (-2/11 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a48 + (1 : ℝ) * a53
  exact (lt_irrefl (0 : ℝ)) hbad

end RealPinwheel.WeakSevenBandData
