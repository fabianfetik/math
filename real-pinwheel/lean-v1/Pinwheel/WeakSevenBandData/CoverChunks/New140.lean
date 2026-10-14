import Pinwheel.WeakSevenBandData.CoverChunks.New139

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem new_node_1914 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : h 0 ≤ (4/25 : ℝ))
    (a46 : -(h 0) < (-5/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1913 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a41 : ((2 : ℝ) * (delta)) ≤ (7/34 : ℝ))
    (a45 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a41 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1912 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a33 : -(h 1) < (-3/22 : ℝ))
    (a36 : -(h 0) < (-2/13 : ℝ))
    (a40 : -(h 2) < (-5/43 : ℝ))
    (a47 : -(h 5) < (-3/29 : ℝ))
    (a48 : ((-2 : ℝ) * (delta)) < (-13/63 : ℝ))
    (a54 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order3 + (2/13 : ℝ) * a33 + (2/13 : ℝ) * a36 + (2/13 : ℝ) * a40 + (2/13 : ℝ) * a47 + (1/13 : ℝ) * a48 + (4/13 : ℝ) * a54 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1911 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a30 : -(h 4) < (-3/28 : ℝ))
    (a33 : -(h 1) < (-3/22 : ℝ))
    (a36 : -(h 0) < (-2/13 : ℝ))
    (a40 : -(h 2) < (-5/43 : ℝ))
    (a47 : -(h 5) < (-3/29 : ℝ))
    (a48 : ((-2 : ℝ) * (delta)) < (-13/63 : ℝ))
    (a53 : -(h 3) < (-6/53 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * a30 + (2/13 : ℝ) * a33 + (2/13 : ℝ) * a36 + (2/13 : ℝ) * a40 + (2/13 : ℝ) * a47 + (1/13 : ℝ) * a48 + (2/13 : ℝ) * a53 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1910 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a30 : -(h 4) < (-3/28 : ℝ))
    (a33 : -(h 1) < (-3/22 : ℝ))
    (a36 : -(h 0) < (-2/13 : ℝ))
    (a47 : -(h 5) < (-3/29 : ℝ))
    (a48 : ((-2 : ℝ) * (delta)) < (-13/63 : ℝ))
    (a52 : -(h 2) < (-4/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * a17 + (2/13 : ℝ) * a30 + (2/13 : ℝ) * a33 + (2/13 : ℝ) * a36 + (2/13 : ℝ) * a47 + (1/13 : ℝ) * a48 + (2/13 : ℝ) * a52 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1909 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a44 : h 1 ≤ (4/29 : ℝ))
    (a51 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a44 + (1 : ℝ) * a51
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1908 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a30 : -(h 4) < (-3/28 : ℝ))
    (a33 : -(h 1) < (-3/22 : ℝ))
    (a40 : -(h 2) < (-5/43 : ℝ))
    (a47 : -(h 5) < (-3/29 : ℝ))
    (a48 : ((-2 : ℝ) * (delta)) < (-13/63 : ℝ))
    (a50 : -(h 0) < (-5/32 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * a17 + (2/13 : ℝ) * a30 + (2/13 : ℝ) * a33 + (2/13 : ℝ) * a40 + (2/13 : ℝ) * a47 + (1/13 : ℝ) * a48 + (2/13 : ℝ) * a50 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1907 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a42 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a49 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a42 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1906 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a33 : -(h 1) < (-3/22 : ℝ))
    (a36 : -(h 0) < (-2/13 : ℝ))
    (a40 : -(h 2) < (-5/43 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a47 : -(h 5) < (-3/29 : ℝ))
    (a53 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order3 + (2/13 : ℝ) * a33 + (2/13 : ℝ) * a36 + (2/13 : ℝ) * a40 + (1/13 : ℝ) * a41 + (2/13 : ℝ) * a47 + (4/13 : ℝ) * a53 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1905 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a46 : h 3 ≤ (4/35 : ℝ))
    (a52 : -(h 3) < (-7/61 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a46 + (1 : ℝ) * a52
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1904 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a30 : -(h 4) < (-3/28 : ℝ))
    (a33 : -(h 1) < (-3/22 : ℝ))
    (a36 : -(h 0) < (-2/13 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a47 : -(h 5) < (-3/29 : ℝ))
    (a51 : -(h 2) < (-22/185 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * a17 + (2/13 : ℝ) * a30 + (2/13 : ℝ) * a33 + (2/13 : ℝ) * a36 + (1/13 : ℝ) * a41 + (2/13 : ℝ) * a47 + (2/13 : ℝ) * a51 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1903 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a44 : h 1 ≤ (4/29 : ℝ))
    (a50 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a44 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1902 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : h 0 ≤ (4/25 : ℝ))
    (a49 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1901 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a30 : -(h 4) < (-3/28 : ℝ))
    (a33 : -(h 1) < (-3/22 : ℝ))
    (a36 : -(h 0) < (-2/13 : ℝ))
    (a40 : -(h 2) < (-5/43 : ℝ))
    (a42 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a44 : h 1 ≤ (4/29 : ℝ))
    (a47 : -(h 5) < (-3/29 : ℝ))
    (a48 : ((-2 : ℝ) * (delta)) < (-13/63 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_1907 h delta _ctx _hno a42 f0
  by_cases p1 : h 0 ≤ (5/32 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/32 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_1908 h delta _ctx _hno a17 a30 a33 a40 a47 a48 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_1909 h delta _ctx _hno a44 f2
  by_cases p3 : h 2 ≤ (4/33 : ℝ)
  swap
  · have f3 : -(h 2) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_1910 h delta _ctx _hno a17 a30 a33 a36 a47 a48 f3
  by_cases p4 : h 3 ≤ (6/53 : ℝ)
  swap
  · have f4 : -(h 3) < (-6/53 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_1911 h delta _ctx _hno a30 a33 a36 a40 a47 a48 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_1912 h delta _ctx _hno a33 a36 a40 a47 a48 f5
  apply _hno 222
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (5/32 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (4/33 : ℝ)) ∧ (h 3 ≤ (6/53 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_1900 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a36 : -(h 0) < (-2/13 : ℝ))
    (a40 : -(h 2) < (-5/43 : ℝ))
    (a44 : -(h 1) < (-4/29 : ℝ))
    (a45 : ((-2 : ℝ) * (delta)) < (-13/63 : ℝ))
    (a51 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a36 + (1/6 : ℝ) * a40 + (1/6 : ℝ) * a44 + (1/6 : ℝ) * a45 + (1/3 : ℝ) * a51 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1899 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a30 : -(h 4) < (-3/28 : ℝ))
    (a36 : -(h 0) < (-2/13 : ℝ))
    (a40 : -(h 2) < (-5/43 : ℝ))
    (a44 : -(h 1) < (-4/29 : ℝ))
    (a45 : ((-2 : ℝ) * (delta)) < (-13/63 : ℝ))
    (a50 : -(h 3) < (-6/53 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a36 + (1/6 : ℝ) * a40 + (1/6 : ℝ) * a44 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a50 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1898 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a30 : -(h 4) < (-3/28 : ℝ))
    (a36 : -(h 0) < (-2/13 : ℝ))
    (a44 : -(h 1) < (-4/29 : ℝ))
    (a45 : ((-2 : ℝ) * (delta)) < (-13/63 : ℝ))
    (a49 : -(h 2) < (-4/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a17 + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a36 + (1/6 : ℝ) * a44 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a49 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1897 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a48 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1896 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a30 : -(h 4) < (-3/28 : ℝ))
    (a40 : -(h 2) < (-5/43 : ℝ))
    (a44 : -(h 1) < (-4/29 : ℝ))
    (a45 : ((-2 : ℝ) * (delta)) < (-13/63 : ℝ))
    (a47 : -(h 0) < (-5/32 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a17 + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a40 + (1/6 : ℝ) * a44 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1895 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a42 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a46 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a42 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1894 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a36 : -(h 0) < (-2/13 : ℝ))
    (a40 : -(h 2) < (-5/43 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a44 : -(h 1) < (-4/29 : ℝ))
    (a50 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a36 + (1/6 : ℝ) * a40 + (1/6 : ℝ) * a41 + (1/6 : ℝ) * a44 + (1/3 : ℝ) * a50 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1893 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a30 : -(h 4) < (-3/28 : ℝ))
    (a36 : -(h 0) < (-2/13 : ℝ))
    (a40 : -(h 2) < (-5/43 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a44 : -(h 1) < (-4/29 : ℝ))
    (a49 : -(h 3) < (-7/61 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a36 + (1/6 : ℝ) * a40 + (1/6 : ℝ) * a41 + (1/6 : ℝ) * a44 + (1/6 : ℝ) * a49 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1892 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a30 : -(h 4) < (-3/28 : ℝ))
    (a36 : -(h 0) < (-2/13 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a44 : -(h 1) < (-4/29 : ℝ))
    (a48 : -(h 2) < (-22/185 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a17 + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a36 + (1/6 : ℝ) * a41 + (1/6 : ℝ) * a44 + (1/6 : ℝ) * a48 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1891 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a47 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1890 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : h 0 ≤ (4/25 : ℝ))
    (a46 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1889 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a30 : -(h 4) < (-3/28 : ℝ))
    (a36 : -(h 0) < (-2/13 : ℝ))
    (a40 : -(h 2) < (-5/43 : ℝ))
    (a42 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a44 : -(h 1) < (-4/29 : ℝ))
    (a45 : ((-2 : ℝ) * (delta)) < (-13/63 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_1895 h delta _ctx _hno a42 f0
  by_cases p1 : h 0 ≤ (5/32 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/32 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_1896 h delta _ctx _hno a17 a30 a40 a44 a45 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_1897 h delta _ctx _hno a16 f2
  by_cases p3 : h 2 ≤ (4/33 : ℝ)
  swap
  · have f3 : -(h 2) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_1898 h delta _ctx _hno a17 a30 a36 a44 a45 f3
  by_cases p4 : h 3 ≤ (6/53 : ℝ)
  swap
  · have f4 : -(h 3) < (-6/53 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_1899 h delta _ctx _hno a30 a36 a40 a44 a45 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_1900 h delta _ctx _hno a36 a40 a44 a45 f5
  apply _hno 222
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (5/32 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (4/33 : ℝ)) ∧ (h 3 ≤ (6/53 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_1888 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a33 : -(h 1) < (-3/22 : ℝ))
    (a36 : -(h 0) < (-2/13 : ℝ))
    (a40 : -(h 2) < (-5/43 : ℝ))
    (a42 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a48 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a36 + (1/6 : ℝ) * a40 + (1/6 : ℝ) * a42 + (1/3 : ℝ) * a48 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1887 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a30 : -(h 4) < (-3/28 : ℝ))
    (a33 : -(h 1) < (-3/22 : ℝ))
    (a36 : -(h 0) < (-2/13 : ℝ))
    (a40 : -(h 2) < (-5/43 : ℝ))
    (a42 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a47 : -(h 3) < (-6/53 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a36 + (1/6 : ℝ) * a40 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1886 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a30 : -(h 4) < (-3/28 : ℝ))
    (a33 : -(h 1) < (-3/22 : ℝ))
    (a36 : -(h 0) < (-2/13 : ℝ))
    (a42 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a46 : -(h 2) < (-4/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a17 + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a36 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a46 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1885 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a45 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1884 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a30 : -(h 4) < (-3/28 : ℝ))
    (a33 : -(h 1) < (-3/22 : ℝ))
    (a40 : -(h 2) < (-5/43 : ℝ))
    (a42 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    (a44 : -(h 0) < (-5/32 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a17 + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a40 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a44 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1883 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a43 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1882 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a27 : h 0 ≤ (4/25 : ℝ))
    (a30 : -(h 4) < (-3/28 : ℝ))
    (a33 : -(h 1) < (-3/22 : ℝ))
    (a36 : -(h 0) < (-2/13 : ℝ))
    (a40 : -(h 2) < (-5/43 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a42 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a44 : h 1 ≤ (4/29 : ℝ))
    (a46 : h 3 ≤ (4/35 : ℝ))
    (a47 : -(h 5) < (-3/29 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (13/63 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-13/63 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_1901 h delta _ctx _hno a17 a30 a33 a36 a40 a42 a44 a47 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_1902 h delta _ctx _hno a27 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_1903 h delta _ctx _hno a44 f2
  by_cases p3 : h 2 ≤ (22/185 : ℝ)
  swap
  · have f3 : -(h 2) < (-22/185 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_1904 h delta _ctx _hno a17 a30 a33 a36 a41 a47 f3
  by_cases p4 : h 3 ≤ (7/61 : ℝ)
  swap
  · have f4 : -(h 3) < (-7/61 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_1905 h delta _ctx _hno a46 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_1906 h delta _ctx _hno a33 a36 a40 a41 a47 f5
  apply _hno 207
  change (((2 : ℝ) * (delta)) ≤ (13/63 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (22/185 : ℝ)) ∧ (h 3 ≤ (7/61 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_1881 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a30 : -(h 4) < (-3/28 : ℝ))
    (a33 : -(h 1) < (-3/22 : ℝ))
    (a36 : -(h 0) < (-2/13 : ℝ))
    (a40 : -(h 2) < (-5/43 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a46 : -(h 3) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a36 + (1/6 : ℝ) * a40 + (1/6 : ℝ) * a41 + (1/6 : ℝ) * a46 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1880 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a30 : -(h 4) < (-3/28 : ℝ))
    (a33 : -(h 1) < (-3/22 : ℝ))
    (a36 : -(h 0) < (-2/13 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a45 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a17 + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a36 + (1/6 : ℝ) * a41 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1879 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a27 : h 0 ≤ (4/25 : ℝ))
    (a30 : -(h 4) < (-3/28 : ℝ))
    (a36 : -(h 0) < (-2/13 : ℝ))
    (a40 : -(h 2) < (-5/43 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a42 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a44 : -(h 1) < (-4/29 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (13/63 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-13/63 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_1889 h delta _ctx _hno a16 a17 a30 a36 a40 a42 a44 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_1890 h delta _ctx _hno a27 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_1891 h delta _ctx _hno a16 f2
  by_cases p3 : h 2 ≤ (22/185 : ℝ)
  swap
  · have f3 : -(h 2) < (-22/185 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_1892 h delta _ctx _hno a17 a30 a36 a41 a44 f3
  by_cases p4 : h 3 ≤ (7/61 : ℝ)
  swap
  · have f4 : -(h 3) < (-7/61 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_1893 h delta _ctx _hno a30 a36 a40 a41 a44 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_1894 h delta _ctx _hno a36 a40 a41 a44 f5
  apply _hno 207
  change (((2 : ℝ) * (delta)) ≤ (13/63 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (22/185 : ℝ)) ∧ (h 3 ≤ (7/61 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_1878 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : h 0 ≤ (4/25 : ℝ))
    (a43 : -(h 0) < (-5/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1877 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a30 : -(h 4) < (-3/28 : ℝ))
    (a33 : -(h 1) < (-3/22 : ℝ))
    (a36 : -(h 0) < (-2/13 : ℝ))
    (a40 : -(h 2) < (-5/43 : ℝ))
    (a42 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_1883 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (5/32 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/32 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_1884 h delta _ctx _hno a17 a30 a33 a40 a42 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_1885 h delta _ctx _hno a16 f2
  by_cases p3 : h 2 ≤ (4/33 : ℝ)
  swap
  · have f3 : -(h 2) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_1886 h delta _ctx _hno a17 a30 a33 a36 a42 f3
  by_cases p4 : h 3 ≤ (6/53 : ℝ)
  swap
  · have f4 : -(h 3) < (-6/53 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_1887 h delta _ctx _hno a30 a33 a36 a40 a42 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_1888 h delta _ctx _hno a33 a36 a40 a42 f5
  apply _hno 222
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (5/32 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (4/33 : ℝ)) ∧ (h 3 ≤ (6/53 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_1876 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a33 : -(h 1) < (-3/22 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ))
    (a36 : -(h 0) < (-2/13 : ℝ))
    (a40 : -(h 2) < (-5/43 : ℝ))
    (a46 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a34 + (1/6 : ℝ) * a36 + (1/6 : ℝ) * a40 + (1/3 : ℝ) * a46 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1875 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a30 : -(h 4) < (-3/28 : ℝ))
    (a33 : -(h 1) < (-3/22 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ))
    (a36 : -(h 0) < (-2/13 : ℝ))
    (a40 : -(h 2) < (-5/43 : ℝ))
    (a45 : -(h 3) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a34 + (1/6 : ℝ) * a36 + (1/6 : ℝ) * a40 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1874 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a27 : h 0 ≤ (4/25 : ℝ))
    (a30 : -(h 4) < (-3/28 : ℝ))
    (a33 : -(h 1) < (-3/22 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ))
    (a36 : -(h 0) < (-2/13 : ℝ))
    (a41 : ((2 : ℝ) * (delta)) ≤ (7/34 : ℝ))
    (a44 : -(h 2) < (-2/17 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_1913 h delta _ctx _hno a41 f0
  by_cases p1 : h 0 ≤ (5/29 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/29 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_1914 h delta _ctx _hno a27 f1
  by_cases p2 : h 1 ≤ (4/29 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/29 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_1915 h delta _ctx _hno a16 a17 a27 a30 a34 a36 a41 a44 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_1916 h delta _ctx _hno a17 a30 a33 a34 a36 f3
  by_cases p4 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_1917 h delta _ctx _hno a30 a33 a34 a36 a44 f4
  by_cases p5 : h 5 ≤ (3/29 : ℝ)
  swap
  · have f5 : -(h 5) < (-3/29 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_1918 h delta _ctx _hno a17 a27 a30 a33 a34 a36 a41 a44 p2 p4 f5
  apply _hno 89
  change (((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)) ∧ (h 0 ≤ (5/29 : ℝ)) ∧ (h 1 ≤ (4/29 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (3/29 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_1873 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a43 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1872 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : h 0 ≤ (4/25 : ℝ))
    (a42 : -(h 0) < (-4/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1871 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a27 : h 0 ≤ (4/25 : ℝ))
    (a30 : -(h 4) < (-3/28 : ℝ))
    (a33 : -(h 1) < (-3/22 : ℝ))
    (a36 : -(h 0) < (-2/13 : ℝ))
    (a40 : -(h 2) < (-5/43 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_1877 h delta _ctx _hno a16 a17 a30 a33 a36 a40 f0
  by_cases p1 : h 0 ≤ (5/29 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/29 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_1878 h delta _ctx _hno a27 f1
  by_cases p2 : h 1 ≤ (4/29 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/29 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_1879 h delta _ctx _hno a16 a17 a27 a30 a36 a40 a41 p0 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_1880 h delta _ctx _hno a17 a30 a33 a36 a41 f3
  by_cases p4 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_1881 h delta _ctx _hno a30 a33 a36 a40 a41 f4
  by_cases p5 : h 5 ≤ (3/29 : ℝ)
  swap
  · have f5 : -(h 5) < (-3/29 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_1882 h delta _ctx _hno a17 a27 a30 a33 a36 a40 a41 p0 p2 p4 f5
  apply _hno 89
  change (((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)) ∧ (h 0 ≤ (5/29 : ℝ)) ∧ (h 1 ≤ (4/29 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (3/29 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_1870 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : h 0 ≤ (4/25 : ℝ))
    (a33 : -(h 1) < (-3/22 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ))
    (a36 : -(h 0) < (-2/13 : ℝ))
    (a40 : h 2 ≤ (5/43 : ℝ))
    (a42 : -(h 4) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_1936 h delta _ctx _hno a33 a36 a42 f0
  by_cases p1 : h 0 ≤ (5/29 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/29 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_1937 h delta _ctx _hno a27 f1
  by_cases p2 : h 1 ≤ (4/29 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/29 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_1938 h delta _ctx _hno a34 a36 a42 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_1939 h delta _ctx _hno a40 f3
  by_cases p4 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_1940 h delta _ctx _hno a33 a34 a36 a42 f4
  by_cases p5 : h 5 ≤ (3/29 : ℝ)
  swap
  · have f5 : -(h 5) < (-3/29 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_1941 h delta _ctx _hno a33 a34 a36 a42 f5
  apply _hno 89
  change (((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)) ∧ (h 0 ≤ (5/29 : ℝ)) ∧ (h 1 ≤ (4/29 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (3/29 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_1869 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a30 : -(h 4) < (-3/28 : ℝ))
    (a33 : -(h 1) < (-3/22 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ))
    (a36 : -(h 0) < (-2/13 : ℝ))
    (a40 : h 2 ≤ (5/43 : ℝ))
    (a41 : -(h 3) < (-3/26 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_1931 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (5/32 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/32 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_1932 h delta _ctx _hno a30 a33 a34 a41 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_1933 h delta _ctx _hno a16 f2
  by_cases p3 : h 2 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_1934 h delta _ctx _hno a40 f3
  by_cases p4 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_1935 h delta _ctx _hno a33 a34 a36 a41 f4
  apply _hno 224
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (5/32 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_1868 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a27 : h 0 ≤ (4/25 : ℝ))
    (a30 : -(h 4) < (-3/28 : ℝ))
    (a33 : -(h 1) < (-3/22 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ))
    (a36 : -(h 0) < (-2/13 : ℝ))
    (a40 : -(h 2) < (-5/43 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_1871 h delta _ctx _hno a16 a17 a27 a30 a33 a36 a40 f0
  by_cases p1 : h 0 ≤ (4/23 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/23 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_1872 h delta _ctx _hno a27 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_1873 h delta _ctx _hno a16 f2
  by_cases p3 : h 2 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_1874 h delta _ctx _hno a16 a17 a27 a30 a33 a34 a36 p0 f3
  by_cases p4 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_1875 h delta _ctx _hno a30 a33 a34 a36 a40 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_1876 h delta _ctx _hno a33 a34 a36 a40 f5
  apply _hno 13
  change (((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)) ∧ (h 0 ≤ (4/23 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_1867 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a39 : -(h 1) < (-6/43 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1866 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : h 0 ≤ (4/25 : ℝ))
    (a38 : -(h 0) < (-4/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a38
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1865 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a37 : ((-2 : ℝ) * (delta)) < (-10/43 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a37
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1864 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a25 : -(h 0) < (-5/33 : ℝ))
    (a30 : -(h 4) < (-3/28 : ℝ))
    (a33 : -(h 1) < (-3/22 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ))
    (a36 : h 0 ≤ (2/13 : ℝ))
    (a39 : h 4 ≤ (6/55 : ℝ))
    (a40 : -(h 5) < (-3/28 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (10/43 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-10/43 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_2025 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (4/25 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/25 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_2026 h delta _ctx _hno a36 f1
  by_cases p2 : h 1 ≤ (6/43 : ℝ)
  swap
  · have f2 : -(h 1) < (-6/43 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_2027 h delta _ctx _hno a16 f2
  by_cases p3 : h 2 ≤ (5/43 : ℝ)
  swap
  · have f3 : -(h 2) < (-5/43 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_2028 h delta _ctx _hno a16 a17 a25 a30 a33 a34 a36 a39 a40
  by_cases p4 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_2029 h delta _ctx _hno a25 a30 a33 a34 a40 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_2030 h delta _ctx _hno a39 f5
  apply _hno 44
  change (((2 : ℝ) * (delta)) ≤ (10/43 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (6/43 : ℝ)) ∧ (h 2 ≤ (5/43 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_1863 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a25 : -(h 0) < (-5/33 : ℝ))
    (a29 : h 2 ≤ (1/8 : ℝ))
    (a33 : -(h 1) < (-3/22 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ))
    (a36 : h 0 ≤ (2/13 : ℝ))
    (a39 : -(h 4) < (-6/55 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (11/52 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-11/52 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_1942 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_1943 h delta _ctx _hno a36 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_1944 h delta _ctx _hno a16 f2
  by_cases p3 : h 2 ≤ (4/29 : ℝ)
  swap
  · have f3 : -(h 2) < (-4/29 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_1945 h delta _ctx _hno a29 f3
  by_cases p4 : h 3 ≤ (7/62 : ℝ)
  swap
  · have f4 : -(h 3) < (-7/62 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_1946 h delta _ctx _hno a16 a25 a33 a34 a36 a39 f4
  by_cases p5 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_1947 h delta _ctx _hno a16 a17 a25 a29 a33 a34 a36 a39 p4 f5
  apply _hno 174
  change (((2 : ℝ) * (delta)) ≤ (11/52 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (4/29 : ℝ)) ∧ (h 3 ≤ (7/62 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_1862 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a25 : -(h 0) < (-5/33 : ℝ))
    (a30 : -(h 4) < (-3/28 : ℝ))
    (a33 : -(h 1) < (-3/22 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ))
    (a38 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a17 + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a34 + (1/6 : ℝ) * a38 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1861 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a37 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a37
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1860 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a27 : h 0 ≤ (4/25 : ℝ))
    (a30 : -(h 4) < (-3/28 : ℝ))
    (a33 : -(h 1) < (-3/22 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ))
    (a36 : -(h 0) < (-2/13 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (10/43 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-10/43 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_1865 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (4/25 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/25 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_1866 h delta _ctx _hno a27 f1
  by_cases p2 : h 1 ≤ (6/43 : ℝ)
  swap
  · have f2 : -(h 1) < (-6/43 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_1867 h delta _ctx _hno a16 f2
  by_cases p3 : h 2 ≤ (5/43 : ℝ)
  swap
  · have f3 : -(h 2) < (-5/43 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_1868 h delta _ctx _hno a16 a17 a27 a30 a33 a34 a36 f3
  by_cases p4 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_1869 h delta _ctx _hno a16 a30 a33 a34 a36 p3 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_1870 h delta _ctx _hno a27 a33 a34 a36 p3 f5
  apply _hno 44
  change (((2 : ℝ) * (delta)) ≤ (10/43 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (6/43 : ℝ)) ∧ (h 2 ≤ (5/43 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_1859 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a35 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a35
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1858 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a25 : -(h 0) < (-5/33 : ℝ))
    (a29 : h 2 ≤ (1/8 : ℝ))
    (a30 : -(h 4) < (-3/28 : ℝ))
    (a33 : -(h 1) < (-3/22 : ℝ))
    (a34 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ))
    (a35 : h 0 ≤ (2/13 : ℝ))
    (a37 : -(h 2) < (-3/25 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_2139 h delta _ctx _hno a34 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_2140 h delta _ctx _hno a35 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_2141 h delta _ctx _hno a16 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_2142 h delta _ctx _hno a13 a17 a25 a30 a33 f3
  by_cases p4 : h 4 ≤ (6/55 : ℝ)
  swap
  · have f4 : -(h 4) < (-6/55 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_2143 h delta _ctx _hno a13 a16 a17 a25 a29 a33 a34 a35 a37 f4
  by_cases p5 : h 5 ≤ (3/28 : ℝ)
  swap
  · have f5 : -(h 5) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_2144 h delta _ctx _hno a13 a17 a25 a30 a33 a37 f5
  apply _hno 104
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (6/55 : ℝ)) ∧ (h 5 ≤ (3/28 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_1857 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a36 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a16 + (1 : ℝ) * a36
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1856 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a27 : h 0 ≤ (4/25 : ℝ))
    (a30 : -(h 4) < (-3/28 : ℝ))
    (a33 : -(h 1) < (-3/22 : ℝ))
    (a34 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (10/43 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-10/43 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_2049 h delta _ctx _hno a34 f0
  by_cases p1 : h 0 ≤ (4/25 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/25 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_2050 h delta _ctx _hno a27 f1
  by_cases p2 : h 1 ≤ (6/43 : ℝ)
  swap
  · have f2 : -(h 1) < (-6/43 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_2051 h delta _ctx _hno a16 f2
  by_cases p3 : h 2 ≤ (5/43 : ℝ)
  swap
  · have f3 : -(h 2) < (-5/43 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_2052 h delta _ctx _hno a13 a16 a17 a27 a30 a33 a34 a35 f3
  by_cases p4 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_2053 h delta _ctx _hno a13 a16 a27 a33 a34 a35 p3 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_2054 h delta _ctx _hno a13 a16 a27 a33 a34 a35 p3 f5
  apply _hno 44
  change (((2 : ℝ) * (delta)) ≤ (10/43 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (6/43 : ℝ)) ∧ (h 2 ≤ (5/43 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_1855 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a25 : -(h 0) < (-5/33 : ℝ))
    (a27 : h 0 ≤ (4/25 : ℝ))
    (a29 : h 2 ≤ (1/8 : ℝ))
    (a30 : -(h 4) < (-3/28 : ℝ))
    (a33 : -(h 1) < (-3/22 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_1859 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_1860 h delta _ctx _hno a16 a17 a27 a30 a33 a34 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_1861 h delta _ctx _hno a16 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_1862 h delta _ctx _hno a17 a25 a30 a33 a34 f3
  by_cases p4 : h 4 ≤ (6/55 : ℝ)
  swap
  · have f4 : -(h 4) < (-6/55 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_1863 h delta _ctx _hno a16 a17 a25 a29 a33 a34 p1 f4
  by_cases p5 : h 5 ≤ (3/28 : ℝ)
  swap
  · have f5 : -(h 5) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_1864 h delta _ctx _hno a16 a17 a25 a30 a33 a34 p1 p4 f5
  apply _hno 104
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (6/55 : ℝ)) ∧ (h 5 ≤ (3/28 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_1854 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a25 : -(h 0) < (-5/33 : ℝ))
    (a27 : h 0 ≤ (4/25 : ℝ))
    (a29 : h 2 ≤ (1/8 : ℝ))
    (a33 : h 1 ≤ (3/22 : ℝ))
    (a36 : -(h 4) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_2157 h delta _ctx _hno f0
  by_cases p1 : h 0 ≤ (8/51 : ℝ)
  swap
  · have f1 : -(h 0) < (-8/51 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_2158 h delta _ctx _hno a13 a17 a23 a27 a33 a36 f1
  by_cases p2 : h 1 ≤ (5/32 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/32 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_2159 h delta _ctx _hno a33 f2
  by_cases p3 : h 2 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_2160 h delta _ctx _hno a13 a17 a23 a25 a29 a33 a36 p1 f3
  by_cases p4 : h 3 ≤ (5/43 : ℝ)
  swap
  · have f4 : -(h 3) < (-5/43 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_2161 h delta _ctx _hno a13 a23 a25 a33 a36 p3 f4
  by_cases p5 : h 5 ≤ (3/26 : ℝ)
  swap
  · have f5 : -(h 5) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_2162 h delta _ctx _hno a13 a23 a25 f5
  apply _hno 226
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (8/51 : ℝ)) ∧ (h 1 ≤ (5/32 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 3 ≤ (5/43 : ℝ)) ∧ (h 5 ≤ (3/26 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_1853 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a25 : -(h 0) < (-5/33 : ℝ))
    (a30 : -(h 4) < (-3/28 : ℝ))
    (a35 : -(h 3) < (-7/57 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order2 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a23 + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a30 + (1/3 : ℝ) * a35 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1852 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a29 : h 2 ≤ (1/8 : ℝ))
    (a34 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a34
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1851 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a16 : h 1 ≤ (5/36 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a25 : -(h 0) < (-5/33 : ℝ))
    (a27 : h 0 ≤ (4/25 : ℝ))
    (a29 : h 2 ≤ (1/8 : ℝ))
    (a30 : -(h 4) < (-3/28 : ℝ))
    (a33 : -(h 1) < (-3/22 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_1855 h delta _ctx _hno a16 a17 a25 a27 a29 a30 a33 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_1856 h delta _ctx _hno a13 a16 a17 a27 a30 a33 p0 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_1857 h delta _ctx _hno a16 f2
  by_cases p3 : h 2 ≤ (3/25 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_1858 h delta _ctx _hno a13 a16 a17 a25 a29 a30 a33 p0 p1 f3
  apply _hno 198
  change (((2 : ℝ) * (delta)) ≤ (8/39 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_1850 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a27 : h 0 ≤ (4/25 : ℝ))
    (a32 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a27 + (1 : ℝ) * a32
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1849 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a31 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2 : ℝ) * _ctx.upper + (1 : ℝ) * a31
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1848 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a25 : -(h 0) < (-5/33 : ℝ))
    (a29 : -(h 2) < (-1/8 : ℝ))
    (a45 : -(h 5) < (-5/47 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order4 + (1/13 : ℝ) * a13 + (2/13 : ℝ) * a17 + (2/13 : ℝ) * a23 + (2/13 : ℝ) * a25 + (2/13 : ℝ) * a29 + (4/13 : ℝ) * a45 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1847 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a25 : -(h 0) < (-5/33 : ℝ))
    (a29 : -(h 2) < (-1/8 : ℝ))
    (a39 : -(h 5) < (-2/19 : ℝ))
    (a44 : -(h 3) < (-7/62 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order4 + (1/13 : ℝ) * a13 + (2/13 : ℝ) * a23 + (2/13 : ℝ) * a25 + (2/13 : ℝ) * a29 + (4/13 : ℝ) * a39 + (2/13 : ℝ) * a44 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1846 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a25 : -(h 0) < (-5/33 : ℝ))
    (a39 : -(h 5) < (-2/19 : ℝ))
    (a43 : -(h 2) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order4 + (1/13 : ℝ) * a13 + (2/13 : ℝ) * a17 + (2/13 : ℝ) * a23 + (2/13 : ℝ) * a25 + (4/13 : ℝ) * a39 + (2/13 : ℝ) * a43 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1845 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a32 : h 1 ≤ (4/29 : ℝ))
    (a42 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a32 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1844 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a17 : -(h 3) < (-1/9 : ℝ))
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a29 : -(h 2) < (-1/8 : ℝ))
    (a39 : -(h 5) < (-2/19 : ℝ))
    (a41 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order4 + (1/13 : ℝ) * a13 + (2/13 : ℝ) * a17 + (2/13 : ℝ) * a23 + (2/13 : ℝ) * a29 + (4/13 : ℝ) * a39 + (2/13 : ℝ) * a41 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1843 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a30 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a40 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1842 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a25 : -(h 0) < (-5/33 : ℝ))
    (a29 : -(h 2) < (-1/8 : ℝ))
    (a42 : -(h 3) < (-4/35 : ℝ))
    (a49 : -(h 5) < (-3/29 : ℝ))
    (a55 : -(h 4) < (-2/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/13 : ℝ) * a13 + (2/13 : ℝ) * a23 + (2/13 : ℝ) * a25 + (2/13 : ℝ) * a29 + (2/13 : ℝ) * a42 + (2/13 : ℝ) * a49 + (2/13 : ℝ) * a55 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1841 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a25 : -(h 0) < (-5/33 : ℝ))
    (a29 : -(h 2) < (-1/8 : ℝ))
    (a33 : -(h 4) < (-3/29 : ℝ))
    (a49 : -(h 5) < (-3/29 : ℝ))
    (a54 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/13 : ℝ) * a13 + (2/13 : ℝ) * a23 + (2/13 : ℝ) * a25 + (2/13 : ℝ) * a29 + (2/13 : ℝ) * a33 + (2/13 : ℝ) * a49 + (2/13 : ℝ) * a54 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1840 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a46 : h 2 ≤ (6/47 : ℝ))
    (a53 : -(h 2) < (-3/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a46 + (1 : ℝ) * a53
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1839 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a41 : h 1 ≤ (3/22 : ℝ))
    (a52 : -(h 1) < (-7/50 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a41 + (1 : ℝ) * a52
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1838 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a29 : -(h 2) < (-1/8 : ℝ))
    (a33 : -(h 4) < (-3/29 : ℝ))
    (a42 : -(h 3) < (-4/35 : ℝ))
    (a49 : -(h 5) < (-3/29 : ℝ))
    (a51 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/13 : ℝ) * a13 + (2/13 : ℝ) * a23 + (2/13 : ℝ) * a29 + (2/13 : ℝ) * a33 + (2/13 : ℝ) * a42 + (2/13 : ℝ) * a49 + (2/13 : ℝ) * a51 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1837 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a30 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a50 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a30 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1836 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a25 : -(h 0) < (-5/33 : ℝ))
    (a29 : -(h 2) < (-1/8 : ℝ))
    (a42 : -(h 3) < (-4/35 : ℝ))
    (a48 : -(h 4) < (-2/19 : ℝ))
    (a55 : -(h 5) < (-3/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/13 : ℝ) * a13 + (2/13 : ℝ) * a23 + (2/13 : ℝ) * a25 + (2/13 : ℝ) * a29 + (2/13 : ℝ) * a42 + (2/13 : ℝ) * a48 + (2/13 : ℝ) * a55 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_1835 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a23 : -(h 1) < (-2/15 : ℝ))
    (a25 : -(h 0) < (-5/33 : ℝ))
    (a29 : -(h 2) < (-1/8 : ℝ))
    (a42 : -(h 3) < (-4/35 : ℝ))
    (a54 : -(h 4) < (-3/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a23 + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a29 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a54 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

end RealPinwheel.WeakSevenBandData
