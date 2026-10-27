import Pinwheel.WeakSevenBandData.CoverChunks.Upper029

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem upper_node_1907 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a29 : h 0 ≤ (5/33 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a36 : h 1 ≤ (2/15 : ℝ))
    (a37 : -(h 3) < (-3/26 : ℝ))
    (a44 : -(h 2) < (-2/17 : ℝ))
    (a47 : -(h 1) < (-3/23 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1908 h delta _ctx _hno a20 a33 a37 a44 a47 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1909 h delta _ctx _hno a29 f1
  by_cases p2 : h 1 ≤ (3/22 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1910 h delta _ctx _hno a36 f2
  by_cases p3 : h 2 ≤ (9/76 : ℝ)
  swap
  · have f3 : -(h 2) < (-9/76 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1911 h delta _ctx _hno a20 a33 a37 a47 f3
  by_cases p4 : h 3 ≤ (5/43 : ℝ)
  swap
  · have f4 : -(h 3) < (-5/43 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1919 h delta _ctx _hno a20 a33 a44 a47 p3 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1927 h delta _ctx _hno a20 a33 a37 a47 f5
  apply _hno 121
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 2 ≤ (9/76 : ℝ)) ∧ (h 3 ≤ (5/43 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_1906 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : h 0 ≤ (5/33 : ℝ))
    (a46 : -(h 0) < (-3/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1905 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a40 : -(h 1) < (-9/70 : ℝ))
    (a44 : -(h 2) < (-2/17 : ℝ))
    (a45 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a51 : -(h 4) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (12/61 : ℝ) * _ctx.order3 + (10/61 : ℝ) * _ctx.min + (2/61 : ℝ) * a20 + (12/61 : ℝ) * a40 + (12/61 : ℝ) * a44 + (11/61 : ℝ) * a45 + (24/61 : ℝ) * a51 + (12/61 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1904 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a40 : -(h 1) < (-9/70 : ℝ))
    (a44 : -(h 2) < (-2/17 : ℝ))
    (a45 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a50 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (10/61 : ℝ) * _ctx.min + (2/61 : ℝ) * a20 + (12/61 : ℝ) * a33 + (12/61 : ℝ) * a40 + (12/61 : ℝ) * a44 + (11/61 : ℝ) * a45 + (12/61 : ℝ) * a50 + (12/61 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1903 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a37 : -(h 3) < (-3/26 : ℝ))
    (a40 : -(h 1) < (-9/70 : ℝ))
    (a45 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a49 : -(h 2) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (10/61 : ℝ) * _ctx.min + (2/61 : ℝ) * a20 + (12/61 : ℝ) * a33 + (12/61 : ℝ) * a37 + (12/61 : ℝ) * a40 + (11/61 : ℝ) * a45 + (12/61 : ℝ) * a49 + (12/61 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1902 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a37 : -(h 3) < (-3/26 : ℝ))
    (a45 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a48 : -(h 1) < (-4/31 : ℝ))
    (a54 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/28 : ℝ) * _ctx.fail1 + (1/42 : ℝ) * a20 + (3/14 : ℝ) * a33 + (3/14 : ℝ) * a37 + (3/28 : ℝ) * a45 + (3/14 : ℝ) * a48 + (4/21 : ℝ) * a54 + (3/14 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1901 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a44 : -(h 2) < (-2/17 : ℝ))
    (a45 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a48 : -(h 1) < (-4/31 : ℝ))
    (a53 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (10/61 : ℝ) * _ctx.min + (2/61 : ℝ) * a20 + (12/61 : ℝ) * a33 + (12/61 : ℝ) * a44 + (11/61 : ℝ) * a45 + (12/61 : ℝ) * a48 + (12/61 : ℝ) * a53 + (12/61 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1900 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a37 : -(h 3) < (-3/26 : ℝ))
    (a45 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a48 : -(h 1) < (-4/31 : ℝ))
    (a52 : -(h 2) < (-33/278 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (10/61 : ℝ) * _ctx.min + (2/61 : ℝ) * a20 + (12/61 : ℝ) * a33 + (12/61 : ℝ) * a37 + (11/61 : ℝ) * a45 + (12/61 : ℝ) * a48 + (12/61 : ℝ) * a52 + (12/61 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1899 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a37 : -(h 3) < (-3/26 : ℝ))
    (a44 : -(h 2) < (-2/17 : ℝ))
    (a45 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a51 : -(h 1) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (10/61 : ℝ) * _ctx.min + (2/61 : ℝ) * a20 + (12/61 : ℝ) * a33 + (12/61 : ℝ) * a37 + (12/61 : ℝ) * a44 + (11/61 : ℝ) * a45 + (12/61 : ℝ) * a51 + (12/61 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1898 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a37 : -(h 3) < (-3/26 : ℝ))
    (a44 : -(h 2) < (-2/17 : ℝ))
    (a45 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a48 : -(h 1) < (-4/31 : ℝ))
    (a50 : -(h 0) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a44 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a48 + (1/6 : ℝ) * a50 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1897 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a49 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a25 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1896 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a25 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a37 : -(h 3) < (-3/26 : ℝ))
    (a44 : -(h 2) < (-2/17 : ℝ))
    (a45 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a48 : -(h 1) < (-4/31 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1897 h delta _ctx _hno a25 f0
  by_cases p1 : h 0 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1898 h delta _ctx _hno a33 a37 a44 a45 a48 f1
  by_cases p2 : h 1 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1899 h delta _ctx _hno a20 a33 a37 a44 a45 f2
  by_cases p3 : h 2 ≤ (33/278 : ℝ)
  swap
  · have f3 : -(h 2) < (-33/278 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1900 h delta _ctx _hno a20 a33 a37 a45 a48 f3
  by_cases p4 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1901 h delta _ctx _hno a20 a33 a44 a45 a48 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1902 h delta _ctx _hno a20 a33 a37 a45 a48 f5
  apply _hno 91
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 2 ≤ (33/278 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_1895 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : h 0 ≤ (5/33 : ℝ))
    (a47 : -(h 0) < (-3/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1894 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a46 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a25 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1893 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a25 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a29 : h 0 ≤ (5/33 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a37 : -(h 3) < (-3/26 : ℝ))
    (a40 : -(h 1) < (-9/70 : ℝ))
    (a44 : -(h 2) < (-2/17 : ℝ))
    (a45 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1894 h delta _ctx _hno a25 f0
  by_cases p1 : h 0 ≤ (3/19 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/19 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1895 h delta _ctx _hno a29 f1
  by_cases p2 : h 1 ≤ (4/31 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/31 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1896 h delta _ctx _hno a20 a25 a33 a37 a44 a45 f2
  by_cases p3 : h 2 ≤ (3/25 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1903 h delta _ctx _hno a20 a33 a37 a40 a45 f3
  by_cases p4 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1904 h delta _ctx _hno a20 a33 a40 a44 a45 f4
  by_cases p5 : h 4 ≤ (3/26 : ℝ)
  swap
  · have f5 : -(h 4) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1905 h delta _ctx _hno a20 a40 a44 a45 f5
  apply _hno 113
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (4/31 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (3/26 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_1892 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a25 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a29 : h 0 ≤ (5/33 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a36 : h 1 ≤ (2/15 : ℝ))
    (a37 : -(h 3) < (-3/26 : ℝ))
    (a40 : -(h 1) < (-9/70 : ℝ))
    (a44 : -(h 2) < (-2/17 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1893 h delta _ctx _hno a20 a25 a29 a33 a37 a40 a44 f0
  by_cases p1 : h 0 ≤ (3/19 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/19 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1906 h delta _ctx _hno a29 f1
  by_cases p2 : h 1 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1907 h delta _ctx _hno a20 a29 a33 a36 a37 a44 f2
  by_cases p3 : h 2 ≤ (12/101 : ℝ)
  swap
  · have f3 : -(h 2) < (-12/101 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1928 h delta _ctx _hno a20 a29 a33 a37 a40 p0 p2 f3
  by_cases p4 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1956 h delta _ctx _hno a20 a29 a33 a40 a44 p0 p3 f4
  by_cases p5 : h 4 ≤ (3/26 : ℝ)
  swap
  · have f5 : -(h 4) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1963 h delta _ctx _hno a20 a37 a40 a44 f5
  apply _hno 117
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 2 ≤ (12/101 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (3/26 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_1891 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a37 : -(h 3) < (-3/26 : ℝ))
    (a43 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (16/59 : ℝ) * _ctx.min + (34/59 : ℝ) * _ctx.lower + (3/59 : ℝ) * _ctx.fail1 + (2/59 : ℝ) * a20 + (18/59 : ℝ) * a33 + (18/59 : ℝ) * a37 + (18/59 : ℝ) * a43 + (18/59 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1890 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : h 0 ≤ (5/33 : ℝ))
    (a42 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1889 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a25 + (1 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1888 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a25 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a29 : h 0 ≤ (5/33 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a36 : h 1 ≤ (2/15 : ℝ))
    (a37 : -(h 3) < (-3/26 : ℝ))
    (a40 : -(h 1) < (-9/70 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1889 h delta _ctx _hno a25 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1890 h delta _ctx _hno a29 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1891 h delta _ctx _hno a20 a33 a37 f2
  by_cases p3 : h 2 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1892 h delta _ctx _hno a20 a25 a29 a33 a36 a37 a40 f3
  by_cases p4 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1964 h delta _ctx _hno a20 a33 a37 a40 f4
  apply _hno 118
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_1887 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : h 0 ≤ (5/33 : ℝ))
    (a39 : -(h 0) < (-7/45 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1886 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a38 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a25 + (1 : ℝ) * a38
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1885 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a25 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a29 : h 0 ≤ (5/33 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a36 : h 1 ≤ (2/15 : ℝ))
    (a37 : -(h 3) < (-3/26 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1886 h delta _ctx _hno a25 f0
  by_cases p1 : h 0 ≤ (7/45 : ℝ)
  swap
  · have f1 : -(h 0) < (-7/45 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1887 h delta _ctx _hno a29 f1
  by_cases p2 : h 1 ≤ (9/70 : ℝ)
  swap
  · have f2 : -(h 1) < (-9/70 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1888 h delta _ctx _hno a20 a25 a29 a33 a36 a37 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1965 h delta _ctx _hno a13 a20 a33 a37 f3
  by_cases p4 : h 4 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 4) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1966 h delta _ctx _hno a13 a20 a25 a27 a29 a37 p2 f4
  apply _hno 55
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (7/45 : ℝ)) ∧ (h 1 ≤ (9/70 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (4/35 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_1884 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a36 : -(h 1) < (-2/15 : ℝ))
    (a48 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/25 : ℝ) * _ctx.order3 + (6/25 : ℝ) * _ctx.lower + (1/25 : ℝ) * _ctx.fail1 + (2/75 : ℝ) * a20 + (12/25 : ℝ) * a33 + (6/25 : ℝ) * a36 + (16/75 : ℝ) * a48 + (6/25 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1883 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a41 : h 3 ≤ (7/62 : ℝ))
    (a47 : -(h 3) < (-5/43 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a41 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1882 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a36 : -(h 1) < (-2/15 : ℝ))
    (a46 : -(h 2) < (-9/76 : ℝ))
    (a53 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.lower + (1/30 : ℝ) * a20 + (2/5 : ℝ) * a33 + (1/5 : ℝ) * a36 + (1/5 : ℝ) * a46 + (1/6 : ℝ) * a53 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1881 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a36 : -(h 1) < (-2/15 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    (a46 : -(h 2) < (-9/76 : ℝ))
    (a52 : -(h 4) < (-5/44 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.lower + (1/30 : ℝ) * a20 + (1/5 : ℝ) * a36 + (1/6 : ℝ) * a42 + (1/5 : ℝ) * a46 + (2/5 : ℝ) * a52 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1880 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a41 : h 3 ≤ (7/62 : ℝ))
    (a51 : -(h 3) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a41 + (1 : ℝ) * a51
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1879 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a36 : -(h 1) < (-2/15 : ℝ))
    (a50 : -(h 2) < (-5/42 : ℝ))
    (a57 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.lower + (1/30 : ℝ) * a20 + (1/5 : ℝ) * a24 + (1/5 : ℝ) * a33 + (1/5 : ℝ) * a36 + (1/5 : ℝ) * a50 + (1/6 : ℝ) * a57 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1878 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a36 : -(h 1) < (-2/15 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    (a50 : -(h 2) < (-5/42 : ℝ))
    (a56 : -(h 4) < (-5/44 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.lower + (1/30 : ℝ) * a20 + (1/5 : ℝ) * a36 + (1/6 : ℝ) * a42 + (1/5 : ℝ) * a50 + (2/5 : ℝ) * a56 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1877 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a41 : h 3 ≤ (7/62 : ℝ))
    (a55 : -(h 3) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a41 + (1 : ℝ) * a55
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1876 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a36 : -(h 1) < (-2/15 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    (a54 : -(h 2) < (-5/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.lower + (1/30 : ℝ) * a20 + (2/5 : ℝ) * a33 + (1/5 : ℝ) * a36 + (1/6 : ℝ) * a42 + (1/5 : ℝ) * a54 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1875 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    (a50 : -(h 2) < (-5/42 : ℝ))
    (a53 : -(h 1) < (-3/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.lower + (1/30 : ℝ) * a20 + (2/5 : ℝ) * a33 + (1/6 : ℝ) * a42 + (1/5 : ℝ) * a50 + (1/5 : ℝ) * a53 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1874 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a36 : -(h 1) < (-2/15 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    (a50 : -(h 2) < (-5/42 : ℝ))
    (a52 : -(h 0) < (-11/73 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.lower + (1/3 : ℝ) * a33 + (1/6 : ℝ) * a36 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a50 + (1/6 : ℝ) * a52 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1873 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a43 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a51 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a43 + (1 : ℝ) * a51
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1872 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a36 : -(h 1) < (-2/15 : ℝ))
    (a41 : h 3 ≤ (7/62 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    (a43 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a50 : -(h 2) < (-5/42 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1873 h delta _ctx _hno a43 f0
  by_cases p1 : h 0 ≤ (11/73 : ℝ)
  swap
  · have f1 : -(h 0) < (-11/73 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1874 h delta _ctx _hno a33 a36 a42 a50 f1
  by_cases p2 : h 1 ≤ (3/22 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1875 h delta _ctx _hno a20 a33 a42 a50 f2
  by_cases p3 : h 2 ≤ (5/41 : ℝ)
  swap
  · have f3 : -(h 2) < (-5/41 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1876 h delta _ctx _hno a20 a33 a36 a42 f3
  by_cases p4 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1877 h delta _ctx _hno a41 f4
  by_cases p5 : h 4 ≤ (5/44 : ℝ)
  swap
  · have f5 : -(h 4) < (-5/44 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1878 h delta _ctx _hno a20 a36 a42 a50 f5
  by_cases p6 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f6 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact upper_node_1879 h delta _ctx _hno a20 a24 a33 a36 a50 f6
  apply _hno 122
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (11/73 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 2 ≤ (5/41 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 4 ≤ (5/44 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem upper_node_1871 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    (a46 : -(h 2) < (-9/76 : ℝ))
    (a49 : -(h 1) < (-3/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (1/5 : ℝ) * _ctx.lower + (1/30 : ℝ) * a20 + (2/5 : ℝ) * a33 + (1/6 : ℝ) * a42 + (1/5 : ℝ) * a46 + (1/5 : ℝ) * a49 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1870 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : h 0 ≤ (5/33 : ℝ))
    (a48 : -(h 0) < (-12/79 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1869 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a43 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a47 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a43 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1868 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a29 : h 0 ≤ (5/33 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a36 : -(h 1) < (-2/15 : ℝ))
    (a41 : h 3 ≤ (7/62 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    (a43 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ))
    (a46 : -(h 2) < (-9/76 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1869 h delta _ctx _hno a43 f0
  by_cases p1 : h 0 ≤ (12/79 : ℝ)
  swap
  · have f1 : -(h 0) < (-12/79 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1870 h delta _ctx _hno a29 f1
  by_cases p2 : h 1 ≤ (3/22 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1871 h delta _ctx _hno a20 a33 a42 a46 f2
  by_cases p3 : h 2 ≤ (5/42 : ℝ)
  swap
  · have f3 : -(h 2) < (-5/42 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1872 h delta _ctx _hno a20 a24 a33 a36 a41 a42 a43 f3
  by_cases p4 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1880 h delta _ctx _hno a41 f4
  by_cases p5 : h 4 ≤ (5/44 : ℝ)
  swap
  · have f5 : -(h 4) < (-5/44 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1881 h delta _ctx _hno a20 a36 a42 a46 f5
  by_cases p6 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f6 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact upper_node_1882 h delta _ctx _hno a20 a33 a36 a46 f6
  apply _hno 120
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (12/79 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 2 ≤ (5/42 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 4 ≤ (5/44 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem upper_node_1867 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    (a45 : -(h 1) < (-3/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/25 : ℝ) * _ctx.order3 + (6/25 : ℝ) * _ctx.lower + (1/25 : ℝ) * _ctx.fail1 + (2/75 : ℝ) * a20 + (12/25 : ℝ) * a33 + (16/75 : ℝ) * a42 + (6/25 : ℝ) * a45 + (6/25 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1866 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : h 0 ≤ (5/33 : ℝ))
    (a44 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1865 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a36 : -(h 1) < (-2/15 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a50 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/14 : ℝ) * _ctx.order3 + (1/28 : ℝ) * _ctx.fail1 + (1/42 : ℝ) * a20 + (3/7 : ℝ) * a33 + (3/14 : ℝ) * a36 + (3/28 : ℝ) * a43 + (4/21 : ℝ) * a50 + (3/14 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1864 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a36 : -(h 1) < (-2/15 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a49 : -(h 4) < (-5/44 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (9/38 : ℝ) * _ctx.order3 + (4/19 : ℝ) * _ctx.min + (3/76 : ℝ) * _ctx.fail1 + (1/38 : ℝ) * a20 + (9/38 : ℝ) * a36 + (17/76 : ℝ) * a43 + (9/19 : ℝ) * a49 + (9/38 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1863 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a41 : h 3 ≤ (7/62 : ℝ))
    (a48 : -(h 3) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a41 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1862 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a36 : -(h 1) < (-2/15 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a47 : -(h 2) < (-5/42 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (12/61 : ℝ) * _ctx.order3 + (10/61 : ℝ) * _ctx.min + (2/61 : ℝ) * a20 + (24/61 : ℝ) * a33 + (12/61 : ℝ) * a36 + (11/61 : ℝ) * a43 + (12/61 : ℝ) * a47 + (12/61 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1861 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    (a46 : -(h 1) < (-3/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (9/38 : ℝ) * _ctx.order3 + (4/19 : ℝ) * _ctx.min + (3/76 : ℝ) * _ctx.fail1 + (1/38 : ℝ) * a20 + (9/19 : ℝ) * a33 + (17/76 : ℝ) * a43 + (9/38 : ℝ) * a46 + (9/38 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1860 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : h 0 ≤ (5/33 : ℝ))
    (a45 : -(h 0) < (-12/79 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1859 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a37 : ((2 : ℝ) * (delta)) ≤ (11/52 : ℝ))
    (a44 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a37 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1858 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a29 : h 0 ≤ (5/33 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a36 : -(h 1) < (-2/15 : ℝ))
    (a37 : ((2 : ℝ) * (delta)) ≤ (11/52 : ℝ))
    (a41 : h 3 ≤ (7/62 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1859 h delta _ctx _hno a37 f0
  by_cases p1 : h 0 ≤ (12/79 : ℝ)
  swap
  · have f1 : -(h 0) < (-12/79 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1860 h delta _ctx _hno a29 f1
  by_cases p2 : h 1 ≤ (3/22 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1861 h delta _ctx _hno a20 a33 a43 f2
  by_cases p3 : h 2 ≤ (5/42 : ℝ)
  swap
  · have f3 : -(h 2) < (-5/42 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1862 h delta _ctx _hno a20 a33 a36 a43 f3
  by_cases p4 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1863 h delta _ctx _hno a41 f4
  by_cases p5 : h 4 ≤ (5/44 : ℝ)
  swap
  · have f5 : -(h 4) < (-5/44 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1864 h delta _ctx _hno a20 a36 a43 f5
  by_cases p6 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f6 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact upper_node_1865 h delta _ctx _hno a20 a33 a36 a43 f6
  apply _hno 120
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (12/79 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 2 ≤ (5/42 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 4 ≤ (5/44 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem upper_node_1857 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a29 : h 0 ≤ (5/33 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a36 : -(h 1) < (-2/15 : ℝ))
    (a37 : ((2 : ℝ) * (delta)) ≤ (11/52 : ℝ))
    (a41 : h 3 ≤ (7/62 : ℝ))
    (a42 : -(h 5) < (-2/19 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1858 h delta _ctx _hno a20 a29 a33 a36 a37 a41 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1866 h delta _ctx _hno a29 f1
  by_cases p2 : h 1 ≤ (3/22 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1867 h delta _ctx _hno a20 a33 a42 f2
  by_cases p3 : h 2 ≤ (9/76 : ℝ)
  swap
  · have f3 : -(h 2) < (-9/76 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1868 h delta _ctx _hno a20 a24 a29 a33 a36 a41 a42 p0 f3
  by_cases p4 : h 3 ≤ (5/43 : ℝ)
  swap
  · have f4 : -(h 3) < (-5/43 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1883 h delta _ctx _hno a41 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1884 h delta _ctx _hno a20 a33 a36 f5
  apply _hno 121
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 2 ≤ (9/76 : ℝ)) ∧ (h 3 ≤ (5/43 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_1856 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a36 : -(h 1) < (-2/15 : ℝ))
    (a41 : -(h 3) < (-7/62 : ℝ))
    (a48 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/25 : ℝ) * _ctx.lower + (1/25 : ℝ) * _ctx.fail1 + (2/75 : ℝ) * a20 + (6/25 : ℝ) * a33 + (6/25 : ℝ) * a36 + (6/25 : ℝ) * a41 + (16/75 : ℝ) * a48 + (6/25 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1855 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a36 : -(h 1) < (-2/15 : ℝ))
    (a47 : -(h 4) < (-5/44 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (18/59 : ℝ) * _ctx.order3 + (16/59 : ℝ) * _ctx.min + (34/59 : ℝ) * _ctx.lower + (3/59 : ℝ) * _ctx.fail1 + (2/59 : ℝ) * a20 + (18/59 : ℝ) * a36 + (36/59 : ℝ) * a47 + (18/59 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1854 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a36 : -(h 1) < (-2/15 : ℝ))
    (a46 : -(h 3) < (-4/35 : ℝ))
    (a52 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/25 : ℝ) * _ctx.lower + (1/25 : ℝ) * _ctx.fail1 + (2/75 : ℝ) * a20 + (6/25 : ℝ) * a33 + (6/25 : ℝ) * a36 + (6/25 : ℝ) * a46 + (16/75 : ℝ) * a52 + (6/25 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1853 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a36 : -(h 1) < (-2/15 : ℝ))
    (a51 : -(h 3) < (-5/43 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (16/59 : ℝ) * _ctx.min + (34/59 : ℝ) * _ctx.lower + (3/59 : ℝ) * _ctx.fail1 + (2/59 : ℝ) * a20 + (18/59 : ℝ) * a33 + (18/59 : ℝ) * a36 + (18/59 : ℝ) * a51 + (18/59 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1852 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a36 : -(h 1) < (-2/15 : ℝ))
    (a46 : -(h 3) < (-4/35 : ℝ))
    (a50 : -(h 2) < (-9/76 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (11/25 : ℝ) * _ctx.lower + (1/25 : ℝ) * a20 + (6/25 : ℝ) * a33 + (6/25 : ℝ) * a36 + (6/25 : ℝ) * a46 + (6/25 : ℝ) * a50 + (6/25 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1851 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a46 : -(h 3) < (-4/35 : ℝ))
    (a49 : -(h 1) < (-3/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (16/59 : ℝ) * _ctx.min + (34/59 : ℝ) * _ctx.lower + (3/59 : ℝ) * _ctx.fail1 + (2/59 : ℝ) * a20 + (18/59 : ℝ) * a33 + (18/59 : ℝ) * a46 + (18/59 : ℝ) * a49 + (18/59 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1850 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : h 0 ≤ (5/33 : ℝ))
    (a48 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1849 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a36 : -(h 1) < (-2/15 : ℝ))
    (a46 : -(h 3) < (-4/35 : ℝ))
    (a47 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/19 : ℝ) * _ctx.min + (3/76 : ℝ) * _ctx.fail1 + (1/38 : ℝ) * a20 + (9/38 : ℝ) * a33 + (9/38 : ℝ) * a36 + (9/38 : ℝ) * a46 + (17/76 : ℝ) * a47 + (9/38 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1848 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a29 : h 0 ≤ (5/33 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a36 : -(h 1) < (-2/15 : ℝ))
    (a46 : -(h 3) < (-4/35 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1849 h delta _ctx _hno a20 a33 a36 a46 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1850 h delta _ctx _hno a29 f1
  by_cases p2 : h 1 ≤ (3/22 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1851 h delta _ctx _hno a20 a33 a46 f2
  by_cases p3 : h 2 ≤ (9/76 : ℝ)
  swap
  · have f3 : -(h 2) < (-9/76 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1852 h delta _ctx _hno a20 a33 a36 a46 f3
  by_cases p4 : h 3 ≤ (5/43 : ℝ)
  swap
  · have f4 : -(h 3) < (-5/43 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1853 h delta _ctx _hno a20 a33 a36 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1854 h delta _ctx _hno a20 a33 a36 a46 f5
  apply _hno 121
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 2 ≤ (9/76 : ℝ)) ∧ (h 3 ≤ (5/43 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_1847 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a36 : -(h 1) < (-2/15 : ℝ))
    (a41 : -(h 3) < (-7/62 : ℝ))
    (a45 : -(h 2) < (-5/42 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (11/25 : ℝ) * _ctx.lower + (1/25 : ℝ) * a20 + (6/25 : ℝ) * a33 + (6/25 : ℝ) * a36 + (6/25 : ℝ) * a41 + (6/25 : ℝ) * a45 + (6/25 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1846 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a41 : -(h 3) < (-7/62 : ℝ))
    (a44 : -(h 1) < (-3/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (16/59 : ℝ) * _ctx.min + (34/59 : ℝ) * _ctx.lower + (3/59 : ℝ) * _ctx.fail1 + (2/59 : ℝ) * a20 + (18/59 : ℝ) * a33 + (18/59 : ℝ) * a41 + (18/59 : ℝ) * a44 + (18/59 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1845 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : h 0 ≤ (5/33 : ℝ))
    (a43 : -(h 0) < (-12/79 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1844 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a37 : ((2 : ℝ) * (delta)) ≤ (11/52 : ℝ))
    (a42 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a37 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1843 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a29 : h 0 ≤ (5/33 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a36 : -(h 1) < (-2/15 : ℝ))
    (a37 : ((2 : ℝ) * (delta)) ≤ (11/52 : ℝ))
    (a41 : -(h 3) < (-7/62 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1844 h delta _ctx _hno a37 f0
  by_cases p1 : h 0 ≤ (12/79 : ℝ)
  swap
  · have f1 : -(h 0) < (-12/79 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1845 h delta _ctx _hno a29 f1
  by_cases p2 : h 1 ≤ (3/22 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1846 h delta _ctx _hno a20 a33 a41 f2
  by_cases p3 : h 2 ≤ (5/42 : ℝ)
  swap
  · have f3 : -(h 2) < (-5/42 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1847 h delta _ctx _hno a20 a33 a36 a41 f3
  by_cases p4 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1848 h delta _ctx _hno a20 a29 a33 a36 f4
  by_cases p5 : h 4 ≤ (5/44 : ℝ)
  swap
  · have f5 : -(h 4) < (-5/44 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1855 h delta _ctx _hno a20 a36 f5
  by_cases p6 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f6 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact upper_node_1856 h delta _ctx _hno a20 a33 a36 a41 f6
  apply _hno 120
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (12/79 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 2 ≤ (5/42 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 4 ≤ (5/44 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem upper_node_1842 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : h 2 ≤ (1/8 : ℝ))
    (a40 : -(h 2) < (-4/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1841 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a23 : h 1 ≤ (5/36 : ℝ))
    (a39 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a23 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1840 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : h 0 ≤ (5/33 : ℝ))
    (a38 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a38
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1839 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a36 : -(h 1) < (-2/15 : ℝ))
    (a37 : ((-2 : ℝ) * (delta)) < (-11/52 : ℝ))
    (a44 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (3/14 : ℝ) * _ctx.order3 + (1/28 : ℝ) * _ctx.fail1 + (1/42 : ℝ) * a20 + (3/7 : ℝ) * a33 + (3/14 : ℝ) * a36 + (3/28 : ℝ) * a37 + (4/21 : ℝ) * a44 + (3/14 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1838 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a36 : -(h 1) < (-2/15 : ℝ))
    (a37 : ((-2 : ℝ) * (delta)) < (-11/52 : ℝ))
    (a43 : -(h 4) < (-5/44 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (9/38 : ℝ) * _ctx.order3 + (4/19 : ℝ) * _ctx.min + (3/76 : ℝ) * _ctx.fail1 + (1/38 : ℝ) * a20 + (9/38 : ℝ) * a36 + (17/76 : ℝ) * a37 + (9/19 : ℝ) * a43 + (9/38 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1837 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a36 : -(h 1) < (-2/15 : ℝ))
    (a37 : ((-2 : ℝ) * (delta)) < (-11/52 : ℝ))
    (a42 : -(h 3) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/19 : ℝ) * _ctx.min + (3/76 : ℝ) * _ctx.fail1 + (1/38 : ℝ) * a20 + (9/38 : ℝ) * a33 + (9/38 : ℝ) * a36 + (17/76 : ℝ) * a37 + (9/38 : ℝ) * a42 + (9/38 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1836 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a36 : -(h 1) < (-2/15 : ℝ))
    (a37 : ((-2 : ℝ) * (delta)) < (-11/52 : ℝ))
    (a41 : -(h 2) < (-5/42 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (12/61 : ℝ) * _ctx.order3 + (10/61 : ℝ) * _ctx.min + (2/61 : ℝ) * a20 + (24/61 : ℝ) * a33 + (12/61 : ℝ) * a36 + (11/61 : ℝ) * a37 + (12/61 : ℝ) * a41 + (12/61 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1835 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a37 : ((-2 : ℝ) * (delta)) < (-11/52 : ℝ))
    (a40 : -(h 1) < (-3/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (9/38 : ℝ) * _ctx.order3 + (4/19 : ℝ) * _ctx.min + (3/76 : ℝ) * _ctx.fail1 + (1/38 : ℝ) * a20 + (9/19 : ℝ) * a33 + (17/76 : ℝ) * a37 + (9/38 : ℝ) * a40 + (9/38 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1834 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : h 0 ≤ (5/33 : ℝ))
    (a39 : -(h 0) < (-12/79 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1833 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a38 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a25 + (1 : ℝ) * a38
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1832 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a25 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a29 : h 0 ≤ (5/33 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a36 : -(h 1) < (-2/15 : ℝ))
    (a37 : ((-2 : ℝ) * (delta)) < (-11/52 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1833 h delta _ctx _hno a25 f0
  by_cases p1 : h 0 ≤ (12/79 : ℝ)
  swap
  · have f1 : -(h 0) < (-12/79 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1834 h delta _ctx _hno a29 f1
  by_cases p2 : h 1 ≤ (3/22 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1835 h delta _ctx _hno a20 a33 a37 f2
  by_cases p3 : h 2 ≤ (5/42 : ℝ)
  swap
  · have f3 : -(h 2) < (-5/42 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1836 h delta _ctx _hno a20 a33 a36 a37 f3
  by_cases p4 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1837 h delta _ctx _hno a20 a33 a36 a37 f4
  by_cases p5 : h 4 ≤ (5/44 : ℝ)
  swap
  · have f5 : -(h 4) < (-5/44 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1838 h delta _ctx _hno a20 a36 a37 f5
  by_cases p6 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f6 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p6
      linarith only [hp]
    exact upper_node_1839 h delta _ctx _hno a20 a33 a36 a37 f6
  apply _hno 120
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (12/79 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 2 ≤ (5/42 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 4 ≤ (5/44 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5, p6⟩

theorem upper_node_1831 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a23 : h 1 ≤ (5/36 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a25 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a29 : h 0 ≤ (5/33 : ℝ))
    (a31 : h 2 ≤ (1/8 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    (a36 : -(h 1) < (-2/15 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (11/52 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-11/52 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1832 h delta _ctx _hno a20 a25 a29 a33 a36 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1840 h delta _ctx _hno a29 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1841 h delta _ctx _hno a23 f2
  by_cases p3 : h 2 ≤ (4/29 : ℝ)
  swap
  · have f3 : -(h 2) < (-4/29 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1842 h delta _ctx _hno a31 f3
  by_cases p4 : h 3 ≤ (7/62 : ℝ)
  swap
  · have f4 : -(h 3) < (-7/62 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_1843 h delta _ctx _hno a20 a29 a33 a36 p0 f4
  by_cases p5 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_1857 h delta _ctx _hno a20 a24 a29 a33 a36 p0 p4 f5
  apply _hno 29
  change (((2 : ℝ) * (delta)) ≤ (11/52 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (4/29 : ℝ)) ∧ (h 3 ≤ (7/62 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_1830 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a29 : h 0 ≤ (5/33 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a35
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1829 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a25 + (1 : ℝ) * a34
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_1828 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a13 : ((-3 : ℝ) * (h 1)) + ((-6 : ℝ) * (delta)) < (-1 : ℝ))
    (a20 : ((-6 : ℝ) * (h 0)) + -(h 5) < (-1 : ℝ))
    (a23 : h 1 ≤ (5/36 : ℝ))
    (a24 : -(h 3) < (-1/9 : ℝ))
    (a25 : ((2 : ℝ) * (delta)) ≤ (10/47 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a29 : h 0 ≤ (5/33 : ℝ))
    (a31 : h 2 ≤ (1/8 : ℝ))
    (a33 : -(h 4) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_1829 h delta _ctx _hno a25 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_1830 h delta _ctx _hno a29 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_1831 h delta _ctx _hno a20 a23 a24 a25 a29 a31 a33 f2
  by_cases p3 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f3 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_1885 h delta _ctx _hno a13 a20 a25 a27 a29 a33 p2 f3
  by_cases p4 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_2032 h delta _ctx _hno a13 a20 a24 a25 a27 a29 a33 p3 f4
  apply _hno 19
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

end RealPinwheel.WeakSevenBandData
