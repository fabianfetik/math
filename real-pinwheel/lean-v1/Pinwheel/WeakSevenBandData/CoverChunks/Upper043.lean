import Pinwheel.WeakSevenBandData.CoverChunks.Upper042

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem upper_node_867 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a21 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a33 : -(h 3) < (-3/26 : ℝ))
    (a46 : -(h 0) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/7 : ℝ) * a21 + (1/7 : ℝ) * a33 + (6/7 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_866 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a33 : -(h 3) < (-3/26 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a44 : -(h 0) < (-5/34 : ℝ))
    (a45 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.min + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a27 + (6/29 : ℝ) * a33 + (6/29 : ℝ) * a42 + (4/29 : ℝ) * a44 + (6/29 : ℝ) * a45 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_865 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a21 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a33 : -(h 3) < (-3/26 : ℝ))
    (a40 : h 1 ≤ (9/70 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a44 : -(h 0) < (-5/34 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_866 h delta _ctx _hno a27 a33 a42 a44 f0
  by_cases p1 : h 0 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_867 h delta _ctx _hno a21 a33 f1
  by_cases p2 : h 1 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_868 h delta _ctx _hno a40 f2
  by_cases p3 : h 2 ≤ (33/278 : ℝ)
  swap
  · have f3 : -(h 2) < (-33/278 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_869 h delta _ctx _hno a14 a27 a33 a42 a44 f3
  by_cases p4 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_870 h delta _ctx _hno a14 a27 a42 a44 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_871 h delta _ctx _hno a14 a27 a33 a42 a44 f5
  apply _hno 91
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 2 ≤ (33/278 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_864 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a29 : -(h 0) < (-1/7 : ℝ))
    (a33 : -(h 3) < (-3/26 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.min + (1/29 : ℝ) * _ctx.fail1 + (6/29 : ℝ) * a27 + (4/29 : ℝ) * a29 + (6/29 : ℝ) * a33 + (6/29 : ℝ) * a42 + (6/29 : ℝ) * a43 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_863 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a21 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a29 : -(h 0) < (-1/7 : ℝ))
    (a33 : -(h 3) < (-3/26 : ℝ))
    (a40 : h 1 ≤ (9/70 : ℝ))
    (a42 : -(h 4) < (-4/35 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_864 h delta _ctx _hno a27 a29 a33 a42 f0
  by_cases p1 : h 0 ≤ (5/34 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/34 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_865 h delta _ctx _hno a14 a21 a27 a33 a40 a42 f1
  by_cases p2 : h 1 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_872 h delta _ctx _hno a40 f2
  by_cases p3 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_873 h delta _ctx _hno a14 a27 a29 a42 f3
  apply _hno 92
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (5/34 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_862 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a29 : -(h 0) < (-1/7 : ℝ))
    (a33 : -(h 3) < (-3/26 : ℝ))
    (a37 : -(h 4) < (-1/9 : ℝ))
    (a41 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order1 + (1/5 : ℝ) * _ctx.min + (1/20 : ℝ) * a14 + (3/20 : ℝ) * a29 + (1/5 : ℝ) * a33 + (1/5 : ℝ) * a37 + (2/5 : ℝ) * a41 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_861 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a29 : -(h 0) < (-1/7 : ℝ))
    (a37 : -(h 4) < (-1/9 : ℝ))
    (a40 : -(h 1) < (-9/70 : ℝ))
    (a44 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.min + (1/23 : ℝ) * _ctx.fail1 + (3/46 : ℝ) * a14 + (5/46 : ℝ) * a29 + (6/23 : ℝ) * a37 + (6/23 : ℝ) * a40 + (6/23 : ℝ) * a44 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_860 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a29 : -(h 0) < (-1/7 : ℝ))
    (a33 : -(h 3) < (-3/26 : ℝ))
    (a43 : -(h 1) < (-3/23 : ℝ))
    (a49 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/23 : ℝ) * _ctx.fail1 + (3/92 : ℝ) * a14 + (3/92 : ℝ) * a24 + (13/92 : ℝ) * a29 + (21/92 : ℝ) * a33 + (6/23 : ℝ) * a43 + (6/23 : ℝ) * a49 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_859 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a29 : -(h 0) < (-1/7 : ℝ))
    (a37 : -(h 4) < (-1/9 : ℝ))
    (a43 : -(h 1) < (-3/23 : ℝ))
    (a48 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.min + (1/23 : ℝ) * _ctx.fail1 + (3/46 : ℝ) * a14 + (5/46 : ℝ) * a29 + (6/23 : ℝ) * a37 + (6/23 : ℝ) * a43 + (6/23 : ℝ) * a48 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_858 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a29 : -(h 0) < (-1/7 : ℝ))
    (a33 : -(h 3) < (-3/26 : ℝ))
    (a37 : -(h 4) < (-1/9 : ℝ))
    (a43 : -(h 1) < (-3/23 : ℝ))
    (a47 : -(h 2) < (-4/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (1/20 : ℝ) * a14 + (3/20 : ℝ) * a29 + (1/5 : ℝ) * a33 + (1/5 : ℝ) * a37 + (1/5 : ℝ) * a43 + (1/5 : ℝ) * a47 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_857 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a29 : -(h 0) < (-1/7 : ℝ))
    (a33 : -(h 3) < (-3/26 : ℝ))
    (a46 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/17 : ℝ) * _ctx.min + (1/17 : ℝ) * _ctx.fail1 + (3/34 : ℝ) * a14 + (3/68 : ℝ) * a24 + (5/34 : ℝ) * a29 + (21/68 : ℝ) * a33 + (6/17 : ℝ) * a46 + (6/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_856 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a33 : -(h 3) < (-3/26 : ℝ))
    (a37 : -(h 4) < (-1/9 : ℝ))
    (a43 : -(h 1) < (-3/23 : ℝ))
    (a45 : -(h 0) < (-6/41 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.min + (1/23 : ℝ) * _ctx.fail1 + (3/46 : ℝ) * a14 + (6/23 : ℝ) * a33 + (6/23 : ℝ) * a37 + (6/23 : ℝ) * a43 + (5/46 : ℝ) * a45 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_855 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a29 : -(h 0) < (-1/7 : ℝ))
    (a33 : -(h 3) < (-3/26 : ℝ))
    (a43 : -(h 1) < (-3/23 : ℝ))
    (a44 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.min + (1/23 : ℝ) * _ctx.fail1 + (3/92 : ℝ) * a24 + (4/23 : ℝ) * a29 + (21/92 : ℝ) * a33 + (6/23 : ℝ) * a43 + (6/23 : ℝ) * a44 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_854 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a29 : -(h 0) < (-1/7 : ℝ))
    (a33 : -(h 3) < (-3/26 : ℝ))
    (a37 : -(h 4) < (-1/9 : ℝ))
    (a43 : -(h 1) < (-3/23 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/32 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_855 h delta _ctx _hno a24 a29 a33 a43 f0
  by_cases p1 : h 0 ≤ (6/41 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/41 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_856 h delta _ctx _hno a14 a33 a37 a43 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_857 h delta _ctx _hno a14 a24 a29 a33 f2
  by_cases p3 : h 2 ≤ (4/33 : ℝ)
  swap
  · have f3 : -(h 2) < (-4/33 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_858 h delta _ctx _hno a14 a29 a33 a37 a43 f3
  by_cases p4 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_859 h delta _ctx _hno a14 a29 a37 a43 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_860 h delta _ctx _hno a14 a24 a29 a33 a43 f5
  apply _hno 93
  change (((2 : ℝ) * (delta)) ≤ (7/32 : ℝ)) ∧ (h 0 ≤ (6/41 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (4/33 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_853 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a33 : -(h 3) < (-3/26 : ℝ))
    (a40 : -(h 1) < (-9/70 : ℝ))
    (a42 : -(h 0) < (-5/34 : ℝ))
    (a48 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/23 : ℝ) * _ctx.fail1 + (3/92 : ℝ) * a14 + (3/92 : ℝ) * a24 + (21/92 : ℝ) * a33 + (6/23 : ℝ) * a40 + (13/92 : ℝ) * a42 + (6/23 : ℝ) * a48 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_852 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a37 : -(h 4) < (-1/9 : ℝ))
    (a40 : -(h 1) < (-9/70 : ℝ))
    (a42 : -(h 0) < (-5/34 : ℝ))
    (a47 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.min + (1/23 : ℝ) * _ctx.fail1 + (3/46 : ℝ) * a14 + (6/23 : ℝ) * a37 + (6/23 : ℝ) * a40 + (5/46 : ℝ) * a42 + (6/23 : ℝ) * a47 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_851 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a33 : -(h 3) < (-3/26 : ℝ))
    (a37 : -(h 4) < (-1/9 : ℝ))
    (a40 : -(h 1) < (-9/70 : ℝ))
    (a42 : -(h 0) < (-5/34 : ℝ))
    (a46 : -(h 2) < (-33/278 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (1/20 : ℝ) * a14 + (1/5 : ℝ) * a33 + (1/5 : ℝ) * a37 + (1/5 : ℝ) * a40 + (3/20 : ℝ) * a42 + (1/5 : ℝ) * a46 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_850 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a33 : -(h 3) < (-3/26 : ℝ))
    (a37 : -(h 4) < (-1/9 : ℝ))
    (a42 : -(h 0) < (-5/34 : ℝ))
    (a45 : -(h 1) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.min + (1/23 : ℝ) * _ctx.fail1 + (3/46 : ℝ) * a14 + (6/23 : ℝ) * a33 + (6/23 : ℝ) * a37 + (5/46 : ℝ) * a42 + (6/23 : ℝ) * a45 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_849 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a21 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a33 : -(h 3) < (-3/26 : ℝ))
    (a44 : -(h 0) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/7 : ℝ) * a21 + (1/7 : ℝ) * a33 + (6/7 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_848 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a33 : -(h 3) < (-3/26 : ℝ))
    (a40 : -(h 1) < (-9/70 : ℝ))
    (a42 : -(h 0) < (-5/34 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.min + (1/23 : ℝ) * _ctx.fail1 + (3/92 : ℝ) * a24 + (21/92 : ℝ) * a33 + (6/23 : ℝ) * a40 + (4/23 : ℝ) * a42 + (6/23 : ℝ) * a43 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_847 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a21 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a33 : -(h 3) < (-3/26 : ℝ))
    (a37 : -(h 4) < (-1/9 : ℝ))
    (a40 : -(h 1) < (-9/70 : ℝ))
    (a42 : -(h 0) < (-5/34 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_848 h delta _ctx _hno a24 a33 a40 a42 f0
  by_cases p1 : h 0 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_849 h delta _ctx _hno a21 a33 f1
  by_cases p2 : h 1 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_850 h delta _ctx _hno a14 a33 a37 a42 f2
  by_cases p3 : h 2 ≤ (33/278 : ℝ)
  swap
  · have f3 : -(h 2) < (-33/278 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_851 h delta _ctx _hno a14 a33 a37 a40 a42 f3
  by_cases p4 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_852 h delta _ctx _hno a14 a37 a40 a42 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_853 h delta _ctx _hno a14 a24 a33 a40 a42 f5
  apply _hno 91
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 2 ≤ (33/278 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_846 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a29 : -(h 0) < (-1/7 : ℝ))
    (a33 : -(h 3) < (-3/26 : ℝ))
    (a40 : -(h 1) < (-9/70 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/23 : ℝ) * _ctx.min + (1/23 : ℝ) * _ctx.fail1 + (3/92 : ℝ) * a24 + (4/23 : ℝ) * a29 + (21/92 : ℝ) * a33 + (6/23 : ℝ) * a40 + (6/23 : ℝ) * a41 + (6/23 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_845 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a21 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a29 : -(h 0) < (-1/7 : ℝ))
    (a33 : -(h 3) < (-3/26 : ℝ))
    (a37 : -(h 4) < (-1/9 : ℝ))
    (a40 : -(h 1) < (-9/70 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_846 h delta _ctx _hno a24 a29 a33 a40 f0
  by_cases p1 : h 0 ≤ (5/34 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/34 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_847 h delta _ctx _hno a14 a21 a24 a33 a37 a40 f1
  by_cases p2 : h 1 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_854 h delta _ctx _hno a14 a24 a29 a33 a37 f2
  by_cases p3 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_861 h delta _ctx _hno a14 a29 a37 a40 f3
  apply _hno 92
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (5/34 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_844 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a16 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a21 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a39 : -(h 0) < (-7/45 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/55 : ℝ) * a16 + (1/55 : ℝ) * a19 + (8/55 : ℝ) * a21 + (54/55 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_843 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : h 3 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a33 : -(h 3) < (-3/26 : ℝ))
    (a38 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * a20 + (1/5 : ℝ) * a33 + (4/5 : ℝ) * a38
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_842 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a16 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a20 : h 3 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a21 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a29 : -(h 0) < (-1/7 : ℝ))
    (a33 : -(h 3) < (-3/26 : ℝ))
    (a37 : -(h 4) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_843 h delta _ctx _hno a20 a33 f0
  by_cases p1 : h 0 ≤ (7/45 : ℝ)
  swap
  · have f1 : -(h 0) < (-7/45 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_844 h delta _ctx _hno a16 a19 a21 f1
  by_cases p2 : h 1 ≤ (9/70 : ℝ)
  swap
  · have f2 : -(h 1) < (-9/70 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_845 h delta _ctx _hno a14 a21 a24 a29 a33 a37 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_862 h delta _ctx _hno a14 a29 a33 a37 f3
  by_cases p4 : h 4 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 4) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_863 h delta _ctx _hno a14 a21 a27 a29 a33 p2 f4
  apply _hno 55
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (7/45 : ℝ)) ∧ (h 1 ≤ (9/70 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (4/35 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_841 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a29 : -(h 0) < (-1/7 : ℝ))
    (a33 : -(h 3) < (-3/26 : ℝ))
    (a36 : -(h 2) < (-1/8 : ℝ))
    (a41 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (1/20 : ℝ) * a14 + (1/5 : ℝ) * a27 + (3/20 : ℝ) * a29 + (1/5 : ℝ) * a33 + (1/5 : ℝ) * a36 + (1/5 : ℝ) * a41 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_840 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a36 : -(h 2) < (-1/8 : ℝ))
    (a37 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a40 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.min + (1/4 : ℝ) * a14 + (1/32 : ℝ) * a24 + (1/4 : ℝ) * a27 + (1/4 : ℝ) * a36 + (3/4 : ℝ) * a37 + (7/32 : ℝ) * a40 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_839 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a33 : -(h 3) < (-3/26 : ℝ))
    (a36 : -(h 2) < (-1/8 : ℝ))
    (a37 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ))
    (a39 : -(h 1) < (-7/54 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.min + (1/4 : ℝ) * a14 + (1/32 : ℝ) * a24 + (7/32 : ℝ) * a33 + (1/4 : ℝ) * a36 + (3/4 : ℝ) * a37 + (1/4 : ℝ) * a39 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_838 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a21 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a38 : -(h 0) < (-1/6 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (8/55 : ℝ) * _ctx.order3 + (9/55 : ℝ) * a21 + (1/55 : ℝ) * a24 + (54/55 : ℝ) * a38
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_837 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a29 : -(h 0) < (-1/7 : ℝ))
    (a36 : -(h 2) < (-1/8 : ℝ))
    (a41 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.min + (1/16 : ℝ) * a14 + (1/32 : ℝ) * a24 + (1/4 : ℝ) * a27 + (3/16 : ℝ) * a29 + (1/4 : ℝ) * a36 + (7/32 : ℝ) * a41 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_836 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a29 : -(h 0) < (-1/7 : ℝ))
    (a33 : -(h 3) < (-3/26 : ℝ))
    (a36 : -(h 2) < (-1/8 : ℝ))
    (a40 : -(h 1) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.min + (1/16 : ℝ) * a14 + (1/32 : ℝ) * a24 + (3/16 : ℝ) * a29 + (7/32 : ℝ) * a33 + (1/4 : ℝ) * a36 + (1/4 : ℝ) * a40 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_835 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a33 : -(h 3) < (-3/26 : ℝ))
    (a36 : -(h 2) < (-1/8 : ℝ))
    (a37 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    (a39 : -(h 0) < (-5/34 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (1/40 : ℝ) * a24 + (1/5 : ℝ) * a27 + (7/40 : ℝ) * a33 + (1/5 : ℝ) * a36 + (1/5 : ℝ) * a37 + (1/5 : ℝ) * a39 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_834 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a29 : -(h 0) < (-1/7 : ℝ))
    (a33 : -(h 3) < (-3/26 : ℝ))
    (a36 : -(h 2) < (-1/8 : ℝ))
    (a38 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (1/40 : ℝ) * a24 + (1/5 : ℝ) * a27 + (1/5 : ℝ) * a29 + (7/40 : ℝ) * a33 + (1/5 : ℝ) * a36 + (1/5 : ℝ) * a38 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_833 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a29 : -(h 0) < (-1/7 : ℝ))
    (a33 : -(h 3) < (-3/26 : ℝ))
    (a36 : -(h 2) < (-1/8 : ℝ))
    (a37 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_834 h delta _ctx _hno a24 a27 a29 a33 a36 f0
  by_cases p1 : h 0 ≤ (5/34 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/34 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_835 h delta _ctx _hno a24 a27 a33 a36 a37 f1
  by_cases p2 : h 1 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_836 h delta _ctx _hno a14 a24 a29 a33 a36 f2
  by_cases p3 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_837 h delta _ctx _hno a14 a24 a27 a29 a36 f3
  apply _hno 92
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (5/34 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_832 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a21 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a29 : -(h 0) < (-1/7 : ℝ))
    (a33 : -(h 3) < (-3/26 : ℝ))
    (a36 : -(h 2) < (-1/8 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_833 h delta _ctx _hno a14 a24 a27 a29 a33 a36 f0
  by_cases p1 : h 0 ≤ (1/6 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/6 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_838 h delta _ctx _hno a21 a24 f1
  by_cases p2 : h 1 ≤ (7/54 : ℝ)
  swap
  · have f2 : -(h 1) < (-7/54 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_839 h delta _ctx _hno a14 a24 a33 a36 p0 f2
  by_cases p3 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_840 h delta _ctx _hno a14 a24 a27 a36 p0 f3
  by_cases p4 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_841 h delta _ctx _hno a14 a27 a29 a33 a36 f4
  apply _hno 14
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (1/6 : ℝ)) ∧ (h 1 ≤ (7/54 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_831 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a21 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a33 : -(h 3) < (-3/26 : ℝ))
    (a35 : -(h 0) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/7 : ℝ) * a21 + (1/7 : ℝ) * a33 + (6/7 : ℝ) * a35
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_830 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a20 : h 3 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a33 : -(h 3) < (-3/26 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * a20 + (1/5 : ℝ) * a33 + (4/5 : ℝ) * a34
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_829 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a16 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a20 : h 3 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a21 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a29 : -(h 0) < (-1/7 : ℝ))
    (a33 : -(h 3) < (-3/26 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_830 h delta _ctx _hno a20 a33 f0
  by_cases p1 : h 0 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_831 h delta _ctx _hno a21 a33 f1
  by_cases p2 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_832 h delta _ctx _hno a14 a21 a24 a27 a29 a33 f2
  by_cases p3 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f3 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_842 h delta _ctx _hno a14 a16 a19 a20 a21 a24 a27 a29 a33 f3
  apply _hno 8
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_828 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a29 : -(h 0) < (-1/7 : ℝ))
    (a32 : -(h 1) < (-2/15 : ℝ))
    (a42 : -(h 5) < (-6/53 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/29 : ℝ) * _ctx.order3 + (12/29 : ℝ) * _ctx.order4 + (1/29 : ℝ) * _ctx.fail1 + (3/116 : ℝ) * a14 + (13/116 : ℝ) * a29 + (6/29 : ℝ) * a32 + (18/29 : ℝ) * a42 + (6/29 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_827 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a29 : -(h 0) < (-1/7 : ℝ))
    (a32 : -(h 1) < (-2/15 : ℝ))
    (a41 : -(h 3) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/17 : ℝ) * _ctx.min + (1/17 : ℝ) * _ctx.fail1 + (3/34 : ℝ) * a14 + (3/68 : ℝ) * a24 + (5/34 : ℝ) * a29 + (6/17 : ℝ) * a32 + (21/68 : ℝ) * a41 + (6/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_826 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a29 : -(h 0) < (-1/7 : ℝ))
    (a32 : -(h 1) < (-2/15 : ℝ))
    (a40 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (19/69 : ℝ) * _ctx.min + (121/1656 : ℝ) * a14 + (7/207 : ℝ) * a19 + (8/207 : ℝ) * a24 + (17/72 : ℝ) * a29 + (64/207 : ℝ) * a32 + (64/207 : ℝ) * a40 + (64/207 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_825 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a29 : -(h 0) < (-1/7 : ℝ))
    (a39 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (171/397 : ℝ) * _ctx.min + (32/397 : ℝ) * _ctx.fail1 + (363/3176 : ℝ) * a14 + (21/397 : ℝ) * a19 + (24/397 : ℝ) * a24 + (661/3176 : ℝ) * a29 + (192/397 : ℝ) * a39 + (192/397 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_824 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a32 : -(h 1) < (-2/15 : ℝ))
    (a36 : -(h 4) < (-1/9 : ℝ))
    (a38 : -(h 0) < (-8/55 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (21/71 : ℝ) * _ctx.min + (4/71 : ℝ) * _ctx.fail1 + (45/568 : ℝ) * a14 + (3/71 : ℝ) * a19 + (24/71 : ℝ) * a32 + (24/71 : ℝ) * a36 + (83/568 : ℝ) * a38 + (24/71 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_823 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ))
    (a37 : ((-2 : ℝ) * (delta)) < (-7/31 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a25 + (1 : ℝ) * a37
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_822 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a25 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ))
    (a29 : -(h 0) < (-1/7 : ℝ))
    (a32 : -(h 1) < (-2/15 : ℝ))
    (a36 : -(h 4) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/31 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/31 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_823 h delta _ctx _hno a25 f0
  by_cases p1 : h 0 ≤ (8/55 : ℝ)
  swap
  · have f1 : -(h 0) < (-8/55 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_824 h delta _ctx _hno a14 a19 a32 a36 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_825 h delta _ctx _hno a14 a19 a24 a29 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_826 h delta _ctx _hno a14 a19 a24 a29 a32 f3
  by_cases p4 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_827 h delta _ctx _hno a14 a24 a29 a32 f4
  by_cases p5 : h 5 ≤ (6/53 : ℝ)
  swap
  · have f5 : -(h 5) < (-6/53 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_828 h delta _ctx _hno a14 a29 a32 f5
  apply _hno 39
  change (((2 : ℝ) * (delta)) ≤ (7/31 : ℝ)) ∧ (h 0 ≤ (8/55 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (6/53 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_821 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a29 : -(h 0) < (-1/7 : ℝ))
    (a32 : -(h 1) < (-2/15 : ℝ))
    (a35 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (19/69 : ℝ) * _ctx.min + (121/1656 : ℝ) * a14 + (7/207 : ℝ) * a19 + (8/207 : ℝ) * a24 + (17/72 : ℝ) * a29 + (64/207 : ℝ) * a32 + (64/207 : ℝ) * a35 + (64/207 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_820 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a21 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a32 : -(h 1) < (-2/15 : ℝ))
    (a34 : -(h 0) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/1097 : ℝ) * _ctx.fail1 + (3/1097 : ℝ) * a14 + (24/1097 : ℝ) * a19 + (171/1097 : ℝ) * a21 + (3/1097 : ℝ) * a24 + (24/1097 : ℝ) * a32 + (1039/1097 : ℝ) * a34 + (24/1097 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_819 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a29 : -(h 0) < (-1/7 : ℝ))
    (a32 : -(h 1) < (-2/15 : ℝ))
    (a33 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (342/1157 : ℝ) * _ctx.min + (64/1157 : ℝ) * _ctx.fail1 + (42/1157 : ℝ) * a19 + (48/1157 : ℝ) * a24 + (256/1157 : ℝ) * a29 + (384/1157 : ℝ) * a32 + (363/1157 : ℝ) * a33 + (384/1157 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_818 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a21 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a25 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ))
    (a29 : -(h 0) < (-1/7 : ℝ))
    (a32 : -(h 1) < (-2/15 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_819 h delta _ctx _hno a19 a24 a29 a32 f0
  by_cases p1 : h 0 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_820 h delta _ctx _hno a14 a19 a21 a24 a32 f1
  by_cases p2 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_821 h delta _ctx _hno a14 a19 a24 a29 a32 f2
  by_cases p3 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f3 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_822 h delta _ctx _hno a14 a19 a24 a25 a29 a32 f3
  apply _hno 8
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_817 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a16 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a21 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a31 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/55 : ℝ) * a16 + (1/55 : ℝ) * a19 + (8/55 : ℝ) * a21 + (54/55 : ℝ) * a31
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_816 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ))
    (a30 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a25 + (1 : ℝ) * a30
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_815 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a16 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a20 : h 3 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a21 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a25 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    (a29 : -(h 0) < (-1/7 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_816 h delta _ctx _hno a25 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_817 h delta _ctx _hno a16 a19 a21 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_818 h delta _ctx _hno a14 a19 a21 a24 a25 a29 f2
  by_cases p3 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f3 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_829 h delta _ctx _hno a14 a16 a19 a20 a21 a24 a27 a29 f3
  by_cases p4 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_880 h delta _ctx _hno a14 a16 a19 a21 a24 a25 a27 a29 p2 p3 f4
  apply _hno 19
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_814 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a25 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ))
    (a28 : ((-2 : ℝ) * (delta)) < (-8/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a25 + (1 : ℝ) * a28
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_813 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a16 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a20 : h 3 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a21 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    (a25 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ))
    (a27 : -(h 1) < (-1/8 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (8/35 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-8/35 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_814 h delta _ctx _hno a25 f0
  by_cases p1 : h 0 ≤ (1/7 : ℝ)
  swap
  · have f1 : -(h 0) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_815 h delta _ctx _hno a14 a16 a19 a20 a21 a24 a25 a27 f1
  by_cases p2 : h 2 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 2) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_901 h delta _ctx _hno a14 a19 a24 f2
  by_cases p3 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f3 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_902 h delta _ctx _hno a14 a20 a24 a27 p1 f3
  apply _hno 33
  change (((2 : ℝ) * (delta)) ≤ (8/35 : ℝ)) ∧ (h 0 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem upper_node_812 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a16 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a21 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a26 : -(h 0) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/55 : ℝ) * a16 + (1/55 : ℝ) * a19 + (8/55 : ℝ) * a21 + (54/55 : ℝ) * a26
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_811 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a15 : h 5 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a25 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/9 : ℝ) * _ctx.min + (2/9 : ℝ) * a15 + (1 : ℝ) * a25
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_810 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a15 : h 5 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a16 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a20 : h 3 + ((8 : ℝ) * (delta)) ≤ (1 : ℝ))
    (a21 : ((6 : ℝ) * (h 0)) + h 3 ≤ (1 : ℝ))
    (a24 : -(h 3) + ((-8 : ℝ) * (h 4)) < (-1 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_811 h delta _ctx _hno a15 f0
  by_cases p1 : h 0 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_812 h delta _ctx _hno a16 a19 a21 f1
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_813 h delta _ctx _hno a14 a16 a19 a20 a21 a24 p0 f2
  apply _hno 3
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem upper_node_809 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a23 : ((-6 : ℝ) * (h 2)) + -(h 3) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (16/9 : ℝ) * _ctx.order0 + (32/9 : ℝ) * _ctx.order1 + (16/9 : ℝ) * _ctx.order4 + (31/9 : ℝ) * _ctx.min + (47/9 : ℝ) * _ctx.lower + (1/9 : ℝ) * a19 + (8/9 : ℝ) * a23 + (16/9 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_808 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a22 : ((-6 : ℝ) * (h 1)) + -(h 3) < (-1 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (702/1951 : ℝ) * _ctx.order0 + (2310/1951 : ℝ) * _ctx.order4 + (4394/1951 : ℝ) * _ctx.min + (385/1951 : ℝ) * _ctx.fail1 + (838/1951 : ℝ) * a14 + (226/1951 : ℝ) * a19 + (502/1951 : ℝ) * a22 + (2310/1951 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_807 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a21 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a24 : -(h 1) < (-1/8 : ℝ))
    (a33 : -(h 4) < (-4/35 : ℝ))
    (a38 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (131/618 : ℝ) * _ctx.order3 + (4/103 : ℝ) * _ctx.fail1 + (3/103 : ℝ) * a14 + (13/618 : ℝ) * a21 + (24/103 : ℝ) * a24 + (275/618 : ℝ) * a33 + (24/103 : ℝ) * a38 + (24/103 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_806 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a21 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a24 : -(h 1) < (-1/8 : ℝ))
    (a33 : -(h 4) < (-4/35 : ℝ))
    (a37 : -(h 3) < (-3/26 : ℝ))
    (a43 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/103 : ℝ) * _ctx.fail1 + (3/103 : ℝ) * a14 + (13/618 : ℝ) * a21 + (24/103 : ℝ) * a24 + (24/103 : ℝ) * a33 + (131/618 : ℝ) * a37 + (24/103 : ℝ) * a43 + (24/103 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_805 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a21 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a24 : -(h 1) < (-1/8 : ℝ))
    (a33 : -(h 4) < (-4/35 : ℝ))
    (a42 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (12/41 : ℝ) * _ctx.min + (2/41 : ℝ) * _ctx.fail1 + (3/41 : ℝ) * a14 + (5/246 : ℝ) * a21 + (12/41 : ℝ) * a24 + (12/41 : ℝ) * a33 + (67/246 : ℝ) * a42 + (12/41 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_804 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a21 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a24 : -(h 1) < (-1/8 : ℝ))
    (a33 : -(h 4) < (-4/35 : ℝ))
    (a37 : -(h 3) < (-3/26 : ℝ))
    (a41 : -(h 2) < (-33/278 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/17 : ℝ) * _ctx.min + (1/17 : ℝ) * a14 + (1/34 : ℝ) * a21 + (4/17 : ℝ) * a24 + (4/17 : ℝ) * a33 + (7/34 : ℝ) * a37 + (4/17 : ℝ) * a41 + (4/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_803 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : h 1 ≤ (9/70 : ℝ))
    (a40 : -(h 1) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_802 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a16 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a39 : -(h 0) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/48 : ℝ) * a14 + (1/6 : ℝ) * a16 + (47/48 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_801 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a21 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a24 : -(h 1) < (-1/8 : ℝ))
    (a33 : -(h 4) < (-4/35 : ℝ))
    (a37 : -(h 3) < (-3/26 : ℝ))
    (a38 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/25 : ℝ) * _ctx.min + (1/25 : ℝ) * _ctx.fail1 + (2/75 : ℝ) * a21 + (6/25 : ℝ) * a24 + (6/25 : ℝ) * a33 + (16/75 : ℝ) * a37 + (6/25 : ℝ) * a38 + (6/25 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_800 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a16 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a21 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a24 : -(h 1) < (-1/8 : ℝ))
    (a31 : h 1 ≤ (9/70 : ℝ))
    (a33 : -(h 4) < (-4/35 : ℝ))
    (a37 : -(h 3) < (-3/26 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_801 h delta _ctx _hno a21 a24 a33 a37 f0
  by_cases p1 : h 0 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_802 h delta _ctx _hno a14 a16 f1
  by_cases p2 : h 1 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_803 h delta _ctx _hno a31 f2
  by_cases p3 : h 2 ≤ (33/278 : ℝ)
  swap
  · have f3 : -(h 2) < (-33/278 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_804 h delta _ctx _hno a14 a21 a24 a33 a37 f3
  by_cases p4 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_805 h delta _ctx _hno a14 a21 a24 a33 f4
  by_cases p5 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact upper_node_806 h delta _ctx _hno a14 a21 a24 a33 a37 f5
  apply _hno 91
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 1 ≤ (3/23 : ℝ)) ∧ (h 2 ≤ (33/278 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem upper_node_799 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a31 : h 1 ≤ (9/70 : ℝ))
    (a36 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a36
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_798 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a16 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a35 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/48 : ℝ) * a14 + (1/6 : ℝ) * a16 + (47/48 : ℝ) * a35
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_797 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a22 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a22 + (1 : ℝ) * a34
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_796 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a16 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a21 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a22 : ((2 : ℝ) * (delta)) ≤ (7/32 : ℝ))
    (a24 : -(h 1) < (-1/8 : ℝ))
    (a31 : h 1 ≤ (9/70 : ℝ))
    (a33 : -(h 4) < (-4/35 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact upper_node_797 h delta _ctx _hno a22 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact upper_node_798 h delta _ctx _hno a14 a16 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact upper_node_799 h delta _ctx _hno a31 f2
  by_cases p3 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f3 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact upper_node_800 h delta _ctx _hno a14 a16 a21 a24 a31 a33 f3
  by_cases p4 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact upper_node_807 h delta _ctx _hno a14 a21 a24 a33 f4
  apply _hno 19
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem upper_node_795 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a21 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a24 : -(h 1) < (-1/8 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a32 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (49/191 : ℝ) * _ctx.min + (13/191 : ℝ) * a14 + (6/191 : ℝ) * a19 + (7/191 : ℝ) * a21 + (55/191 : ℝ) * a24 + (55/191 : ℝ) * a28 + (55/191 : ℝ) * a32 + (55/191 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_794 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a19 : ((-8 : ℝ) * (h 3)) + -(h 5) < (-1 : ℝ))
    (a21 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a31 : -(h 1) < (-9/70 : ℝ))
    (a36 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (24/487 : ℝ) * _ctx.fail1 + (18/487 : ℝ) * a14 + (131/3896 : ℝ) * a19 + (13/487 : ℝ) * a21 + (144/487 : ℝ) * a28 + (144/487 : ℝ) * a31 + (1021/3896 : ℝ) * a36 + (144/487 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_793 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a21 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a31 : -(h 1) < (-9/70 : ℝ))
    (a35 : -(h 3) < (-3/26 : ℝ))
    (a41 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/103 : ℝ) * _ctx.fail1 + (3/103 : ℝ) * a14 + (13/618 : ℝ) * a21 + (24/103 : ℝ) * a28 + (24/103 : ℝ) * a31 + (131/618 : ℝ) * a35 + (24/103 : ℝ) * a41 + (24/103 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_792 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a21 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a31 : -(h 1) < (-9/70 : ℝ))
    (a40 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (12/41 : ℝ) * _ctx.min + (2/41 : ℝ) * _ctx.fail1 + (3/41 : ℝ) * a14 + (5/246 : ℝ) * a21 + (12/41 : ℝ) * a28 + (12/41 : ℝ) * a31 + (67/246 : ℝ) * a40 + (12/41 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_791 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a21 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a31 : -(h 1) < (-9/70 : ℝ))
    (a35 : -(h 3) < (-3/26 : ℝ))
    (a39 : -(h 2) < (-33/278 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (4/17 : ℝ) * _ctx.min + (1/17 : ℝ) * a14 + (1/34 : ℝ) * a21 + (4/17 : ℝ) * a28 + (4/17 : ℝ) * a31 + (7/34 : ℝ) * a35 + (4/17 : ℝ) * a39 + (4/17 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_790 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a21 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a35 : -(h 3) < (-3/26 : ℝ))
    (a38 : -(h 1) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (12/41 : ℝ) * _ctx.min + (2/41 : ℝ) * _ctx.fail1 + (3/41 : ℝ) * a14 + (5/246 : ℝ) * a21 + (12/41 : ℝ) * a28 + (67/246 : ℝ) * a35 + (12/41 : ℝ) * a38 + (12/41 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_789 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a14 : -(h 0) + ((-8 : ℝ) * (delta)) < (-1 : ℝ))
    (a16 : ((6 : ℝ) * (h 0)) + h 5 ≤ (1 : ℝ))
    (a37 : -(h 0) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/48 : ℝ) * a14 + (1/6 : ℝ) * a16 + (47/48 : ℝ) * a37
  exact (lt_irrefl (0 : ℝ)) hbad

theorem upper_node_788 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : UpperLargestCtx h delta)
    (_hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta)
    (a21 : ((-6 : ℝ) * (h 0)) + -(h 3) < (-1 : ℝ))
    (a28 : -(h 4) < (-1/9 : ℝ))
    (a31 : -(h 1) < (-9/70 : ℝ))
    (a35 : -(h 3) < (-3/26 : ℝ))
    (a36 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (6/25 : ℝ) * _ctx.min + (1/25 : ℝ) * _ctx.fail1 + (2/75 : ℝ) * a21 + (6/25 : ℝ) * a28 + (6/25 : ℝ) * a31 + (16/75 : ℝ) * a35 + (6/25 : ℝ) * a36 + (6/25 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

end RealPinwheel.WeakSevenBandData
