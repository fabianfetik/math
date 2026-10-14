import Pinwheel.WeakSevenBandData.CoverChunks.New155

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem new_node_634 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a15 : -(h 0) < (-1/6 : ℝ))
    (a25 : -(h 1) < (-5/38 : ℝ))
    (a37 : -(h 2) < (-2/17 : ℝ))
    (a43 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a15 + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a37 + (1/3 : ℝ) * a43 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_633 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a15 : -(h 0) < (-1/6 : ℝ))
    (a25 : -(h 1) < (-5/38 : ℝ))
    (a29 : -(h 4) < (-3/29 : ℝ))
    (a37 : -(h 2) < (-2/17 : ℝ))
    (a42 : -(h 3) < (-9/80 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a15 + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a29 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_632 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a15 : -(h 0) < (-1/6 : ℝ))
    (a25 : -(h 1) < (-5/38 : ℝ))
    (a29 : -(h 4) < (-3/29 : ℝ))
    (a41 : -(h 2) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a15 + (1/6 : ℝ) * a25 + (1/3 : ℝ) * a29 + (1/6 : ℝ) * a41 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_631 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a15 : -(h 0) < (-1/6 : ℝ))
    (a28 : h 1 ≤ (4/29 : ℝ))
    (a29 : -(h 4) < (-3/29 : ℝ))
    (a34 : ((2 : ℝ) * (delta)) ≤ (7/34 : ℝ))
    (a37 : -(h 2) < (-2/17 : ℝ))
    (a39 : h 0 ≤ (12/71 : ℝ))
    (a40 : -(h 1) < (-2/15 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (9/44 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-9/44 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_671 h delta _ctx _hno a15 a28 a29 a34 a37 a39 a40 f0
  by_cases p1 : h 0 ≤ (3/17 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/17 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_672 h delta _ctx _hno a39 f1
  by_cases p2 : h 1 ≤ (3/22 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_673 h delta _ctx _hno a13 a15 a28 a29 a37 a39 p0 f2
  by_cases p3 : h 3 ≤ (1/9 : ℝ)
  swap
  · have f3 : -(h 3) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_674 h delta _ctx _hno a13 a15 a29 a37 a40 f3
  by_cases p4 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f4 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_675 h delta _ctx _hno a13 a15 a37 a40 f4
  apply _hno 48
  change (((2 : ℝ) * (delta)) ≤ (9/44 : ℝ)) ∧ (h 0 ≤ (3/17 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_630 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a25 : -(h 1) < (-5/38 : ℝ))
    (a28 : h 1 ≤ (4/29 : ℝ))
    (a29 : -(h 4) < (-3/29 : ℝ))
    (a31 : h 0 ≤ (6/35 : ℝ))
    (a34 : ((2 : ℝ) * (delta)) ≤ (7/34 : ℝ))
    (a37 : -(h 2) < (-2/17 : ℝ))
    (a39 : -(h 0) < (-12/71 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (9/44 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-9/44 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_635 h delta _ctx _hno a25 a28 a29 a31 a34 a37 a39 f0
  by_cases p1 : h 0 ≤ (3/17 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/17 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_636 h delta _ctx _hno a31 f1
  by_cases p2 : h 1 ≤ (3/22 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_637 h delta _ctx _hno a13 a28 a29 a31 a37 a39 f2
  by_cases p3 : h 3 ≤ (1/9 : ℝ)
  swap
  · have f3 : -(h 3) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_638 h delta _ctx _hno a13 a25 a29 a37 a39 f3
  by_cases p4 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f4 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_639 h delta _ctx _hno a13 a25 a37 a39 f4
  apply _hno 48
  change (((2 : ℝ) * (delta)) ≤ (9/44 : ℝ)) ∧ (h 0 ≤ (3/17 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_629 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : ((2 : ℝ) * (delta)) ≤ (7/34 : ℝ))
    (a38 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a38
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_628 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : -(h 0) < (-1/6 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a41 : -(h 1) < (-2/15 : ℝ))
    (a51 : -(h 2) < (-3/25 : ℝ))
    (a57 : -(h 5) < (-2/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order3 + (4/13 : ℝ) * _ctx.order4 + (2/13 : ℝ) * a15 + (1/13 : ℝ) * a34 + (2/13 : ℝ) * a41 + (2/13 : ℝ) * a51 + (6/13 : ℝ) * a57 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_627 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : -(h 0) < (-1/6 : ℝ))
    (a29 : -(h 4) < (-3/29 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a41 : -(h 1) < (-2/15 : ℝ))
    (a47 : -(h 5) < (-3/29 : ℝ))
    (a51 : -(h 2) < (-3/25 : ℝ))
    (a56 : -(h 3) < (-3/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * a15 + (2/13 : ℝ) * a29 + (1/13 : ℝ) * a34 + (2/13 : ℝ) * a41 + (2/13 : ℝ) * a47 + (2/13 : ℝ) * a51 + (2/13 : ℝ) * a56 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_626 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : -(h 0) < (-1/6 : ℝ))
    (a29 : -(h 4) < (-3/29 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a41 : -(h 1) < (-2/15 : ℝ))
    (a47 : -(h 5) < (-3/29 : ℝ))
    (a55 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order3 + (2/13 : ℝ) * a15 + (4/13 : ℝ) * a29 + (1/13 : ℝ) * a34 + (2/13 : ℝ) * a41 + (2/13 : ℝ) * a47 + (2/13 : ℝ) * a55 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_625 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a37 : h 1 ≤ (5/37 : ℝ))
    (a54 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a37 + (1 : ℝ) * a54
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_624 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a40 : h 0 ≤ (12/71 : ℝ))
    (a53 : -(h 0) < (-3/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a40 + (1 : ℝ) * a53
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_623 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a52 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a26 + (1 : ℝ) * a52
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_622 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : -(h 0) < (-1/6 : ℝ))
    (a29 : -(h 4) < (-3/29 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a38 : -(h 2) < (-2/17 : ℝ))
    (a41 : -(h 1) < (-2/15 : ℝ))
    (a47 : -(h 5) < (-3/29 : ℝ))
    (a52 : -(h 3) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * a15 + (2/13 : ℝ) * a29 + (1/13 : ℝ) * a34 + (2/13 : ℝ) * a38 + (2/13 : ℝ) * a41 + (2/13 : ℝ) * a47 + (2/13 : ℝ) * a52 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_621 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : -(h 0) < (-1/6 : ℝ))
    (a26 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a29 : -(h 4) < (-3/29 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a37 : h 1 ≤ (5/37 : ℝ))
    (a40 : h 0 ≤ (12/71 : ℝ))
    (a41 : -(h 1) < (-2/15 : ℝ))
    (a47 : -(h 5) < (-3/29 : ℝ))
    (a51 : -(h 2) < (-3/25 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_623 h delta _ctx _hno a26 f0
  by_cases p1 : h 0 ≤ (3/17 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/17 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_624 h delta _ctx _hno a40 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_625 h delta _ctx _hno a37 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_626 h delta _ctx _hno a15 a29 a34 a41 a47 f3
  by_cases p4 : h 3 ≤ (3/28 : ℝ)
  swap
  · have f4 : -(h 3) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_627 h delta _ctx _hno a15 a29 a34 a41 a47 a51 f4
  by_cases p5 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_628 h delta _ctx _hno a15 a34 a41 a51 f5
  apply _hno 5
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (3/17 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (3/28 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_620 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a37 : h 1 ≤ (5/37 : ℝ))
    (a50 : -(h 1) < (-5/36 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a37 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_619 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a40 : h 0 ≤ (12/71 : ℝ))
    (a49 : -(h 0) < (-6/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a40 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_618 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a48 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a26 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_617 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : -(h 0) < (-1/6 : ℝ))
    (a26 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a29 : -(h 4) < (-3/29 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a37 : h 1 ≤ (5/37 : ℝ))
    (a38 : -(h 2) < (-2/17 : ℝ))
    (a40 : h 0 ≤ (12/71 : ℝ))
    (a41 : -(h 1) < (-2/15 : ℝ))
    (a47 : -(h 5) < (-3/29 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_618 h delta _ctx _hno a26 f0
  by_cases p1 : h 0 ≤ (6/35 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/35 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_619 h delta _ctx _hno a40 f1
  by_cases p2 : h 1 ≤ (5/36 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/36 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_620 h delta _ctx _hno a37 f2
  by_cases p3 : h 2 ≤ (3/25 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_621 h delta _ctx _hno a15 a26 a29 a34 a37 a40 a41 a47 f3
  by_cases p4 : h 3 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_622 h delta _ctx _hno a15 a29 a34 a38 a41 a47 f4
  apply _hno 113
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (6/35 : ℝ)) ∧ (h 1 ≤ (5/36 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_616 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : -(h 0) < (-1/6 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a38 : -(h 2) < (-2/17 : ℝ))
    (a41 : -(h 1) < (-2/15 : ℝ))
    (a46 : -(h 3) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/11 : ℝ) * _ctx.order4 + (4/11 : ℝ) * _ctx.min + (2/11 : ℝ) * a15 + (3/11 : ℝ) * a34 + (2/11 : ℝ) * a38 + (2/11 : ℝ) * a41 + (2/11 : ℝ) * a46 + (2/11 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_615 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : -(h 0) < (-1/6 : ℝ))
    (a29 : -(h 4) < (-3/29 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a41 : -(h 1) < (-2/15 : ℝ))
    (a45 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a15 + (1/3 : ℝ) * a29 + (1/6 : ℝ) * a34 + (1/6 : ℝ) * a41 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_614 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a37 : h 1 ≤ (5/37 : ℝ))
    (a44 : -(h 1) < (-4/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a37 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_613 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a40 : h 0 ≤ (12/71 : ℝ))
    (a43 : -(h 0) < (-5/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a40 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_612 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a42 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a26 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_611 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a38 : -(h 2) < (-2/17 : ℝ))
    (a40 : -(h 0) < (-12/71 : ℝ))
    (a52 : -(h 1) < (-2/15 : ℝ))
    (a57 : -(h 3) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/11 : ℝ) * _ctx.order4 + (4/11 : ℝ) * _ctx.min + (3/11 : ℝ) * a34 + (2/11 : ℝ) * a38 + (2/11 : ℝ) * a40 + (2/11 : ℝ) * a52 + (2/11 : ℝ) * a57 + (2/11 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_610 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a29 : -(h 4) < (-3/29 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a40 : -(h 0) < (-12/71 : ℝ))
    (a49 : -(h 5) < (-3/29 : ℝ))
    (a52 : -(h 1) < (-2/15 : ℝ))
    (a56 : -(h 2) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order3 + (4/13 : ℝ) * a29 + (1/13 : ℝ) * a34 + (2/13 : ℝ) * a40 + (2/13 : ℝ) * a49 + (2/13 : ℝ) * a52 + (2/13 : ℝ) * a56 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_609 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a37 : h 1 ≤ (5/37 : ℝ))
    (a55 : -(h 1) < (-5/36 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a37 + (1 : ℝ) * a55
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_608 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a51 : h 0 ≤ (8/47 : ℝ))
    (a54 : -(h 0) < (-6/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a51 + (1 : ℝ) * a54
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_607 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a53 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a26 + (1 : ℝ) * a53
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_606 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a38 : -(h 2) < (-2/17 : ℝ))
    (a43 : -(h 1) < (-7/53 : ℝ))
    (a51 : -(h 0) < (-8/47 : ℝ))
    (a56 : -(h 3) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/11 : ℝ) * _ctx.order4 + (4/11 : ℝ) * _ctx.min + (3/11 : ℝ) * a34 + (2/11 : ℝ) * a38 + (2/11 : ℝ) * a43 + (2/11 : ℝ) * a51 + (2/11 : ℝ) * a56 + (2/11 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_605 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a29 : -(h 4) < (-3/29 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a43 : -(h 1) < (-7/53 : ℝ))
    (a49 : -(h 5) < (-3/29 : ℝ))
    (a51 : -(h 0) < (-8/47 : ℝ))
    (a55 : -(h 2) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order3 + (4/13 : ℝ) * a29 + (1/13 : ℝ) * a34 + (2/13 : ℝ) * a43 + (2/13 : ℝ) * a49 + (2/13 : ℝ) * a51 + (2/13 : ℝ) * a55 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_604 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a29 : -(h 4) < (-3/29 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a38 : -(h 2) < (-2/17 : ℝ))
    (a49 : -(h 5) < (-3/29 : ℝ))
    (a51 : -(h 0) < (-8/47 : ℝ))
    (a54 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order3 + (4/13 : ℝ) * a29 + (1/13 : ℝ) * a34 + (2/13 : ℝ) * a38 + (2/13 : ℝ) * a49 + (2/13 : ℝ) * a51 + (2/13 : ℝ) * a54 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_603 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a31 : h 0 ≤ (6/35 : ℝ))
    (a53 : -(h 0) < (-4/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a53
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_602 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a52 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a26 + (1 : ℝ) * a52
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_601 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a38 : -(h 2) < (-2/17 : ℝ))
    (a40 : -(h 0) < (-12/71 : ℝ))
    (a43 : -(h 1) < (-7/53 : ℝ))
    (a55 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a34 + (1/6 : ℝ) * a38 + (1/6 : ℝ) * a40 + (1/6 : ℝ) * a43 + (1/3 : ℝ) * a55 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_600 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a38 : -(h 2) < (-2/17 : ℝ))
    (a40 : -(h 0) < (-12/71 : ℝ))
    (a43 : -(h 1) < (-7/53 : ℝ))
    (a54 : -(h 3) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/11 : ℝ) * _ctx.order4 + (4/11 : ℝ) * _ctx.min + (3/11 : ℝ) * a34 + (2/11 : ℝ) * a38 + (2/11 : ℝ) * a40 + (2/11 : ℝ) * a43 + (2/11 : ℝ) * a54 + (2/11 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_599 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a29 : -(h 4) < (-3/29 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a40 : -(h 0) < (-12/71 : ℝ))
    (a43 : -(h 1) < (-7/53 : ℝ))
    (a49 : -(h 5) < (-3/29 : ℝ))
    (a53 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order3 + (4/13 : ℝ) * a29 + (1/13 : ℝ) * a34 + (2/13 : ℝ) * a40 + (2/13 : ℝ) * a43 + (2/13 : ℝ) * a49 + (2/13 : ℝ) * a53 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_598 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a29 : -(h 4) < (-3/29 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a37 : h 1 ≤ (5/37 : ℝ))
    (a38 : -(h 2) < (-2/17 : ℝ))
    (a40 : -(h 0) < (-12/71 : ℝ))
    (a49 : -(h 5) < (-3/29 : ℝ))
    (a51 : h 0 ≤ (8/47 : ℝ))
    (a52 : -(h 1) < (-2/15 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_607 h delta _ctx _hno a26 f0
  by_cases p1 : h 0 ≤ (6/35 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/35 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_608 h delta _ctx _hno a51 f1
  by_cases p2 : h 1 ≤ (5/36 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/36 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_609 h delta _ctx _hno a37 f2
  by_cases p3 : h 2 ≤ (3/25 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_610 h delta _ctx _hno a29 a34 a40 a49 a52 f3
  by_cases p4 : h 3 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_611 h delta _ctx _hno a34 a38 a40 a52 f4
  apply _hno 113
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (6/35 : ℝ)) ∧ (h 1 ≤ (5/36 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_597 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a29 : -(h 4) < (-3/29 : ℝ))
    (a31 : h 0 ≤ (6/35 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a38 : -(h 2) < (-2/17 : ℝ))
    (a43 : -(h 1) < (-7/53 : ℝ))
    (a49 : -(h 5) < (-3/29 : ℝ))
    (a51 : -(h 0) < (-8/47 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-3/14 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_602 h delta _ctx _hno a26 f0
  by_cases p1 : h 0 ≤ (4/23 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/23 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_603 h delta _ctx _hno a31 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_604 h delta _ctx _hno a29 a34 a38 a49 a51 f2
  by_cases p3 : h 2 ≤ (3/25 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_605 h delta _ctx _hno a29 a34 a43 a49 a51 f3
  by_cases p4 : h 3 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_606 h delta _ctx _hno a34 a38 a43 a51 f4
  apply _hno 197
  change (((2 : ℝ) * (delta)) ≤ (3/14 : ℝ)) ∧ (h 0 ≤ (4/23 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_596 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a50 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a26 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_595 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a29 : -(h 4) < (-3/29 : ℝ))
    (a31 : h 0 ≤ (6/35 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a37 : h 1 ≤ (5/37 : ℝ))
    (a38 : -(h 2) < (-2/17 : ℝ))
    (a40 : -(h 0) < (-12/71 : ℝ))
    (a43 : -(h 1) < (-7/53 : ℝ))
    (a49 : -(h 5) < (-3/29 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_596 h delta _ctx _hno a26 f0
  by_cases p1 : h 0 ≤ (8/47 : ℝ)
  swap
  · have f1 : -(h 0) < (-8/47 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_597 h delta _ctx _hno a26 a29 a31 a34 a38 a43 a49 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_598 h delta _ctx _hno a26 a29 a34 a37 a38 a40 a49 p1 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_599 h delta _ctx _hno a29 a34 a40 a43 a49 f3
  by_cases p4 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_600 h delta _ctx _hno a34 a38 a40 a43 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_601 h delta _ctx _hno a34 a38 a40 a43 f5
  apply _hno 71
  change (((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)) ∧ (h 0 ≤ (8/47 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_594 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a38 : -(h 2) < (-2/17 : ℝ))
    (a40 : -(h 0) < (-12/71 : ℝ))
    (a43 : -(h 1) < (-7/53 : ℝ))
    (a48 : -(h 3) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/11 : ℝ) * _ctx.order4 + (4/11 : ℝ) * _ctx.min + (3/11 : ℝ) * a34 + (2/11 : ℝ) * a38 + (2/11 : ℝ) * a40 + (2/11 : ℝ) * a43 + (2/11 : ℝ) * a48 + (2/11 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_593 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a29 : -(h 4) < (-3/29 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a40 : -(h 0) < (-12/71 : ℝ))
    (a43 : -(h 1) < (-7/53 : ℝ))
    (a47 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/3 : ℝ) * a29 + (1/6 : ℝ) * a34 + (1/6 : ℝ) * a40 + (1/6 : ℝ) * a43 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_592 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a37 : h 1 ≤ (5/37 : ℝ))
    (a46 : -(h 1) < (-4/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a37 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_591 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a31 : h 0 ≤ (6/35 : ℝ))
    (a45 : -(h 0) < (-5/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_590 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a44 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a26 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_589 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 1) < (-5/38 : ℝ))
    (a29 : -(h 4) < (-3/29 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a38 : -(h 2) < (-2/17 : ℝ))
    (a40 : -(h 0) < (-12/71 : ℝ))
    (a44 : -(h 3) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a29 + (1/6 : ℝ) * a34 + (1/6 : ℝ) * a38 + (1/6 : ℝ) * a40 + (1/6 : ℝ) * a44 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_588 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a29 : -(h 4) < (-3/29 : ℝ))
    (a31 : h 0 ≤ (6/35 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a37 : h 1 ≤ (5/37 : ℝ))
    (a38 : -(h 2) < (-2/17 : ℝ))
    (a40 : -(h 0) < (-12/71 : ℝ))
    (a43 : -(h 1) < (-7/53 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_590 h delta _ctx _hno a26 f0
  by_cases p1 : h 0 ≤ (5/29 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/29 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_591 h delta _ctx _hno a31 f1
  by_cases p2 : h 1 ≤ (4/29 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/29 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_592 h delta _ctx _hno a37 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_593 h delta _ctx _hno a29 a34 a40 a43 f3
  by_cases p4 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_594 h delta _ctx _hno a34 a38 a40 a43 f4
  by_cases p5 : h 5 ≤ (3/29 : ℝ)
  swap
  · have f5 : -(h 5) < (-3/29 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_595 h delta _ctx _hno a26 a29 a31 a34 a37 a38 a40 a43 f5
  apply _hno 89
  change (((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)) ∧ (h 0 ≤ (5/29 : ℝ)) ∧ (h 1 ≤ (4/29 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (3/29 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_587 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a31 : h 0 ≤ (6/35 : ℝ))
    (a42 : -(h 0) < (-3/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_586 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a26 + (1 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_585 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : -(h 0) < (-1/6 : ℝ))
    (a25 : -(h 1) < (-5/38 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a38 : -(h 2) < (-2/17 : ℝ))
    (a44 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a15 + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a34 + (1/6 : ℝ) * a38 + (1/3 : ℝ) * a44 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_584 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : -(h 0) < (-1/6 : ℝ))
    (a25 : -(h 1) < (-5/38 : ℝ))
    (a29 : -(h 4) < (-3/29 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a38 : -(h 2) < (-2/17 : ℝ))
    (a43 : -(h 3) < (-9/80 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a15 + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a29 + (1/6 : ℝ) * a34 + (1/6 : ℝ) * a38 + (1/6 : ℝ) * a43 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_583 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : -(h 0) < (-1/6 : ℝ))
    (a25 : -(h 1) < (-5/38 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a42 : -(h 2) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (2/5 : ℝ) * _ctx.order4 + (3/5 : ℝ) * _ctx.min + (1/5 : ℝ) * a15 + (1/5 : ℝ) * a25 + (2/5 : ℝ) * a34 + (1/5 : ℝ) * a42 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_582 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : -(h 0) < (-1/6 : ℝ))
    (a26 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a29 : -(h 4) < (-3/29 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a37 : h 1 ≤ (5/37 : ℝ))
    (a38 : -(h 2) < (-2/17 : ℝ))
    (a40 : h 0 ≤ (12/71 : ℝ))
    (a41 : -(h 1) < (-2/15 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_612 h delta _ctx _hno a26 f0
  by_cases p1 : h 0 ≤ (5/29 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/29 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_613 h delta _ctx _hno a40 f1
  by_cases p2 : h 1 ≤ (4/29 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/29 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_614 h delta _ctx _hno a37 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_615 h delta _ctx _hno a15 a29 a34 a41 f3
  by_cases p4 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_616 h delta _ctx _hno a15 a34 a38 a41 f4
  by_cases p5 : h 5 ≤ (3/29 : ℝ)
  swap
  · have f5 : -(h 5) < (-3/29 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_617 h delta _ctx _hno a15 a26 a29 a34 a37 a38 a40 a41 f5
  apply _hno 89
  change (((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)) ∧ (h 0 ≤ (5/29 : ℝ)) ∧ (h 1 ≤ (4/29 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (3/29 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_581 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 1) < (-5/38 : ℝ))
    (a26 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a29 : -(h 4) < (-3/29 : ℝ))
    (a31 : h 0 ≤ (6/35 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a37 : h 1 ≤ (5/37 : ℝ))
    (a38 : -(h 2) < (-2/17 : ℝ))
    (a40 : -(h 0) < (-12/71 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_586 h delta _ctx _hno a26 f0
  by_cases p1 : h 0 ≤ (3/17 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/17 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_587 h delta _ctx _hno a31 f1
  by_cases p2 : h 1 ≤ (7/53 : ℝ)
  swap
  · have f2 : -(h 1) < (-7/53 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_588 h delta _ctx _hno a26 a29 a31 a34 a37 a38 a40 f2
  by_cases p3 : h 3 ≤ (1/9 : ℝ)
  swap
  · have f3 : -(h 3) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_589 h delta _ctx _hno a25 a29 a34 a38 a40 f3
  apply _hno 73
  change (((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)) ∧ (h 0 ≤ (3/17 : ℝ)) ∧ (h 1 ≤ (7/53 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_580 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a39 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a26 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_579 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : -(h 0) < (-1/6 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a37 : -(h 1) < (-5/37 : ℝ))
    (a41 : -(h 2) < (-2/17 : ℝ))
    (a52 : -(h 3) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/11 : ℝ) * _ctx.order4 + (4/11 : ℝ) * _ctx.min + (2/11 : ℝ) * a15 + (3/11 : ℝ) * a34 + (2/11 : ℝ) * a37 + (2/11 : ℝ) * a41 + (2/11 : ℝ) * a52 + (2/11 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_578 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : -(h 0) < (-1/6 : ℝ))
    (a29 : -(h 4) < (-3/29 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a37 : -(h 1) < (-5/37 : ℝ))
    (a47 : -(h 5) < (-3/29 : ℝ))
    (a51 : -(h 2) < (-3/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order3 + (2/13 : ℝ) * a15 + (4/13 : ℝ) * a29 + (1/13 : ℝ) * a34 + (2/13 : ℝ) * a37 + (2/13 : ℝ) * a47 + (2/13 : ℝ) * a51 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_577 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a28 : h 1 ≤ (4/29 : ℝ))
    (a50 : -(h 1) < (-5/36 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a28 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_576 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a29 : -(h 4) < (-3/29 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a37 : -(h 1) < (-5/37 : ℝ))
    (a41 : -(h 2) < (-2/17 : ℝ))
    (a47 : -(h 5) < (-3/29 : ℝ))
    (a49 : -(h 0) < (-6/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order3 + (4/13 : ℝ) * a29 + (1/13 : ℝ) * a34 + (2/13 : ℝ) * a37 + (2/13 : ℝ) * a41 + (2/13 : ℝ) * a47 + (2/13 : ℝ) * a49 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_575 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a48 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a26 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_574 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : -(h 0) < (-1/6 : ℝ))
    (a26 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a28 : h 1 ≤ (4/29 : ℝ))
    (a29 : -(h 4) < (-3/29 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a37 : -(h 1) < (-5/37 : ℝ))
    (a41 : -(h 2) < (-2/17 : ℝ))
    (a47 : -(h 5) < (-3/29 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_575 h delta _ctx _hno a26 f0
  by_cases p1 : h 0 ≤ (6/35 : ℝ)
  swap
  · have f1 : -(h 0) < (-6/35 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_576 h delta _ctx _hno a29 a34 a37 a41 a47 f1
  by_cases p2 : h 1 ≤ (5/36 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/36 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_577 h delta _ctx _hno a28 f2
  by_cases p3 : h 2 ≤ (3/25 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_578 h delta _ctx _hno a15 a29 a34 a37 a47 f3
  by_cases p4 : h 3 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_579 h delta _ctx _hno a15 a34 a37 a41 f4
  apply _hno 113
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (6/35 : ℝ)) ∧ (h 1 ≤ (5/36 : ℝ)) ∧ (h 2 ≤ (3/25 : ℝ)) ∧ (h 3 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_573 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : -(h 0) < (-1/6 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a37 : -(h 1) < (-5/37 : ℝ))
    (a41 : -(h 2) < (-2/17 : ℝ))
    (a46 : -(h 3) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/11 : ℝ) * _ctx.order4 + (4/11 : ℝ) * _ctx.min + (2/11 : ℝ) * a15 + (3/11 : ℝ) * a34 + (2/11 : ℝ) * a37 + (2/11 : ℝ) * a41 + (2/11 : ℝ) * a46 + (2/11 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_572 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : -(h 0) < (-1/6 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a37 : -(h 1) < (-5/37 : ℝ))
    (a45 : -(h 2) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order3 + (2/5 : ℝ) * _ctx.order4 + (3/5 : ℝ) * _ctx.min + (1/5 : ℝ) * a15 + (2/5 : ℝ) * a34 + (1/5 : ℝ) * a37 + (1/5 : ℝ) * a45 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_571 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : -(h 0) < (-1/6 : ℝ))
    (a29 : -(h 4) < (-3/29 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a41 : -(h 2) < (-2/17 : ℝ))
    (a44 : -(h 1) < (-4/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a15 + (1/3 : ℝ) * a29 + (1/6 : ℝ) * a34 + (1/6 : ℝ) * a41 + (1/6 : ℝ) * a44 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_570 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a31 : h 0 ≤ (6/35 : ℝ))
    (a43 : -(h 0) < (-5/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_569 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a42 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a26 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_568 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : -(h 0) < (-1/6 : ℝ))
    (a33 : -(h 2) < (-4/35 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a37 : -(h 1) < (-5/37 : ℝ))
    (a42 : -(h 4) < (-3/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a15 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a34 + (1/6 : ℝ) * a37 + (1/3 : ℝ) * a42 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_567 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : -(h 0) < (-1/6 : ℝ))
    (a26 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a28 : h 1 ≤ (4/29 : ℝ))
    (a29 : -(h 4) < (-3/29 : ℝ))
    (a31 : h 0 ≤ (6/35 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a37 : -(h 1) < (-5/37 : ℝ))
    (a41 : -(h 2) < (-2/17 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_569 h delta _ctx _hno a26 f0
  by_cases p1 : h 0 ≤ (5/29 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/29 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_570 h delta _ctx _hno a31 f1
  by_cases p2 : h 1 ≤ (4/29 : ℝ)
  swap
  · have f2 : -(h 1) < (-4/29 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_571 h delta _ctx _hno a15 a29 a34 a41 f2
  by_cases p3 : h 2 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 2) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_572 h delta _ctx _hno a15 a34 a37 f3
  by_cases p4 : h 3 ≤ (4/35 : ℝ)
  swap
  · have f4 : -(h 3) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_573 h delta _ctx _hno a15 a34 a37 a41 f4
  by_cases p5 : h 5 ≤ (3/29 : ℝ)
  swap
  · have f5 : -(h 5) < (-3/29 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_574 h delta _ctx _hno a15 a26 a28 a29 a34 a37 a41 f5
  apply _hno 89
  change (((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)) ∧ (h 0 ≤ (5/29 : ℝ)) ∧ (h 1 ≤ (4/29 : ℝ)) ∧ (h 2 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (4/35 : ℝ)) ∧ (h 5 ≤ (3/29 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_566 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a28 : h 1 ≤ (4/29 : ℝ))
    (a40 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a28 + (1 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_565 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a31 : h 0 ≤ (6/35 : ℝ))
    (a39 : -(h 0) < (-5/28 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_564 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a38 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a26 + (1 : ℝ) * a38
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_563 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : -(h 0) < (-1/6 : ℝ))
    (a25 : -(h 1) < (-5/38 : ℝ))
    (a33 : -(h 2) < (-4/35 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a41 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/13 : ℝ) * _ctx.order3 + (4/13 : ℝ) * _ctx.order4 + (2/13 : ℝ) * a15 + (2/13 : ℝ) * a25 + (2/13 : ℝ) * a33 + (1/13 : ℝ) * a34 + (6/13 : ℝ) * a41 + (2/13 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_562 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : -(h 0) < (-1/6 : ℝ))
    (a25 : -(h 1) < (-5/38 : ℝ))
    (a33 : -(h 2) < (-4/35 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a40 : -(h 4) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a15 + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a33 + (1/6 : ℝ) * a34 + (1/3 : ℝ) * a40 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_561 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : -(h 0) < (-1/6 : ℝ))
    (a25 : -(h 1) < (-5/38 : ℝ))
    (a29 : -(h 4) < (-3/29 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a39 : -(h 3) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order2 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a15 + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a29 + (1/6 : ℝ) * a34 + (1/3 : ℝ) * a39 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_560 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : -(h 0) < (-1/6 : ℝ))
    (a25 : -(h 1) < (-5/38 : ℝ))
    (a26 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a29 : -(h 4) < (-3/29 : ℝ))
    (a31 : h 0 ≤ (6/35 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a37 : h 1 ≤ (5/37 : ℝ))
    (a38 : -(h 2) < (-2/17 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-6/29 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_580 h delta _ctx _hno a26 f0
  by_cases p1 : h 0 ≤ (12/71 : ℝ)
  swap
  · have f1 : -(h 0) < (-12/71 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_581 h delta _ctx _hno a25 a26 a29 a31 a34 a37 a38 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_582 h delta _ctx _hno a15 a26 a29 a34 a37 a38 p1 f2
  by_cases p3 : h 2 ≤ (3/23 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_583 h delta _ctx _hno a15 a25 a34 f3
  by_cases p4 : h 3 ≤ (9/80 : ℝ)
  swap
  · have f4 : -(h 3) < (-9/80 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_584 h delta _ctx _hno a15 a25 a29 a34 a38 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_585 h delta _ctx _hno a15 a25 a34 a38 f5
  apply _hno 149
  change (((2 : ℝ) * (delta)) ≤ (6/29 : ℝ)) ∧ (h 0 ≤ (12/71 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (9/80 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_559 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a15 : -(h 0) < (-1/6 : ℝ))
    (a26 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a28 : h 1 ≤ (4/29 : ℝ))
    (a29 : -(h 4) < (-3/29 : ℝ))
    (a31 : h 0 ≤ (6/35 : ℝ))
    (a33 : -(h 2) < (-4/35 : ℝ))
    (a34 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    (a37 : -(h 1) < (-5/37 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_564 h delta _ctx _hno a26 f0
  by_cases p1 : h 0 ≤ (5/28 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/28 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_565 h delta _ctx _hno a31 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_566 h delta _ctx _hno a28 f2
  by_cases p3 : h 2 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 2) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_567 h delta _ctx _hno a15 a26 a28 a29 a31 a34 a37 f3
  by_cases p4 : h 4 ≤ (3/28 : ℝ)
  swap
  · have f4 : -(h 4) < (-3/28 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_568 h delta _ctx _hno a15 a33 a34 a37 f4
  apply _hno 83
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (5/28 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (2/17 : ℝ)) ∧ (h 4 ≤ (3/28 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_558 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a31 : h 0 ≤ (6/35 : ℝ))
    (a36 : -(h 0) < (-4/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a31 + (1 : ℝ) * a36
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_557 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a26 : ((2 : ℝ) * (delta)) ≤ (6/29 : ℝ))
    (a35 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a26 + (1 : ℝ) * a35
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_556 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a15 : -(h 0) < (-1/6 : ℝ))
    (a25 : -(h 1) < (-5/38 : ℝ))
    (a33 : -(h 2) < (-4/35 : ℝ))
    (a39 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a15 + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a33 + (1/3 : ℝ) * a39 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_555 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((-2 : ℝ) * (delta)) < (-12/59 : ℝ))
    (a15 : -(h 0) < (-1/6 : ℝ))
    (a25 : -(h 1) < (-5/38 : ℝ))
    (a29 : -(h 4) < (-3/29 : ℝ))
    (a38 : -(h 3) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order2 + (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a13 + (1/6 : ℝ) * a15 + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a29 + (1/3 : ℝ) * a38 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

end RealPinwheel.WeakSevenBandData
