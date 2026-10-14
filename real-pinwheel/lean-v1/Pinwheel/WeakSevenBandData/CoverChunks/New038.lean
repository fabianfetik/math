import Pinwheel.WeakSevenBandData.CoverChunks.New037

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem new_node_10074 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a30 : -(h 4) < (-4/37 : ℝ))
    (a45 : -(h 3) < (-5/43 : ℝ))
    (a49 : -(h 2) < (-3/23 : ℝ))
    (a51 : -(h 0) < (-4/27 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order1 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a30 + (1/5 : ℝ) * a45 + (2/5 : ℝ) * a49 + (1/5 : ℝ) * a51 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10073 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a50 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10072 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a38 : -(h 2) < (-7/54 : ℝ))
    (a40 : -(h 0) < (-5/34 : ℝ))
    (a45 : -(h 3) < (-5/43 : ℝ))
    (a48 : -(h 1) < (-5/38 : ℝ))
    (a58 : -(h 5) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order4 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a38 + (1/6 : ℝ) * a40 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a48 + (1/3 : ℝ) * a58 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10071 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a38 : -(h 2) < (-7/54 : ℝ))
    (a40 : -(h 0) < (-5/34 : ℝ))
    (a48 : -(h 1) < (-5/38 : ℝ))
    (a53 : -(h 4) < (-5/46 : ℝ))
    (a57 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a38 + (1/5 : ℝ) * a40 + (1/5 : ℝ) * a48 + (1/5 : ℝ) * a53 + (1/5 : ℝ) * a57 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10070 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : h 1 ≤ (2/15 : ℝ))
    (a56 : -(h 1) < (-3/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a24 + (1 : ℝ) * a56
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10069 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a38 : -(h 2) < (-7/54 : ℝ))
    (a45 : -(h 3) < (-5/43 : ℝ))
    (a48 : -(h 1) < (-5/38 : ℝ))
    (a53 : -(h 4) < (-5/46 : ℝ))
    (a55 : -(h 0) < (-4/27 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a38 + (1/5 : ℝ) * a45 + (1/5 : ℝ) * a48 + (1/5 : ℝ) * a53 + (1/5 : ℝ) * a55 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10068 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a54 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a54
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10067 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a30 : -(h 4) < (-4/37 : ℝ))
    (a38 : -(h 2) < (-7/54 : ℝ))
    (a40 : -(h 0) < (-5/34 : ℝ))
    (a45 : -(h 3) < (-5/43 : ℝ))
    (a48 : -(h 1) < (-5/38 : ℝ))
    (a54 : -(h 5) < (-4/37 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a38 + (1/6 : ℝ) * a40 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a48 + (1/6 : ℝ) * a54 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10066 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a24 : h 1 ≤ (2/15 : ℝ))
    (a38 : -(h 2) < (-7/54 : ℝ))
    (a40 : -(h 0) < (-5/34 : ℝ))
    (a45 : -(h 3) < (-5/43 : ℝ))
    (a48 : -(h 1) < (-5/38 : ℝ))
    (a53 : -(h 4) < (-5/46 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_10068 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (4/27 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/27 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_10069 h delta _ctx _hno a38 a45 a48 a53 f1
  by_cases p2 : h 1 ≤ (3/22 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_10070 h delta _ctx _hno a24 f2
  by_cases p3 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_10071 h delta _ctx _hno a38 a40 a48 a53 f3
  by_cases p4 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_10072 h delta _ctx _hno a38 a40 a45 a48 f4
  apply _hno 108
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (4/27 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_10065 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a30 : -(h 4) < (-4/37 : ℝ))
    (a38 : -(h 2) < (-7/54 : ℝ))
    (a40 : -(h 0) < (-5/34 : ℝ))
    (a48 : -(h 1) < (-5/38 : ℝ))
    (a52 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a30 + (1/5 : ℝ) * a38 + (1/5 : ℝ) * a40 + (1/5 : ℝ) * a48 + (1/5 : ℝ) * a52 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10064 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a30 : -(h 4) < (-4/37 : ℝ))
    (a40 : -(h 0) < (-5/34 : ℝ))
    (a45 : -(h 3) < (-5/43 : ℝ))
    (a48 : -(h 1) < (-5/38 : ℝ))
    (a51 : -(h 2) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a30 + (1/5 : ℝ) * a40 + (1/5 : ℝ) * a45 + (1/5 : ℝ) * a48 + (1/5 : ℝ) * a51 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10063 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a30 : -(h 4) < (-4/37 : ℝ))
    (a38 : -(h 2) < (-7/54 : ℝ))
    (a45 : -(h 3) < (-5/43 : ℝ))
    (a48 : -(h 1) < (-5/38 : ℝ))
    (a50 : -(h 0) < (-4/27 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a30 + (1/5 : ℝ) * a38 + (1/5 : ℝ) * a45 + (1/5 : ℝ) * a48 + (1/5 : ℝ) * a50 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10062 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a49 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10061 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a30 : -(h 4) < (-4/37 : ℝ))
    (a35 : -(h 1) < (-3/23 : ℝ))
    (a38 : -(h 2) < (-7/54 : ℝ))
    (a40 : -(h 0) < (-5/34 : ℝ))
    (a45 : -(h 3) < (-5/43 : ℝ))
    (a51 : -(h 5) < (-2/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a38 + (1/6 : ℝ) * a40 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a51 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10060 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a30 : -(h 4) < (-4/37 : ℝ))
    (a35 : -(h 1) < (-3/23 : ℝ))
    (a38 : -(h 2) < (-7/54 : ℝ))
    (a40 : -(h 0) < (-5/34 : ℝ))
    (a50 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a30 + (1/5 : ℝ) * a35 + (1/5 : ℝ) * a38 + (1/5 : ℝ) * a40 + (1/5 : ℝ) * a50 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10059 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a30 : -(h 4) < (-4/37 : ℝ))
    (a35 : -(h 1) < (-3/23 : ℝ))
    (a40 : -(h 0) < (-5/34 : ℝ))
    (a45 : -(h 3) < (-5/43 : ℝ))
    (a48 : h 1 ≤ (5/38 : ℝ))
    (a49 : -(h 2) < (-3/23 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_10073 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (4/27 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/27 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_10074 h delta _ctx _hno a30 a45 a49 f1
  by_cases p2 : h 1 ≤ (3/22 : ℝ)
  swap
  · have f2 : -(h 1) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_10075 h delta _ctx _hno a48 f2
  by_cases p3 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f3 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_10076 h delta _ctx _hno a30 a40 a49 f3
  by_cases p4 : h 5 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 5) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_10077 h delta _ctx _hno a35 a40 a45 a49 f4
  apply _hno 108
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (4/27 : ℝ)) ∧ (h 1 ≤ (3/22 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_10058 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a24 : h 1 ≤ (2/15 : ℝ))
    (a30 : -(h 4) < (-4/37 : ℝ))
    (a38 : -(h 2) < (-7/54 : ℝ))
    (a40 : -(h 0) < (-5/34 : ℝ))
    (a45 : -(h 3) < (-5/43 : ℝ))
    (a48 : -(h 1) < (-5/38 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/23 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_10062 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (4/27 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/27 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_10063 h delta _ctx _hno a30 a38 a45 a48 f1
  by_cases p2 : h 2 ≤ (3/23 : ℝ)
  swap
  · have f2 : -(h 2) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_10064 h delta _ctx _hno a30 a40 a45 a48 f2
  by_cases p3 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_10065 h delta _ctx _hno a30 a38 a40 a48 f3
  by_cases p4 : h 4 ≤ (5/46 : ℝ)
  swap
  · have f4 : -(h 4) < (-5/46 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_10066 h delta _ctx _hno a13 a24 a38 a40 a45 a48 f4
  by_cases p5 : h 5 ≤ (4/37 : ℝ)
  swap
  · have f5 : -(h 5) < (-4/37 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_10067 h delta _ctx _hno a30 a38 a40 a45 a48 f5
  apply _hno 55
  change (((2 : ℝ) * (delta)) ≤ (5/23 : ℝ)) ∧ (h 0 ≤ (4/27 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (5/46 : ℝ)) ∧ (h 5 ≤ (4/37 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_10057 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a37 : h 0 ≤ (4/27 : ℝ))
    (a47 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a37 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10056 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a46 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10055 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a24 : h 1 ≤ (2/15 : ℝ))
    (a35 : -(h 1) < (-3/23 : ℝ))
    (a37 : h 0 ≤ (4/27 : ℝ))
    (a38 : -(h 2) < (-7/54 : ℝ))
    (a40 : -(h 0) < (-5/34 : ℝ))
    (a45 : h 3 ≤ (5/43 : ℝ))
    (a46 : -(h 4) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_10078 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_10079 h delta _ctx _hno a37 f1
  by_cases p2 : h 1 ≤ (5/38 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/38 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_10080 h delta _ctx _hno a13 a24 a37 a38 a40 a46 f2
  by_cases p3 : h 2 ≤ (3/23 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_10081 h delta _ctx _hno a13 a37 a40 a46 p2 f3
  by_cases p4 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_10082 h delta _ctx _hno a45 f4
  by_cases p5 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_10083 h delta _ctx _hno a35 a38 a40 a46 f5
  apply _hno 30
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (5/38 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_10054 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a24 : h 1 ≤ (2/15 : ℝ))
    (a30 : -(h 4) < (-4/37 : ℝ))
    (a35 : -(h 1) < (-3/23 : ℝ))
    (a37 : h 0 ≤ (4/27 : ℝ))
    (a38 : -(h 2) < (-7/54 : ℝ))
    (a40 : -(h 0) < (-5/34 : ℝ))
    (a45 : -(h 3) < (-5/43 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_10056 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_10057 h delta _ctx _hno a37 f1
  by_cases p2 : h 1 ≤ (5/38 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/38 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_10058 h delta _ctx _hno a13 a24 a30 a38 a40 a45 f2
  by_cases p3 : h 2 ≤ (3/23 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_10059 h delta _ctx _hno a13 a30 a35 a40 a45 p2 f3
  by_cases p4 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_10060 h delta _ctx _hno a30 a35 a38 a40 f4
  by_cases p5 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_10061 h delta _ctx _hno a30 a35 a38 a40 a45 f5
  apply _hno 30
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (5/38 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_10053 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a29 : h 2 ≤ (2/15 : ℝ))
    (a44 : -(h 2) < (-3/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10052 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : h 1 ≤ (2/15 : ℝ))
    (a43 : -(h 1) < (-6/43 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a24 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10051 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a37 : h 0 ≤ (4/27 : ℝ))
    (a42 : -(h 0) < (-5/31 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a37 + (1 : ℝ) * a42
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10050 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a41 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10049 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a32 : -(h 0) < (-1/7 : ℝ))
    (a35 : -(h 1) < (-3/23 : ℝ))
    (a38 : -(h 2) < (-7/54 : ℝ))
    (a43 : -(h 5) < (-3/26 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.order3 + (1/3 : ℝ) * _ctx.order4 + (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a32 + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a38 + (1/2 : ℝ) * a43 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10048 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a24 : h 1 ≤ (2/15 : ℝ))
    (a30 : -(h 4) < (-4/37 : ℝ))
    (a32 : -(h 0) < (-1/7 : ℝ))
    (a35 : -(h 1) < (-3/23 : ℝ))
    (a38 : -(h 2) < (-7/54 : ℝ))
    (a40 : h 0 ≤ (5/34 : ℝ))
    (a42 : -(h 3) < (-2/17 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_10092 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_10093 h delta _ctx _hno a40 f1
  by_cases p2 : h 1 ≤ (5/38 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/38 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_10094 h delta _ctx _hno a13 a24 a32 a38 a40 a42 f2
  by_cases p3 : h 2 ≤ (3/23 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_10095 h delta _ctx _hno a13 a32 a35 a40 a42 p2 f3
  by_cases p4 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_10096 h delta _ctx _hno a30 a32 a35 a38 f4
  by_cases p5 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_10097 h delta _ctx _hno a30 a32 a35 a38 a42 f5
  apply _hno 30
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (5/38 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_10047 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : h 1 ≤ (2/15 : ℝ))
    (a41 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a24 + (1 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10046 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a24 : h 1 ≤ (2/15 : ℝ))
    (a29 : h 2 ≤ (2/15 : ℝ))
    (a30 : -(h 4) < (-4/37 : ℝ))
    (a35 : -(h 1) < (-3/23 : ℝ))
    (a37 : h 0 ≤ (4/27 : ℝ))
    (a38 : -(h 2) < (-7/54 : ℝ))
    (a40 : -(h 0) < (-5/34 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_10050 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (5/31 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/31 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_10051 h delta _ctx _hno a37 f1
  by_cases p2 : h 1 ≤ (6/43 : ℝ)
  swap
  · have f2 : -(h 1) < (-6/43 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_10052 h delta _ctx _hno a24 f2
  by_cases p3 : h 2 ≤ (3/22 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/22 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_10053 h delta _ctx _hno a29 f3
  by_cases p4 : h 3 ≤ (5/43 : ℝ)
  swap
  · have f4 : -(h 3) < (-5/43 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_10054 h delta _ctx _hno a13 a24 a30 a35 a37 a38 a40 f4
  by_cases p5 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f5 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_10055 h delta _ctx _hno a13 a24 a35 a37 a38 a40 p4 f5
  apply _hno 228
  change (((2 : ℝ) * (delta)) ≤ (5/24 : ℝ)) ∧ (h 0 ≤ (5/31 : ℝ)) ∧ (h 1 ≤ (6/43 : ℝ)) ∧ (h 2 ≤ (3/22 : ℝ)) ∧ (h 3 ≤ (5/43 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_10045 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a39 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10044 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 2) < (-1/8 : ℝ))
    (a37 : -(h 0) < (-4/27 : ℝ))
    (a47 : -(h 3) < (-3/26 : ℝ))
    (a50 : -(h 1) < (-5/38 : ℝ))
    (a56 : -(h 4) < (-4/35 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a25 + (1/5 : ℝ) * a37 + (1/5 : ℝ) * a47 + (1/5 : ℝ) * a50 + (1/5 : ℝ) * a56 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10043 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a42 : h 3 ≤ (5/43 : ℝ))
    (a55 : -(h 3) < (-5/43 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a42 + (1 : ℝ) * a55
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10042 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a37 : -(h 0) < (-4/27 : ℝ))
    (a43 : -(h 4) < (-1/9 : ℝ))
    (a47 : -(h 3) < (-3/26 : ℝ))
    (a50 : -(h 1) < (-5/38 : ℝ))
    (a54 : -(h 2) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a37 + (1/5 : ℝ) * a43 + (1/5 : ℝ) * a47 + (1/5 : ℝ) * a50 + (1/5 : ℝ) * a54 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10041 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : h 1 ≤ (2/15 : ℝ))
    (a53 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a24 + (1 : ℝ) * a53
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10040 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : h 0 ≤ (3/20 : ℝ))
    (a52 : -(h 0) < (-4/25 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a52
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10039 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a51 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a51
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10038 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 2) < (-1/8 : ℝ))
    (a35 : -(h 1) < (-3/23 : ℝ))
    (a37 : -(h 0) < (-4/27 : ℝ))
    (a43 : -(h 4) < (-1/9 : ℝ))
    (a47 : -(h 3) < (-3/26 : ℝ))
    (a53 : -(h 5) < (-2/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a43 + (1/6 : ℝ) * a47 + (1/6 : ℝ) * a53 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10037 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a42 : h 3 ≤ (5/43 : ℝ))
    (a52 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a42 + (1 : ℝ) * a52
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10036 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a37 : -(h 0) < (-4/27 : ℝ))
    (a43 : -(h 4) < (-1/9 : ℝ))
    (a47 : -(h 3) < (-3/26 : ℝ))
    (a51 : -(h 2) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order1 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a37 + (1/5 : ℝ) * a43 + (1/5 : ℝ) * a47 + (2/5 : ℝ) * a51 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10035 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a24 : h 1 ≤ (2/15 : ℝ))
    (a25 : -(h 2) < (-1/8 : ℝ))
    (a34 : h 0 ≤ (3/20 : ℝ))
    (a37 : -(h 0) < (-4/27 : ℝ))
    (a42 : h 3 ≤ (5/43 : ℝ))
    (a43 : -(h 4) < (-1/9 : ℝ))
    (a47 : -(h 3) < (-3/26 : ℝ))
    (a50 : -(h 1) < (-5/38 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-7/34 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_10039 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (4/25 : ℝ)
  swap
  · have f1 : -(h 0) < (-4/25 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_10040 h delta _ctx _hno a34 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_10041 h delta _ctx _hno a24 f2
  by_cases p3 : h 2 ≤ (3/23 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_10042 h delta _ctx _hno a37 a43 a47 a50 f3
  by_cases p4 : h 3 ≤ (5/43 : ℝ)
  swap
  · have f4 : -(h 3) < (-5/43 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_10043 h delta _ctx _hno a42 f4
  by_cases p5 : h 4 ≤ (4/35 : ℝ)
  swap
  · have f5 : -(h 4) < (-4/35 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_10044 h delta _ctx _hno a25 a37 a47 a50 f5
  apply _hno 45
  change (((2 : ℝ) * (delta)) ≤ (7/34 : ℝ)) ∧ (h 0 ≤ (4/25 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (5/43 : ℝ)) ∧ (h 4 ≤ (4/35 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_10034 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : h 0 ≤ (3/20 : ℝ))
    (a49 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10033 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a48 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10032 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a24 : h 1 ≤ (2/15 : ℝ))
    (a25 : -(h 2) < (-1/8 : ℝ))
    (a34 : h 0 ≤ (3/20 : ℝ))
    (a35 : -(h 1) < (-3/23 : ℝ))
    (a37 : -(h 0) < (-4/27 : ℝ))
    (a42 : h 3 ≤ (5/43 : ℝ))
    (a43 : -(h 4) < (-1/9 : ℝ))
    (a47 : -(h 3) < (-3/26 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_10033 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_10034 h delta _ctx _hno a34 f1
  by_cases p2 : h 1 ≤ (5/38 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/38 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_10035 h delta _ctx _hno a13 a24 a25 a34 a37 a42 a43 a47 f2
  by_cases p3 : h 2 ≤ (3/23 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_10036 h delta _ctx _hno a37 a43 a47 f3
  by_cases p4 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_10037 h delta _ctx _hno a42 f4
  by_cases p5 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_10038 h delta _ctx _hno a25 a35 a37 a43 a47 f5
  apply _hno 30
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (5/38 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_10031 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : h 1 ≤ (2/15 : ℝ))
    (a46 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a24 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10030 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : h 0 ≤ (3/20 : ℝ))
    (a45 : -(h 0) < (-3/20 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a45
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10029 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a44 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10028 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 2) < (-1/8 : ℝ))
    (a35 : -(h 1) < (-3/23 : ℝ))
    (a37 : -(h 0) < (-4/27 : ℝ))
    (a42 : -(h 3) < (-5/43 : ℝ))
    (a48 : -(h 5) < (-2/19 : ℝ))
    (a53 : -(h 4) < (-1/9 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a48 + (1/6 : ℝ) * a53 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10027 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 2) < (-1/8 : ℝ))
    (a30 : -(h 4) < (-4/37 : ℝ))
    (a35 : -(h 1) < (-3/23 : ℝ))
    (a37 : -(h 0) < (-4/27 : ℝ))
    (a48 : -(h 5) < (-2/19 : ℝ))
    (a52 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a30 + (1/6 : ℝ) * a35 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a48 + (1/6 : ℝ) * a52 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10026 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a45 : h 1 ≤ (5/38 : ℝ))
    (a51 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a45 + (1 : ℝ) * a51
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10025 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : h 0 ≤ (3/20 : ℝ))
    (a50 : -(h 0) < (-3/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a50
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10024 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a49 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a49
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10023 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 2) < (-1/8 : ℝ))
    (a42 : -(h 3) < (-5/43 : ℝ))
    (a45 : -(h 1) < (-5/38 : ℝ))
    (a50 : -(h 4) < (-1/9 : ℝ))
    (a52 : -(h 0) < (-10/67 : ℝ))
    (a58 : -(h 5) < (-2/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a50 + (1/6 : ℝ) * a52 + (1/6 : ℝ) * a58 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10022 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 2) < (-1/8 : ℝ))
    (a45 : -(h 1) < (-5/38 : ℝ))
    (a50 : -(h 4) < (-1/9 : ℝ))
    (a52 : -(h 0) < (-10/67 : ℝ))
    (a57 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a25 + (1/5 : ℝ) * a45 + (1/5 : ℝ) * a50 + (1/5 : ℝ) * a52 + (1/5 : ℝ) * a57 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10021 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a42 : -(h 3) < (-5/43 : ℝ))
    (a45 : -(h 1) < (-5/38 : ℝ))
    (a50 : -(h 4) < (-1/9 : ℝ))
    (a52 : -(h 0) < (-10/67 : ℝ))
    (a56 : -(h 2) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a42 + (1/5 : ℝ) * a45 + (1/5 : ℝ) * a50 + (1/5 : ℝ) * a52 + (1/5 : ℝ) * a56 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10020 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : h 1 ≤ (2/15 : ℝ))
    (a55 : -(h 1) < (-5/37 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a24 + (1 : ℝ) * a55
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10019 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : h 0 ≤ (3/20 : ℝ))
    (a54 : -(h 0) < (-5/33 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a54
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10018 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 2) < (-1/8 : ℝ))
    (a42 : -(h 3) < (-5/43 : ℝ))
    (a45 : -(h 1) < (-5/38 : ℝ))
    (a50 : -(h 4) < (-1/9 : ℝ))
    (a52 : -(h 0) < (-10/67 : ℝ))
    (a53 : ((-2 : ℝ) * (delta)) < (-13/64 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a50 + (1/6 : ℝ) * a52 + (1/6 : ℝ) * a53 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10017 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 2) < (-1/8 : ℝ))
    (a37 : -(h 0) < (-4/27 : ℝ))
    (a42 : -(h 3) < (-5/43 : ℝ))
    (a45 : -(h 1) < (-5/38 : ℝ))
    (a50 : -(h 4) < (-1/9 : ℝ))
    (a56 : -(h 5) < (-4/37 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.lower + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a50 + (1/6 : ℝ) * a56 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10016 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 2) < (-1/8 : ℝ))
    (a37 : -(h 0) < (-4/27 : ℝ))
    (a45 : -(h 1) < (-5/38 : ℝ))
    (a50 : -(h 4) < (-1/9 : ℝ))
    (a55 : -(h 3) < (-2/17 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a25 + (1/5 : ℝ) * a37 + (1/5 : ℝ) * a45 + (1/5 : ℝ) * a50 + (1/5 : ℝ) * a55 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10015 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a37 : -(h 0) < (-4/27 : ℝ))
    (a42 : -(h 3) < (-5/43 : ℝ))
    (a45 : -(h 1) < (-5/38 : ℝ))
    (a50 : -(h 4) < (-1/9 : ℝ))
    (a54 : -(h 2) < (-4/31 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a37 + (1/5 : ℝ) * a42 + (1/5 : ℝ) * a45 + (1/5 : ℝ) * a50 + (1/5 : ℝ) * a54 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10014 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : h 1 ≤ (2/15 : ℝ))
    (a53 : -(h 1) < (-1/7 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a24 + (1 : ℝ) * a53
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10013 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : h 1 ≤ (2/15 : ℝ))
    (a25 : -(h 2) < (-1/8 : ℝ))
    (a34 : h 0 ≤ (3/20 : ℝ))
    (a42 : -(h 3) < (-5/43 : ℝ))
    (a45 : -(h 1) < (-5/38 : ℝ))
    (a50 : -(h 4) < (-1/9 : ℝ))
    (a52 : -(h 0) < (-10/67 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (13/64 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-13/64 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_10018 h delta _ctx _hno a25 a42 a45 a50 a52 f0
  by_cases p1 : h 0 ≤ (5/33 : ℝ)
  swap
  · have f1 : -(h 0) < (-5/33 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_10019 h delta _ctx _hno a34 f1
  by_cases p2 : h 1 ≤ (5/37 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/37 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_10020 h delta _ctx _hno a24 f2
  by_cases p3 : h 2 ≤ (3/23 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_10021 h delta _ctx _hno a42 a45 a50 a52 f3
  by_cases p4 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_10022 h delta _ctx _hno a25 a45 a50 a52 f4
  by_cases p5 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_10023 h delta _ctx _hno a25 a42 a45 a50 a52 f5
  apply _hno 254
  change (((2 : ℝ) * (delta)) ≤ (13/64 : ℝ)) ∧ (h 0 ≤ (5/33 : ℝ)) ∧ (h 1 ≤ (5/37 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_10012 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 2) < (-1/8 : ℝ))
    (a37 : -(h 0) < (-4/27 : ℝ))
    (a42 : -(h 3) < (-5/43 : ℝ))
    (a45 : -(h 1) < (-5/38 : ℝ))
    (a50 : -(h 4) < (-1/9 : ℝ))
    (a51 : ((-2 : ℝ) * (delta)) < (-13/64 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/6 : ℝ) * _ctx.min + (1/6 : ℝ) * a25 + (1/6 : ℝ) * a37 + (1/6 : ℝ) * a42 + (1/6 : ℝ) * a45 + (1/6 : ℝ) * a50 + (1/6 : ℝ) * a51 + (1/6 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10011 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : h 1 ≤ (2/15 : ℝ))
    (a25 : -(h 2) < (-1/8 : ℝ))
    (a34 : h 0 ≤ (3/20 : ℝ))
    (a37 : -(h 0) < (-4/27 : ℝ))
    (a42 : -(h 3) < (-5/43 : ℝ))
    (a45 : -(h 1) < (-5/38 : ℝ))
    (a50 : -(h 4) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (13/64 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-13/64 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_10012 h delta _ctx _hno a25 a37 a42 a45 a50 f0
  by_cases p1 : h 0 ≤ (10/67 : ℝ)
  swap
  · have f1 : -(h 0) < (-10/67 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_10013 h delta _ctx _hno a24 a25 a34 a42 a45 a50 f1
  by_cases p2 : h 1 ≤ (1/7 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/7 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_10014 h delta _ctx _hno a24 f2
  by_cases p3 : h 2 ≤ (4/31 : ℝ)
  swap
  · have f3 : -(h 2) < (-4/31 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_10015 h delta _ctx _hno a37 a42 a45 a50 f3
  by_cases p4 : h 3 ≤ (2/17 : ℝ)
  swap
  · have f4 : -(h 3) < (-2/17 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_10016 h delta _ctx _hno a25 a37 a45 a50 f4
  by_cases p5 : h 5 ≤ (4/37 : ℝ)
  swap
  · have f5 : -(h 5) < (-4/37 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_10017 h delta _ctx _hno a25 a37 a42 a45 a50 f5
  apply _hno 122
  change (((2 : ℝ) * (delta)) ≤ (13/64 : ℝ)) ∧ (h 0 ≤ (10/67 : ℝ)) ∧ (h 1 ≤ (1/7 : ℝ)) ∧ (h 2 ≤ (4/31 : ℝ)) ∧ (h 3 ≤ (2/17 : ℝ)) ∧ (h 5 ≤ (4/37 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_10010 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 2) < (-1/8 : ℝ))
    (a30 : -(h 4) < (-4/37 : ℝ))
    (a37 : -(h 0) < (-4/27 : ℝ))
    (a45 : -(h 1) < (-5/38 : ℝ))
    (a49 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a25 + (1/5 : ℝ) * a30 + (1/5 : ℝ) * a37 + (1/5 : ℝ) * a45 + (1/5 : ℝ) * a49 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10009 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : h 1 ≤ (2/15 : ℝ))
    (a48 : -(h 1) < (-2/15 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a24 + (1 : ℝ) * a48
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10008 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : h 0 ≤ (3/20 : ℝ))
    (a47 : -(h 0) < (-3/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a47
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10007 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a46 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a46
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10006 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a25 : -(h 2) < (-1/8 : ℝ))
    (a30 : -(h 4) < (-4/37 : ℝ))
    (a34 : h 0 ≤ (3/20 : ℝ))
    (a35 : -(h 1) < (-3/23 : ℝ))
    (a37 : -(h 0) < (-4/27 : ℝ))
    (a42 : -(h 3) < (-5/43 : ℝ))
    (a45 : h 1 ≤ (5/38 : ℝ))
    (a48 : -(h 5) < (-2/19 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_10024 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (3/19 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/19 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_10025 h delta _ctx _hno a34 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_10026 h delta _ctx _hno a45 f2
  by_cases p3 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_10027 h delta _ctx _hno a25 a30 a35 a37 a48 f3
  by_cases p4 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_10028 h delta _ctx _hno a25 a35 a37 a42 a48 f4
  apply _hno 213
  change (((2 : ℝ) * (delta)) ≤ (8/39 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_10005 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a25 : -(h 2) < (-1/8 : ℝ))
    (a30 : -(h 4) < (-4/37 : ℝ))
    (a35 : -(h 1) < (-3/23 : ℝ))
    (a37 : -(h 0) < (-4/27 : ℝ))
    (a47 : -(h 3) < (-1/8 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a25 + (1/5 : ℝ) * a30 + (1/5 : ℝ) * a35 + (1/5 : ℝ) * a37 + (1/5 : ℝ) * a47 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10004 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a30 : -(h 4) < (-4/37 : ℝ))
    (a37 : -(h 0) < (-4/27 : ℝ))
    (a42 : -(h 3) < (-5/43 : ℝ))
    (a46 : -(h 2) < (-3/23 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/5 : ℝ) * _ctx.order1 + (1/5 : ℝ) * _ctx.min + (2/5 : ℝ) * _ctx.lower + (1/5 : ℝ) * a30 + (1/5 : ℝ) * a37 + (1/5 : ℝ) * a42 + (2/5 : ℝ) * a46 + (1/5 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10003 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a24 : h 1 ≤ (2/15 : ℝ))
    (a25 : -(h 2) < (-1/8 : ℝ))
    (a30 : -(h 4) < (-4/37 : ℝ))
    (a34 : h 0 ≤ (3/20 : ℝ))
    (a37 : -(h 0) < (-4/27 : ℝ))
    (a42 : -(h 3) < (-5/43 : ℝ))
    (a45 : -(h 1) < (-5/38 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (8/39 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-8/39 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_10007 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (3/19 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/19 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_10008 h delta _ctx _hno a34 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_10009 h delta _ctx _hno a24 f2
  by_cases p3 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f3 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_10010 h delta _ctx _hno a25 a30 a37 a45 f3
  by_cases p4 : h 4 ≤ (1/9 : ℝ)
  swap
  · have f4 : -(h 4) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_10011 h delta _ctx _hno a24 a25 a34 a37 a42 a45 f4
  apply _hno 213
  change (((2 : ℝ) * (delta)) ≤ (8/39 : ℝ)) ∧ (h 0 ≤ (3/19 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 4 ≤ (1/9 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem new_node_10002 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : h 0 ≤ (3/20 : ℝ))
    (a44 : -(h 0) < (-2/13 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a44
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10001 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a43 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a43
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_10000 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a24 : h 1 ≤ (2/15 : ℝ))
    (a25 : -(h 2) < (-1/8 : ℝ))
    (a34 : h 0 ≤ (3/20 : ℝ))
    (a35 : -(h 1) < (-3/23 : ℝ))
    (a37 : -(h 0) < (-4/27 : ℝ))
    (a42 : h 3 ≤ (5/43 : ℝ))
    (a43 : -(h 4) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_10029 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (3/20 : ℝ)
  swap
  · have f1 : -(h 0) < (-3/20 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_10030 h delta _ctx _hno a34 f1
  by_cases p2 : h 1 ≤ (2/15 : ℝ)
  swap
  · have f2 : -(h 1) < (-2/15 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_10031 h delta _ctx _hno a24 f2
  by_cases p3 : h 3 ≤ (3/26 : ℝ)
  swap
  · have f3 : -(h 3) < (-3/26 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_10032 h delta _ctx _hno a13 a24 a25 a34 a35 a37 a42 a43 f3
  apply _hno 68
  change (((2 : ℝ) * (delta)) ≤ (2/9 : ℝ)) ∧ (h 0 ≤ (3/20 : ℝ)) ∧ (h 1 ≤ (2/15 : ℝ)) ∧ (h 3 ≤ (3/26 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem new_node_9999 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a24 : h 1 ≤ (2/15 : ℝ))
    (a25 : -(h 2) < (-1/8 : ℝ))
    (a30 : -(h 4) < (-4/37 : ℝ))
    (a34 : h 0 ≤ (3/20 : ℝ))
    (a35 : -(h 1) < (-3/23 : ℝ))
    (a37 : -(h 0) < (-4/27 : ℝ))
    (a42 : -(h 3) < (-5/43 : ℝ))
    : False := by
  by_cases p0 : ((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)
  swap
  · have f0 : ((-2 : ℝ) * (delta)) < (-4/19 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact new_node_10001 h delta _ctx _hno a13 f0
  by_cases p1 : h 0 ≤ (2/13 : ℝ)
  swap
  · have f1 : -(h 0) < (-2/13 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact new_node_10002 h delta _ctx _hno a34 f1
  by_cases p2 : h 1 ≤ (5/38 : ℝ)
  swap
  · have f2 : -(h 1) < (-5/38 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact new_node_10003 h delta _ctx _hno a13 a24 a25 a30 a34 a37 a42 f2
  by_cases p3 : h 2 ≤ (3/23 : ℝ)
  swap
  · have f3 : -(h 2) < (-3/23 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact new_node_10004 h delta _ctx _hno a30 a37 a42 f3
  by_cases p4 : h 3 ≤ (1/8 : ℝ)
  swap
  · have f4 : -(h 3) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact new_node_10005 h delta _ctx _hno a25 a30 a35 a37 f4
  by_cases p5 : h 5 ≤ (2/19 : ℝ)
  swap
  · have f5 : -(h 5) < (-2/19 : ℝ) := by
      have hp := lt_of_not_ge p5
      linarith only [hp]
    exact new_node_10006 h delta _ctx _hno a13 a25 a30 a34 a35 a37 a42 p2 f5
  apply _hno 30
  change (((2 : ℝ) * (delta)) ≤ (4/19 : ℝ)) ∧ (h 0 ≤ (2/13 : ℝ)) ∧ (h 1 ≤ (5/38 : ℝ)) ∧ (h 2 ≤ (3/23 : ℝ)) ∧ (h 3 ≤ (1/8 : ℝ)) ∧ (h 5 ≤ (2/19 : ℝ))
  exact ⟨p0, p1, p2, p3, p4, p5⟩

theorem new_node_9998 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a29 : h 2 ≤ (2/15 : ℝ))
    (a41 : -(h 2) < (-3/22 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a29 + (1 : ℝ) * a41
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9997 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a24 : h 1 ≤ (2/15 : ℝ))
    (a40 : -(h 1) < (-6/43 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a24 + (1 : ℝ) * a40
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9996 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a34 : h 0 ≤ (3/20 : ℝ))
    (a39 : -(h 0) < (-5/31 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a34 + (1 : ℝ) * a39
  exact (lt_irrefl (0 : ℝ)) hbad

theorem new_node_9995 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : NewLargestCtx h delta)
    (_hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta)
    (a13 : ((2 : ℝ) * (delta)) ≤ (12/59 : ℝ))
    (a38 : ((-2 : ℝ) * (delta)) < (-5/24 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * a13 + (1 : ℝ) * a38
  exact (lt_irrefl (0 : ℝ)) hbad

end RealPinwheel.WeakSevenBandData
