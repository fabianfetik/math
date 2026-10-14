import Pinwheel.WeakSevenBandData.CoverChunks.Second001

/-! Generated rational cover replay; source existence remains external here. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace RealPinwheel.WeakSevenBandData

theorem second_node_26 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a18 : -(h 1) < (-5389160/47230299 : ℝ))
    (a19 : -(h 0) < (-352893426530/1586876332767 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/2 : ℝ) * _ctx.order2 + (1 : ℝ) * _ctx.order3 + (3/2 : ℝ) * _ctx.order4 + (2 : ℝ) * _ctx.min + (5/2 : ℝ) * _ctx.lower + (1/2 : ℝ) * a18 + (1/2 : ℝ) * a19 + (1/2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_25 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a17 : -(h 0) < (-83/379 : ℝ))
    (a18 : -(h 1) < (-5389160/47230299 : ℝ))
    : False := by
  by_cases p0 : h 0 ≤ (352893426530/1586876332767 : ℝ)
  swap
  · have f0 : -(h 0) < (-352893426530/1586876332767 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact second_node_26 h delta _ctx _hno a18 f0
  by_cases p1 : ((2 : ℝ) * (delta)) ≤ (1635980674/8055209811 : ℝ)
  swap
  · have f1 : ((-2 : ℝ) * (delta)) < (-1635980674/8055209811 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact second_node_27 h delta _ctx _hno a17 a18 f1
  by_cases p2 : h 1 ≤ (933539800/8055209811 : ℝ)
  swap
  · have f2 : -(h 1) < (-933539800/8055209811 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact second_node_28 h delta _ctx _hno a17 f2
  by_cases p3 : h 2 ≤ (817990337/8055209811 : ℝ)
  swap
  · have f3 : -(h 2) < (-817990337/8055209811 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact second_node_29 h delta _ctx _hno a17 a18 f3
  apply _hno 9
  change (h 0 ≤ (352893426530/1586876332767 : ℝ)) ∧ (((2 : ℝ) * (delta)) ≤ (1635980674/8055209811 : ℝ)) ∧ (h 1 ≤ (933539800/8055209811 : ℝ)) ∧ (h 2 ≤ (817990337/8055209811 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem second_node_24 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 1) < (-1/9 : ℝ))
    (a17 : -(h 0) < (-83/379 : ℝ))
    (a18 : ((-2 : ℝ) * (delta)) < (-9772466/47230299 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/9 : ℝ) * _ctx.order2 + (4/9 : ℝ) * _ctx.order3 + (2/3 : ℝ) * _ctx.order4 + (8/9 : ℝ) * _ctx.min + (2/9 : ℝ) * a16 + (2/9 : ℝ) * a17 + (5/9 : ℝ) * a18 + (2/9 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_23 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 1) < (-1/9 : ℝ))
    (a18 : -(h 0) < (-10857200/47230299 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/2 : ℝ) * _ctx.order2 + (1 : ℝ) * _ctx.order3 + (3/2 : ℝ) * _ctx.order4 + (2 : ℝ) * _ctx.min + (5/2 : ℝ) * _ctx.lower + (1/2 : ℝ) * a16 + (1/2 : ℝ) * a18 + (1/2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_22 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 1) < (-1/9 : ℝ))
    (a17 : -(h 0) < (-83/379 : ℝ))
    : False := by
  by_cases p0 : h 0 ≤ (10857200/47230299 : ℝ)
  swap
  · have f0 : -(h 0) < (-10857200/47230299 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact second_node_23 h delta _ctx _hno a16 f0
  by_cases p1 : ((2 : ℝ) * (delta)) ≤ (9772466/47230299 : ℝ)
  swap
  · have f1 : ((-2 : ℝ) * (delta)) < (-9772466/47230299 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact second_node_24 h delta _ctx _hno a16 a17 f1
  by_cases p2 : h 1 ≤ (5389160/47230299 : ℝ)
  swap
  · have f2 : -(h 1) < (-5389160/47230299 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact second_node_25 h delta _ctx _hno a17 f2
  by_cases p3 : h 2 ≤ (4886233/47230299 : ℝ)
  swap
  · have f3 : -(h 2) < (-4886233/47230299 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact second_node_30 h delta _ctx _hno a16 a17 f3
  apply _hno 6
  change (h 0 ≤ (10857200/47230299 : ℝ)) ∧ (((2 : ℝ) * (delta)) ≤ (9772466/47230299 : ℝ)) ∧ (h 1 ≤ (5389160/47230299 : ℝ)) ∧ (h 2 ≤ (4886233/47230299 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem second_node_21 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 1) < (-1/9 : ℝ))
    : False := by
  by_cases p0 : h 0 ≤ (83/379 : ℝ)
  swap
  · have f0 : -(h 0) < (-83/379 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact second_node_22 h delta _ctx _hno a16 f0
  by_cases p1 : h 1 ≤ (47/379 : ℝ)
  swap
  · have f1 : -(h 1) < (-47/379 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact second_node_31 h delta _ctx _hno f1
  by_cases p2 : h 2 ≤ (83/758 : ℝ)
  swap
  · have f2 : -(h 2) < (-83/758 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact second_node_39 h delta _ctx _hno a16 f2
  apply _hno 8
  change (h 0 ≤ (83/379 : ℝ)) ∧ (h 1 ≤ (47/379 : ℝ)) ∧ (h 2 ≤ (83/758 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem second_node_20 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 0) < (-2/9 : ℝ))
    (a17 : -(h 1) < (-73/689 : ℝ))
    (a18 : -(h 2) < (-56129/542367 : ℝ))
    (a19 : -(h 3) < (-1247718281/12059888669 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.order4 + (1/2 : ℝ) * _ctx.min + (3/4 : ℝ) * _ctx.lower + (1/4 : ℝ) * a16 + (1/4 : ℝ) * a17 + (1/4 : ℝ) * a18 + (1/4 : ℝ) * a19 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_19 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 0) < (-2/9 : ℝ))
    (a19 : -(h 2) < (-3879780526/36179666007 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order1 + (1/3 : ℝ) * _ctx.order3 + (2/3 : ℝ) * _ctx.order4 + (1 : ℝ) * _ctx.min + (4/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * a16 + (2/3 : ℝ) * a19 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_18 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 0) < (-2/9 : ℝ))
    (a18 : -(h 2) < (-56129/542367 : ℝ))
    (a19 : -(h 1) < (-1323923842/12059888669 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order3 + (2/3 : ℝ) * _ctx.order4 + (1 : ℝ) * _ctx.min + (4/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * a16 + (1/3 : ℝ) * a18 + (1/3 : ℝ) * a19 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_17 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 0) < (-2/9 : ℝ))
    (a17 : -(h 1) < (-73/689 : ℝ))
    (a19 : ((-2 : ℝ) * (delta)) < (-2495436562/12059888669 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/9 : ℝ) * _ctx.order2 + (4/9 : ℝ) * _ctx.order3 + (2/3 : ℝ) * _ctx.order4 + (8/9 : ℝ) * _ctx.min + (2/9 : ℝ) * a16 + (2/9 : ℝ) * a17 + (5/9 : ℝ) * a19 + (2/9 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_16 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a17 : -(h 1) < (-73/689 : ℝ))
    (a18 : -(h 2) < (-56129/542367 : ℝ))
    (a19 : -(h 0) < (-8316733826/36179666007 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order3 + (2/3 : ℝ) * _ctx.order4 + (1 : ℝ) * _ctx.min + (4/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * a17 + (1/3 : ℝ) * a18 + (1/3 : ℝ) * a19 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_15 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 0) < (-2/9 : ℝ))
    (a17 : -(h 1) < (-73/689 : ℝ))
    (a18 : -(h 2) < (-56129/542367 : ℝ))
    : False := by
  by_cases p0 : h 0 ≤ (8316733826/36179666007 : ℝ)
  swap
  · have f0 : -(h 0) < (-8316733826/36179666007 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact second_node_16 h delta _ctx _hno a17 a18 f0
  by_cases p1 : ((2 : ℝ) * (delta)) ≤ (2495436562/12059888669 : ℝ)
  swap
  · have f1 : ((-2 : ℝ) * (delta)) < (-2495436562/12059888669 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact second_node_17 h delta _ctx _hno a16 a17 f1
  by_cases p2 : h 1 ≤ (1323923842/12059888669 : ℝ)
  swap
  · have f2 : -(h 1) < (-1323923842/12059888669 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact second_node_18 h delta _ctx _hno a16 a18 f2
  by_cases p3 : h 2 ≤ (3879780526/36179666007 : ℝ)
  swap
  · have f3 : -(h 2) < (-3879780526/36179666007 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact second_node_19 h delta _ctx _hno a16 f3
  by_cases p4 : h 3 ≤ (1247718281/12059888669 : ℝ)
  swap
  · have f4 : -(h 3) < (-1247718281/12059888669 : ℝ) := by
      have hp := lt_of_not_ge p4
      linarith only [hp]
    exact second_node_20 h delta _ctx _hno a16 a17 a18 f4
  apply _hno 7
  change (h 0 ≤ (8316733826/36179666007 : ℝ)) ∧ (((2 : ℝ) * (delta)) ≤ (2495436562/12059888669 : ℝ)) ∧ (h 1 ≤ (1323923842/12059888669 : ℝ)) ∧ (h 2 ≤ (3879780526/36179666007 : ℝ)) ∧ (h 3 ≤ (1247718281/12059888669 : ℝ))
  exact ⟨p0, p1, p2, p3, p4⟩

theorem second_node_14 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 0) < (-2/9 : ℝ))
    (a18 : -(h 1) < (-59770/542367 : ℝ))
    (a19 : -(h 2) < (-4886233/47230299 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/3 : ℝ) * _ctx.order3 + (2/3 : ℝ) * _ctx.order4 + (1 : ℝ) * _ctx.min + (4/3 : ℝ) * _ctx.lower + (1/3 : ℝ) * a16 + (1/3 : ℝ) * a18 + (1/3 : ℝ) * a19 + (1/3 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_13 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 0) < (-2/9 : ℝ))
    (a19 : -(h 1) < (-5389160/47230299 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/2 : ℝ) * _ctx.order2 + (1 : ℝ) * _ctx.order3 + (3/2 : ℝ) * _ctx.order4 + (2 : ℝ) * _ctx.min + (5/2 : ℝ) * _ctx.lower + (1/2 : ℝ) * a16 + (1/2 : ℝ) * a19 + (1/2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_12 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 0) < (-2/9 : ℝ))
    (a18 : -(h 1) < (-59770/542367 : ℝ))
    (a19 : ((-2 : ℝ) * (delta)) < (-9772466/47230299 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/9 : ℝ) * _ctx.order2 + (4/9 : ℝ) * _ctx.order3 + (2/3 : ℝ) * _ctx.order4 + (8/9 : ℝ) * _ctx.min + (2/9 : ℝ) * a16 + (2/9 : ℝ) * a18 + (5/9 : ℝ) * a19 + (2/9 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_11 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a18 : -(h 1) < (-59770/542367 : ℝ))
    (a19 : -(h 0) < (-10857200/47230299 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/2 : ℝ) * _ctx.order2 + (1 : ℝ) * _ctx.order3 + (3/2 : ℝ) * _ctx.order4 + (2 : ℝ) * _ctx.min + (5/2 : ℝ) * _ctx.lower + (1/2 : ℝ) * a18 + (1/2 : ℝ) * a19 + (1/2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_10 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 0) < (-2/9 : ℝ))
    (a18 : -(h 1) < (-59770/542367 : ℝ))
    : False := by
  by_cases p0 : h 0 ≤ (10857200/47230299 : ℝ)
  swap
  · have f0 : -(h 0) < (-10857200/47230299 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact second_node_11 h delta _ctx _hno a18 f0
  by_cases p1 : ((2 : ℝ) * (delta)) ≤ (9772466/47230299 : ℝ)
  swap
  · have f1 : ((-2 : ℝ) * (delta)) < (-9772466/47230299 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact second_node_12 h delta _ctx _hno a16 a18 f1
  by_cases p2 : h 1 ≤ (5389160/47230299 : ℝ)
  swap
  · have f2 : -(h 1) < (-5389160/47230299 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact second_node_13 h delta _ctx _hno a16 f2
  by_cases p3 : h 2 ≤ (4886233/47230299 : ℝ)
  swap
  · have f3 : -(h 2) < (-4886233/47230299 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact second_node_14 h delta _ctx _hno a16 a18 f3
  apply _hno 6
  change (h 0 ≤ (10857200/47230299 : ℝ)) ∧ (((2 : ℝ) * (delta)) ≤ (9772466/47230299 : ℝ)) ∧ (h 1 ≤ (5389160/47230299 : ℝ)) ∧ (h 2 ≤ (4886233/47230299 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem second_node_9 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 0) < (-2/9 : ℝ))
    (a17 : -(h 1) < (-73/689 : ℝ))
    (a18 : ((-2 : ℝ) * (delta)) < (-112258/542367 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (2/9 : ℝ) * _ctx.order2 + (4/9 : ℝ) * _ctx.order3 + (2/3 : ℝ) * _ctx.order4 + (8/9 : ℝ) * _ctx.min + (2/9 : ℝ) * a16 + (2/9 : ℝ) * a17 + (5/9 : ℝ) * a18 + (2/9 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_8 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a17 : -(h 1) < (-73/689 : ℝ))
    (a18 : -(h 0) < (-124660/542367 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/2 : ℝ) * _ctx.order2 + (1 : ℝ) * _ctx.order3 + (3/2 : ℝ) * _ctx.order4 + (2 : ℝ) * _ctx.min + (5/2 : ℝ) * _ctx.lower + (1/2 : ℝ) * a17 + (1/2 : ℝ) * a18 + (1/2 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_7 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 0) < (-2/9 : ℝ))
    (a17 : -(h 1) < (-73/689 : ℝ))
    : False := by
  by_cases p0 : h 0 ≤ (124660/542367 : ℝ)
  swap
  · have f0 : -(h 0) < (-124660/542367 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact second_node_8 h delta _ctx _hno a17 f0
  by_cases p1 : ((2 : ℝ) * (delta)) ≤ (112258/542367 : ℝ)
  swap
  · have f1 : ((-2 : ℝ) * (delta)) < (-112258/542367 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact second_node_9 h delta _ctx _hno a16 a17 f1
  by_cases p2 : h 1 ≤ (59770/542367 : ℝ)
  swap
  · have f2 : -(h 1) < (-59770/542367 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact second_node_10 h delta _ctx _hno a16 f2
  by_cases p3 : h 2 ≤ (56129/542367 : ℝ)
  swap
  · have f3 : -(h 2) < (-56129/542367 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact second_node_15 h delta _ctx _hno a16 a17 f3
  apply _hno 5
  change (h 0 ≤ (124660/542367 : ℝ)) ∧ (((2 : ℝ) * (delta)) ≤ (112258/542367 : ℝ)) ∧ (h 1 ≤ (59770/542367 : ℝ)) ∧ (h 2 ≤ (56129/542367 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem second_node_6 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 0) < (-2/9 : ℝ))
    (a17 : ((-2 : ℝ) * (delta)) < (-146/689 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1/4 : ℝ) * _ctx.order1 + (1/2 : ℝ) * _ctx.order2 + (3/4 : ℝ) * _ctx.order3 + (1 : ℝ) * _ctx.order4 + (5/4 : ℝ) * _ctx.min + (1/4 : ℝ) * a16 + (3/4 : ℝ) * a17 + (1/4 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_5 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a17 : -(h 0) < (-162/689 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * _ctx.order1 + (2 : ℝ) * _ctx.order2 + (3 : ℝ) * _ctx.order3 + (4 : ℝ) * _ctx.order4 + (5 : ℝ) * _ctx.min + (6 : ℝ) * _ctx.lower + (1 : ℝ) * a17 + (1 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_4 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a16 : -(h 0) < (-2/9 : ℝ))
    : False := by
  by_cases p0 : h 0 ≤ (162/689 : ℝ)
  swap
  · have f0 : -(h 0) < (-162/689 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact second_node_5 h delta _ctx _hno f0
  by_cases p1 : ((2 : ℝ) * (delta)) ≤ (146/689 : ℝ)
  swap
  · have f1 : ((-2 : ℝ) * (delta)) < (-146/689 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact second_node_6 h delta _ctx _hno a16 f1
  by_cases p2 : h 1 ≤ (73/689 : ℝ)
  swap
  · have f2 : -(h 1) < (-73/689 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact second_node_7 h delta _ctx _hno a16 f2
  apply _hno 4
  change (h 0 ≤ (162/689 : ℝ)) ∧ (((2 : ℝ) * (delta)) ≤ (146/689 : ℝ)) ∧ (h 1 ≤ (73/689 : ℝ))
  exact ⟨p0, p1, p2⟩

theorem second_node_3 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    : False := by
  by_cases p0 : h 0 ≤ (2/9 : ℝ)
  swap
  · have f0 : -(h 0) < (-2/9 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact second_node_4 h delta _ctx _hno f0
  by_cases p1 : h 1 ≤ (1/9 : ℝ)
  swap
  · have f1 : -(h 1) < (-1/9 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact second_node_21 h delta _ctx _hno f1
  apply _hno 1
  change (h 0 ≤ (2/9 : ℝ)) ∧ (h 1 ≤ (1/9 : ℝ))
  exact ⟨p0, p1⟩

theorem second_node_2 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    (a15 : -(h 0) < (-1/4 : ℝ))
    : False := by
  have hbad : (0 : ℝ) < 0 := by
    linear_combination (1 : ℝ) * _ctx.order1 + (2 : ℝ) * _ctx.order2 + (3 : ℝ) * _ctx.order3 + (4 : ℝ) * _ctx.order4 + (5 : ℝ) * _ctx.min + (6 : ℝ) * _ctx.lower + (1 : ℝ) * a15 + (1 : ℝ) * _ctx.simplex
  exact (lt_irrefl (0 : ℝ)) hbad

theorem second_node_1 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    : False := by
  by_cases p0 : h 0 ≤ (1/4 : ℝ)
  swap
  · have f0 : -(h 0) < (-1/4 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact second_node_2 h delta _ctx _hno f0
  by_cases p1 : ((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)
  swap
  · have f1 : ((-2 : ℝ) * (delta)) < (-1/5 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact second_node_3 h delta _ctx _hno
  by_cases p2 : h 1 ≤ (1/8 : ℝ)
  swap
  · have f2 : -(h 1) < (-1/8 : ℝ) := by
      have hp := lt_of_not_ge p2
      linarith only [hp]
    exact second_node_61 h delta _ctx _hno f2
  by_cases p3 : h 3 ≤ (1/10 : ℝ)
  swap
  · have f3 : -(h 3) < (-1/10 : ℝ) := by
      have hp := lt_of_not_ge p3
      linarith only [hp]
    exact second_node_69 h delta _ctx _hno
  apply _hno 2
  change (h 0 ≤ (1/4 : ℝ)) ∧ (((2 : ℝ) * (delta)) ≤ (1/5 : ℝ)) ∧ (h 1 ≤ (1/8 : ℝ)) ∧ (h 3 ≤ (1/10 : ℝ))
  exact ⟨p0, p1, p2, p3⟩

theorem second_node_0 (h : Fin 6 → ℝ) (delta : ℝ)
    (_ctx : SecondCtx h delta)
    (_hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta)
    : False := by
  by_cases p0 : h 0 ≤ (1/5 : ℝ)
  swap
  · have f0 : -(h 0) < (-1/5 : ℝ) := by
      have hp := lt_of_not_ge p0
      linarith only [hp]
    exact second_node_1 h delta _ctx _hno
  by_cases p1 : h 1 ≤ (3/25 : ℝ)
  swap
  · have f1 : -(h 1) < (-3/25 : ℝ) := by
      have hp := lt_of_not_ge p1
      linarith only [hp]
    exact second_node_123 h delta _ctx _hno f1
  apply _hno 3
  change (h 0 ≤ (1/5 : ℝ)) ∧ (h 1 ≤ (3/25 : ℝ))
  exact ⟨p0, p1⟩

end RealPinwheel.WeakSevenBandData
