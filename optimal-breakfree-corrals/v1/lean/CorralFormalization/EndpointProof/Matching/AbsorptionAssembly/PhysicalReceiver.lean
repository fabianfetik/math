import CorralFormalization.EndpointProof.Matching.AbsorptionAssembly.PhysicalMatching

/-!
Physical inventory accounting and the full deterministic receiving theorem
for the uniform exact-matching theorem.  Quantitative probability, capacity and rounding suppliers
remain explicit inputs; this file proves their finite composition.
-/

open scoped Classical BigOperators

namespace EndpointMatching.AbsorptionAssembly

open EndpointFlow.AbelianTransport

noncomputable section

variable {G : Type*} [AddCommGroup G]

theorem signedTarget_slice_tail (X Y C : Finset G) :
    slice (signedTarget X Y C) 0 = X.image (fun x => (0, -x)) := by
  ext ⟨p, a⟩
  fin_cases p <;> simp [slice, signedTarget]

theorem signedTarget_slice_head (X Y C : Finset G) :
    slice (signedTarget X Y C) 1 = Y.image (fun y => (1, y)) := by
  ext ⟨p, a⟩
  fin_cases p <;> simp [slice, signedTarget]

theorem signedTarget_slice_color (X Y C : Finset G) :
    slice (signedTarget X Y C) 2 = C.image (fun c => (2, -c)) := by
  ext ⟨p, a⟩
  fin_cases p <;> simp [slice, signedTarget]

theorem signedTarget_balanced {X Y C : Finset G}
    (hXY : X.card = Y.card) (hXC : X.card = C.card) : Balanced (signedTarget X Y C) := by
  have ht : (slice (signedTarget X Y C) 0).card = X.card := by
    rw [signedTarget_slice_tail, Finset.card_image_of_injective]
    exact fun a b h => neg_injective (congrArg Prod.snd h)
  have hh : (slice (signedTarget X Y C) 1).card = Y.card := by
    rw [signedTarget_slice_head, Finset.card_image_of_injective]
    exact fun a b h => congrArg Prod.snd h
  have hc : (slice (signedTarget X Y C) 2).card = C.card := by
    rw [signedTarget_slice_color, Finset.card_image_of_injective]
    exact fun a b h => neg_injective (congrArg Prod.snd h)
  intro p
  fin_cases p
  · rfl
  · change (slice (signedTarget X Y C) 1).card = (slice (signedTarget X Y C) 0).card
    rw [hh, ht]
    exact hXY.symm
  · change (slice (signedTarget X Y C) 2).card = (slice (signedTarget X Y C) 0).card
    rw [hc, ht]
    exact hXC.symm

theorem signedTarget_sum (X Y C : Finset G) :
    ∑ v ∈ signedTarget X Y C, v.2 = -(∑ x ∈ X, x) + (∑ y ∈ Y, y) - ∑ c ∈ C, c := by
  have hXY : Disjoint (X.image (fun x : G => ((0 : Fin 3), -x)))
      (Y.image (fun y => ((1 : Fin 3), y))) := by
    apply Finset.disjoint_left.mpr
    rintro _ hX hY
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hX
    obtain ⟨y, _, hy⟩ := Finset.mem_image.mp hY
    have := congrArg Prod.fst (hx.trans hy.symm)
    norm_num at this
  have hC : Disjoint
      (X.image (fun x : G => ((0 : Fin 3), -x)) ∪ Y.image (fun y => ((1 : Fin 3), y)))
      (C.image (fun c => ((2 : Fin 3), -c))) := by
    apply Finset.disjoint_left.mpr
    rintro _ hXY hC
    obtain ⟨c, _, hc⟩ := Finset.mem_image.mp hC
    rcases Finset.mem_union.mp hXY with hX | hY
    · obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hX
      have := congrArg Prod.fst (hx.trans hc.symm)
      exact (by decide : (0 : Fin 3) ≠ 2) this
    · obtain ⟨y, _, hy⟩ := Finset.mem_image.mp hY
      have := congrArg Prod.fst (hy.trans hc.symm)
      exact (by decide : (1 : Fin 3) ≠ 2) this
  unfold signedTarget
  rw [Finset.sum_union hC, Finset.sum_union hXY]
  rw [Finset.sum_image, Finset.sum_image, Finset.sum_image]
  · change (∑ x ∈ X, -x) + (∑ y ∈ Y, y) + (∑ c ∈ C, -c) = _
    rw [Finset.sum_neg_distrib (s := X) (fun x : G => x),
      Finset.sum_neg_distrib (s := C) (fun c : G => c)]
    simp only [sub_eq_add_neg]
  · intro a ha b hb hab
    exact neg_injective (congrArg Prod.snd hab)
  · intro a ha b hb hab
    exact congrArg Prod.snd hab
  · intro a ha b hb hab
    exact neg_injective (congrArg Prod.snd hab)

theorem signedTarget_zeroSum {X Y C : Finset G}
    (hchecksum : (∑ c ∈ C, c) = (∑ y ∈ Y, y) - ∑ x ∈ X, x) :
    ∑ v ∈ signedTarget X Y C, v.2 = 0 := by
  rw [signedTarget_sum, hchecksum]
  abel

theorem signedTarget_card (X Y C : Finset G) :
    (signedTarget X Y C).card = X.card + Y.card + C.card := by
  have hparts : (signedTarget X Y C).card =
      ∑ p : Fin 3, (slice (signedTarget X Y C) p).card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext v
      simp [slice]
    · intro p _ q _ hpq
      apply Finset.disjoint_left.mpr
      intro v hp hq
      exact hpq ((Finset.mem_filter.mp hp).2.symm.trans (Finset.mem_filter.mp hq).2)
  rw [hparts, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  rw [signedTarget_slice_tail, signedTarget_slice_head, signedTarget_slice_color]
  rw [Finset.card_image_of_injective _ (fun a b h => neg_injective (congrArg Prod.snd h)),
    Finset.card_image_of_injective _ (fun a b h => congrArg Prod.snd h),
    Finset.card_image_of_injective _ (fun a b h => neg_injective (congrArg Prod.snd h))]
  omega

theorem signedTarget_sdiff (RX RY RC X Y C : Finset G) :
    signedTarget RX RY RC \ signedTarget X Y C =
      signedTarget (RX \ X) (RY \ Y) (RC \ C) := by
  ext ⟨p, a⟩
  simp only [Finset.mem_sdiff]
  fin_cases p
  · change ((0, a) ∈ signedTarget RX RY RC ∧ (0, a) ∉ signedTarget X Y C) ↔
      (0, a) ∈ signedTarget (RX \ X) (RY \ Y) (RC \ C)
    have ha := signedTarget_tail_mem RX RY RC (-a)
    have hb := signedTarget_tail_mem X Y C (-a)
    have hc := signedTarget_tail_mem (RX \ X) (RY \ Y) (RC \ C) (-a)
    simp only [neg_neg] at ha hb hc
    simp only [ha, hb, hc, Finset.mem_sdiff]
  · change ((1, a) ∈ signedTarget RX RY RC ∧ (1, a) ∉ signedTarget X Y C) ↔
      (1, a) ∈ signedTarget (RX \ X) (RY \ Y) (RC \ C)
    simp only [signedTarget_head_mem, Finset.mem_sdiff]
  · change ((2, a) ∈ signedTarget RX RY RC ∧ (2, a) ∉ signedTarget X Y C) ↔
      (2, a) ∈ signedTarget (RX \ X) (RY \ Y) (RC \ C)
    have ha := signedTarget_color_mem RX RY RC (-a)
    have hb := signedTarget_color_mem X Y C (-a)
    have hc := signedTarget_color_mem (RX \ X) (RY \ Y) (RC \ C) (-a)
    simp only [neg_neg] at ha hb hc
    simp only [ha, hb, hc, Finset.mem_sdiff]

/-- The physical disjointness/nonzero-color hypotheses justify that the
separate zero treatment in the near supplier has at most one root to cover. -/
theorem signedTarget_zero_unique {X Y C : Finset G} (hXY : Disjoint X Y)
    (hC : (0 : G) ∉ C) {p q : Fin 3}
    (hp : (p, 0) ∈ signedTarget X Y C) (hq : (q, 0) ∈ signedTarget X Y C) : p = q := by
  fin_cases p <;> fin_cases q <;> first
    | rfl
    | (exfalso; simp_all [signedTarget, Prod.mk.injEq, Finset.disjoint_left])

/-- The receiver's deterministic conclusion with physical sets and colors.
The raw core is selected after H7 and before the actual near matching.
The two probabilistic/existence suppliers, and the numerical inequalities
needed to invoke them, are explicit assumptions. -/
theorem physical_exact_of_suppliers {RX RY RC X Y C : Finset G}
    {rawMinus : Finset (Vertex G)} {capacity coreBound : ℕ}
    (hminus : rawMinus ⊆ signedTarget RX RY RC)
    (hcore : RawCoreSupply rawMinus capacity coreBound)
    (hexclusion : (RX \ X).card + (RY \ Y).card + (RC \ C).card + 1 ≤ capacity)
    (hXY : X.card = Y.card) (hXC : X.card = C.card)
    (hchecksum : (∑ c ∈ C, c) = (∑ y ∈ Y, y) - ∑ x ∈ X, x)
    (hnear : ∀ A : Finset (Vertex G), A ⊆ signedTarget X Y C →
      (∀ v ∈ A, v.2 ≠ 0) → Balanced A → (∑ v ∈ A, v.2 = 0) → A.card ≤ coreBound →
      Nonempty (CompatibleNearMatching (signedTarget X Y C) A capacity)) :
    Nonempty (PhysicalDifferenceMatching X Y C) := by
  have hbudget : (signedTarget RX RY RC \ signedTarget X Y C).card + 1 ≤ capacity := by
    simpa only [signedTarget_sdiff, signedTarget_card] using hexclusion
  obtain ⟨M⟩ := exact_on_actualTarget_of_suppliers hminus hcore hbudget
    (signedTarget_balanced hXY hXC) (signedTarget_zeroSum hchecksum) hnear
  exact ⟨physicalDifferenceMatching_of_signedMatching M⟩


end
end EndpointMatching.AbsorptionAssembly
