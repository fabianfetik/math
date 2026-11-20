import CorralFormalization.PositiveGapWord

namespace CorralFormalization.OneSwapOdd

/-- A cut strictly after one prefix and at or before its successor identifies
both endpoints after a cyclic translation.  In particular `δ = g` is allowed.
The hypotheses refer to actual consecutive entries of a monotone prefix
sequence, rather than an independently specified endpoint table. -/
theorem prefix_cut_endpoints (n W q j g δ : ℕ) (v : ℕ → ℕ)
    (hW : 0 < W) (hq : q < W) (hv : Monotone v)
    (hbound : ∀ k, k < n → v k < W) (hj : j + 1 < n)
    (hδ : 0 < δ) (hδg : δ ≤ g)
    (hcut : v j + q + δ = W) (hnext : v (j + 1) = v j + g) :
    let S := Finset.univ.image (fun k : Fin n => (v k.val + q) % W)
    ∃ hn : S.Nonempty, S.min' hn = g - δ ∧ W - S.max' hn = δ := by
  let S := Finset.univ.image (fun k : Fin n => (v k.val + q) % W)
  have hj0 : j < n := by omega
  have hb0 := hbound j hj0
  have hb1 := hbound (j + 1) hj
  have hpmod : (v j + q) % W = W - δ := by
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hnmod : (v (j + 1) + q) % W = g - δ := by
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  have hp : W - δ ∈ S := by
    exact Finset.mem_image.mpr ⟨⟨j, hj0⟩, Finset.mem_univ _, hpmod⟩
  have hn : g - δ ∈ S := by
    exact Finset.mem_image.mpr ⟨⟨j + 1, hj⟩, Finset.mem_univ _, hnmod⟩
  have hne : S.Nonempty := ⟨W - δ, hp⟩
  refine ⟨hne, le_antisymm (Finset.min'_le _ _ hn) ?_, ?_⟩
  · apply Finset.le_min'
    intro x hx
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx
    have hbk := hbound k.val k.isLt
    by_cases hk : k.val ≤ j
    · have hvk := hv hk
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    · have hvk := hv (by omega : j + 1 ≤ k.val)
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
  · have hmax : S.max' hne = W - δ := by
      apply le_antisymm
      · apply Finset.max'_le
        intro x hx
        obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx
        have hbk := hbound k.val k.isLt
        by_cases hk : k.val ≤ j
        · have hvk := hv hk
          rw [Nat.mod_eq_of_lt (by omega)]
          omega
        · have hvk := hv (by omega : j + 1 ≤ k.val)
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
          omega
      · exact Finset.le_max' _ _ hp
    rw [hmax]
    omega

end CorralFormalization.OneSwapOdd
