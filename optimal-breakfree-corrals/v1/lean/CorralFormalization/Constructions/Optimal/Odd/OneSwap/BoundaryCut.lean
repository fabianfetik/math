import CorralFormalization.Constructions.Optimal.Odd.OneSwap.Cut

/-!
# Endpoint calculation when the cut falls in the closing gap

The ordinary prefix-cut theorem treats a successor which is another proper
prefix. This independent boundary case treats the closing gap back to the
first point, with an arbitrary positive monotone prefix sequence.
-/

namespace CorralFormalization.OneSwapOdd

/-- If the last proper prefix is followed by the wrap gap, its translated
row has minimum `g-δ` and tail deficit `δ`, exactly as in the ordinary
interior-cut case. The initial prefix is the actual `0` of a gap word. -/
theorem prefix_cut_endpoints_at_wrap (n W q j g δ : ℕ) (v : ℕ → ℕ)
    (hW : 0 < W) (hq : q < W) (hv : Monotone v) (hv0 : v 0 = 0)
    (hj : j + 1 = n) (hδ : 0 < δ) (hδg : δ ≤ g)
    (hcut : v j + q + δ = W) (hwrap : v j + g = W) :
    let S := Finset.univ.image (fun k : Fin n => (v k.val + q) % W)
    ∃ hn : S.Nonempty, S.min' hn = g - δ ∧ W - S.max' hn = δ := by
  let S := Finset.univ.image (fun k : Fin n => (v k.val + q) % W)
  have hn : 0 < n := by omega
  have hjn : j < n := by omega
  have hqeq : g - δ = q := by omega
  have hqmem : q ∈ S := by
    refine Finset.mem_image.mpr ⟨⟨0,hn⟩,Finset.mem_univ _,?_⟩
    simp [hv0, Nat.mod_eq_of_lt hq]
  have hpmod : (v j + q) % W = W - δ := by
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hpmem : W - δ ∈ S := by
    exact Finset.mem_image.mpr ⟨⟨j,hjn⟩,Finset.mem_univ _,hpmod⟩
  have hne : S.Nonempty := ⟨q,hqmem⟩
  refine ⟨hne,?_,?_⟩
  · rw [hqeq]
    apply le_antisymm (Finset.min'_le S q hqmem)
    apply Finset.le_min'
    intro x hx
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hx
    have hvk := hv (show k.val ≤ j by omega)
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · have hmax : S.max' hne = W - δ := by
      apply le_antisymm
      · apply Finset.max'_le
        intro x hx
        obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hx
        have hvk := hv (show k.val ≤ j by omega)
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
      · exact Finset.le_max' S _ hpmem
    rw [hmax]
    omega

/-- Both possible following gaps are covered: the next proper prefix or
the cyclic wrap gap. No precomputed endpoint table is assumed. -/
theorem prefix_cut_endpoints_including_wrap (n W q j g δ : ℕ) (v : ℕ → ℕ)
    (hW : 0 < W) (hq : q < W) (hv : Monotone v) (hv0 : v 0 = 0)
    (hbound : ∀ k, k < n → v k < W) (hδ : 0 < δ) (hδg : δ ≤ g)
    (hcut : v j + q + δ = W)
    (hfollow : (j + 1 < n ∧ v (j + 1) = v j + g) ∨
      (j + 1 = n ∧ v j + g = W)) :
    let S := Finset.univ.image (fun k : Fin n => (v k.val + q) % W)
    ∃ hn : S.Nonempty, S.min' hn = g - δ ∧ W - S.max' hn = δ := by
  rcases hfollow with ⟨hj,hnext⟩ | ⟨hj,hwrap⟩
  · exact prefix_cut_endpoints n W q j g δ v hW hq hv hbound hj hδ hδg hcut hnext
  · exact prefix_cut_endpoints_at_wrap n W q j g δ v hW hq hv hv0 hj hδ hδg hcut hwrap

end CorralFormalization.OneSwapOdd
