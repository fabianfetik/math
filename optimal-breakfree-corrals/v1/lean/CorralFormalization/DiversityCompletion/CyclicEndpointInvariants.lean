import CorralFormalization.DiversityCompletion.EndpointPathSupplier

/-! Deterministic endpoint-completion bookkeeping. These are facts about
a supplied simple rainbow prefix; they do not assert a completion path. -/

namespace CorralFormalization.LatinCompletion.TerraceCompletion

/-- The sum of the actual directed differences telescopes from the first
vertex of a nonempty path to its last vertex, in the physical residue group. -/
theorem pathGaps_sum_cast {n : ℕ} [NeZero n] (a b : ZMod n) (xs : List (ZMod n)) :
    ((pathGaps ((a::xs) ++ [b])).sum : ZMod n) = b-a := by
  induction xs generalizing a with
  | nil => simp [pathGaps]
  | cons c xs ih =>
    simp only [List.cons_append, pathGaps, List.sum_cons, Nat.cast_add,
      ZMod.natCast_zmod_val]
    have hc : ((pathGaps (c :: (xs ++ [b]))).sum : ZMod n) = b-c := by
      simpa only [List.cons_append] using ih c
    rw [hc]
    abel

theorem RainbowPrefix.sum_colors {n : ℕ} [NeZero n] (P : RainbowPrefix n) :
    ((pathGaps P.path).sum : ZMod n) = P.last-P.first :=
  pathGaps_sum_cast P.first P.last P.interior

/-- The sum of all residues vanishes when the cyclic order is odd. -/
theorem sum_all_residues_odd {n : ℕ} [NeZero n] (hn : Odd n) :
    (∑ x : ZMod n, x) = 0 := by
  have hequiv : (∑ i : Fin n, ((i.val : ℕ) : ZMod n)) = ∑ x : ZMod n, x := by
    apply Fintype.sum_equiv (ZMod.finEquiv n).toEquiv
    intro i
    have hv : ((ZMod.finEquiv n) i).val = i.val := by
      cases n with
      | zero => exact (NeZero.ne 0 rfl).elim
      | succ n => rfl
    rw [← hv, ZMod.natCast_zmod_val]
    rfl
  rw [← hequiv, Fin.sum_univ_eq_sum_range, ← Nat.cast_sum, Finset.sum_range_id]
  obtain ⟨k, hk⟩ := hn
  have hk' : n = 2*k+1 := by omega
  have hs : n-1 = 2*k := by omega
  rw [hs]
  have hdiv : n*(2*k)/2 = n*k := by
    have : n*(2*k) = (n*k)*2 := by ring
    rw [this, Nat.mul_div_cancel _ (by omega : 0<2)]
  rw [hdiv, Nat.cast_mul, ZMod.natCast_self, zero_mul]

namespace RainbowPrefix

noncomputable def usedColorResidues {n : ℕ} (P : RainbowPrefix n) : Finset (ZMod n) := by
  classical
  exact (pathGaps P.path).toFinset.image (fun d : ℕ => (d : ZMod n))

noncomputable def remainingColorResidues {n : ℕ} [NeZero n]
    (P : RainbowPrefix n) : Finset (ZMod n) := by
  classical
  exact (Finset.univ.erase 0) \ P.usedColorResidues

noncomputable def remainingVertices {n : ℕ} [NeZero n]
    (P : RainbowPrefix n) : Finset (ZMod n) := by
  classical
  exact (Finset.univ.erase 0) \ P.interior.toFinset

theorem interior_nodup {n : ℕ} (P : RainbowPrefix n) : P.interior.Nodup := by
  have h := P.simple.of_append_left
  exact (List.nodup_cons.mp h).2

theorem interior_nonzero {n : ℕ} [NeZero n] (P : RainbowPrefix n) :
    P.interior.toFinset ⊆ Finset.univ.erase 0 := by
  classical
  intro x hx
  apply Finset.mem_erase.mpr
  refine ⟨?_, Finset.mem_univ _⟩
  apply P.nonzero x
  simp only [List.mem_append, List.mem_cons]
  exact Or.inl (Or.inr (List.mem_toFinset.mp hx))

theorem remainingVertices_card {n : ℕ} [NeZero n] (P : RainbowPrefix n) :
    P.remainingVertices.card = n-1-P.interior.length := by
  classical
  rw [remainingVertices, Finset.card_sdiff, Finset.inter_eq_left.mpr P.interior_nonzero,
      Finset.card_erase_of_mem (Finset.mem_univ (0 : ZMod n)), Finset.card_univ,
      ZMod.card, List.toFinset_card_of_nodup P.interior_nodup]

theorem remainingVertices_card_alt {n : ℕ} [NeZero n] (P : RainbowPrefix n) :
    P.remainingVertices.card = n-(P.path.length-1) := by
  rw [P.remainingVertices_card]
  simp only [path, List.length_append, List.length_cons, List.length_nil]
  omega

theorem remainingVertices_density {n : ℕ} [NeZero n] (P : RainbowPrefix n)
    (t : ℕ) (ht : P.path.length-1 ≤ t) : n-t ≤ P.remainingVertices.card := by
  rw [P.remainingVertices_card_alt]
  omega

theorem remainingVertices_endpoints {n : ℕ} [NeZero n] (P : RainbowPrefix n) :
    P.first ∈ P.remainingVertices ∧ P.last ∈ P.remainingVertices ∧ P.first ≠ P.last := by
  classical
  have hs : (P.first :: (P.interior ++ [P.last])).Nodup := by
    simpa only [List.cons_append] using P.simple
  have hf := (List.nodup_cons.mp hs).1
  have ht := (List.nodup_cons.mp hs).2
  have hf' : P.first ∉ P.interior := by
    intro hx
    exact hf (List.mem_append_left _ hx)
  have hl' : P.last ∉ P.interior := by
    intro hx
    exact ((List.nodup_append.mp ht).2.2 P.last hx P.last (by simp)) rfl
  have hne : P.first ≠ P.last := by
    intro he
    exact hf (List.mem_append_right _ (by simp [he]))
  have hf0 : P.first ≠ 0 := P.nonzero P.first (by simp)
  have hl0 : P.last ≠ 0 := P.nonzero P.last (by simp)
  refine ⟨?_, ?_, hne⟩ <;> simp [remainingVertices, hf0, hl0, hf', hl']

theorem cast_injOn_used {n : ℕ} [NeZero n] (P : RainbowPrefix n) :
    Set.InjOn (fun d : ℕ => (d : ZMod n)) (pathGaps P.path).toFinset := by
  intro a ha b hb hab
  have ha' := P.colors a (List.mem_toFinset.mp ha)
  have hb' := P.colors b (List.mem_toFinset.mp hb)
  have h := congrArg ZMod.val hab
  simpa only [ZMod.val_natCast_of_lt ha'.2, ZMod.val_natCast_of_lt hb'.2] using h

theorem usedColorResidues_card {n : ℕ} [NeZero n] (P : RainbowPrefix n) :
    P.usedColorResidues.card = P.path.length-1 := by
  classical
  have hrain : (pathGaps P.path).Nodup := by simpa [RainbowPrefix.path] using P.rainbow
  rw [usedColorResidues, Finset.card_image_of_injOn (P.cast_injOn_used),
      List.toFinset_card_of_nodup hrain, pathGaps_length]

theorem usedColorResidues_sum {n : ℕ} [NeZero n] (P : RainbowPrefix n) :
    (∑ x ∈ P.usedColorResidues, x) = P.last-P.first := by
  classical
  have hrain : (pathGaps P.path).Nodup := by simpa [RainbowPrefix.path] using P.rainbow
  rw [usedColorResidues, Finset.sum_image P.cast_injOn_used,
      List.sum_toFinset _ hrain, ← Nat.cast_list_sum]
  exact P.sum_colors

theorem usedColorResidues_nonzero {n : ℕ} [NeZero n] (P : RainbowPrefix n) :
    P.usedColorResidues ⊆ Finset.univ.erase 0 := by
  classical
  intro x hx
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
  have h := P.colors d (List.mem_toFinset.mp hd)
  apply Finset.mem_erase.mpr
  refine ⟨?_, Finset.mem_univ _⟩
  intro he
  have hv := congrArg ZMod.val he
  simp only [ZMod.val_natCast_of_lt h.2, ZMod.val_zero] at hv
  omega

theorem remainingColorResidues_card {n : ℕ} [NeZero n] (P : RainbowPrefix n) :
    P.remainingColorResidues.card = n-1-(P.path.length-1) := by
  classical
  rw [remainingColorResidues, Finset.card_sdiff,
      Finset.inter_eq_left.mpr P.usedColorResidues_nonzero,
      Finset.card_erase_of_mem (Finset.mem_univ (0 : ZMod n)), Finset.card_univ,
      ZMod.card, P.usedColorResidues_card]

/-- The remaining color count has the required one-less-than-vertices size. -/
theorem remaining_counts {n : ℕ} [NeZero n] (P : RainbowPrefix n) :
    P.remainingColorResidues.card + 1 = P.remainingVertices.card := by
  rw [P.remainingColorResidues_card, P.remainingVertices_card]
  have hs := Finset.card_le_card P.interior_nonzero
  rw [List.toFinset_card_of_nodup P.interior_nodup,
      Finset.card_erase_of_mem (Finset.mem_univ (0 : ZMod n)), Finset.card_univ,
      ZMod.card] at hs
  have hcol := Finset.card_le_card P.usedColorResidues_nonzero
  rw [P.usedColorResidues_card,
      Finset.card_erase_of_mem (Finset.mem_univ (0 : ZMod n)), Finset.card_univ,
      ZMod.card] at hcol
  simp only [path, List.length_append, List.length_cons, List.length_nil] at hcol ⊢
  omega

theorem remainingColorResidues_sum {n : ℕ} [NeZero n]
    (P : RainbowPrefix n) (hn : Odd n) :
    (∑ x ∈ P.remainingColorResidues, x) = P.first-P.last := by
  classical
  have hall : (∑ x ∈ (Finset.univ.erase 0 : Finset (ZMod n)), x) = 0 := by
    have he := Finset.sum_erase_add (Finset.univ : Finset (ZMod n))
      (fun x => x) (Finset.mem_univ (0 : ZMod n))
    simpa [sum_all_residues_odd hn] using he
  have hdiff := Finset.sum_sdiff (f := fun x : ZMod n => x) P.usedColorResidues_nonzero
  change (∑ x ∈ P.remainingColorResidues, x) + (∑ x ∈ P.usedColorResidues, x) = _ at hdiff
  rw [P.usedColorResidues_sum, hall] at hdiff
  linear_combination hdiff

theorem remainingColorResidues_mem {n : ℕ} [NeZero n]
    (P : RainbowPrefix n) (d : ℕ) (hd : 0 < d ∧ d < n) :
    (d : ZMod n) ∈ P.remainingColorResidues ↔ d ∉ pathGaps P.path := by
  classical
  have hcast : (d : ZMod n) ≠ 0 := by
    intro he
    have hv := congrArg ZMod.val he
    simp only [ZMod.val_natCast_of_lt hd.2, ZMod.val_zero] at hv
    omega
  simp only [remainingColorResidues, Finset.mem_sdiff, Finset.mem_erase,
    Finset.mem_univ, and_true, usedColorResidues, Finset.mem_image,
    List.mem_toFinset]
  constructor
  · rintro ⟨_,h⟩ hc
    exact h ⟨d,hc,rfl⟩
  · intro h
    refine ⟨hcast, ?_⟩
    rintro ⟨e,he,heq⟩
    have he' := P.colors e he
    have hv := congrArg ZMod.val heq
    simp only [ZMod.val_natCast_of_lt he'.2, ZMod.val_natCast_of_lt hd.2] at hv
    exact h (hv ▸ he)

end RainbowPrefix

/-- An explicit directed simple path on exactly W with each color in D once. -/
def EndpointPathClaim {n : ℕ} [NeZero n] (W D : Finset (ZMod n))
    (x y : ZMod n) : Prop :=
  ∃ middle : List (ZMod n),
    ((x::middle) ++ [y]).Nodup ∧
    (∀ z, z ∈ (x::middle) ++ [y] ↔ z ∈ W) ∧
    (pathGaps ((x::middle) ++ [y])).Nodup ∧
    (∀ d : ℕ, d ∈ pathGaps ((x::middle) ++ [y]) ↔
      0 < d ∧ d < n ∧ (d : ZMod n) ∈ D)

/-- A finite-instance form of directed endpoint completion. The size
parameter t encodes the allowed number of deleted vertices. -/
structure EndpointCompletionAt (n t : ℕ) [NeZero n] : Prop where
  complete : ∀ (W D : Finset (ZMod n)) (x y : ZMod n),
    n-t ≤ W.card → x ∈ W → y ∈ W → x ≠ y → 0 ∉ D →
    D.card+1 = W.card → (∑ z ∈ D, z) = y-x → EndpointPathClaim W D x y

/-- The quantified endpoint-completion hypothesis from the paper, expressed
using finite sets and explicit directed paths. -/
def OddCyclicRainbowEndpointCompletion : Prop :=
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∃ n0 : ℕ,
    ∀ (n : ℕ) [NeZero n], Odd n → n0 ≤ n →
      ∀ (W D : Finset (ZMod n)) (x y : ZMod n),
        (n : ℝ) - ε0*(n : ℝ) ≤ (W.card : ℝ) →
        x ∈ W → y ∈ W → x ≠ y → 0 ∉ D →
        D.card+1 = W.card → (∑ z ∈ D, z) = y-x → EndpointPathClaim W D x y

theorem oddCyclicEndpointCompletion_local (H : OddCyclicRainbowEndpointCompletion) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∃ n0 : ℕ,
      ∀ (n : ℕ) [NeZero n] (t : ℕ), Odd n → n0 ≤ n → t ≤ n →
        (t : ℝ) ≤ ε0*(n : ℝ) → EndpointCompletionAt n t := by
  obtain ⟨ε0,he,n0,H⟩ := H
  refine ⟨ε0,he,n0,?_⟩
  intro n inst t hn hn0 htn ht
  refine ⟨?_⟩
  intro W D x y hcard hx hy hxy hz hcount hsum
  have hc : ((n-t : ℕ) : ℝ) ≤ (W.card : ℝ) := by exact_mod_cast hcard
  rw [Nat.cast_sub htn] at hc
  have hd : (n : ℝ) - ε0*(n : ℝ) ≤ (W.card : ℝ) := by linarith
  exact H n hn hn0 W D x y hd hx hy hxy hz hcount hsum

/-- The actual complement of any valid prefix meets the endpoint hypothesis'
vertex, count and sum conditions; a supplied completion gives its path. -/
theorem RainbowPrefix.complementaryPath_of_endpoint {n t : ℕ} [NeZero n]
    (P : RainbowPrefix n) (hodd : Odd n) (ht : P.path.length-1 ≤ t)
    (H : EndpointCompletionAt n t) : Nonempty P.ComplementaryPath := by
  classical
  obtain ⟨hfirst,hlast,hne⟩ := P.remainingVertices_endpoints
  have hz : (0 : ZMod n) ∉ P.remainingColorResidues := by
    simp [RainbowPrefix.remainingColorResidues]
  obtain ⟨middle,hsimple,hvertices,hrainbow,hcolors⟩ :=
    H.complete P.remainingVertices P.remainingColorResidues P.last P.first
      (P.remainingVertices_density t ht) hlast hfirst hne.symm hz
      P.remaining_counts (P.remainingColorResidues_sum hodd)
  refine ⟨{
    interior := middle
    simple := hsimple
    vertices := ?_
    rainbow := hrainbow
    colors := ?_
  }⟩
  · intro z
    rw [hvertices]
    simp [RainbowPrefix.remainingVertices]
  · intro d
    rw [hcolors]
    by_cases hd : 0 < d ∧ d < n
    · rw [P.remainingColorResidues_mem d hd]
    · constructor <;> intro h <;> exact (hd ⟨h.1,h.2.1⟩).elim

end CorralFormalization.LatinCompletion.TerraceCompletion
