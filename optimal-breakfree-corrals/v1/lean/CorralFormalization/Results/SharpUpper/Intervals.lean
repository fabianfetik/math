import CorralFormalization.ConstructionSupport.PhysicalRows
import CorralFormalization.CyclicShift

/-!
# Every interval of `n` sites meets a valid row

This is the physical geometric input to the sharp global counting argument.
The conclusion is stated using the same `n` possible gap labels used by the
uniform gap-permutation space.
-/

namespace CorralFormalization.Results.SharpUpper

open Finset PhysicalCorral

/-- A row with every cyclic gap at most `n` has a site among `0,...,n-1`.
The wrap gap alone proves the assertion after choosing the usual cut. -/
theorem exists_row_site_lt {M n : ℕ} (S : Finset ℕ) (hne : S.Nonempty)
    (hbound : ∀ x ∈ S, x < M)
    (hgap : ∀ g ∈ finiteCyclicGapInventory M S, g ≤ n) :
    ∃ s ∈ S, s < n := by
  have hsne : S.sort (· ≤ ·) ≠ [] := by
    intro hs
    obtain ⟨s, hsS⟩ := hne
    have : s ∈ S.sort (· ≤ ·) := (mem_sort (· ≤ ·)).mpr hsS
    simp [hs] at this
  cases hs : S.sort (· ≤ ·) with
  | nil => exact False.elim (hsne hs)
  | cons c cs =>
    have hc : c ∈ S := (mem_sort (· ≤ ·)).mp (by simp [hs])
    have hl : (c :: cs).getLast (by simp) ∈ S :=
      (mem_sort (· ≤ ·)).mp (by simp [hs])
    have hlM := hbound _ hl
    have hw : c + M - (c :: cs).getLast (by simp) ≤ n := by
      apply hgap
      simp [finiteCyclicGapInventory, hs, cyclicGaps]
    exact ⟨c, hc, by omega⟩

/-- Every interval of the `n` consecutive sites immediately after `x`
meets the row. Rotation invariance of the exact gap inventory pays for
moving the cut; this is a theorem about physical sites. -/
theorem row_meets_next_interval {M n : ℕ} [NeZero M]
    (S : Finset ℕ) (hne : S.Nonempty) (hbound : ∀ s ∈ S, s < M)
    (hgap : ∀ g ∈ finiteCyclicGapInventory M S, g ≤ n) (x : ZMod M) :
    ∃ a : Fin n, x + (a.val + 1 : ℕ) ∈ physicalSites M S := by
  let c : ℕ := (-x - 1).val
  let T := S.image (fun s => (s+c)%M)
  have hM : 0 < M := NeZero.pos M
  have hTne : T.Nonempty := hne.image _
  have hTbound : ∀ t ∈ T, t < M := by
    intro t ht
    obtain ⟨s, _, rfl⟩ := mem_image.mp ht
    exact Nat.mod_lt _ hM
  have hTgap : ∀ g ∈ finiteCyclicGapInventory M T, g ≤ n := by
    simpa only [T, finite_set_cyclic_gap_rotate M c S hM hbound] using hgap
  obtain ⟨p, hpT, hpn⟩ := exists_row_site_lt T hTne hTbound hTgap
  obtain ⟨s, hsS, hsp⟩ := mem_image.mp hpT
  have hpcast : (p : ZMod M) = (s : ZMod M) + (-x-1) := by
    rw [← hsp, ZMod.natCast_mod, Nat.cast_add]
    simp [c]
  refine ⟨⟨p,hpn⟩, mem_image.mpr ⟨s,hsS,?_⟩⟩
  change (s : ZMod M) = x + (p + 1 : ℕ)
  push_cast
  linear_combination -hpcast

/-- The manuscript's interval observation for every row of every actual
`CorralRows` witness. No completeness or optimality premise is needed. -/
theorem corral_row_meets_next_interval {h n : ℕ} [NeZero (width n)]
    (R : CorralRows h n) (i : Fin h) (x : ZMod (width n)) :
    ∃ a : Fin n, x + (a.val + 1 : ℕ) ∈ physicalSites (width n) (R.sites i) := by
  apply row_meets_next_interval (R.sites i) (R.nonempty i) (R.bounded i) _ x
  intro g hg
  rw [R.gaps] at hg
  exact ((fullGapList_mem n g).mp (Multiset.mem_coe.mp hg)).2

/-- For a set of disjoint physical rows, the `n` candidate next sites hit
at least as many distinct labels as there are rows. -/
theorem disjoint_rows_dense_next {M n : ℕ} [NeZero M] {ι : Type*} [Fintype ι]
    (R : ι → Finset (ZMod M))
    (hdisj : ∀ i k, i ≠ k → Disjoint (R i) (R k))
    (hhit : ∀ i (x : ZMod M), ∃ a : Fin n, x + (a.val + 1 : ℕ) ∈ R i)
    (F : Finset (ZMod M)) (hsub : ∀ i, R i ⊆ F) (x : ZMod M) :
    Fintype.card ι ≤ (univ.filter (fun a : Fin n => x + (a.val + 1 : ℕ) ∈ F)).card := by
  classical
  choose a ha using fun i => hhit i x
  have hainj : Function.Injective a := by
    intro i k hik
    by_contra hne
    exact disjoint_left.mp (hdisj i k hne) (ha i) (hik ▸ ha k)
  have hmem : ∀ i, a i ∈ univ.filter (fun b : Fin n => x + (b.val + 1 : ℕ) ∈ F) := by
    intro i
    exact mem_filter.mpr ⟨mem_univ _, hsub i (ha i)⟩
  calc
    Fintype.card ι = (univ.image a).card := by rw [card_image_of_injective _ hainj]; simp
    _ ≤ _ := card_le_card (by intro b hb; obtain ⟨i,_,rfl⟩ := mem_image.mp hb; exact hmem i)

end CorralFormalization.Results.SharpUpper
