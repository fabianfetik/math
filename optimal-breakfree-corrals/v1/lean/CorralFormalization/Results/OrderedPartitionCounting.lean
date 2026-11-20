import CorralFormalization.DiversityCompletion.OptimalCorralCensus

/-!
# From unordered families to ordered row histories

Each finite unlabelled family of `h` distinct rows gives exactly `h!`
different orderings, and orderings from distinct families are disjoint. This
is the finite quotient needed when a prefix count is transferred back to
the actual physical census. No estimate on the number of allowed row
extensions is assumed or proved in this file.
-/

namespace CorralFormalization.Results.OrderedPartitionCounting

open Finset

variable {α : Type*} [DecidableEq α]

/-- Every ordering of the rows in a finite, unlabelled family. -/
noncomputable def familyOrderings (F : Finset α) : Finset (List α) :=
  F.toList.permutations.toFinset

theorem mem_familyOrderings_iff (F : Finset α) (xs : List α) :
    xs ∈ familyOrderings F ↔ xs.Perm F.toList := by
  simp [familyOrderings, List.mem_permutations]

theorem familyOrderings_nodup (F : Finset α) (xs : List α)
    (hx : xs ∈ familyOrderings F) : xs.Nodup :=
  ((mem_familyOrderings_iff F xs).mp hx).nodup_iff.mpr (Finset.nodup_toList F)

/-- The ordering recovers the exact physical family, hence orderings of two
different families can never coincide. -/
theorem familyOrderings_recover (F : Finset α) (xs : List α)
    (hx : xs ∈ familyOrderings F) : xs.toFinset = F := by
  have hp := (mem_familyOrderings_iff F xs).mp hx
  ext x
  simpa only [List.mem_toFinset, Finset.mem_toList] using hp.mem_iff (a := x)

theorem familyOrderings_card (F : Finset α) :
    (familyOrderings F).card = F.card.factorial := by
  rw [familyOrderings, List.toFinset_card_of_nodup
    (List.nodup_permutations _ (Finset.nodup_toList F)), List.length_permutations,
    Finset.length_toList]

noncomputable def orderingsOfFamilies (𝓕 : Finset (Finset α)) : Finset (List α) :=
  𝓕.biUnion familyOrderings

/-- Exact `h!` multiplicity before imposing any geometric or probability
bound. The members of `𝓕` are the actual unordered families, not labels. -/
theorem orderingsOfFamilies_card (𝓕 : Finset (Finset α)) (h : ℕ)
    (hcard : ∀ F ∈ 𝓕, F.card = h) :
    (orderingsOfFamilies 𝓕).card = 𝓕.card * h.factorial := by
  classical
  rw [orderingsOfFamilies, Finset.card_biUnion]
  · calc
      _ = ∑ _F ∈ 𝓕, h.factorial := by
        apply Finset.sum_congr rfl
        intro F hF
        rw [familyOrderings_card, hcard F hF]
      _ = 𝓕.card * h.factorial := by simp
  · intro F hF G hG hne
    apply Finset.disjoint_left.mpr
    intro xs hxF hxG
    have hFG : F = G := (familyOrderings_recover F xs hxF).symm.trans
      (familyOrderings_recover G xs hxG)
    exact hne hFG

/-- Any enclosing set of ordered histories already carries the exact
factorial multiplicity of the unlabelled families. -/
theorem factorial_mul_families_le_histories
    (𝓕 : Finset (Finset α)) (h : ℕ) (H : Finset (List α))
    (hcard : ∀ F ∈ 𝓕, F.card = h)
    (hcontains : ∀ F ∈ 𝓕, familyOrderings F ⊆ H) :
    𝓕.card * h.factorial ≤ H.card := by
  rw [← orderingsOfFamilies_card 𝓕 h hcard]
  apply Finset.card_le_card
  intro xs hxs
  obtain ⟨F, hF, hxsF⟩ := Finset.mem_biUnion.mp hxs
  exact hcontains F hF hxsF

/-- The first `h-1` rows determine the whole ordering whenever every
`h-1`-row subfamily has at most one completion in `𝓕`. This isolates the
last-row-from-the-complement fact from the subsequent branching estimate. -/
theorem prefix_injective_of_unique_completion
    (𝓕 : Finset (Finset α)) (h : ℕ) (hh : 1 ≤ h)
    (hcard : ∀ F ∈ 𝓕, F.card = h)
    (hunique : ∀ F ∈ 𝓕, ∀ G ∈ 𝓕, ∀ S : Finset α,
      S ⊆ F → S ⊆ G → S.card + 1 = h → F = G) :
    Set.InjOn (fun xs : List α => xs.take (h-1)) (orderingsOfFamilies 𝓕 : Set (List α)) := by
  classical
  intro xs hxs ys hys heq
  change xs.take (h-1) = ys.take (h-1) at heq
  obtain ⟨F, hF, hxsF⟩ := Finset.mem_biUnion.mp hxs
  obtain ⟨G, hG, hysG⟩ := Finset.mem_biUnion.mp hys
  have hxp := (mem_familyOrderings_iff F xs).mp hxsF
  have hyp := (mem_familyOrderings_iff G ys).mp hysG
  have hxlen : xs.length = h := by simpa [Finset.length_toList, hcard F hF] using hxp.length_eq
  have hylen : ys.length = h := by simpa [Finset.length_toList, hcard G hG] using hyp.length_eq
  let S := (xs.take (h-1)).toFinset
  have hSF : S ⊆ F := by
    intro x hx
    have hxx : x ∈ xs.take (h-1) := List.mem_toFinset.mp hx
    rw [← familyOrderings_recover F xs hxsF]
    exact List.mem_toFinset.mpr (List.mem_of_mem_take hxx)
  have hSG : S ⊆ G := by
    intro x hx
    have hyy : x ∈ ys.take (h-1) := by
      rw [← heq]
      exact List.mem_toFinset.mp hx
    rw [← familyOrderings_recover G ys hysG]
    exact List.mem_toFinset.mpr (List.mem_of_mem_take hyy)
  have hS : S.card + 1 = h := by
    have hnd : (xs.take (h-1)).Nodup := (familyOrderings_nodup F xs hxsF).take
    rw [show S.card = (xs.take (h-1)).length from List.toFinset_card_of_nodup hnd]
    rw [List.length_take, hxlen, Nat.min_eq_left (by omega : h-1 ≤ h)]
    omega
  have hFG : F = G := hunique F hF G hG S hSF hSG hS
  subst G
  have hperm : xs.Perm ys := hxp.trans hyp.symm
  have htail : (xs.drop (h-1)).Perm (ys.drop (h-1)) := by
    have hparts : (xs.take (h-1) ++ xs.drop (h-1)).Perm
        (ys.take (h-1) ++ ys.drop (h-1)) := by simpa only [List.take_append_drop] using hperm
    rw [← heq] at hparts
    exact (List.perm_append_left_iff (xs.take (h-1))).mp hparts
  have hyone : (ys.drop (h-1)).length = 1 := by simp [List.length_drop, hylen]; omega
  obtain ⟨y, hy⟩ := List.length_eq_one_iff.mp hyone
  have hdrop : xs.drop (h-1) = ys.drop (h-1) := by
    rw [hy] at htail ⊢
    exact List.perm_singleton.mp htail
  calc
    xs = xs.take (h-1) ++ xs.drop (h-1) := (List.take_append_drop _ _).symm
    _ = ys.take (h-1) ++ ys.drop (h-1) := by rw [heq, hdrop]
    _ = ys := List.take_append_drop _ _

theorem ordered_prefixes_card
    (𝓕 : Finset (Finset α)) (h : ℕ) (hh : 1 ≤ h)
    (hcard : ∀ F ∈ 𝓕, F.card = h)
    (hunique : ∀ F ∈ 𝓕, ∀ G ∈ 𝓕, ∀ S : Finset α,
      S ⊆ F → S ⊆ G → S.card + 1 = h → F = G) :
    ((orderingsOfFamilies 𝓕).image (fun xs => xs.take (h-1))).card =
      𝓕.card * h.factorial := by
  rw [Finset.card_image_of_injOn (prefix_injective_of_unique_completion 𝓕 h hh hcard hunique),
    orderingsOfFamilies_card 𝓕 h hcard]

/-- If exactly one row of a partition is omitted, that row is the complement
of the union of the other rows in the physical site set. -/
theorem missing_row_eq_residual {β : Type*} [DecidableEq β]
    (V : Finset β) (F S : Finset (Finset β)) (R : Finset β)
    (hS : S ⊆ F) (hcard : S.card + 1 = F.card)
    (hcover : F.biUnion id = V)
    (hdis : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → Disjoint A B)
    (hRF : R ∈ F) (hRS : R ∉ S) :
    R = V \ S.biUnion id := by
  classical
  have hdiff : (F \ S).card = 1 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hS]
    omega
  have huniq := Finset.card_le_one.mp (show (F \ S).card ≤ 1 by omega)
  ext x
  constructor
  · intro hx
    apply Finset.mem_sdiff.mpr
    constructor
    · rw [← hcover]
      exact Finset.mem_biUnion.mpr ⟨R,hRF,hx⟩
    · intro hmem
      obtain ⟨A,hAS,hxA⟩ := Finset.mem_biUnion.mp hmem
      have hne : R ≠ A := by intro heq; subst A; exact hRS hAS
      exact (Finset.disjoint_left.mp (hdis R hRF A (hS hAS) hne)) hx hxA
  · intro hx
    obtain ⟨hxV,hxS⟩ := Finset.mem_sdiff.mp hx
    rw [← hcover] at hxV
    obtain ⟨A,hAF,hxA⟩ := Finset.mem_biUnion.mp hxV
    have hAS : A ∉ S := by
      intro hAS
      exact hxS (Finset.mem_biUnion.mpr ⟨A,hAS,hxA⟩)
    have hAR : A = R := huniq A (Finset.mem_sdiff.mpr ⟨hAF,hAS⟩)
      R (Finset.mem_sdiff.mpr ⟨hRF,hRS⟩)
    simpa [hAR] using hxA

/-- Two partitions cannot differ only in their final row: their common
`h-1` rows already determine the same physical complement. -/
theorem partition_unique_completion {β : Type*} [DecidableEq β]
    (V : Finset β) (𝓕 : Finset (Finset (Finset β))) (h : ℕ)
    (hcard : ∀ F ∈ 𝓕, F.card = h)
    (hcover : ∀ F ∈ 𝓕, F.biUnion id = V)
    (hdis : ∀ F ∈ 𝓕, ∀ A ∈ F, ∀ B ∈ F, A ≠ B → Disjoint A B)
    (F : Finset (Finset β)) (hF : F ∈ 𝓕)
    (G : Finset (Finset β)) (hG : G ∈ 𝓕) (S : Finset (Finset β))
    (hSF : S ⊆ F) (hSG : S ⊆ G) (hS : S.card + 1 = h) : F = G := by
  classical
  have hltF : S.card < F.card := by rw [hcard F hF]; omega
  have hltG : S.card < G.card := by rw [hcard G hG]; omega
  obtain ⟨RF,hRF,hRFS⟩ := Finset.exists_mem_notMem_of_card_lt_card hltF
  obtain ⟨RG,hRG,hRGS⟩ := Finset.exists_mem_notMem_of_card_lt_card hltG
  have hRFres : RF = V \ S.biUnion id := missing_row_eq_residual V F S RF hSF
    (by rw [hcard F hF]; exact hS) (hcover F hF) (hdis F hF) hRF hRFS
  have hRGres : RG = V \ S.biUnion id := missing_row_eq_residual V G S RG hSG
    (by rw [hcard G hG]; exact hS) (hcover G hG) (hdis G hG) hRG hRGS
  have hsame : RF = RG := hRFres.trans hRGres.symm
  apply Finset.Subset.antisymm
  · intro R hR
    by_cases hRS : R ∈ S
    · exact hSG hRS
    · have hRres := missing_row_eq_residual V F S R hSF
        (by rw [hcard F hF]; exact hS) (hcover F hF) (hdis F hF) hR hRS
      have hRRG : R = RG := hRres.trans hRGres.symm
      simpa [hRRG] using hRG
  · intro R hR
    by_cases hRS : R ∈ S
    · exact hSF hRS
    · have hRres := missing_row_eq_residual V G S R hSG
        (by rw [hcard G hG]; exact hS) (hcover G hG) (hdis G hG) hR hRS
      have hRRF : R = RF := hRres.trans hRFres.symm
      simpa [hRRF] using hRF

/-- For actual finite partitions, the ordered `h-1` prefixes have exactly
`h!` representations per unlabelled family. -/
theorem partition_prefixes_card {β : Type*} [DecidableEq β]
    (V : Finset β) (𝓕 : Finset (Finset (Finset β))) (h : ℕ) (hh : 1 ≤ h)
    (hcard : ∀ F ∈ 𝓕, F.card = h)
    (hcover : ∀ F ∈ 𝓕, F.biUnion id = V)
    (hdis : ∀ F ∈ 𝓕, ∀ A ∈ F, ∀ B ∈ F, A ≠ B → Disjoint A B) :
    ((orderingsOfFamilies 𝓕).image (fun xs => xs.take (h-1))).card =
      𝓕.card * h.factorial :=
  ordered_prefixes_card 𝓕 h hh hcard (partition_unique_completion V 𝓕 h hcard hcover hdis)

/-- Prefixes actually arising from orderings of the specified families. -/
noncomputable def familyPrefixes (𝓕 : Finset (Finset α)) (k : ℕ) : Finset (List α) :=
  (orderingsOfFamilies 𝓕).image (List.take k)

theorem ordering_length (𝓕 : Finset (Finset α)) (h : ℕ)
    (hcard : ∀ F ∈ 𝓕, F.card = h) (xs : List α)
    (hxs : xs ∈ orderingsOfFamilies 𝓕) : xs.length = h := by
  obtain ⟨F,hF,hxsF⟩ := Finset.mem_biUnion.mp hxs
  have hp := (mem_familyOrderings_iff F xs).mp hxsF
  simpa [Finset.length_toList, hcard F hF] using hp.length_eq

/-- Every prefix of length `k+1` extends one of length `k` by an allowed
actual row. The allowed extensions are given independently of the bound. -/
theorem familyPrefixes_succ_subset
    (𝓕 : Finset (Finset α)) (h k : ℕ)
    (hcard : ∀ F ∈ 𝓕, F.card = h) (hk : k < h)
    (allowed : List α → Finset α)
    (hnext : ∀ xs ∈ orderingsOfFamilies 𝓕, ∀ (j : ℕ) (hj : j < xs.length),
      xs[j] ∈ allowed (xs.take j)) :
    familyPrefixes 𝓕 (k+1) ⊆
      (familyPrefixes 𝓕 k).biUnion (fun p => (allowed p).image (fun a => p ++ [a])) := by
  classical
  intro q hq
  obtain ⟨xs,hxs,rfl⟩ := Finset.mem_image.mp hq
  have hlen := ordering_length 𝓕 h hcard xs hxs
  have hkl : k < xs.length := by omega
  rw [List.take_succ_eq_append_getElem hkl]
  apply Finset.mem_biUnion.mpr
  refine ⟨xs.take k,Finset.mem_image.mpr ⟨xs,hxs,rfl⟩,?_⟩
  exact Finset.mem_image.mpr ⟨xs[k],hnext xs hxs k hkl,rfl⟩

theorem familyPrefixes_card_succ_le
    (𝓕 : Finset (Finset α)) (h k : ℕ)
    (hcard : ∀ F ∈ 𝓕, F.card = h) (hk : k < h)
    (allowed : List α → Finset α)
    (hnext : ∀ xs ∈ orderingsOfFamilies 𝓕, ∀ (j : ℕ) (hj : j < xs.length),
      xs[j] ∈ allowed (xs.take j)) (b : ℝ)
    (hbranch : ∀ p ∈ familyPrefixes 𝓕 k, ((allowed p).card : ℝ) ≤ b) :
    ((familyPrefixes 𝓕 (k+1)).card : ℝ) ≤
      ((familyPrefixes 𝓕 k).card : ℝ) * b := by
  classical
  have hn : (familyPrefixes 𝓕 (k+1)).card ≤
      ∑ p ∈ familyPrefixes 𝓕 k, (allowed p).card := by
    calc
      _ ≤ ((familyPrefixes 𝓕 k).biUnion
          (fun p => (allowed p).image (fun a => p ++ [a]))).card :=
        Finset.card_le_card (familyPrefixes_succ_subset 𝓕 h k hcard hk allowed hnext)
      _ ≤ ∑ p ∈ familyPrefixes 𝓕 k, ((allowed p).image (fun a => p ++ [a])).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ p ∈ familyPrefixes 𝓕 k, (allowed p).card :=
        Finset.sum_le_sum (fun p _ => Finset.card_image_le)
  calc
    ((familyPrefixes 𝓕 (k+1)).card : ℝ) ≤
        ∑ p ∈ familyPrefixes 𝓕 k, ((allowed p).card : ℝ) := by exact_mod_cast hn
    _ ≤ ∑ _p ∈ familyPrefixes 𝓕 k, b := Finset.sum_le_sum hbranch
    _ = ((familyPrefixes 𝓕 k).card : ℝ) * b := by simp

/-- Product bound for arbitrary, history-dependent extension sets. This is
deterministic counting; it never assumes independent successive choices. -/
theorem familyPrefixes_card_le_product
    (𝓕 : Finset (Finset α)) (h : ℕ)
    (hcard : ∀ F ∈ 𝓕, F.card = h) (allowed : List α → Finset α)
    (hnext : ∀ xs ∈ orderingsOfFamilies 𝓕, ∀ (j : ℕ) (hj : j < xs.length),
      xs[j] ∈ allowed (xs.take j)) (b : ℕ → ℝ)
    (hb : ∀ j, 0 ≤ b j)
    (hbranch : ∀ j < h, ∀ p ∈ familyPrefixes 𝓕 j, ((allowed p).card : ℝ) ≤ b j) :
    ∀ k ≤ h, ((familyPrefixes 𝓕 k).card : ℝ) ≤ ∏ j ∈ Finset.range k, b j := by
  intro k
  induction k with
  | zero =>
    intro _
    have hsub : familyPrefixes 𝓕 0 ⊆ {[]} := by
      intro xs hxs
      obtain ⟨ys,_,rfl⟩ := Finset.mem_image.mp hxs
      simp
    have hc := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hc
    simpa using (show ((familyPrefixes 𝓕 0).card : ℝ) ≤ 1 by exact_mod_cast hc)
  | succ k ih =>
    intro hk
    have hklt : k < h := by omega
    have hprev := ih (by omega)
    have hstep := familyPrefixes_card_succ_le 𝓕 h k hcard hklt allowed hnext (b k)
      (hbranch k hklt)
    calc
      ((familyPrefixes 𝓕 (k+1)).card : ℝ) ≤ ((familyPrefixes 𝓕 k).card : ℝ) * b k := hstep
      _ ≤ (∏ j ∈ Finset.range k, b j) * b k := mul_le_mul_of_nonneg_right hprev (hb k)
      _ = ∏ j ∈ Finset.range (k+1), b j := (Finset.prod_range_succ b k).symm

/-- The exact partition quotient and the history-dependent product bound
in a single finite inequality. -/
theorem partition_count_from_branching {β : Type*} [DecidableEq β]
    (V : Finset β) (𝓕 : Finset (Finset (Finset β))) (h : ℕ) (hh : 1 ≤ h)
    (hcard : ∀ F ∈ 𝓕, F.card = h)
    (hcover : ∀ F ∈ 𝓕, F.biUnion id = V)
    (hdis : ∀ F ∈ 𝓕, ∀ A ∈ F, ∀ B ∈ F, A ≠ B → Disjoint A B)
    (allowed : List (Finset β) → Finset (Finset β))
    (hnext : ∀ xs ∈ orderingsOfFamilies 𝓕, ∀ (j : ℕ) (hj : j < xs.length),
      xs[j] ∈ allowed (xs.take j)) (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j)
    (hbranch : ∀ j < h, ∀ p ∈ familyPrefixes 𝓕 j, ((allowed p).card : ℝ) ≤ b j) :
    (𝓕.card : ℝ) * (h.factorial : ℝ) ≤ ∏ j ∈ Finset.range (h-1), b j := by
  have hprod := familyPrefixes_card_le_product 𝓕 h hcard allowed hnext b hb hbranch
    (h-1) (by omega)
  rw [familyPrefixes, partition_prefixes_card V 𝓕 h hh hcard hcover hdis] at hprod
  exact_mod_cast hprod

end CorralFormalization.Results.OrderedPartitionCounting
