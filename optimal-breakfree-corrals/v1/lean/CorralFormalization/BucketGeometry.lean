import CorralFormalization.Basic

namespace CorralFormalization

/-- Translation by a whole block rotates the block index while preserving the
local remainder. This is the coordinate step used in equation (9) of the
corrected paper; it does not assert that any particular bucket is nonempty. -/
theorem translate_block_remainder
    (h K b s r : ℕ) (hh : 0 < h) (hr : r < K) :
    (b * K + r + K * s) % (h * K) = ((b + s) % h) * K + r := by
  have hrwidth : r < h * K := by nlinarith
  have hblock : (b + s) % h < h := Nat.mod_lt _ hh
  have hresult : ((b + s) % h) * K + r < h * K := by nlinarith
  calc
    (b * K + r + K * s) % (h * K) = ((b + s) * K + r) % (h * K) := by
      congr 1
      ring
    _ = (((b + s) * K) % (h * K) + r % (h * K)) % (h * K) :=
      Nat.add_mod _ _ _
    _ = (((b + s) % h) * K + r) % (h * K) := by
      rw [Nat.mul_mod_mul_right, Nat.mod_eq_of_lt hrwidth]
    _ = ((b + s) % h) * K + r := Nat.mod_eq_of_lt hresult

/-- Local remainders of points of `Q` in the block indexed by `ell`.
This matches the corrected manuscript's definition of `B_ell`. -/
def localBucket (K ell : ℕ) (Q : Finset ℕ) : Finset ℕ :=
  (Finset.range K).filter (fun r => ell * K + r ∈ Q)

/-- Rotate the physical representatives in `Q` by `K*s` on the `h*K` clock. -/
def translatedSites (h K s : ℕ) (Q : Finset ℕ) : Finset ℕ :=
  Q.image (fun q => (q + K * s) % (h * K))

/-- The sites in the first block after translation are exactly the local
remainders in the unique source block that rotates to block zero. -/
theorem first_block_iff_local_bucket
    (h K s ell r : ℕ) (Q : Finset ℕ)
    (hh : 0 < h) (hK : 0 < K) (hell : ell < h) (hr : r < K)
    (hQ : ∀ q ∈ Q, q < h * K) (hfirst : (ell + s) % h = 0) :
    r ∈ translatedSites h K s Q ↔ r ∈ localBucket K ell Q := by
  constructor
  · intro hmem
    obtain ⟨q, hq, hshift⟩ := Finset.mem_image.mp hmem
    have hquot : q / K < h := (Nat.div_lt_iff_lt_mul hK).2 (hQ q hq)
    have hrem : q % K < K := Nat.mod_lt q hK
    have hdecomp : (q / K) * K + q % K = q := by
      simpa [Nat.add_comm] using Nat.mod_add_div' q K
    have htrans := translate_block_remainder h K (q / K) s (q % K) hh hrem
    rw [hdecomp] at htrans
    have heval : ((q / K + s) % h) * K + q % K = r := htrans.symm.trans hshift
    have hzero : (q / K + s) % h = 0 := by
      by_contra hnz
      have hone : 1 ≤ (q / K + s) % h := Nat.one_le_iff_ne_zero.mpr hnz
      have hmul : K ≤ ((q / K + s) % h) * K := by
        simpa using Nat.mul_le_mul_right K hone
      omega
    have hmod : (q / K + s) % h = (ell + s) % h := by simp [hzero, hfirst]
    have hindex : q / K = ell :=
      (Nat.ModEq.add_right_cancel' s hmod).eq_of_lt_of_lt hquot hell
    have hlocal : q % K = r := by simpa [hzero] using heval
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_range.mpr hr
    · have hpoint : ell * K + r = q := by rw [← hindex, ← hlocal, hdecomp]
      simpa [hpoint] using hq
  · intro hmem
    obtain ⟨_, hpoint⟩ := Finset.mem_filter.mp hmem
    apply Finset.mem_image.mpr
    refine ⟨ell * K + r, hpoint, ?_⟩
    simpa [hfirst] using translate_block_remainder h K ell s r hh hr

/-- If the source bucket that rotates to block zero is nonempty, its least
local remainder is the least physical site after translation. This is the
head identity in equation (9), under the paper's explicit bucket convention. -/
theorem first_site_eq_bucket_min
    (h K s ell : ℕ) (Q : Finset ℕ)
    (hh : 0 < h) (hK : 0 < K) (hell : ell < h)
    (hQ : ∀ q ∈ Q, q < h * K) (hfirst : (ell + s) % h = 0)
    (hne : (localBucket K ell Q).Nonempty) :
    ∃ hsites : (translatedSites h K s Q).Nonempty,
      (translatedSites h K s Q).min' hsites = (localBucket K ell Q).min' hne := by
  let m := (localBucket K ell Q).min' hne
  have hm : m ∈ localBucket K ell Q := Finset.min'_mem _ hne
  have hmrange : m < K := Finset.mem_range.mp (Finset.mem_filter.mp hm).1
  have hrot : m ∈ translatedSites h K s Q :=
    (first_block_iff_local_bucket h K s ell m Q hh hK hell hmrange hQ hfirst).2 hm
  have hsites : (translatedSites h K s Q).Nonempty := ⟨m, hrot⟩
  refine ⟨hsites, le_antisymm (Finset.min'_le _ m hrot) ?_⟩
  apply Finset.le_min' _ hsites m
  intro x hx
  by_cases hxrange : x < K
  · have hbucket : x ∈ localBucket K ell Q :=
      (first_block_iff_local_bucket h K s ell x Q hh hK hell hxrange hQ hfirst).1 hx
    exact Finset.min'_le _ x hbucket
  · omega

/-- The points in the final translated block have exactly the local
remainders from the unique source block that rotates to that block. -/
theorem last_block_iff_local_bucket
    (h K s b r : ℕ) (Q : Finset ℕ)
    (hh : 0 < h) (hK : 0 < K) (hb : b < h) (hr : r < K)
    (hQ : ∀ q ∈ Q, q < h * K) (hlast : (b + s) % h = h - 1) :
    (h - 1) * K + r ∈ translatedSites h K s Q ↔ r ∈ localBucket K b Q := by
  constructor
  · intro hmem
    obtain ⟨q, hq, hshift⟩ := Finset.mem_image.mp hmem
    have hquot : q / K < h := (Nat.div_lt_iff_lt_mul hK).2 (hQ q hq)
    have hrem : q % K < K := Nat.mod_lt q hK
    have hdecomp : (q / K) * K + q % K = q := by
      simpa [Nat.add_comm] using Nat.mod_add_div' q K
    have htrans := translate_block_remainder h K (q / K) s (q % K) hh hrem
    rw [hdecomp] at htrans
    have heval : ((q / K + s) % h) * K + q % K = (h - 1) * K + r :=
      htrans.symm.trans hshift
    have hindexlt : (q / K + s) % h < h := Nat.mod_lt _ hh
    have hlastindex : (q / K + s) % h = h - 1 := by
      by_contra hne
      have hle : (q / K + s) % h + 1 ≤ h - 1 := by omega
      have hmul := Nat.mul_le_mul_right K hle
      have hlt : ((q / K + s) % h) * K + q % K <
          (((q / K + s) % h) + 1) * K := by nlinarith
      omega
    have hmod : (q / K + s) % h = (b + s) % h := by simp [hlastindex, hlast]
    have hindex : q / K = b :=
      (Nat.ModEq.add_right_cancel' s hmod).eq_of_lt_of_lt hquot hb
    have hlocal : q % K = r := by rw [hlastindex] at heval; omega
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_range.mpr hr
    · have hpoint : b * K + r = q := by rw [← hindex, ← hlocal, hdecomp]
      simpa [hpoint] using hq
  · intro hmem
    obtain ⟨_, hpoint⟩ := Finset.mem_filter.mp hmem
    apply Finset.mem_image.mpr
    refine ⟨b * K + r, hpoint, ?_⟩
    simpa [hlast] using translate_block_remainder h K b s r hh hr

/-- If the source bucket that rotates to the final block is nonempty, the
last translated site and its tail deficit are its largest local remainder
placed in that final block. This is the tail identity in equation (9). -/
theorem last_site_and_tail_eq_bucket_max
    (h K s b : ℕ) (Q : Finset ℕ)
    (hh : 0 < h) (hK : 0 < K) (hb : b < h)
    (hQ : ∀ q ∈ Q, q < h * K) (hlast : (b + s) % h = h - 1)
    (hne : (localBucket K b Q).Nonempty) :
    ∃ hsites : (translatedSites h K s Q).Nonempty,
      (translatedSites h K s Q).max' hsites =
        (h - 1) * K + (localBucket K b Q).max' hne ∧
      h * K - (translatedSites h K s Q).max' hsites =
        K - (localBucket K b Q).max' hne := by
  let m := (localBucket K b Q).max' hne
  have hm : m ∈ localBucket K b Q := Finset.max'_mem _ hne
  have hmrange : m < K := Finset.mem_range.mp (Finset.mem_filter.mp hm).1
  have hrot : (h - 1) * K + m ∈ translatedSites h K s Q :=
    (last_block_iff_local_bucket h K s b m Q hh hK hb hmrange hQ hlast).2 hm
  have hsites : (translatedSites h K s Q).Nonempty := ⟨_, hrot⟩
  have hwidth : (h - 1) * K + K = h * K := by
    have hh' : h - 1 + 1 = h := Nat.sub_add_cancel hh
    nlinarith
  have hmax : (translatedSites h K s Q).max' hsites = (h - 1) * K + m := by
    apply le_antisymm
    · apply Finset.max'_le _ hsites ((h - 1) * K + m)
      intro x hx
      obtain ⟨q, _, hxq⟩ := Finset.mem_image.mp hx
      have hxlt : x < h * K := by
        rw [← hxq]
        exact Nat.mod_lt _ (Nat.mul_pos hh hK)
      by_cases hsmall : x < (h - 1) * K
      · omega
      · have hstart : (h - 1) * K ≤ x := by omega
        have hrem : x - (h - 1) * K < K := by omega
        have hxpoint : (h - 1) * K + (x - (h - 1) * K) ∈
            translatedSites h K s Q := by simpa [Nat.add_sub_of_le hstart] using hx
        have hbucket : x - (h - 1) * K ∈ localBucket K b Q :=
          (last_block_iff_local_bucket h K s b _ Q hh hK hb hrem hQ hlast).1 hxpoint
        have hle : x - (h - 1) * K ≤ m := Finset.le_max' _ _ hbucket
        omega
    · exact Finset.le_max' _ _ hrot
  refine ⟨hsites, hmax, ?_⟩
  rw [hmax]
  omega

/-- Concrete source-block indices for an owner `s`, including the wrap at
`s=0`. They agree with `ell = -s mod h` and its cyclic predecessor. -/
theorem source_block_indices
    (h s : ℕ) (hh : 0 < h) (hs : s < h) :
    let ell := (h - s) % h
    let b := h - 1 - s
    ell < h ∧ (ell + s) % h = 0 ∧ b < h ∧
      (b + s) % h = h - 1 ∧ (b + 1) % h = ell ∧
      b = (ell + h - 1) % h := by
  dsimp
  have hell : (h - s) % h < h := Nat.mod_lt _ hh
  have hfirst : ((h - s) % h + s) % h = 0 := by
    by_cases hs0 : s = 0
    · simp [hs0]
    · have hsub : h - s < h := by omega
      rw [Nat.mod_eq_of_lt hsub]
      have hsum : h - s + s = h := by omega
      rw [hsum, Nat.mod_self]
  have hb : h - 1 - s < h := by omega
  have hlast : (h - 1 - s + s) % h = h - 1 := by
    have hsum : h - 1 - s + s = h - 1 := by omega
    rw [hsum, Nat.mod_eq_of_lt (by omega : h - 1 < h)]
  have hpred : (h - 1 - s + 1) % h = (h - s) % h := by
    have hsum : h - 1 - s + 1 + s = h := by omega
    have hcongr : (h - 1 - s + 1 + s) ≡ ((h - s) % h + s) [MOD h] := by
      change (h - 1 - s + 1 + s) % h = ((h - s) % h + s) % h
      rw [hsum, Nat.mod_self, hfirst]
    have hcancel := Nat.ModEq.add_right_cancel' s hcongr
    change (h - 1 - s + 1) % h = ((h - s) % h) % h at hcancel
    simpa [Nat.mod_eq_of_lt hell] using hcancel
  have hpred_explicit : h - 1 - s = ((h - s) % h + h - 1) % h := by
    have hsum : (h - s) % h + h - 1 + 1 = (h - s) % h + h := by omega
    have hright : ((h - s) % h + h) % h = (h - s) % h := by
      simp [Nat.mod_eq_of_lt hell]
    have hcongr : (h - 1 - s + 1) ≡ (((h - s) % h + h - 1) + 1) [MOD h] := by
      change (h - 1 - s + 1) % h = (((h - s) % h + h - 1) + 1) % h
      rw [hsum, hright, hpred]
    have hcancel := Nat.ModEq.add_right_cancel' 1 hcongr
    change (h - 1 - s) % h = ((h - s) % h + h - 1) % h at hcancel
    simpa [Nat.mod_eq_of_lt hb] using hcancel
  exact ⟨hell, hfirst, hb, hlast, hpred, hpred_explicit⟩

/-- Equation (9) for the paper's literal bucket definition: if the two
relevant source buckets are nonempty, their local extrema give the actual
first site and tail deficit of the translated physical set. The concrete
paper must still prove that its specific buckets are nonempty. -/
theorem explicit_bucket_endpoint_geometry
    (h K s : ℕ) (Q : Finset ℕ)
    (hh : 0 < h) (hK : 0 < K) (hs : s < h)
    (hQ : ∀ q ∈ Q, q < h * K)
    (hfirst : (localBucket K ((h - s) % h) Q).Nonempty)
    (hlast : (localBucket K (h - 1 - s) Q).Nonempty) :
    ∃ hsites : (translatedSites h K s Q).Nonempty,
      (translatedSites h K s Q).min' hsites =
        (localBucket K ((h - s) % h) Q).min' hfirst ∧
      h * K - (translatedSites h K s Q).max' hsites =
        K - (localBucket K (h - 1 - s) Q).max' hlast := by
  obtain ⟨hell, hrotatefirst, hb, hrotatelast, _⟩ := source_block_indices h s hh hs
  obtain ⟨hsites, hhead⟩ := first_site_eq_bucket_min h K s ((h - s) % h) Q
    hh hK hell hQ hrotatefirst hfirst
  obtain ⟨_, _, htail⟩ := last_site_and_tail_eq_bucket_max h K s (h - 1 - s) Q
    hh hK hb hQ hrotatelast hlast
  exact ⟨hsites, hhead, htail⟩

/-- Literal finite-set form of the paper's fiber lemma. If `P` contains
exactly one representative of each residue modulo `K`, its `h` block
translates partition all physical sites of the `h*K` clock. -/
theorem transversal_block_translates_partition
    (h K : ℕ) (P : Finset ℕ) (hh : 0 < h) (hK : 0 < K)
    (hPbound : ∀ q ∈ P, q < h * K)
    (htransversal : ∀ r, r < K → ∃! q, q ∈ P ∧ q % K = r)
    (x : ℕ) (hx : x < h * K) :
    ∃! s : Fin h, x ∈ translatedSites h K s.val P := by
  let : NeZero h := ⟨by omega⟩
  have hxrem : x % K < K := Nat.mod_lt x hK
  obtain ⟨q, ⟨hqP, hqrem⟩, hquniq⟩ := htransversal (x % K) hxrem
  have hqquot : q / K < h := (Nat.div_lt_iff_lt_mul hK).2 (hPbound q hqP)
  have hxquot : x / K < h := (Nat.div_lt_iff_lt_mul hK).2 hx
  have hqdecomp : (q / K) * K + q % K = q := by
    simpa [Nat.add_comm] using Nat.mod_add_div' q K
  have hxdecomp : (x / K) * K + x % K = x := by
    simpa [Nat.add_comm] using Nat.mod_add_div' x K
  let iq : Fin h := ⟨q / K, hqquot⟩
  let ix : Fin h := ⟨x / K, hxquot⟩
  let owner : Fin h := ix - iq
  have hsum : iq + owner = ix := by simp [owner]
  have htrans (s : Fin h) : (q + K * s.val) % (h * K) =
      ((q / K + s.val) % h) * K + q % K := by
    have h := translate_block_remainder h K (q / K) s.val (q % K) hh
      (Nat.mod_lt q hK)
    simpa [hqdecomp] using h
  have hownerindex : (q / K + owner.val) % h = x / K := by
    simpa [Fin.val_add, iq, ix] using congrArg Fin.val hsum
  refine ⟨owner, ?_, ?_⟩
  · apply Finset.mem_image.mpr
    refine ⟨q, hqP, ?_⟩
    rw [htrans, hownerindex, hqrem, hxdecomp]
  · intro s hs
    obtain ⟨y, hyP, hyshift⟩ := Finset.mem_image.mp hs
    have hyrem : y % K = x % K := by
      have hmod : ((y + K * s.val) % (h * K)) % K = y % K := by
        rw [Nat.mod_mul_left_mod, Nat.add_mul_mod_self_left]
      rw [hyshift] at hmod
      exact hmod.symm
    have hyq : y = q := hquniq y ⟨hyP, hyrem⟩
    subst y
    have heval : ((q / K + s.val) % h) * K + q % K = x := by
      rw [← htrans]
      exact hyshift
    have hmul : ((q / K + s.val) % h) * K = (x / K) * K := by
      rw [← hxdecomp] at heval
      omega
    have hindex : (q / K + s.val) % h = x / K := Nat.mul_right_cancel hK hmul
    have hsum' : iq + s = ix := by
      apply Fin.ext
      simpa [Fin.val_add, iq, ix] using hindex
    apply add_left_cancel (a := iq)
    exact hsum'.trans hsum.symm

end CorralFormalization
