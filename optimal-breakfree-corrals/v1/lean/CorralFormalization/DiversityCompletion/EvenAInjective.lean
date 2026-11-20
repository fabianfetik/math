import CorralFormalization.DiversityCompletion.EvenSwitches

/-! Literal bit recovery from the actual D4 A-row, without an assumed
decoder. Sorting the physical sites recovers every prefix position. -/

namespace CorralFormalization.EvenSwitches

theorem properPrefixSites_get (g : List ℕ) (i : ℕ) (hi : i < g.length) :
    (properPrefixSites g)[i]'(by rw [properPrefixSites_length]; exact hi) =
      (g.take i).sum := by
  induction g generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => simp [properPrefixSites]
    | succ i =>
      have hi' : i < xs.length := by simpa using hi
      simp only [properPrefixSites, List.getElem_cons_succ, List.getElem_map,
        List.take_succ_cons, List.sum_cons]
      rw [ih i hi']

theorem rowA_sorted_prefixes (m : ℕ) (hm : 1 ≤ m) (a : Choices m) :
    (rowA m a).sort (· ≤ ·) = properPrefixSites (switchedWordA m a) := by
  have hp : ∀ x ∈ switchedWordA m a, 0 < x := by
    intro x hx
    exact ((fullGapList_mem _ _).mp ((switchedWordA_perm m hm a).mem_iff.mp hx)).1
  have ho := properPrefixSites_strict (switchedWordA m a) hp
  have hd : (properPrefixSites (switchedWordA m a)).Nodup :=
    ho.imp (by intro x y h; omega)
  rw [rowA_eq_properPrefixes m hm a]
  exact (List.toFinset_sort (· ≤ ·) hd).2 (ho.imp (by intro x y h; omega))

theorem rowA_same_sites (m : ℕ) (hm : 1 ≤ m) (a b : Choices m)
    (heq : rowA m a = rowA m b) (i : ℕ) (hi : i < order m) :
    siteA m a i = siteA m b i := by
  have hp : properPrefixSites (switchedWordA m a) = properPrefixSites (switchedWordA m b) := by
    calc
      _ = (rowA m a).sort (· ≤ ·) := (rowA_sorted_prefixes m hm a).symm
      _ = (rowA m b).sort (· ≤ ·) := by rw [heq]
      _ = _ := rowA_sorted_prefixes m hm b
  have ha : i < (properPrefixSites (switchedWordA m a)).length := by
    rw [properPrefixSites_length, switchedWordA_length]; exact hi
  have hb : i < (properPrefixSites (switchedWordA m b)).length := by
    rw [properPrefixSites_length, switchedWordA_length]; exact hi
  have hla : i < (switchedWordA m a).length := by rw [switchedWordA_length]; exact hi
  have hlb : i < (switchedWordA m b).length := by rw [switchedWordA_length]; exact hi
  have hg := congrArg (fun l : List ℕ => l.getD i 0) hp
  rw [List.getD_eq_getElem _ 0 ha, List.getD_eq_getElem _ 0 hb] at hg
  rw [properPrefixSites_get (switchedWordA m a) i hla,
    properPrefixSites_get (switchedWordA m b) i hlb] at hg
  exact (siteA_eq_prefix m hm a i hi).trans (hg.trans (siteA_eq_prefix m hm b i hi).symm)

/-- Each D3 bit is recovered from the actual row A, uniformly for all
allowed m, including the empty upper-bit range at m=1. -/
theorem rowA_injective (m : ℕ) (hm : 1 ≤ m) : Function.Injective (rowA m) := by
  intro a b heq
  apply Prod.ext
  · funext i
    have hi := i.isLt
    let j := i.val + 1
    have hj : j ≤ 2*m := by dsimp [j]; omega
    have hs := rowA_same_sites m hm a b heq (2*j+1) (by unfold order; omega)
    rw [siteA_lower m a j hj, siteA_lower m b j hj] at hs
    unfold lowerA at hs
    have hf : 0 < height m - 1 := by unfold height; omega
    have hc := Nat.mul_right_cancel hf hs
    have hv : eta m a.1 j = eta m b.1 j := by
      omega
    have ht : (a.1 i).toNat = (b.1 i).toNat := by
      dsimp [j] at hv
      simpa only [eta_recover] using hv
    cases ha : a.1 i <;> cases hb : b.1 i <;> simp_all [Bool.toNat]
  · funext i
    have hi := i.isLt
    let j := i.val + 2
    have hs := rowA_same_sites m hm a b heq (4*m+2+2*j) (by unfold order; dsimp [j]; omega)
    rw [siteA_upper m a j, siteA_upper m b j] at hs
    have hv : epsilon m a.2 j = epsilon m b.2 j := by
      unfold upperA at hs
      omega
    have ht : (a.2 i).toNat = (b.2 i).toNat := by
      dsimp [j] at hv
      simpa only [epsilon_recover] using hv
    cases ha : a.2 i <;> cases hb : b.2 i <;> simp_all [Bool.toNat]

/-- No two bit choices give the same actual A row on the physical clock. -/
theorem rowA_physical_injective (m : ℕ) (hm : 1 ≤ m) :
    Function.Injective (fun a : Choices m => PhysicalCorral.physicalSites (clock m) (rowA m a)) := by
  let : NeZero (clock m) := ⟨by unfold clock height order; positivity⟩
  intro a b heq
  apply rowA_injective m hm
  have h := congrArg (fun S : Finset (ZMod (clock m)) => S.image ZMod.val) heq
  rw [PhysicalCorral.physicalSites_decode (rowA m a) (rowA_bounded m hm a),
    PhysicalCorral.physicalSites_decode (rowA m b) (rowA_bounded m hm b)] at h
  exact h

end CorralFormalization.EvenSwitches
