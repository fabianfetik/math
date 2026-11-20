import CorralFormalization.Results.SharpUpper.RootedRows

/-!
# The sharp number of choices after any physical row prefix

The finite set `J` consists of actual unlabelled physical rows. Its local
inventory and disjointness hypotheses are used to prove the interval density,
occupied cardinality and rooted-row sample injection; no corral-count bound is
assumed.
-/

namespace CorralFormalization.Results.SharpUpper

open Finset PhysicalCorral

variable {M n : ℕ} [NeZero M]

lemma validRows_site_card (S : Finset (ZMod M)) (hS : S ∈ validRows M n) :
    S.card = n := by
  have hg := congrArg Multiset.card ((mem_filter.mp hS).2)
  rw [finiteCyclicGapInventory_card, card_image_of_injective _ (ZMod.val_injective M)] at hg
  simpa [fullGapList] using hg

lemma validRows_meets_next_interval (hn : 2 ≤ n) (S : Finset (ZMod M))
    (hS : S ∈ validRows M n) (x : ZMod M) :
    ∃ a : Fin n, x + (a.val+1 : ℕ) ∈ S := by
  have hcard : (S.image ZMod.val).card = n := by
    rw [card_image_of_injective _ (ZMod.val_injective M), validRows_site_card S hS]
  have hne : (S.image ZMod.val).Nonempty := card_pos.mp (by omega)
  have hb : ∀ s ∈ S.image ZMod.val, s < M := by
    intro s hs
    obtain ⟨y,_,rfl⟩ := mem_image.mp hs
    exact ZMod.val_lt _
  have hh := row_meets_next_interval (S.image ZMod.val) hne hb (fun g hg => by
    rw [(mem_filter.mp hS).2] at hg
    exact ((fullGapList_mem n g).mp (Multiset.mem_coe.mp hg)).2) x
  simpa only [physicalSites_encode] using hh

lemma validRows_union_card (J : Finset (Finset (ZMod M)))
    (hJ : J ⊆ validRows M n)
    (hdis : ∀ S ∈ J, ∀ T ∈ J, S ≠ T → Disjoint S T) :
    (J.biUnion id).card = J.card * n := by
  classical
  rw [card_biUnion]
  · have hh : ∀ S ∈ J, S.card = n := fun S hS => validRows_site_card S (hJ hS)
    change (∑ S ∈ J, S.card) = _
    rw [sum_congr rfl hh]
    simp
  · exact hdis

lemma validRows_union_dense (hn : 2 ≤ n) (J : Finset (Finset (ZMod M)))
    (hJ : J ⊆ validRows M n)
    (hdis : ∀ S ∈ J, ∀ T ∈ J, S ≠ T → Disjoint S T) :
    DenseNextSites (n := n) (J.biUnion id) J.card := by
  classical
  intro x
  have hc := disjoint_rows_dense_next (fun S : J => S.val)
    (fun S T hST => hdis S.val S.property T.val T.property (fun h => hST (Subtype.ext h)))
    (fun S y => validRows_meets_next_interval hn S.val (hJ S.property) y)
    (J.biUnion id) (fun S y hy => mem_biUnion.mpr ⟨S.val,S.property,hy⟩) x
  simpa only [Fintype.card_coe] using hc

/-- The concrete sharp one-row choice bound, before substituting `M=hn`
and `|F|=jn`. All sample-space multiplicities have been paid. -/
theorem disjointValidRows_card_le (hn : 2 ≤ n) (F : Finset (ZMod M))
    {j : ℕ} (hjn : j ≤ n) (hd : DenseNextSites (n := n) F j) :
    ((disjointValidRows F n).card : ℝ) ≤
      (((M-F.card : ℕ) : ℝ) / (n : ℝ)) * (n.factorial : ℝ) * avoidanceFactor n j := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have htail : 0 < ((n-j).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (n-j)
  have hdesc : 0 < (n.descFactorial j : ℝ) := by exact_mod_cast (Nat.descFactorial_pos.mpr hjn)
  have hfact : (n.factorial : ℝ) = ((n-j).factorial : ℝ) * (n.descFactorial j : ℝ) := by
    exact_mod_cast (Nat.factorial_mul_descFactorial hjn).symm
  have hc : ((disjointValidRows F n).card : ℝ) * (n : ℝ) ≤
      ((M-F.card : ℕ) : ℝ) * ((n-j : ℕ) : ℝ)^j * ((n-j).factorial : ℝ) := by
    exact_mod_cast disjointValidRows_mul_card_le hn F hjn hd
  calc
    _ = (((disjointValidRows F n).card : ℝ) * (n : ℝ)) / (n : ℝ) := by field_simp
    _ ≤ (((M-F.card : ℕ) : ℝ) * ((n-j : ℕ) : ℝ)^j * ((n-j).factorial : ℝ)) / (n : ℝ) :=
      div_le_div_of_nonneg_right hc (le_of_lt hnR)
    _ = _ := by
      rw [hfact, avoidanceFactor]
      field_simp

/-- The exact `(h-j)n! (n-j)^j/(n)_j` choice bound used in the
manuscript, for any genuine disjoint prefix of physical rows. -/
theorem physical_row_branching_bound {h n : ℕ} [NeZero (h*n)]
    (hn : 2 ≤ n) (J : Finset (Finset (ZMod (h*n))))
    (hJ : J ⊆ validRows (h*n) n)
    (hdis : ∀ S ∈ J, ∀ T ∈ J, S ≠ T → Disjoint S T)
    (hJn : J.card ≤ n) :
    ((disjointValidRows (J.biUnion id) n).card : ℝ) ≤
      ((h-J.card : ℕ) : ℝ) * (n.factorial : ℝ) * avoidanceFactor n J.card := by
  have hc := disjointValidRows_card_le hn (J.biUnion id) hJn (validRows_union_dense hn J hJ hdis)
  rw [validRows_union_card J hJ hdis, ← Nat.sub_mul] at hc
  have heq : (((h-J.card : ℕ) * n : ℕ) : ℝ) / (n : ℝ) = ((h-J.card : ℕ) : ℝ) := by
    push_cast
    exact mul_div_cancel_right₀ _ (by exact_mod_cast (show n ≠ 0 by omega))
  rw [heq] at hc
  exact hc

end CorralFormalization.Results.SharpUpper
