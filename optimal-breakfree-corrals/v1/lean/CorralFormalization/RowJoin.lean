import CorralFormalization.Basic

namespace CorralFormalization

/-- The physical row obtained by placing the `C` component before the
owner-matched `D` component on a clock of width `U+V`. -/
def joinedRow {h : ℕ} (U : ℕ) (C D : Fin h → Finset ℕ)
    (π : Equiv.Perm (Fin h)) (i : Fin h) : Finset ℕ :=
  C i ∪ (D (π i)).image (fun y => U + y)

/-- Component bounds imply that every site of every joined row is a physical
site of the combined clock. -/
theorem joined_row_site_lt {h U V : ℕ} (C D : Fin h → Finset ℕ)
    (π : Equiv.Perm (Fin h))
    (hC : ∀ i x, x ∈ C i → x < U)
    (hD : ∀ i y, y ∈ D i → y < V)
    (i : Fin h) (x : ℕ) (hx : x ∈ joinedRow U C D π i) : x < U + V := by
  rcases Finset.mem_union.mp hx with hxC | hxD
  · have := hC i x hxC
    omega
  · obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp hxD
    have := hD (π i) y hy
    omega

/-- If each factor gives a unique physical owner, joining rows through any
owner permutation gives a unique owner for every site of the combined clock.
This proves the physical partition part of the paper's join, conditional on
the two factor partitions. It does not assert the cyclic-gap inventory. -/
theorem joined_rows_unique_owner {h U V : ℕ} (C D : Fin h → Finset ℕ)
    (π : Equiv.Perm (Fin h))
    (hCbound : ∀ i x, x ∈ C i → x < U)
    (hC : ∀ x, x < U → ∃! i, x ∈ C i)
    (hD : ∀ y, y < V → ∃! j, y ∈ D j)
    (x : ℕ) (hx : x < U + V) : ∃! i, x ∈ joinedRow U C D π i := by
  by_cases hxC : x < U
  · obtain ⟨i, hi, huniq⟩ := hC x hxC
    refine ⟨i, Finset.mem_union.mpr (Or.inl hi), ?_⟩
    intro j hj
    rcases Finset.mem_union.mp hj with hjC | hjD
    · exact huniq j hjC
    · obtain ⟨y, _, heq⟩ := Finset.mem_image.mp hjD
      omega
  · have hU : U ≤ x := by omega
    have hy : x - U < V := by omega
    obtain ⟨t, ht, huniq⟩ := hD (x - U) hy
    refine ⟨π.symm t, ?_, ?_⟩
    · apply Finset.mem_union.mpr
      right
      apply Finset.mem_image.mpr
      refine ⟨x - U, ?_, ?_⟩
      · simpa using ht
      · omega
    · intro j hj
      rcases Finset.mem_union.mp hj with hjC | hjD
      · have := hCbound j x hjC
        omega
      · obtain ⟨y, hyD, heq⟩ := Finset.mem_image.mp hjD
        have hyEq : y = x - U := by omega
        rw [hyEq] at hyD
        have howner : π j = t := huniq (π j) hyD
        apply π.injective
        simpa using howner

/-- The joined rows partition precisely the combined physical clock, provided
the bounded component rows partition their respective clocks. -/
theorem joined_rows_partition_iff {h U V : ℕ} (C D : Fin h → Finset ℕ)
    (π : Equiv.Perm (Fin h))
    (hCbound : ∀ i x, x ∈ C i → x < U)
    (hDbound : ∀ i y, y ∈ D i → y < V)
    (hC : ∀ x, x < U → ∃! i, x ∈ C i)
    (hD : ∀ y, y < V → ∃! j, y ∈ D j)
    (x : ℕ) : x < U + V ↔ ∃! i, x ∈ joinedRow U C D π i := by
  constructor
  · exact joined_rows_unique_owner C D π hCbound hC hD x
  · rintro ⟨i, hi, _⟩
    exact joined_row_site_lt C D π hCbound hDbound i x hi

/-- Under equal heads or equal tails, the seam contribution to the joined
gap multiset is exactly the union of the two removed wrap contributions.
The identification of the actual ordered row gaps with these parts is a
separate obligation. -/
theorem joined_gap_inventory_of_endpoint_match
    (interiorC interiorD : Multiset ℕ) (fC tC fD tD : ℕ)
    (hmatch : fC = fD ∨ tC = tD) :
    interiorC + interiorD + Multiset.ofList (newSeams fC tC fD tD) =
      interiorC + interiorD + Multiset.ofList (oldWraps fC tC fD tD) := by
  rcases hmatch with hheads | htails
  · rw [seam_inventory_restore_of_equal_heads fC tC fD tD hheads]
  · rw [seam_inventory_restore_of_equal_tails fC tC fD tD htails]

end CorralFormalization
