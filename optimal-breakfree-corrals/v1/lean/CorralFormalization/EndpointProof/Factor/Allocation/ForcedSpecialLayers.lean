import CorralFormalization.EndpointProof.Factor.Allocation.ReserveRoom
import CorralFormalization.EndpointProof.Factor.Allocation.Capped

/-! # Quantitative endpoint-forced special-layer selection -/

open scoped BigOperators Classical symmDiff
namespace EndpointFactor.Allocation
open EndpointLayeredSample
variable {α : Type*} [DecidableEq α]

/-- If forcing terminals loses at most `f` raw points compared with the
ideal capped class, the physical edit distance increases by at most `2f`. -/
theorem forced_capped_explicit_bound (raw target chosen : Finset α)
    (capacity f : ℕ) (q n d s : ℝ)
    (hq : 0 ≤ q) (hd : 0 ≤ d) (hs : 0 ≤ s)
    (hchosen : chosen ⊆ target) (hcard : chosen.card = capacity)
    (hnear : min (raw ∩ target).card capacity ≤ (raw ∩ chosen).card + f)
    (hraw : |(raw.card : ℝ) - q*n| ≤ s)
    (hcapacity : (capacity : ℝ) = q*n - q*d)
    (hmissing : ((raw \ target).card : ℝ) ≤ d) :
    ((raw ∆ chosen).card : ℝ) ≤ (2+q)*d+s+2*f := by
  have htargetcap : capacity ≤ target.card := by
    rw [← hcard]
    exact Finset.card_le_card hchosen
  have hroom : capacity ≤ ((raw ∩ target) ∪ (target ∩ target)).card := by
    have hset : (raw ∩ target) ∪ (target ∩ target) = target := by
      ext x
      simp
    rw [hset]
    exact htargetcap
  obtain ⟨ideal, _, hidealcard, _, hidealinter, _⟩ :=
    exists_capped_retain_fill raw target target capacity hroom
  have hideal := capped_symmDiff_explicit_bound raw target ideal capacity q n d s
    hq hd hs hidealcard hidealinter hraw hcapacity hmissing
  have hbalance := symmDiff_card_balance raw chosen
  have hbalanceIdeal := symmDiff_card_balance raw ideal
  rw [hcard] at hbalance
  rw [hidealcard, hidealinter] at hbalanceIdeal
  have hnat : (raw ∆ chosen).card ≤ (raw ∆ ideal).card + 2*f := by omega
  have hreal : ((raw ∆ chosen).card : ℝ) ≤ ((raw ∆ ideal).card : ℝ) + 2*(f : ℝ) := by
    exact_mod_cast hnat
  linarith

/-- The actual categorical labels of the first, second and last layers. -/
def specialVertexRole {m : ℕ} (i : Fin 3) : VertexRole m :=
  Sum.inl ⟨i.val + 1, by omega⟩

theorem specialVertexRole_injective {m : ℕ} :
    Function.Injective (@specialVertexRole m) := by
  intro i j hij
  have h : (⟨i.val+1, by omega⟩ : Fin 4) = ⟨j.val+1, by omega⟩ := Sum.inl.inj hij
  have hval : i.val+1 = j.val+1 := congrArg Fin.val h
  exact Fin.ext (Nat.add_right_cancel hval)

/-- Starts are forced into the first layer, ends into the last. -/
def specialForced {α : Type*} [DecidableEq α] (X Y : Finset α) (i : Fin 3) : Finset α :=
  if i = 0 then X else if i = 2 then Y else ∅

theorem specialForced_disjoint (X Y : Finset α) (hXY : Disjoint X Y) :
    ∀ i j, i ≠ j → Disjoint (specialForced X Y i) (specialForced X Y j) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [specialForced, Fin.ext_iff, hXY.symm]

theorem specialForced_union (X Y : Finset α) :
    forcedUnion (specialForced X Y) = X ∪ Y := by
  ext x
  simp [forcedUnion, specialForced, Fin.exists_fin_succ]

variable {G : Type*} [Fintype G] [DecidableEq G] {m : ℕ}

/-- The manuscript's three special classes, constructed from one actual
categorical sample. The numerical hypotheses are exactly the target-size,
missing-point, terminal-size and reserve-slack inputs needed here. -/
theorem exists_explicit_special_vertex_layers
    (dist : Densities m) (sample : Sample G m) (W X Y : Finset G)
    (ℓ : ℕ) (missing tolerance : ℝ)
    (hsize : SizeEvent dist tolerance sample)
    (hmissing0 : 0 ≤ missing) (htol : 0 ≤ tolerance)
    (hmiss : (((Finset.univ : Finset G) \ W).card : ℝ) ≤ missing)
    (hlayer : (ℓ : ℝ) = dist.q * Fintype.card G - dist.q * missing)
    (hslack : 4 * (missing + tolerance) ≤ dist.r * Fintype.card G)
    (hX : X ⊆ W) (hY : Y ⊆ W) (hXY : Disjoint X Y)
    (hXYcard : X.card = Y.card) (hXcap : X.card ≤ ℓ) :
    ∃ chosen : Fin 3 → Finset G,
      X ⊆ chosen 0 ∧ Y ⊆ chosen 2 ∧
      (∀ i, chosen i ⊆ W ∧ (chosen i).card = ℓ ∧
        ((vertexSet sample (specialVertexRole i) ∆ chosen i).card : ℝ) ≤
          (2+dist.q)*missing+tolerance+4*X.card) ∧
      (∀ i j, i ≠ j → Disjoint (chosen i) (chosen j)) ∧
      (∀ i, chosen i ⊆ forcedCarrier
        (fun j => vertexSet sample (specialVertexRole j)) (specialForced X Y)
          W (vertexSet sample (reserveVertex m))) := by
  let raw (i : Fin 3) := vertexSet sample (specialVertexRole i)
  let forced := specialForced X Y
  let reserve := vertexSet sample (reserveVertex m)
  let cap : Fin 3 → ℕ := fun _ => ℓ
  have hrawdisj : ∀ i j, i ≠ j → Disjoint (raw i) (raw j) := by
    intro i j hij
    exact vertexSet_disjoint sample (fun h => hij (specialVertexRole_injective h))
  have hresdisj : ∀ i, Disjoint (raw i) reserve := by
    intro i
    apply vertexSet_disjoint
    intro h
    have h' := Sum.inl.inj h
    have := congrArg Fin.val h'
    dsimp [specialVertexRole, reserveVertex] at this
    omega
  have hrawsize (i : Fin 3) :
      |((raw i).card : ℝ) - dist.q * Fintype.card G| ≤ tolerance := by
    have h := hsize.1 (specialVertexRole i)
    fin_cases i <;> simpa [raw, specialVertexRole, vertexWeight, mul_comm] using h
  have hressize : |(reserve.card : ℝ) - dist.r * Fintype.card G| ≤ tolerance := by
    have h := hsize.1 (reserveVertex m)
    simpa [reserve, reserveVertex, vertexWeight, mul_comm] using h
  have hsubmiss (R : Finset G) : ((R \ W).card : ℝ) ≤ missing := by
    have hsub : R \ W ⊆ (Finset.univ : Finset G) \ W := by
      intro x hx
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hx).2⟩
    have hc := Finset.card_le_card hsub
    have hc' : ((R \ W).card : ℝ) ≤ (((Finset.univ : Finset G) \ W).card : ℝ) := by
      exact_mod_cast hc
    exact hc'.trans hmiss
  have hdef : ∀ i, (cap i : ℝ) ≤ ((raw i ∩ W).card : ℝ) + (missing+tolerance) := by
    intro i
    exact special_deficit_bound (raw i) W ℓ dist.q (Fintype.card G) missing tolerance
      dist.q_nonneg hmissing0 (hrawsize i) hlayer (hsubmiss (raw i))
  have hreslower := eligible_reserve_lower reserve W dist.r (Fintype.card G)
    missing tolerance hressize (hsubmiss reserve)
  have hrespay : (3 : ℝ) * (missing+tolerance) ≤ ((reserve ∩ W).card : ℝ) := by
    linarith
  have hroom1 := special_capacity_from_deficits 3 raw W reserve cap
    (missing+tolerance) hdef hrespay
  have hroom := forcedCarrier_room_of_disjoint_reserve 3 raw forced W reserve cap
    hrawdisj hresdisj hroom1
  have hforceW : ∀ i, forced i ⊆ W := by
    intro i
    fin_cases i <;> simp [forced, specialForced, hX, hY]
  have hforcecap : ∀ i, (forced i).card ≤ cap i := by
    intro i
    fin_cases i <;> simp [forced, specialForced, cap, hXcap, ← hXYcard]
  obtain ⟨chosen, hchosen, hpair, _⟩ := exists_forced_classes 3 raw forced W reserve cap
    hrawdisj (specialForced_disjoint X Y hXY) hforceW hforcecap hroom
  have hFcard : (forcedUnion forced).card ≤ 2*X.card := by
    rw [show forcedUnion forced = X ∪ Y by exact specialForced_union X Y]
    have h := Finset.card_union_le X Y
    omega
  refine ⟨chosen, ?_, ?_, ?_, hpair, ?_⟩
  · simpa [forced, specialForced] using (hchosen 0).1
  · simpa [forced, specialForced] using (hchosen 2).1
  · intro i
    have hbound := forced_capped_explicit_bound (raw i) W (chosen i) ℓ
      (forcedUnion forced).card dist.q (Fintype.card G) missing tolerance
      dist.q_nonneg hmissing0 htol (hchosen i).2.2.1 (hchosen i).2.2.2.1
      (hchosen i).2.2.2.2 (hrawsize i) hlayer (hsubmiss (raw i))
    have hFreal : ((forcedUnion forced).card : ℝ) ≤ 2*X.card := by exact_mod_cast hFcard
    exact ⟨(hchosen i).2.2.1, (hchosen i).2.2.2.1, by dsimp [raw] at hbound; linarith⟩
  · intro i
    exact (hchosen i).2.1

/-- Special layers built from the promised carrier and router vertices from
the reserve can consume generic raw points only when they were prescribed
as starts or ends. This is the actual `2K` generic-loss mechanism. -/
theorem generic_blocked_subset_forced (sample : Sample G m) (W X Y router : Finset G)
    (chosen : Fin 3 → Finset G) (role : Fin m)
    (hchosen : ∀ i, chosen i ⊆ forcedCarrier
      (fun j => vertexSet sample (specialVertexRole j)) (specialForced X Y)
        W (vertexSet sample (reserveVertex m)))
    (hrouter : router ⊆ vertexSet sample (reserveVertex m)) :
    vertexSet sample (Sum.inr role) ∩ ((Finset.univ.biUnion chosen) ∪ router) ⊆ X ∪ Y := by
  intro x hx
  obtain ⟨hgeneric, hblocked⟩ := Finset.mem_inter.mp hx
  have hspecial (i : Fin 3) : Disjoint (vertexSet sample (Sum.inr role))
      (vertexSet sample (specialVertexRole i)) := by
    apply vertexSet_disjoint
    intro h
    cases h
  have hreserve : Disjoint (vertexSet sample (Sum.inr role))
      (vertexSet sample (reserveVertex m)) := by
    apply vertexSet_disjoint
    intro h
    cases h
  rcases Finset.mem_union.mp hblocked with hclasses | hrouterx
  · obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hclasses
    have hc := hchosen i hi
    rcases Finset.mem_union.mp hc with hrawreserve | hforce
    · rcases Finset.mem_union.mp hrawreserve with hraw | hres
      · obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hraw
        exact (Finset.disjoint_left.mp (hspecial j) hgeneric (Finset.mem_inter.mp hj).1).elim
      · exact (Finset.disjoint_left.mp hreserve hgeneric (Finset.mem_inter.mp hres).1).elim
    · simpa [specialForced_union] using hforce
  · exact (Finset.disjoint_left.mp hreserve hgeneric (hrouter hrouterx)).elim

theorem generic_blocked_card (sample : Sample G m) (W X Y router : Finset G)
    (chosen : Fin 3 → Finset G) (role : Fin m)
    (hchosen : ∀ i, chosen i ⊆ forcedCarrier
      (fun j => vertexSet sample (specialVertexRole j)) (specialForced X Y)
        W (vertexSet sample (reserveVertex m)))
    (hrouter : router ⊆ vertexSet sample (reserveVertex m))
    (hXYcard : X.card = Y.card) :
    (vertexSet sample (Sum.inr role) ∩ ((Finset.univ.biUnion chosen) ∪ router)).card ≤
      2*X.card := by
  have hsub := generic_blocked_subset_forced sample W X Y router chosen role hchosen hrouter
  have hc := Finset.card_le_card hsub
  have hu := Finset.card_union_le X Y
  omega

end EndpointFactor.Allocation
