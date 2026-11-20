import CorralFormalization.EndpointProof.Flow.Matchings

/-!
Actual parameter counting and greedy inverse-closed packings for the regular
layouts.  Each exceptional equation has at most n solutions in G².  The
only nonunit coefficient used is two, whose injectivity follows from odd
cardinality.  No field or prime-order hypothesis is present.
-/

open scoped BigOperators

namespace EndpointFlow

set_option maxHeartbeats 2500000
set_option maxRecDepth 2048

abbrev PairIndex := {ij : Fin 9 × Fin 9 // ij.1 < ij.2}
abbrev EquationIndex := Sum (Fin 9) (Sum (PairIndex × Bool) (Fin 9 × Fin 6 × Bool))

theorem pairIndex_card : Fintype.card PairIndex = 36 := by decide
theorem equationIndex_card : Fintype.card EquationIndex = 189 := by decide

section Counting

variable {G : Type*} [CommRing G] [Fintype G] [DecidableEq G]

def levelSet (f : G × G → G) (c : G) : Finset (G × G) :=
  Finset.univ.filter (fun xy ↦ f xy = c)

def FiberSmall (f : G × G → G) : Prop :=
  (∀ x, Function.Injective (fun y ↦ f (x,y))) ∨
  (∀ y, Function.Injective (fun x ↦ f (x,y)))

theorem levelSet_card_le (f : G × G → G) (c : G) (hf : FiberSmall f) :
    (levelSet f c).card ≤ Fintype.card G := by
  rcases hf with hf | hf
  · have hi : Set.InjOn Prod.fst (levelSet f c : Set (G × G)) := by
      intro a ha b hb he
      apply Prod.ext he
      apply hf a.1
      calc
        f (a.1,a.2) = c := (Finset.mem_filter.mp ha).2
        _ = f (a.1,b.2) := by rw [he]; exact (Finset.mem_filter.mp hb).2.symm
    calc
      (levelSet f c).card = ((levelSet f c).image Prod.fst).card :=
        (Finset.card_image_of_injOn hi).symm
      _ ≤ (Finset.univ : Finset G).card := Finset.card_le_card (by simp)
      _ = Fintype.card G := Finset.card_univ
  · have hi : Set.InjOn Prod.snd (levelSet f c : Set (G × G)) := by
      intro a ha b hb he
      apply Prod.ext ?_ he
      apply hf a.2
      calc
        f (a.1,a.2) = c := (Finset.mem_filter.mp ha).2
        _ = f (b.1,a.2) := by rw [he]; exact (Finset.mem_filter.mp hb).2.symm
    calc
      (levelSet f c).card = ((levelSet f c).image Prod.snd).card :=
        (Finset.card_image_of_injOn hi).symm
      _ ≤ (Finset.univ : Finset G).card := Finset.card_le_card (by simp)
      _ = Fintype.card G := Finset.card_univ

theorem base_fiberSmall (s a : G) (p : Fin 3) :
    FiberSmall (fun xy ↦ base s p xy-a) := by
  fin_cases p
  · right; intro y x z h; simpa [base] using h
  · left; intro x y z h; simpa [base] using h
  · right; intro y x z h; simpa [base] using h

theorem combination_fiberSmall (hodd : Odd (Fintype.card G))
    (s a b : G) (p q : Fin 3) (plus : Bool)
    (hn : plus = true ∨ p ≠ q) :
    FiberSmall (fun xy ↦ if plus then
      (base s p xy-a)+(base s q xy-b) else
      (base s p xy-a)-(base s q xy-b)) := by
  have hd := EndpointSelector.doubling_injective_of_odd (G := G) hodd
  fin_cases p <;> fin_cases q <;> cases plus
  all_goals simp_all only [Bool.false_eq_true,false_or,
    true_or,ne_eq,not_true_eq_false,↓reduceIte]
  all_goals first
    | (left; intro x y z h; simp [base] at h
       first | linear_combination h | linear_combination -h
             | (apply hd; linear_combination h) | (apply hd; linear_combination -h))
    | (right; intro y x z h; simp [base] at h
       first | linear_combination h | linear_combination -h
             | (apply hd; linear_combination h) | (apply hd; linear_combination -h))

def equationBad (L : Layout) (r : Fin 6 → G) : EquationIndex → Finset (G × G)
  | Sum.inl j => levelSet (flow L r · j) 0
  | Sum.inr (Sum.inl ⟨ij,plus⟩) => levelSet (fun xy ↦ if plus then
      flow L r xy ij.val.1 + flow L r xy ij.val.2 else
      flow L r xy ij.val.1 - flow L r xy ij.val.2) 0
  | Sum.inr (Sum.inr ⟨j,k,b⟩) =>
      levelSet (flow L r · j) (if b then -r k else r k)

def badParameters (L : Layout) (r : Fin 6 → G) : Finset (G × G) :=
  Finset.univ.biUnion (equationBad L r)

theorem equationBad_card_le (hodd : Odd (Fintype.card G))
    (L : Layout) (r : Fin 6 → G) (hr : OffsetDistinct L r) (e : EquationIndex) :
    (equationBad L r e).card ≤ Fintype.card G := by
  rcases e with j | (⟨ij,plus⟩ | ⟨j,k,b⟩)
  · exact levelSet_card_le _ _ (base_fiberSmall _ _ _)
  · by_cases hn : plus = true ∨ path L ij.val.1 ≠ path L ij.val.2
    · exact levelSet_card_le _ _ (combination_fiberSmall hodd _ _ _ _ _ _ hn)
    · have hp : plus = false := by cases plus <;> simp_all
      have hpath : path L ij.val.1 = path L ij.val.2 := by tauto
      have hne := hr ij.val.1 ij.val.2 (ne_of_lt ij.property) hpath
      have hempty : equationBad L r (Sum.inr (Sum.inl (ij,plus))) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro xy hxy
        have he := (Finset.mem_filter.mp hxy).2
        change (if plus then _ else _) = 0 at he
        simp only [hp,Bool.false_eq_true,↓reduceIte] at he
        dsimp [flow] at he
        rw [hpath] at he
        apply hne
        linear_combination -he
      rw [hempty]; simp
  · exact levelSet_card_le _ _ (base_fiberSmall _ _ _)

/-- The literal affine-solution count, for the actual equations in the displayed layouts. -/
theorem badParameters_card_le (hodd : Odd (Fintype.card G))
    (L : Layout) (r : Fin 6 → G) (hr : OffsetDistinct L r) :
    (badParameters L r).card ≤ 189 * Fintype.card G := by
  calc
    (badParameters L r).card ≤ ∑ e : EquationIndex, (equationBad L r e).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _e : EquationIndex, Fintype.card G :=
      Finset.sum_le_sum (fun e _ ↦ equationBad_card_le hodd L r hr e)
    _ = 189 * Fintype.card G := by simp [pairIndex_card]

theorem valid_of_not_mem_badParameters (L : Layout) (r : Fin 6 → G)
    (xy : G × G) (hxy : xy ∉ badParameters L r) : Valid L r xy := by
  have havoid (e : EquationIndex) : xy ∉ equationBad L r e := by
    intro he
    exact hxy (Finset.mem_biUnion.mpr ⟨e,Finset.mem_univ _,he⟩)
  have hn (j : Fin 9) : flow L r xy j ≠ 0 := by
    intro he
    exact havoid (Sum.inl j) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩)
  have hc (i j : Fin 9) (hij : i < j) :
      flow L r xy i ≠ flow L r xy j ∧ flow L r xy i ≠ -flow L r xy j := by
    let ij : PairIndex := ⟨(i,j),hij⟩
    constructor
    · intro he
      apply havoid (Sum.inr (Sum.inl (ij,false)))
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      change flow L r xy i-flow L r xy j = 0
      rw [he,sub_self]
    · intro he
      apply havoid (Sum.inr (Sum.inl (ij,true)))
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      change flow L r xy i+flow L r xy j = 0
      rw [he,neg_add_cancel]
  refine ⟨hn,?_,?_⟩
  · intro i j hij
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact hc i j hij
    · have hh := hc j i hji
      exact ⟨Ne.symm hh.1,fun he ↦ hh.2 (by linear_combination he)⟩
  · apply Finset.disjoint_left.mpr
    intro x hx hrx
    obtain ⟨⟨j,b⟩,_,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨⟨k,c⟩,_,hc⟩ := Finset.mem_image.mp hrx
    have he : flow L r xy j = r k ∨ flow L r xy j = -r k := by
      cases b <;> cases c <;> simp only [signedFlow,Bool.false_eq_true,
        ↓reduceIte] at hc
      · exact Or.inl hc.symm
      · exact Or.inr hc.symm
      · exact Or.inr (by linear_combination hc)
      · exact Or.inl (neg_inj.mp hc).symm
    rcases he with he | he
    · exact havoid (Sum.inr (Sum.inr (j,k,false)))
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩)
    · exact havoid (Sum.inr (Sum.inr (j,k,true)))
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩)

def hitParameters (L : Layout) (r : Fin 6 → G) (F : Finset G) : Finset (G × G) :=
  Finset.univ.biUnion (fun j : Fin 9 ↦
    F.biUnion (fun c ↦ levelSet (flow L r · j) c ∪ levelSet (flow L r · j) (-c)))

theorem hitParameters_card_le (L : Layout) (r : Fin 6 → G) (F : Finset G) :
    (hitParameters L r F).card ≤ 18 * F.card * Fintype.card G := by
  have hc (j : Fin 9) (c : G) :
      (levelSet (flow L r · j) c ∪ levelSet (flow L r · j) (-c)).card ≤
        2*Fintype.card G := by
    exact (Finset.card_union_le _ _).trans (by
      have h1 := levelSet_card_le (fun xy ↦ flow L r xy j) c (base_fiberSmall _ _ _)
      have h2 := levelSet_card_le (fun xy ↦ flow L r xy j) (-c) (base_fiberSmall _ _ _)
      omega)
  calc
    (hitParameters L r F).card ≤ ∑ j : Fin 9,
        (F.biUnion (fun c ↦ levelSet (flow L r · j) c ∪
          levelSet (flow L r · j) (-c))).card := Finset.card_biUnion_le
    _ ≤ ∑ _j : Fin 9, F.card * (2*Fintype.card G) := by
      apply Finset.sum_le_sum
      intro j _
      exact Finset.card_biUnion_le_card_mul F _ _ (fun c _ ↦ hc j c)
    _ = 18 * F.card * Fintype.card G := by simp; ring

theorem disjoint_of_not_mem_hitParameters (L : Layout) (r : Fin 6 → G)
    (xy : G × G) (F : Finset G) (hh : xy ∉ hitParameters L r F) :
    Disjoint (orbitSupport L r xy) F := by
  apply Finset.disjoint_left.mpr
  intro x hx hF
  obtain ⟨⟨j,b⟩,_,he⟩ := Finset.mem_image.mp hx
  apply hh
  apply Finset.mem_biUnion.mpr
  refine ⟨j,Finset.mem_univ _,Finset.mem_biUnion.mpr ⟨x,hF,?_⟩⟩
  cases b
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩)
  · apply Finset.mem_union_right
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    change -flow L r xy j = x at he
    linear_combination -he

/-- A fresh actual pair (x,y), with no candidate-existence premise. -/
theorem exists_valid_avoiding (hodd : Odd (Fintype.card G))
    (L : Layout) (r : Fin 6 → G) (hr : OffsetDistinct L r) (F : Finset G)
    (hsize : 189 + 18*F.card < Fintype.card G) :
    ∃ xy : G × G, Valid L r xy ∧ Disjoint (orbitSupport L r xy) F := by
  have hn : 0 < Fintype.card G := Fintype.card_pos
  have hbound : (badParameters L r ∪ hitParameters L r F).card <
      (Finset.univ : Finset (G × G)).card := by
    apply lt_of_le_of_lt (Finset.card_union_le _ _) ?_
    have hb := badParameters_card_le hodd L r hr
    have hh := hitParameters_card_le L r F
    have hmul := Nat.mul_lt_mul_of_pos_right hsize hn
    simp only [Fintype.card_prod,Finset.card_univ]
    nlinarith
  obtain ⟨xy,_,hxy⟩ := Finset.exists_mem_notMem_of_card_lt_card hbound
  exact ⟨xy,valid_of_not_mem_badParameters L r xy
      (fun h ↦ hxy (Finset.mem_union_left _ h)),
    disjoint_of_not_mem_hitParameters L r xy F
      (fun h ↦ hxy (Finset.mem_union_right _ h))⟩

theorem exists_disjoint_packing (hodd : Odd (Fintype.card G))
    (L : Layout) (r : Fin 6 → G) (hr : OffsetDistinct L r) (M : ℕ)
    (hsize : 189 + 324*M < Fintype.card G) :
    ∃ U : Finset (G × G), U.card = M ∧ (∀ xy ∈ U, Valid L r xy) ∧
      (U : Set (G × G)).Pairwise
        (fun xy zw ↦ Disjoint (orbitSupport L r xy) (orbitSupport L r zw)) := by
  induction M with
  | zero => exact ⟨∅,rfl,by simp,by simp⟩
  | succ M ih =>
    obtain ⟨U,hU,hvalid,hpair⟩ := ih (by omega)
    let F := U.biUnion (orbitSupport L r)
    have hF : F.card ≤ 18*M := by
      have h := Finset.card_biUnion_le_card_mul U (orbitSupport L r) 18
        (fun xy _ ↦ orbitSupport_card_le L r xy)
      simpa [F,hU,Nat.mul_comm] using h
    obtain ⟨xy,hv,hd⟩ := exists_valid_avoiding hodd L r hr F (by omega)
    have hxy : xy ∉ U := by
      intro hm
      have hs := flow_mem_orbitSupport L r xy 0
      exact Finset.disjoint_left.mp hd hs (Finset.mem_biUnion.mpr ⟨xy,hm,hs⟩)
    have hdis (zw : G × G) (hzw : zw ∈ U) :
        Disjoint (orbitSupport L r xy) (orbitSupport L r zw) := by
      apply Finset.disjoint_left.mpr
      intro z hz hz'
      exact Finset.disjoint_left.mp hd hz (Finset.mem_biUnion.mpr ⟨zw,hzw,hz'⟩)
    refine ⟨insert xy U,by simp [hxy,hU],?_,?_⟩
    · intro zw hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hv
      · exact hvalid zw hz
    · intro zw hz tu ht hne
      rcases Finset.mem_insert.mp hz with rfl | hzU
      · rcases Finset.mem_insert.mp ht with rfl | htU
        · exact False.elim (hne rfl)
        · exact hdis tu htU
      · rcases Finset.mem_insert.mp ht with rfl | htU
        · exact (hdis zw hzU).symm
        · exact hpair hzU htU hne

/-- The conservative 324-per-candidate charge still gives the connector-prefix floor(n/1000). -/
theorem exists_linear_orbit_packing (hodd : Odd (Fintype.card G))
    (L : Layout) (r : Fin 6 → G) (hr : OffsetDistinct L r)
    (hn : 1000 ≤ Fintype.card G) :
    ∃ U : Finset (G × G), U.card = Fintype.card G/1000 ∧
      (∀ xy ∈ U, Valid L r xy) ∧
      (U : Set (G × G)).Pairwise
        (fun xy zw ↦ Disjoint (orbitSupport L r xy) (orbitSupport L r zw)) := by
  exact exists_disjoint_packing hodd L r hr _ (by omega)

end Counting

end EndpointFlow
