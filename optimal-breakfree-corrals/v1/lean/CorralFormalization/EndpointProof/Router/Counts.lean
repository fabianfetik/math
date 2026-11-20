import CorralFormalization.EndpointProof.Router.Fibers
import Mathlib.Data.List.FinRange

/-! # Router collision and numerical-exclusion counts

These are actual finite sets of parameter triples.  The 121n² and 18Ln²
bounds are proved from the fixed coordinate tables and the odd-order
fibre theorem, without taking affine counting as a premise.
-/
namespace EndpointRouter
namespace Switch

open Affine
open scoped BigOperators
universe u
variable {G : Type u} [AddCommGroup G]

def withParameters (S : Switch G) (t : Parameters G) : Switch G :=
  {S with h := t.1, d := t.2.1, f := t.2.2}

@[simp] theorem withParameters_legal (S : Switch G) (t : Parameters G) :
    (S.withParameters t).LegalPorts ↔ S.LegalPorts := Iff.rfl

theorem parameterized_vertex (S : Switch G) (t : Parameters G) (i : Fin 12) :
    (S.withParameters t).vertexValue i = Affine.value (S.vertexConstant i) (vertexCoefficient i) t := by
  rw [← vertex_affine]
  rfl

theorem parameterized_color (S : Switch G) (t : Parameters G) (i : Fin 10) :
    (S.withParameters t).colorValue i = Affine.value (S.colorConstant i) (colorCoefficient i) t := by
  rw [← color_affine]
  rfl

variable [Fintype G] [DecidableEq G]

private theorem equality_count_of_classification (hodd : Odd (Fintype.card G))
    (a b : G) (p q : Fin 3 → ℤ)
    (h : (p = q ∧ a ≠ b) ∨ ∃ k, SmallCoefficient (p k-q k)) :
    ((Finset.univ : Finset (Parameters G)).filter
      (fun t => Affine.value a p t = Affine.value b q t)).card ≤ (Fintype.card G)^2 := by
  rcases h with ⟨rfl,hab⟩ | ⟨k,hk⟩
  · have hempty : ((Finset.univ : Finset (Parameters G)).filter
        (fun t => Affine.value a p t = Affine.value b p t)) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro t _ he
      unfold Affine.value at he
      exact hab (add_right_cancel (add_right_cancel (add_right_cancel he)))
    simp [hempty]
  · exact Affine.equation_card_le hodd a b p q k hk

def vertexPairs : Finset (Fin 12 × Fin 12) := Finset.univ.filter (fun p => p.1 < p.2)
def colorPairs : Finset (Fin 10 × Fin 10) := Finset.univ.filter (fun p => p.1 < p.2)

@[simp] theorem vertexPairs_card : vertexPairs.card = 66 := by decide
@[simp] theorem colorPairs_card : colorPairs.card = 45 := by decide

def vertexCollision (S : Switch G) (p : Fin 12 × Fin 12) : Finset (Parameters G) :=
  Finset.univ.filter (fun t => (S.withParameters t).vertexValue p.1 = (S.withParameters t).vertexValue p.2)

def colorCollision (S : Switch G) (p : Fin 10 × Fin 10) : Finset (Parameters G) :=
  Finset.univ.filter (fun t => (S.withParameters t).colorValue p.1 = (S.withParameters t).colorValue p.2)

def zeroColor (S : Switch G) (i : Fin 10) : Finset (Parameters G) :=
  Finset.univ.filter (fun t => (S.withParameters t).colorValue i = 0)

theorem vertexCollision_card_le (hodd : Odd (Fintype.card G))
    (S : Switch G) (h : S.LegalPorts) (p : Fin 12 × Fin 12) (hp : p ∈ vertexPairs) :
    (S.vertexCollision p).card ≤ (Fintype.card G)^2 := by
  have hne : p.1 ≠ p.2 := ne_of_lt (Finset.mem_filter.mp hp).2
  simpa only [vertexCollision,parameterized_vertex] using
    equality_count_of_classification hodd _ _ _ _ (vertex_collision_classification S h p.1 p.2 hne)

theorem colorCollision_card_le (hodd : Odd (Fintype.card G))
    (S : Switch G) (h : S.LegalPorts) (p : Fin 10 × Fin 10) (hp : p ∈ colorPairs) :
    (S.colorCollision p).card ≤ (Fintype.card G)^2 := by
  have hne : p.1 ≠ p.2 := ne_of_lt (Finset.mem_filter.mp hp).2
  simpa only [colorCollision,parameterized_color] using
    equality_count_of_classification hodd _ _ _ _ (color_collision_classification S h p.1 p.2 hne)

theorem zeroColor_card_le (hodd : Odd (Fintype.card G)) (S : Switch G) (i : Fin 10) :
    (S.zeroColor i).card ≤ (Fintype.card G)^2 := by
  obtain ⟨k,hk⟩ := zero_color_coefficient i
  have hs : SmallCoefficient (colorCoefficient i k) := by
    rcases hk with hk | hk
    · exact Or.inl hk
    · exact Or.inr (Or.inl hk)
  simpa only [zeroColor,parameterized_color] using
    Affine.fiber_card_le hodd (S.colorConstant i) (colorCoefficient i) k hs 0

/-- The union of the exact 66+45+10 equation-solution sets. -/
def collisionBad (S : Switch G) : Finset (Parameters G) :=
  vertexPairs.biUnion S.vertexCollision ∪ colorPairs.biUnion S.colorCollision ∪
    Finset.univ.biUnion S.zeroColor

theorem collisionBad_card_le (hodd : Odd (Fintype.card G))
    (S : Switch G) (h : S.LegalPorts) :
    S.collisionBad.card ≤ 121 * (Fintype.card G)^2 := by
  have hv : (vertexPairs.biUnion S.vertexCollision).card ≤ 66*(Fintype.card G)^2 := by
    calc
      _ ≤ ∑ p ∈ vertexPairs, (S.vertexCollision p).card := Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ vertexPairs, (Fintype.card G)^2 :=
        Finset.sum_le_sum (fun p hp => vertexCollision_card_le hodd S h p hp)
      _ = _ := by simp
  have hc : (colorPairs.biUnion S.colorCollision).card ≤ 45*(Fintype.card G)^2 := by
    calc
      _ ≤ ∑ p ∈ colorPairs, (S.colorCollision p).card := Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ colorPairs, (Fintype.card G)^2 :=
        Finset.sum_le_sum (fun p hp => colorCollision_card_le hodd S h p hp)
      _ = _ := by simp
  have hz : ((Finset.univ : Finset (Fin 10)).biUnion S.zeroColor).card ≤ 10*(Fintype.card G)^2 := by
    calc
      _ ≤ ∑ i : Fin 10, (S.zeroColor i).card := Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin 10, (Fintype.card G)^2 :=
        Finset.sum_le_sum (fun i _ => zeroColor_card_le hodd S i)
      _ = _ := by simp
  have h1 := Finset.card_union_le (vertexPairs.biUnion S.vertexCollision) (colorPairs.biUnion S.colorCollision)
  have h2 := Finset.card_union_le
    (vertexPairs.biUnion S.vertexCollision ∪ colorPairs.biUnion S.colorCollision) (Finset.univ.biUnion S.zeroColor)
  dsimp [collisionBad]
  omega

theorem collisionFree_of_not_mem_collisionBad (S : Switch G) (t : Parameters G)
    (ht : t ∉ S.collisionBad) : (S.withParameters t).CollisionFree := by
  have hv : ∀ i j : Fin 12, i < j →
      (S.withParameters t).vertexValue i ≠ (S.withParameters t).vertexValue j := by
    intro i j hij he
    apply ht
    exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_biUnion.mpr ⟨(i,j),by simp [vertexPairs,hij],by simp [vertexCollision,he]⟩))
  have hc : ∀ i j : Fin 10, i < j →
      (S.withParameters t).colorValue i ≠ (S.withParameters t).colorValue j := by
    intro i j hij he
    apply ht
    exact Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨(i,j),by simp [colorPairs,hij],by simp [colorCollision,he]⟩))
  constructor
  · rw [vertices_ofFn,List.nodup_ofFn]
    intro i j he
    rcases lt_trichotomy i j with hij | hij | hij
    · exact (hv i j hij he).elim
    · exact hij
    · exact (hv j i hij he.symm).elim
  · rw [colors_ofFn,List.nodup_ofFn]
    intro i j he
    rcases lt_trichotomy i j with hij | hij | hij
    · exact (hc i j hij he).elim
    · exact hij
    · exact (hc j i hij he.symm).elim

/-- The eighteen random requests, with their vertex/colour tags retained. -/
abbrev Request := Sum (Fin 8) (Fin 10)

def randomRequest (S : Switch G) (t : Parameters G) : Request → G
  | .inl i => (S.withParameters t).vertexValue ⟨i.val+4,by omega⟩
  | .inr i => (S.withParameters t).colorValue i

/-- The combined numerical support deliberately forgets the request tag. -/
def numericalSupport (S : Switch G) (t : Parameters G) : Finset G :=
  Finset.univ.image (S.randomRequest t)

theorem numericalSupport_card_le (S : Switch G) (t : Parameters G) :
    (S.numericalSupport t).card ≤ 18 := by
  exact Finset.card_image_le.trans (by simp [Fintype.card_sum])

theorem random_vertex_unit (i : Fin 8) :
    ∃ k : Fin 3, vertexCoefficient ⟨i.val+4,by omega⟩ k = 1 ∨
      vertexCoefficient ⟨i.val+4,by omega⟩ k = -1 := by
  fin_cases i
  all_goals first
    | exact ⟨0,by decide⟩
    | exact ⟨1,by decide⟩
    | exact ⟨2,by decide⟩

theorem randomRequest_fiber_card_le (hodd : Odd (Fintype.card G))
    (S : Switch G) (i : Request) (z : G) :
    ((Finset.univ : Finset (Parameters G)).filter (fun t => S.randomRequest t i = z)).card ≤
      (Fintype.card G)^2 := by
  cases i with
  | inl i =>
    obtain ⟨k,hk⟩ := random_vertex_unit i
    have hs : SmallCoefficient (vertexCoefficient ⟨i.val+4,by omega⟩ k) := by
      rcases hk with hk | hk
      · exact Or.inl hk
      · exact Or.inr (Or.inl hk)
    simpa only [randomRequest,parameterized_vertex] using
      Affine.fiber_card_le hodd (S.vertexConstant ⟨i.val+4,by omega⟩)
        (vertexCoefficient ⟨i.val+4,by omega⟩) k hs z
  | inr i =>
    obtain ⟨k,hk⟩ := zero_color_coefficient i
    have hs : SmallCoefficient (colorCoefficient i k) := by
      rcases hk with hk | hk
      · exact Or.inl hk
      · exact Or.inr (Or.inl hk)
    simpa only [randomRequest,parameterized_color] using
      Affine.fiber_card_le hodd (S.colorConstant i) (colorCoefficient i) k hs z

def forbiddenBad (S : Switch G) (F : Finset G) : Finset (Parameters G) :=
  F.biUnion (fun z => Finset.univ.biUnion (fun i : Request =>
    Finset.univ.filter (fun t => S.randomRequest t i = z)))

theorem forbiddenBad_card_le (hodd : Odd (Fintype.card G)) (S : Switch G) (F : Finset G) :
    (S.forbiddenBad F).card ≤ 18*F.card*(Fintype.card G)^2 := by
  have hz (z : G) : ((Finset.univ : Finset Request).biUnion (fun i =>
      (Finset.univ : Finset (Parameters G)).filter (fun t => S.randomRequest t i = z))).card ≤
        18*(Fintype.card G)^2 := by
    calc
      _ ≤ ∑ i : Request, ((Finset.univ : Finset (Parameters G)).filter
          (fun t => S.randomRequest t i = z)).card := Finset.card_biUnion_le
      _ ≤ ∑ _i : Request, (Fintype.card G)^2 :=
        Finset.sum_le_sum (fun i _ => randomRequest_fiber_card_le hodd S i z)
      _ = _ := by simp [Fintype.card_sum]
  calc
    _ ≤ ∑ z ∈ F, ((Finset.univ : Finset Request).biUnion (fun i =>
        (Finset.univ : Finset (Parameters G)).filter (fun t => S.randomRequest t i = z))).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _z ∈ F, 18*(Fintype.card G)^2 := Finset.sum_le_sum (fun z _ => hz z)
    _ = _ := by simp; ring

theorem not_mem_forbiddenBad_iff (S : Switch G) (F : Finset G) (t : Parameters G) :
    t ∉ S.forbiddenBad F ↔ Disjoint (S.numericalSupport t) F := by
  constructor
  · intro ht
    apply Finset.disjoint_left.mpr
    intro z hz hzF
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hz
    apply ht
    exact Finset.mem_biUnion.mpr ⟨z,hzF,Finset.mem_biUnion.mpr
      ⟨i,Finset.mem_univ _,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩⟩
  · intro hd ht
    obtain ⟨z,hz,hi⟩ := Finset.mem_biUnion.mp ht
    obtain ⟨i,_,hit⟩ := Finset.mem_biUnion.mp hi
    have he := (Finset.mem_filter.mp hit).2
    apply Finset.disjoint_left.mp hd _ hz
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,he⟩

/-- A fresh collision-free actual affine switch exists whenever the
counted exclusions leave at least one parameter triple. -/
theorem exists_fresh_parameters (hodd : Odd (Fintype.card G))
    (S : Switch G) (h : S.LegalPorts) (F : Finset G)
    (hbudget : 121+18*F.card < Fintype.card G) :
    ∃ t : Parameters G, (S.withParameters t).CollisionFree ∧
      Disjoint (S.numericalSupport t) F := by
  let bad := S.collisionBad ∪ S.forbiddenBad F
  have hb : bad.card < (Finset.univ : Finset (Parameters G)).card := by
    have h1 := Finset.card_union_le S.collisionBad (S.forbiddenBad F)
    have h2 := collisionBad_card_le hodd S h
    have h3 := forbiddenBad_card_le hodd S F
    have hn : 0 < (Fintype.card G)^2 := pow_pos Fintype.card_pos 2
    have hmul := Nat.mul_lt_mul_of_pos_right hbudget hn
    have heq : (Finset.univ : Finset (Parameters G)).card = (Fintype.card G)^3 := by
      simp [Parameters,Fintype.card_prod,pow_succ,pow_two,Nat.mul_assoc]
    rw [heq]
    calc
      bad.card ≤ S.collisionBad.card + (S.forbiddenBad F).card := h1
      _ ≤ 121*(Fintype.card G)^2 + 18*F.card*(Fintype.card G)^2 := Nat.add_le_add h2 h3
      _ = (121+18*F.card)*(Fintype.card G)^2 := by ring
      _ < Fintype.card G * (Fintype.card G)^2 := hmul
      _ = (Fintype.card G)^3 := by ring
  obtain ⟨t,_,ht⟩ := Finset.exists_mem_notMem_of_card_lt_card hb
  have hnot : t ∉ S.collisionBad ∧ t ∉ S.forbiddenBad F := by
    simpa only [bad,Finset.mem_union,not_or] using ht
  exact ⟨t,collisionFree_of_not_mem_collisionBad S t hnot.1,
    (not_mem_forbiddenBad_iff S F t).mp hnot.2⟩

end Switch
end EndpointRouter
