import CorralFormalization.EndpointProof.Transitions.ConvolutionDegrees
import CorralFormalization.EndpointProof.Transitions.VertexDeletion
import CorralFormalization.EndpointProof.Matching.Fractional.ActualRemainder.Geometry

/-!
# The actual additive hypergraph and explicit ordinary-transition edge weights

Every index `(u,v)` denotes the actual tagged edge
`{(0,u),(1,v),(2,-u-v)}`.  Zero weights exclude edges outside the later
target or containing two added vertices.  No edge existence is assumed.
-/

open scoped Classical BigOperators

namespace EndpointTransitions

noncomputable section

open EndpointFractionalRawEvent EndpointFlow.AbelianTransport
open EndpointMatching.Fractional.Rounding EndpointMatching.Fractional.ActualRemainder

variable {G : Type*} [AddCommGroup G] [Fintype G]

def additiveEdge (e : G × G) : Finset (Fin 3 × G) :=
  {(0,e.1),(1,e.2),(2,-e.1-e.2)}

theorem additiveEdge_valid (e : G × G) : Hyperedge (additiveEdge e) := by
  exact ⟨e.1,e.2,-e.1-e.2,by abel,rfl⟩

theorem additiveEdge_card (e : G × G) : (additiveEdge e).card = 3 := by
  exact EndpointMatching.AbsorptionAssembly.hyperedge_card_eq_three (additiveEdge_valid e)

theorem additiveEdge_injective : Function.Injective (additiveEdge (G := G)) := by
  intro e f hef
  have h₀ : (0,e.1) ∈ additiveEdge f := hef ▸ (by simp [additiveEdge])
  have h₁ : (1,e.2) ∈ additiveEdge f := hef ▸ (by simp [additiveEdge])
  have he₀ : e.1=f.1 := by simpa [additiveEdge] using h₀
  have he₁ : e.2=f.2 := by simpa [additiveEdge] using h₁
  exact Prod.ext he₀ he₁

theorem additiveEdge_linear : IsLinear (additiveEdge (G := G)) := by
  intro e f hef
  have h := hyperedge_inter_card_le_one (additiveEdge_valid e) (additiveEdge_valid f)
    (fun h => hef (additiveEdge_injective h))
  apply Finset.card_le_one.mpr
  intro v hv w hw
  exact Finset.card_le_one.mp h v (by simpa only [Finset.mem_inter] using hv)
    w (by simpa only [Finset.mem_inter] using hw)

/-- The sum has disjoint supports: all core, or exactly one added role. -/
def ordinaryWeight (R T : Fin 3 → Finset G) (a : Fin 3 → ℝ) (q : ℝ) (e : G × G) : ℝ :=
  coreWeight q (a 0) (a 1) (a 2) *
    setBit (core (R 0) (T 0)) e.1 * setBit (core (R 1) (T 1)) e.2 *
      setBit (core (R 2) (T 2)) (-e.1-e.2) +
  rootWeight q (a 1) (a 2) *
    setBit (additions (R 0) (T 0)) e.1 * setBit (core (R 1) (T 1)) e.2 *
      setBit (core (R 2) (T 2)) (-e.1-e.2) +
  rootWeight q (a 0) (a 2) *
    setBit (core (R 0) (T 0)) e.1 * setBit (additions (R 1) (T 1)) e.2 *
      setBit (core (R 2) (T 2)) (-e.1-e.2) +
  rootWeight q (a 0) (a 1) *
    setBit (core (R 0) (T 0)) e.1 * setBit (core (R 1) (T 1)) e.2 *
      setBit (additions (R 2) (T 2)) (-e.1-e.2)

theorem ordinaryWeight_bounds {R T : Fin 3 → Finset G} {a : Fin 3 → ℝ} {q : ℝ}
    (hq : 0 < q) (ha : ∀ i, DensityWindow q (a i)) (e : G × G) :
    0 ≤ ordinaryWeight R T a q e ∧ ordinaryWeight R T a q e ≤ 1 := by
  have hw₀ := coreWeight_bounds hq (ha 0) (ha 1) (ha 2)
  have hw₁ := rootWeight_bounds hq (ha 1) (ha 2)
  have hw₂ := rootWeight_bounds hq (ha 0) (ha 2)
  have hw₃ := rootWeight_bounds hq (ha 0) (ha 1)
  rcases e with ⟨u,v⟩
  by_cases hR₀ : u ∈ R 0 <;> by_cases hT₀ : u ∈ T 0 <;>
    by_cases hR₁ : v ∈ R 1 <;> by_cases hT₁ : v ∈ T 1 <;>
    by_cases hR₂ : -u-v ∈ R 2 <;> by_cases hT₂ : -u-v ∈ T 2 <;>
    simp [ordinaryWeight,setBit,core,additions,hR₀,hT₀,hR₁,hT₁,hR₂,hT₂]
  all_goals first | exact ⟨hw₀.1.le,hw₀.2⟩ | exact ⟨hw₁.1.le,hw₁.2⟩ |
    exact ⟨hw₂.1.le,hw₂.2⟩ | exact ⟨hw₃.1.le,hw₃.2⟩

theorem coreWeight_swap (q a b c : ℝ) : coreWeight q a b c = coreWeight q b a c := by
  unfold coreWeight alpha
  congr 1 <;> ring

theorem coreWeight_reverse (q a b c : ℝ) : coreWeight q a b c = coreWeight q c a b := by
  unfold coreWeight alpha
  congr 1 <;> ring

theorem load_zero (w : G × G → ℝ) (x : G) :
    weightedLoad additiveEdge w (0,x) = ∑ y, w (x,y) := by
  simp [weightedLoad,additiveEdge,Fintype.sum_prod_type,Finset.sum_ite_irrel]
  rw [Finset.sum_comm]
  simp

theorem load_one (w : G × G → ℝ) (x : G) :
    weightedLoad additiveEdge w (1,x) = ∑ y, w (y,x) := by
  simp [weightedLoad,additiveEdge,Fintype.sum_prod_type,eq_comm]

theorem load_two (w : G × G → ℝ) (x : G) :
    weightedLoad additiveEdge w (2,x) = ∑ y, w (y,-x-y) := by
  have heq (u v : G) : x = -u-v ↔ v = -x-u := by
    simp only [eq_sub_iff_add_eq, eq_neg_iff_add_eq_zero]
    constructor <;> intro h
    · calc v+u+x = x+v+u := by abel
           _ = 0 := h
    · calc x+v+u = v+u+x := by abel
           _ = 0 := h
  simp [weightedLoad,additiveEdge,Fintype.sum_prod_type,heq]

theorem core_bit {R T : Finset G} {x : G} (hx : x ∈ core R T) :
    setBit (core R T) x = 1 ∧ setBit (additions R T) x = 0 := by
  have hR := (Finset.mem_inter.mp hx).1
  have hT := (Finset.mem_inter.mp hx).2
  simp [setBit,core,additions,hR,hT]

theorem additions_bit {R T : Finset G} {x : G} (hx : x ∈ additions R T) :
    setBit (core R T) x = 0 ∧ setBit (additions R T) x = 1 := by
  have hT := (Finset.mem_sdiff.mp hx).1
  have hR := (Finset.mem_sdiff.mp hx).2
  simp [setBit,core,additions,hR,hT]

theorem pairCount_eq_reverse_sum (R U : Finset G) (x : G) :
    pairCount R U x = ∑ y, setBit R y*setBit U (x-y) := by
  rw [pairCount_comm]
  unfold pairCount
  apply Finset.sum_congr rfl
  intro y _
  ring

private theorem fin3_mk_two (h : 2 < 3) : (⟨2,h⟩ : Fin 3) = 2 := rfl

/-- The concrete hypergraph weighted incidence sum equals the ordinary-transition formula
at every actual core vertex, in all three tagged roles. -/
theorem ordinaryWeight_core_load (R T : Fin 3 → Finset G) (a : Fin 3 → ℝ)
    (q : ℝ) (i : Fin 3) (x : G) (hx : x ∈ core (R i) (T i)) :
    weightedLoad additiveEdge (ordinaryWeight R T a q) (i,x) =
      coreDegreeFormula R T a q i x := by
  have hb := core_bit hx
  have hneg (y : G) : -y-x = -x-y := by abel
  have hthird (y : G) : -y-(-x-y) = x := by abel
  fin_cases i
  all_goals dsimp only at *
  all_goals norm_num only [Fin.isValue] at hb hx ⊢
  all_goals try simp only [Fin.mk_zero,Fin.mk_one,fin3_mk_two] at hb hx ⊢
  all_goals first |
    trans (∑ y, ordinaryWeight R T a q (x,y)); · exact load_zero _ _ |
    trans (∑ y, ordinaryWeight R T a q (y,x)); · exact load_one _ _ |
    trans (∑ y, ordinaryWeight R T a q (y,-x-y)); · exact load_two _ _
  all_goals simp only [ordinaryWeight, Prod.fst, Prod.snd]
  all_goals try simp only [hthird,hneg]
  all_goals rw [hb.1,hb.2]
  all_goals simp only [mul_one,mul_zero,one_mul,zero_mul,add_zero,zero_add]
  all_goals simp [coreDegreeFormula,partner₁,partner₂]
  all_goals simp_rw [pairCount_eq_reverse_sum,Finset.mul_sum]
  all_goals simp only [← Finset.sum_add_distrib]
  all_goals apply Finset.sum_congr rfl
  all_goals intro y _
  all_goals simp only [coreWeight,rootWeight,alpha,div_eq_mul_inv,mul_inv_rev]
  all_goals ring

/-- The concrete hypergraph weighted incidence sum at a later added root. -/
theorem ordinaryWeight_root_load (R T : Fin 3 → Finset G) (a : Fin 3 → ℝ)
    (q : ℝ) (i : Fin 3) (x : G) (hx : x ∈ additions (R i) (T i)) :
    weightedLoad additiveEdge (ordinaryWeight R T a q) (i,x) =
      rootDegreeFormula R T a q i x := by
  have hb := additions_bit hx
  have hneg (y : G) : -y-x = -x-y := by abel
  have hthird (y : G) : -y-(-x-y) = x := by abel
  fin_cases i
  all_goals dsimp only at *
  all_goals norm_num only [Fin.isValue] at hb hx ⊢
  all_goals try simp only [Fin.mk_zero,Fin.mk_one,fin3_mk_two] at hb hx ⊢
  all_goals first |
    trans (∑ y, ordinaryWeight R T a q (x,y)); · exact load_zero _ _ |
    trans (∑ y, ordinaryWeight R T a q (y,x)); · exact load_one _ _ |
    trans (∑ y, ordinaryWeight R T a q (y,-x-y)); · exact load_two _ _
  all_goals simp only [ordinaryWeight, Prod.fst, Prod.snd]
  all_goals try simp only [hthird,hneg]
  all_goals rw [hb.1,hb.2]
  all_goals simp only [mul_one,mul_zero,one_mul,zero_mul,add_zero,zero_add]
  all_goals simp [rootDegreeFormula,partner₁,partner₂]
  all_goals simp_rw [pairCount_eq_reverse_sum,Finset.mul_sum]
  all_goals apply Finset.sum_congr rfl
  all_goals intro y _
  all_goals simp only [rootWeight,div_eq_mul_inv,mul_inv_rev]
  all_goals ring

def targetVertices (T : Fin 3 → Finset G) : Finset (Fin 3 × G) :=
  Finset.univ.biUnion (fun i => (T i).image (fun x => (i,x)))

@[simp] theorem mem_targetVertices (T : Fin 3 → Finset G) (i : Fin 3) (x : G) :
    (i,x) ∈ targetVertices T ↔ x ∈ T i := by
  simp [targetVertices]

theorem targetVertices_card (T : Fin 3 → Finset G) :
    (targetVertices T).card = ∑ i, (T i).card := by
  rw [targetVertices, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro i _
    exact Finset.card_image_of_injective _ (fun x y hxy => Prod.mk.inj hxy |>.2)
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro v hi hj
    obtain ⟨x, _, hix⟩ := Finset.mem_image.mp hi
    obtain ⟨y, _, hjy⟩ := Finset.mem_image.mp hj
    exact hij (congrArg Prod.fst (hix.trans hjy.symm))

theorem ordinaryWeight_supported (R T : Fin 3 → Finset G) (a : Fin 3 → ℝ)
    (q : ℝ) (e : G × G) (he : 0 < ordinaryWeight R T a q e) :
    additiveEdge e ⊆ targetVertices T := by
  have h₀ : e.1 ∈ T 0 := by
    by_contra ht
    have hz : ordinaryWeight R T a q e = 0 := by
      simp [ordinaryWeight,setBit,core,additions,ht]
    linarith
  have h₁ : e.2 ∈ T 1 := by
    by_contra ht
    have hz : ordinaryWeight R T a q e = 0 := by
      simp [ordinaryWeight,setBit,core,additions,ht]
    linarith
  have h₂ : -e.1-e.2 ∈ T 2 := by
    by_contra ht
    have hz : ordinaryWeight R T a q e = 0 := by
      simp [ordinaryWeight,setBit,core,additions,ht]
    linarith
  intro v hv
  simp only [additiveEdge,Finset.mem_insert,Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl <;> simpa only [mem_targetVertices] using (by assumption)

/-- The actual weighted hypergraph degree, rather than a supplied degree
certificate, satisfies ordinary transition lemma's error outside the nine exceptional inventories. -/
theorem ordinaryWeight_load_error {R T : Fin 3 → Finset G} {a : Fin 3 → ℝ}
    {q η : ℝ} (hq : 0 < q) (hqone : q ≤ 1)
    (ha : ∀ i, DensityWindow q (a i)) (hraw : ∀ i, FourierGood (R i) (a i) η)
    (hη : 0 ≤ η) (hηone : η ≤ 1)
    (htarget : ∀ i, |((T i).card : ℝ)-q*(Fintype.card G : ℝ)| ≤ η*(Fintype.card G : ℝ))
    (hloss : ∀ i, (((R i) \ (T i)).card : ℝ) ≤ η*(Fintype.card G : ℝ))
    (v : Fin 3 × G) (hv : v ∈ targetVertices T)
    (hgood : v ∉ badVertices R T a η) :
    |weightedLoad additiveEdge (ordinaryWeight R T a q) v-q^2*(Fintype.card G : ℝ)/2| ≤
      14*η*(Fintype.card G : ℝ) := by
  rcases v with ⟨i,x⟩
  have hx : x ∈ T i := (mem_targetVertices T i x).mp hv
  have hlabel : -x ∉ badLabels R T a η i := by
    intro h
    exact hgood ((mem_badVertices R T a η i x).mpr ⟨hx,h⟩)
  have herr := convolution_degree_errors hq hqone ha hraw hη hηone htarget hloss i x hlabel
  by_cases hr : x ∈ R i
  · rw [ordinaryWeight_core_load R T a q i x (Finset.mem_inter.mpr ⟨hr,hx⟩)]
    exact herr.1
  · rw [ordinaryWeight_root_load R T a q i x (Finset.mem_sdiff.mpr ⟨hx,hr⟩)]
    exact herr.2.trans (by nlinarith [mul_nonneg hη (Nat.cast_nonneg (α := ℝ) (Fintype.card G))])

end
end EndpointTransitions
