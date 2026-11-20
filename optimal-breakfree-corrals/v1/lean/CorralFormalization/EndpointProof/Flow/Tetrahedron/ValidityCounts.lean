import CorralFormalization.EndpointProof.Flow.Tetrahedron.SectionSensitivity
open scoped Classical BigOperators
namespace EndpointMatching.Tetrahedron
open CorralFormalization.EndpointProof.Probability.QuadraticDeletion
noncomputable section
variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- A coordinate occurring in exactly one of two different directions. -/
def mixSolvedCoordinate (i j : Fin 6) : Fin 3 :=
  ![![0,0,0,1,2,0], ![0,0,1,0,0,2], ![0,1,0,0,0,1],
    ![1,0,0,0,1,0], ![2,0,0,1,0,0], ![0,2,1,0,0,0]] i j

def directionCoeff (i : Fin 6) (k : Fin 3) : ℤ :=
  ![![1,0,0], ![0,1,0], ![0,0,1], ![1,1,0], ![-1,0,1], ![0,-1,-1]] i k

def mixDirection (i j : Fin 6) (minus : Bool) (t : TetrahedronParameters G) : G :=
  tetrahedronDirection i t + (if minus then -tetrahedronDirection j t else tetrahedronDirection j t)

def mixFreeCoordinates (i j : Fin 6) (t : TetrahedronParameters G) : G × G :=
  match (mixSolvedCoordinate i j).val with
  | 0 => (t.2.1,t.2.2)
  | 1 => (t.1,t.2.2)
  | _ => (t.1,t.2.1)

def mixBase (i j : Fin 6) (u : G × G) : TetrahedronParameters G :=
  match (mixSolvedCoordinate i j).val with
  | 0 => (0,u.1,u.2)
  | 1 => (u.1,0,u.2)
  | _ => (u.1,u.2,0)

def mixRecover (i j : Fin 6) (minus : Bool) (h : G) (u : G × G) : TetrahedronParameters G :=
  let k := mixSolvedCoordinate i j
  let coeff := directionCoeff i k + (if minus then -directionCoeff j k else directionCoeff j k)
  let t₀ := mixBase i j u
  let v := if coeff = 1 then h - mixDirection i j minus t₀ else -(h - mixDirection i j minus t₀)
  match k.val with
  | 0 => (v,u.1,u.2)
  | 1 => (u.1,v,u.2)
  | _ => (u.1,u.2,v)

omit [Fintype G] in
theorem mixRecover_correct (i j : Fin 6) (hij : i ≠ j) (minus : Bool)
    (t : TetrahedronParameters G) :
    mixRecover i j minus (mixDirection i j minus t) (mixFreeCoordinates i j t) = t := by
  rcases t with ⟨a,b,c⟩
  fin_cases i <;> fin_cases j <;> cases minus <;>
    simp_all [mixRecover, mixDirection, mixFreeCoordinates, mixBase, mixSolvedCoordinate,
      directionCoeff, tetrahedronDirection]
  all_goals abel

theorem mix_free_injective (i j : Fin 6) (hij : i ≠ j) (minus : Bool) (h : G) :
    Set.InjOn (mixFreeCoordinates i j)
      (↑((Finset.univ : Finset (TetrahedronParameters G)).filter
        (fun t => mixDirection i j minus t = h)) : Set (TetrahedronParameters G)) := by
  intro t ht u hu he
  have ht' := (Finset.mem_filter.mp ht).2
  have hu' := (Finset.mem_filter.mp hu).2
  calc
    t = mixRecover i j minus (mixDirection i j minus t) (mixFreeCoordinates i j t) :=
      (mixRecover_correct i j hij minus t).symm
    _ = mixRecover i j minus (mixDirection i j minus u) (mixFreeCoordinates i j u) := by
      rw [ht',hu',he]
    _ = u := mixRecover_correct i j hij minus u

theorem mix_section_card_le (i j : Fin 6) (hij : i ≠ j) (minus : Bool) (h : G) :
    ((Finset.univ : Finset (TetrahedronParameters G)).filter
      (fun t => mixDirection i j minus t = h)).card ≤ (Fintype.card G)^2 := by
  have hc := Finset.card_le_card_of_injOn
    (s := (Finset.univ : Finset (TetrahedronParameters G)).filter
      (fun t => mixDirection i j minus t = h))
    (t := (Finset.univ : Finset (G × G))) (mixFreeCoordinates i j)
    (by intro t ht; simp) (mix_free_injective i j hij minus h)
  simpa [Fintype.card_prod, pow_two] using hc

/-- Signs in an equality of two affine representatives, expressed as one
of the two mixed-direction equations. -/
def flipGroup (b : Bool) (x : G) : G := if b then -x else x

def collisionMixMinus (i j : Fin 12) (neg : Bool) : Bool :=
  if tetrahedronNegative i == tetrahedronNegative j then !neg else neg

def collisionTarget (r : TetrahedronRoots G) (i j : Fin 12) (neg : Bool) : G :=
  flipGroup (tetrahedronNegative i)
    (flipGroup neg (tetrahedronOffset r j) - tetrahedronOffset r i)

omit [Fintype G] in
theorem collision_reduction (r : TetrahedronRoots G) (i j : Fin 12) (neg : Bool)
    (t : TetrahedronParameters G) :
    flipGroup (tetrahedronNegative i)
      (tetrahedronRepresentative r i t - flipGroup neg (tetrahedronRepresentative r j t)) =
    mixDirection (tetrahedronDirectionIndex i) (tetrahedronDirectionIndex j)
      (collisionMixMinus i j neg) t - collisionTarget r i j neg := by
  cases neg <;> cases hi : tetrahedronNegative i <;> cases hj : tetrahedronNegative j <;>
    simp [tetrahedronRepresentative, flipGroup, mixDirection, collisionMixMinus,
      collisionTarget, hi, hj]
  all_goals abel

theorem representative_collision_card_le_distinct_directions
    (r : TetrahedronRoots G) (i j : Fin 12)
    (hij : tetrahedronDirectionIndex i ≠ tetrahedronDirectionIndex j) (neg : Bool) :
    ((Finset.univ : Finset (TetrahedronParameters G)).filter
      (fun t => tetrahedronRepresentative r i t = flipGroup neg (tetrahedronRepresentative r j t))).card ≤
        (Fintype.card G)^2 := by
  have hsub : (Finset.univ : Finset (TetrahedronParameters G)).filter
      (fun t => tetrahedronRepresentative r i t = flipGroup neg (tetrahedronRepresentative r j t)) ⊆
      Finset.univ.filter (fun t =>
        mixDirection (tetrahedronDirectionIndex i) (tetrahedronDirectionIndex j)
          (collisionMixMinus i j neg) t = collisionTarget r i j neg) := by
    intro t ht
    have ht' := (Finset.mem_filter.mp ht).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have h := collision_reduction r i j neg t
    rw [ht', sub_self] at h
    have hz : mixDirection (tetrahedronDirectionIndex i) (tetrahedronDirectionIndex j)
        (collisionMixMinus i j neg) t - collisionTarget r i j neg = 0 := by
      simpa [flipGroup] using h.symm
    exact sub_eq_zero.mp hz
  exact (Finset.card_le_card hsub).trans
    (mix_section_card_le (tetrahedronDirectionIndex i) (tetrahedronDirectionIndex j)
      hij (collisionMixMinus i j neg) (collisionTarget r i j neg))

/-- The two representatives in a common direction have opposite signs. -/
theorem parallel_representatives_opposite (i j : Fin 12) (hij : i ≠ j)
    (hd : tetrahedronDirectionIndex i = tetrahedronDirectionIndex j) :
    tetrahedronNegative i ≠ tetrahedronNegative j := by
  fin_cases i <;> fin_cases j <;>
    simp_all [tetrahedronDirectionIndex, tetrahedronNegative]

def parallelRoot (r : TetrahedronRoots G) (i : Fin 6) : G :=
  ![r.b₂,r.a₁,r.a₂,r.c₁,r.c₂,r.b₁] i

omit [Fintype G] in
theorem parallelRoot_ne_zero (r : TetrahedronRoots G) (hr : admissibleRoots r) (i : Fin 6) :
    parallelRoot r i ≠ 0 := by
  rcases hr with ⟨_,_,_,ha1,ha2,hb1,hb2,hc1,hc2⟩
  fin_cases i <;> simp_all [parallelRoot]

omit [Fintype G] in
theorem parallel_representatives_sum (r : TetrahedronRoots G) (i j : Fin 12)
    (hij : i ≠ j) (hd : tetrahedronDirectionIndex i = tetrahedronDirectionIndex j)
    (t : TetrahedronParameters G) :
    tetrahedronRepresentative r i t + tetrahedronRepresentative r j t =
      parallelRoot r (tetrahedronDirectionIndex i) := by
  fin_cases i <;> fin_cases j <;>
    simp_all [tetrahedronRepresentative, tetrahedronDirectionIndex, tetrahedronNegative,
      tetrahedronOffset, tetrahedronDirection, parallelRoot]
  all_goals abel

/-- Two parallel representatives cannot be inverse, because their sum is
one of the six nonzero roots. -/
theorem parallel_neg_collision_empty (r : TetrahedronRoots G) (hr : admissibleRoots r)
    (i j : Fin 12) (hij : i ≠ j)
    (hd : tetrahedronDirectionIndex i = tetrahedronDirectionIndex j) :
    (Finset.univ : Finset (TetrahedronParameters G)).filter
      (fun t => tetrahedronRepresentative r i t = -tetrahedronRepresentative r j t) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro t ht
  have he := (Finset.mem_filter.mp ht).2
  have hsum := parallel_representatives_sum r i j hij hd t
  have hz : parallelRoot r (tetrahedronDirectionIndex i) = 0 := by
    rw [← hsum, he, neg_add_cancel]
  exact parallelRoot_ne_zero r hr _ hz

/-- Equality of parallel representatives has at most |G|² solutions;
odd order makes doubling injective. -/
theorem parallel_eq_collision_card_le (hodd : Odd (Fintype.card G))
    (r : TetrahedronRoots G) (i j : Fin 12) (hij : i ≠ j)
    (hd : tetrahedronDirectionIndex i = tetrahedronDirectionIndex j) :
    ((Finset.univ : Finset (TetrahedronParameters G)).filter
      (fun t => tetrahedronRepresentative r i t = tetrahedronRepresentative r j t)).card ≤
        (Fintype.card G)^2 := by
  have hsign := parallel_representatives_opposite i j hij hd
  have hmix : collisionMixMinus i j false = false := by
    unfold collisionMixMinus
    simp [hsign]
  have hc : (Nat.card G).Coprime 2 := by
    rw [Nat.card_eq_fintype_card]
    exact hodd.coprime_two_right
  have hdouble : Function.Injective (fun x : G => x+x) := by
    simpa only [two_nsmul] using hc.nsmul_right_bijective.injective
  let d := tetrahedronDirectionIndex i
  let C : Finset (TetrahedronParameters G) := Finset.univ
  have hsection : ∀ g,
      ((C.filter (fun t => tetrahedronDirection d t = g)).card : ℝ) ≤
        (Fintype.card G : ℝ)^2 := by
    intro g
    exact_mod_cast direction_section_card_le d g
  have hbound := section_bound_of_injective C (tetrahedronDirection d)
    (fun x : G => x+x) hdouble ((Fintype.card G : ℝ)^2) (by positivity)
      hsection (collisionTarget r i j false)
  have hsub : (Finset.univ : Finset (TetrahedronParameters G)).filter
      (fun t => tetrahedronRepresentative r i t = tetrahedronRepresentative r j t) ⊆
      C.filter (fun t => tetrahedronDirection d t + tetrahedronDirection d t =
        collisionTarget r i j false) := by
    intro t ht
    have ht' := (Finset.mem_filter.mp ht).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have h := collision_reduction r i j false t
    simp only [flipGroup, Bool.false_eq_true, ↓reduceIte, ht', sub_self, neg_zero] at h
    rw [hmix, ← hd] at h
    simp only [ite_self, mixDirection, Bool.false_eq_true, ↓reduceIte] at h
    exact sub_eq_zero.mp h.symm
  have hcard : (((Finset.univ : Finset (TetrahedronParameters G)).filter
      (fun t => tetrahedronRepresentative r i t = tetrahedronRepresentative r j t)).card : ℝ)
      ≤ (Fintype.card G : ℝ)^2 :=
    (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans hbound
  exact_mod_cast hcard

/-- Any collision, of either sign, between two distinct representatives
excludes at most |G|² parameter triples. -/
theorem representative_collision_card_le (hodd : Odd (Fintype.card G))
    (r : TetrahedronRoots G) (hr : admissibleRoots r) (i j : Fin 12)
    (hij : i ≠ j) (neg : Bool) :
    ((Finset.univ : Finset (TetrahedronParameters G)).filter
      (fun t => tetrahedronRepresentative r i t = flipGroup neg (tetrahedronRepresentative r j t))).card ≤
        (Fintype.card G)^2 := by
  by_cases hd : tetrahedronDirectionIndex i = tetrahedronDirectionIndex j
  · cases neg with
    | false => simpa [flipGroup] using parallel_eq_collision_card_le hodd r i j hij hd
    | true =>
      rw [show (Finset.univ : Finset (TetrahedronParameters G)).filter
        (fun t => tetrahedronRepresentative r i t = flipGroup true (tetrahedronRepresentative r j t)) = ∅ by
          simpa [flipGroup] using parallel_neg_collision_empty r hr i j hij hd]
      simp
  · exact representative_collision_card_le_distinct_directions r i j hd neg

/-- The six root coordinates against which every new orbit must be fresh. -/
def rootCoordinate (r : TetrahedronRoots G) : Fin 6 → G :=
  ![r.a₁,r.a₂,r.b₁,r.b₂,r.c₁,r.c₂]

/-- Distinct new nonzero inverse orbits, all disjoint from the root orbits. -/
def geometricallyValid (r : TetrahedronRoots G) (t : TetrahedronParameters G) : Prop :=
  (∀ i, tetrahedronRepresentative r i t ≠ 0) ∧
  (∀ i j, i < j → tetrahedronRepresentative r i t ≠ tetrahedronRepresentative r j t ∧
    tetrahedronRepresentative r i t ≠ -tetrahedronRepresentative r j t) ∧
  (∀ i k, tetrahedronRepresentative r i t ≠ rootCoordinate r k ∧
    tetrahedronRepresentative r i t ≠ -rootCoordinate r k)

abbrev OrderedRepresentativePair := {ij : Fin 12 × Fin 12 // ij.1 < ij.2}

instance : Fintype OrderedRepresentativePair := by
  classical
  unfold OrderedRepresentativePair
  infer_instance

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem orderedRepresentativePair_card : Fintype.card OrderedRepresentativePair = 66 := by decide

/-- Twelve zeros, 132 signed pair collisions, and 144 signed root hits. -/
abbrev ForbiddenEquation := Fin 12 ⊕ (OrderedRepresentativePair × Bool) ⊕ (Fin 12 × Fin 6 × Bool)

theorem forbiddenEquation_card : Fintype.card ForbiddenEquation = 288 := by
  simp [ForbiddenEquation, Fintype.card_sum, Fintype.card_prod, orderedRepresentativePair_card]

def forbiddenEquationSolutions (r : TetrahedronRoots G) : ForbiddenEquation → Finset (TetrahedronParameters G)
  | Sum.inl i => Finset.univ.filter (fun t => tetrahedronRepresentative r i t = 0)
  | Sum.inr (Sum.inl (ij,neg)) => Finset.univ.filter (fun t =>
      tetrahedronRepresentative r ij.1.1 t = flipGroup neg (tetrahedronRepresentative r ij.1.2 t))
  | Sum.inr (Sum.inr (i,k,neg)) => Finset.univ.filter (fun t =>
      tetrahedronRepresentative r i t = flipGroup neg (rootCoordinate r k))

theorem forbiddenEquationSolutions_card_le (hodd : Odd (Fintype.card G))
    (r : TetrahedronRoots G) (hr : admissibleRoots r) (e : ForbiddenEquation) :
    (forbiddenEquationSolutions r e).card ≤ (Fintype.card G)^2 := by
  rcases e with i | ⟨⟨ij,neg⟩ | ⟨i,k,neg⟩⟩
  · have h := representative_section_card_le r i 0
    exact_mod_cast h
  · have hij : ij.1.1 ≠ ij.1.2 := ne_of_lt ij.2
    exact representative_collision_card_le hodd r hr ij.1.1 ij.1.2 hij neg
  · have h := representative_section_card_le r i (flipGroup neg (rootCoordinate r k))
    exact_mod_cast h

def invalidParameterSet (r : TetrahedronRoots G) : Finset (TetrahedronParameters G) :=
  Finset.univ.biUnion (forbiddenEquationSolutions r)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem not_invalid_implies_geometricallyValid (r : TetrahedronRoots G)
    (t : TetrahedronParameters G) (hgood : t ∉ invalidParameterSet r) :
    geometricallyValid r t := by
  have hnot (e : ForbiddenEquation) : t ∉ forbiddenEquationSolutions r e := by
    intro ht
    exact hgood (Finset.mem_biUnion.mpr ⟨e,Finset.mem_univ _,ht⟩)
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    apply hnot (Sum.inl i)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩
  · intro i j hij
    let ij : OrderedRepresentativePair := ⟨(i,j),hij⟩
    constructor
    · intro he
      apply hnot (Sum.inr (Sum.inl (ij,false)))
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩
    · intro he
      apply hnot (Sum.inr (Sum.inl (ij,true)))
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩
  · intro i k
    constructor
    · intro he
      apply hnot (Sum.inr (Sum.inr (i,k,false)))
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩
    · intro he
      apply hnot (Sum.inr (Sum.inr (i,k,true)))
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩

/-- At most 288|G|² parameter triples violate the globally valid geometric
conditions. This is the written paired-cover candidate-count bound, before Q sampling. -/
theorem invalidParameterSet_card_le (hodd : Odd (Fintype.card G))
    (r : TetrahedronRoots G) (hr : admissibleRoots r) :
    (invalidParameterSet r).card ≤ 288 * (Fintype.card G)^2 := by
  calc
    _ ≤ ∑ e : ForbiddenEquation, (forbiddenEquationSolutions r e).card := Finset.card_biUnion_le
    _ ≤ ∑ _e : ForbiddenEquation, (Fintype.card G)^2 :=
      Finset.sum_le_sum (fun e _ => forbiddenEquationSolutions_card_le hodd r hr e)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, forbiddenEquation_card, nsmul_eq_mul]
      norm_num

def validParameterSet (r : TetrahedronRoots G) : Finset (TetrahedronParameters G) :=
  Finset.univ.filter (geometricallyValid r)

theorem validParameterSet_card_lower (hodd : Odd (Fintype.card G))
    (r : TetrahedronRoots G) (hr : admissibleRoots r) :
    (Fintype.card G)^3 - 288 * (Fintype.card G)^2 ≤ (validParameterSet r).card := by
  have hsub : (Finset.univ : Finset (TetrahedronParameters G)) \ invalidParameterSet r ⊆
      validParameterSet r := by
    intro t ht
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      not_invalid_implies_geometricallyValid r t (Finset.mem_sdiff.mp ht).2⟩
  have hsplit := Finset.card_sdiff_add_card_inter
    (Finset.univ : Finset (TetrahedronParameters G)) (invalidParameterSet r)
  have hbad := invalidParameterSet_card_le hodd r hr
  have hle := Finset.card_le_card hsub
  have huniv : (Finset.univ : Finset (TetrahedronParameters G)).card = (Fintype.card G)^3 := by
    simp [TetrahedronParameters, Fintype.card_prod, pow_succ, Nat.mul_assoc]
  have hinter : ((Finset.univ : Finset (TetrahedronParameters G)) ∩ invalidParameterSet r).card =
      (invalidParameterSet r).card := by simp
  rw [huniv,hinter] at hsplit
  omega

end
end EndpointMatching.Tetrahedron
