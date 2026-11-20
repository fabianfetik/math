import CorralFormalization.EndpointProof.Matching.Fractional.RawEvent.Adaptive

/-! Absolute row sums retain the raw Fourier masks. Later target edits are
paid only by column membership changes, rather than asserting Fourier
accuracy for an edited target. -/
open scoped BigOperators Classical symmDiff

namespace EndpointFractionalRawEvent
open EndpointOriginalReservoir EndpointFullProduct
noncomputable section
variable {G : Type*} [Fintype G] [AddCommGroup G]

def blockRowSum (q : ℝ) (S T : Finset G) (a : G → G) : ℝ :=
  ∑ z ∈ S, |setBit T (a z)-q|

def twoBlockRowSum (q : ℝ) (S T : Finset G) (a : Equiv.Perm G) : ℝ :=
  blockRowSum q S T a+blockRowSum q T S a.symm

/-- The exact raw absolute row-sum identity for one partner block. -/
theorem blockRowSum_identity (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (S T : Finset G) (a : G → G) :
    blockRowSum q S T a = q*(S.card : ℝ)+
      (1-2*q)*(∑ g, setBit S g*setBit T (a g)) := by
  have hb (z : G) : |setBit T (a z)-q| = q+(1-2*q)*setBit T (a z) := by
    by_cases hz : a z ∈ T
    · simp only [setBit,hz,ite_true]
      rw [abs_of_nonneg (by linarith)]
      ring
    · simp only [setBit,hz,ite_false,zero_sub,abs_neg,abs_of_nonneg hq0,mul_zero,add_zero]
  have hs : (∑ g, setBit S g*setBit T (a g)) = ∑ z ∈ S, setBit T (a z) := by
    simp [setBit,Finset.sum_filter,← ite_and,and_comm,Finset.filter_filter]
    congr 1
    ext g
    simp
  unfold blockRowSum
  simp_rw [hb]
  rw [hs,Finset.sum_add_distrib,← Finset.mul_sum]
  simp
  ring

/-- The two partner blocks have the same raw edge count, by a genuine
permutation reindexing. -/
theorem twoBlockRowSum_identity (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (S T : Finset G) (a : Equiv.Perm G) :
    twoBlockRowSum q S T a = q*((S.card : ℝ)+T.card)+
      2*(1-2*q)*(∑ g, setBit S g*setBit T (a g)) := by
  have hr : (∑ g, setBit T g*setBit S (a.symm g)) =
      ∑ g, setBit S g*setBit T (a g) := by
    rw [← Equiv.sum_comp a (fun g => setBit T g*setBit S (a.symm g))]
    simp [mul_comm]
  rw [twoBlockRowSum,blockRowSum_identity q hq0 hq1,blockRowSum_identity q hq0 hq1,hr]
  ring

def partnerFirst (i : Fin 3) : Fin 3 := if i=0 then 1 else 0
def partnerSecond (i : Fin 3) : Fin 3 := if i=2 then 1 else 2

def partnerPerm (i : Fin 3) (v : G) : Equiv.Perm G :=
  if i=0 then ⟨fun x => x-v,fun x => x+v,by intro x; simp,by intro x; simp⟩
  else if i=1 then ⟨fun x => v-x,fun x => v-x,by intro x; simp,by intro x; simp⟩
  else ⟨fun x => x+v,fun x => x-v,by intro x; simp,by intro x; simp⟩

def rawRowSum (q : ℝ) (s : OriginalSample G) (i : Fin 3) (v : G) : ℝ :=
  twoBlockRowSum q (rawSet s (partnerFirst i)) (rawSet s (partnerSecond i)) (partnerPerm i v)

def targetRawRowSum (q : ℝ) (s : OriginalSample G) (T : PhysicalTarget G) (i : Fin 3) (v : G) : ℝ :=
  blockRowSum q (T (partnerFirst i)) (rawSet s (partnerSecond i)) (partnerPerm i v)+
  blockRowSum q (T (partnerSecond i)) (rawSet s (partnerFirst i)) (partnerPerm i v).symm

/-- This is the manuscript's exact raw identity, for every numerical root.
The nonzero-colour restriction is needed only when invoking GoodDegrees. -/
theorem rawRowSum_identity (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (s : OriginalSample G) (i : Fin 3) (v : G) :
    rawRowSum q s i v =
      q*(((rawSet s (partnerFirst i)).card : ℝ)+(rawSet s (partnerSecond i)).card)+
      2*(1-2*q)*rawDegree s i v := by
  unfold rawRowSum
  rw [twoBlockRowSum_identity q hq0 hq1]
  have hd : (∑ g, setBit (rawSet s (partnerFirst i)) g*
      setBit (rawSet s (partnerSecond i)) (partnerPerm i v g)) = rawDegree s i v := by
    rw [rawDegree_eq_targetDegree]
    fin_cases i <;> simp [partnerFirst,partnerSecond,partnerPerm,targetDegree,rawTarget]
  rw [hd]

/-- Raw sizes plus raw degrees pay the two-block absolute row sum, keeping
the useful nonnegative coefficient 1-2q in the exact identity. -/
theorem GoodRawEvent.rawRowSum_le {q ρ ε : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2)
    (hρ : 0 ≤ ρ) (hε : ε ≤ ρ) {s : OriginalSample G} (h : GoodRawEvent q ρ ε s)
    (i : Fin 3) (v : G) (hv : i=2 → v ≠ 0) :
    rawRowSum q s i v ≤ 4*q^2*(Fintype.card G : ℝ)+2*ρ*(Fintype.card G : ℝ) := by
  have hs₁ := (abs_le.mp (h.1.rawSize (partnerFirst i))).2
  have hs₂ := (abs_le.mp (h.1.rawSize (partnerSecond i))).2
  have hd := (abs_le.mp (h.2 i v hv)).2
  have hn : (0 : ℝ) ≤ Fintype.card G := Nat.cast_nonneg _
  have hc : 0 ≤ 1-2*q := by linarith
  have hs := mul_le_mul_of_nonneg_left (add_le_add hs₁ hs₂) hq0
  have hdeg := mul_le_mul_of_nonneg_left hd (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hc)
  have heps := mul_nonneg (mul_nonneg hq0 (sub_nonneg.mpr hε)) hn
  have hqr := mul_nonneg (mul_nonneg hq0 hρ) hn
  have hqcube := mul_nonneg (mul_nonneg (sq_nonneg q) hq0) hn
  rw [rawRowSum_identity q hq0 (by linarith) s i v]
  nlinarith

private theorem blockRowSum_edit (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (S S' T : Finset G) (a : G → G) :
    blockRowSum q S T a ≤ blockRowSum q S' T a+((S ∆ S').card : ℝ) := by
  have hc (g : G) : 0 ≤ |setBit T (a g)-q| ∧ |setBit T (a g)-q| ≤ 1 := by
    constructor
    · exact abs_nonneg _
    · by_cases hg : a g ∈ T <;> simp [setBit,hg,abs_le] <;> constructor <;> linarith
  have hd (g : G) : setBit S g*|setBit T (a g)-q| ≤
      setBit S' g*|setBit T (a g)-q|+setBit (S ∆ S') g := by
    have hcg := hc g
    simp only [setBit] at hcg
    by_cases hS : g ∈ S <;> by_cases hS' : g ∈ S' <;>
      simp [setBit,Finset.mem_symmDiff,hS,hS'] <;> linarith [hcg.1,hcg.2]
  have hs := Finset.sum_le_sum (fun g (_ : g ∈ Finset.univ) => hd g)
  have he (V : Finset G) : (∑ g, setBit V g*|setBit T (a g)-q|) = blockRowSum q V T a := by
    simp [setBit,blockRowSum,Finset.sum_filter]
  rw [Finset.sum_add_distrib,he,he] at hs
  simpa [setBit] using hs

/-- Replacing the raw partner column sets by a later target costs only its
actual physical edit distance. The masks stay raw. -/
theorem targetRawRowSum_le_rawRowSum_add_edits (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (s : OriginalSample G) (T : PhysicalTarget G) (i : Fin 3) (v : G) :
    targetRawRowSum q s T i v ≤ rawRowSum q s i v+editDistance T (rawTarget s) := by
  have h₁ := blockRowSum_edit q hq0 hq1 (T (partnerFirst i))
    (rawSet s (partnerFirst i)) (rawSet s (partnerSecond i)) (partnerPerm i v)
  have h₂ := blockRowSum_edit q hq0 hq1 (T (partnerSecond i))
    (rawSet s (partnerSecond i)) (rawSet s (partnerFirst i)) (partnerPerm i v).symm
  have he : (((T (partnerFirst i) ∆ rawSet s (partnerFirst i)).card : ℝ)+
      ((T (partnerSecond i) ∆ rawSet s (partnerSecond i)).card : ℝ)) ≤ editDistance T (rawTarget s) := by
    fin_cases i <;> simp [partnerFirst,partnerSecond,editDistance,rawTarget,Fin.sum_univ_succ] <;>
      positivity
  dsimp [targetRawRowSum,rawRowSum,twoBlockRowSum]
  linarith

/-- The manuscript's raw-mask row bound on every later nearby target,
without requiring the edited target to retain any Fourier estimate. -/
theorem fractionalRawEvent_targetRawRowSum_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2)
    {s : OriginalSample G} (h : fractionalRawEvent q s) (T : PhysicalTarget G)
    (hT : editDistance T (rawTarget s) ≤ rho q*(Fintype.card G : ℝ))
    (i : Fin 3) (v : G) (hv : i=2 → v ≠ 0) :
    targetRawRowSum q s T i v ≤ 5*q^2*(Fintype.card G : ℝ) := by
  have hr := h.rawRowSum_le hq0 hq1 (by unfold rho; positivity) (epsilon_le_rho q hq0 hq1) i v hv
  have he := targetRawRowSum_le_rawRowSum_add_edits q hq0 (by linarith) s T i v
  have hn : (0 : ℝ) ≤ Fintype.card G := Nat.cast_nonneg _
  unfold rho at hT hr
  nlinarith [mul_nonneg (sq_nonneg q) hn]

end
end EndpointFractionalRawEvent
