import CorralFormalization.EndpointProof.Matching.Fractional.RawEvent.Joint
import Mathlib.Data.Finset.SymmDiff

/-!
Uniform deterministic consequences of the raw event for every later target.
The quantifier over targets is inside the same event, so targets may be
chosen after inspecting the complete original sample.
-/
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical ComplexConjugate NNReal symmDiff

namespace EndpointFractionalRawEvent
open EndpointOriginalReservoir EndpointFullProduct
noncomputable section
variable {G : Type*} [Fintype G] [AddCommGroup G]

abbrev PhysicalTarget (G : Type*) := Fin 3 → Finset G

def setBit (S : Finset G) (g : G) : ℝ := if g ∈ S then 1 else 0

def targetDegree (T : PhysicalTarget G) (i : Fin 3) (v : G) : ℝ :=
  if i = 0 then ∑ y, setBit (T 1) y * setBit (T 2) (y-v)
  else if i = 1 then ∑ x, setBit (T 0) x * setBit (T 2) (v-x)
  else ∑ x, setBit (T 0) x * setBit (T 1) (x+v)

/-- The manuscript's physical edit distance, counting all three roles. -/
def editDistance (T U : PhysicalTarget G) : ℝ :=
  ∑ i, ((T i ∆ U i).card : ℝ)

def rawTarget (s : OriginalSample G) : PhysicalTarget G := rawSet s

theorem rawDegree_eq_targetDegree (s : OriginalSample G) (i : Fin 3) (v : G) :
    rawDegree s i v = targetDegree (rawTarget s) i v := by
  have hb (j : Fin 3) (g : G) : setBit (rawTarget s j) g = rawBit s j g :=
    (rawBit_eq s j g).symm
  simp only [rawDegree,targetDegree,hb]

private theorem sum_setBit (S : Finset G) : ∑ g, setBit S g = (S.card : ℝ) := by
  simp [setBit]

private theorem setBit_abs_sub (S T : Finset G) (g : G) :
    |setBit S g-setBit T g| = setBit (S ∆ T) g := by
  by_cases hS : g ∈ S <;> by_cases hT : g ∈ T <;>
    norm_num [setBit,Finset.mem_symmDiff,hS,hT]

private theorem product_abs_sub_setBit (S T S' T' : Finset G) (a b : G) :
    |setBit S a*setBit T b-setBit S' a*setBit T' b| ≤
      setBit (S ∆ S') a+setBit (T ∆ T') b := by
  by_cases hS : a ∈ S <;> by_cases hT : b ∈ T <;>
    by_cases hS' : a ∈ S' <;> by_cases hT' : b ∈ T' <;>
    norm_num [setBit,Finset.mem_symmDiff,hS,hT,hS',hT']

/-- Changing the two partner sets loses or gains at most their total edits
at any numerical root. Root membership itself is not required. -/
theorem productCount_edit_bound (S T S' T' : Finset G) (a b : Equiv.Perm G) :
    |(∑ g, setBit S (a g)*setBit T (b g))-
      (∑ g, setBit S' (a g)*setBit T' (b g))| ≤
      ((S ∆ S').card : ℝ)+((T ∆ T').card : ℝ) := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ g, |setBit S (a g)*setBit T (b g)-setBit S' (a g)*setBit T' (b g)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ g, (setBit (S ∆ S') (a g)+setBit (T ∆ T') (b g)) := by
      exact Finset.sum_le_sum (fun g _ => product_abs_sub_setBit _ _ _ _ _ _)
    _ = ((S ∆ S').card : ℝ)+((T ∆ T').card : ℝ) := by
      rw [Finset.sum_add_distrib,Equiv.sum_comp a,Equiv.sum_comp b,sum_setBit,sum_setBit]

/-- Uniform raw-to-actual degree stability for every root and every target. -/
theorem targetDegree_edit_bound (T U : PhysicalTarget G) (i : Fin 3) (v : G) :
    |targetDegree T i v-targetDegree U i v| ≤ editDistance T U := by
  let subR : Equiv.Perm G := ⟨fun x => x-v,fun x => x+v,by intro x; simp,by intro x; simp⟩
  let subL : Equiv.Perm G := ⟨fun x => v-x,fun x => v-x,by intro x; simp,by intro x; simp⟩
  let addR : Equiv.Perm G := ⟨fun x => x+v,fun x => x-v,by intro x; simp,by intro x; simp⟩
  have he : editDistance T U = ((T 0 ∆ U 0).card : ℝ)+
      ((T 1 ∆ U 1).card : ℝ)+((T 2 ∆ U 2).card : ℝ) := by
    simp [editDistance,Fin.sum_univ_succ]; ring
  rw [he]
  fin_cases i
  · have h := productCount_edit_bound (T 1) (T 2) (U 1) (U 2) (Equiv.refl G) subR
    simp [subR] at h
    simp only [targetDegree]
    norm_num
    linarith [Nat.cast_nonneg (α := ℝ) (T 0 ∆ U 0).card]
  · have h := productCount_edit_bound (T 0) (T 2) (U 0) (U 2) (Equiv.refl G) subL
    simp [subL] at h
    simp only [targetDegree]
    norm_num
    linarith [Nat.cast_nonneg (α := ℝ) (T 1 ∆ U 1).card]
  · have h := productCount_edit_bound (T 0) (T 1) (U 0) (U 1) (Equiv.refl G) addR
    simp [addR] at h
    simp only [targetDegree]
    norm_num
    linarith [Nat.cast_nonneg (α := ℝ) (T 2 ∆ U 2).card]

/-- Edit stability of one role size. -/
theorem size_edit_bound (T U : PhysicalTarget G) (i : Fin 3) :
    |((T i).card : ℝ)-(U i).card| ≤ editDistance T U := by
  have h : |((T i).card : ℝ)-(U i).card| ≤ ((T i ∆ U i).card : ℝ) := by
    rw [← sum_setBit (T i),← sum_setBit (U i),← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ g, |setBit (T i) g-setBit (U i) g| := Finset.abs_sum_le_sum_abs _ _
      _ = ((T i ∆ U i).card : ℝ) := by simp_rw [setBit_abs_sub]; exact sum_setBit _
  apply h.trans
  change ((T i ∆ U i).card : ℝ) ≤ ∑ j, ((T j ∆ U j).card : ℝ)
  exact Finset.single_le_sum (f := fun j : Fin 3 => ((T j ∆ U j).card : ℝ))
    (fun j _ => Nat.cast_nonneg (α := ℝ) _) (Finset.mem_univ i)

/-- All later targets, including choices adaptive to the original sample,
inherit the paid raw-degree bound. -/
theorem GoodDegrees.all_targets {q ρ : ℝ} {s : OriginalSample G} (h : GoodDegrees q ρ s) :
    ∀ (T : PhysicalTarget G) (i : Fin 3) (v : G), (i=2 → v ≠ 0) →
      |targetDegree T i v-q^2*(Fintype.card G : ℝ)| ≤
        ρ*(Fintype.card G : ℝ)+editDistance T (rawTarget s) := by
  intro T i v hv
  calc
    _ ≤ |targetDegree T i v-rawDegree s i v|+
      |rawDegree s i v-q^2*(Fintype.card G : ℝ)| := abs_sub_le _ _ _
    _ ≤ editDistance T (rawTarget s)+ρ*(Fintype.card G : ℝ) := by
      apply add_le_add
      · rw [rawDegree_eq_targetDegree]; exact targetDegree_edit_bound T (rawTarget s) i v
      · exact h i v hv
    _ = _ := by ring

/-- The trivial character and the actual edit distance bound each later
role size. Balance can subsequently identify this with a common m. -/
theorem GoodFourier.all_target_sizes {q ε : ℝ} {s : OriginalSample G} (h : GoodFourier q ε s) :
    ∀ (T : PhysicalTarget G) (i : Fin 3),
      |((T i).card : ℝ)-q*(Fintype.card G : ℝ)| ≤
        ε*(Fintype.card G : ℝ)+editDistance T (rawTarget s) := by
  intro T i
  calc
    _ ≤ |((T i).card : ℝ)-(rawSet s i).card|+
      |((rawSet s i).card : ℝ)-q*(Fintype.card G : ℝ)| := abs_sub_le _ _ _
    _ ≤ editDistance T (rawTarget s)+ε*(Fintype.card G : ℝ) :=
      add_le_add (size_edit_bound T (rawTarget s) i) (h.rawSize i)
    _ = _ := by ring

/-- An explicit useful consequence at distance at most rho*n, all targets
simultaneously on the single fractional raw event. -/
theorem fractionalRawEvent_adaptive {q : ℝ} {s : OriginalSample G} (h : fractionalRawEvent q s) :
    ∀ T : PhysicalTarget G, editDistance T (rawTarget s) ≤ rho q*(Fintype.card G : ℝ) →
      (∀ i, |((T i).card : ℝ)-q*(Fintype.card G : ℝ)| ≤
        (epsilon q+rho q)*(Fintype.card G : ℝ)) ∧
      (∀ i v, (i=2 → v ≠ 0) →
        |targetDegree T i v-q^2*(Fintype.card G : ℝ)| ≤
          2*rho q*(Fintype.card G : ℝ)) := by
  intro T hT
  constructor
  · intro i
    have hb := h.1.all_target_sizes T i
    nlinarith
  · intro i v hv
    have hb := h.2.all_targets T i v hv
    nlinarith

/-- Every later nearby target has role sizes in the supplier's qn/2 to 2qn
range, with no separate balance or positivity premise on the target. -/
theorem fractionalRawEvent_target_size_bounds {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1/2)
    {s : OriginalSample G} (h : fractionalRawEvent q s) (T : PhysicalTarget G)
    (hT : editDistance T (rawTarget s) ≤ rho q*(Fintype.card G : ℝ)) (i : Fin 3) :
    q*(Fintype.card G : ℝ)/2 ≤ ((T i).card : ℝ) ∧
      ((T i).card : ℝ) ≤ 2*q*(Fintype.card G : ℝ) := by
  have hs := (fractionalRawEvent_adaptive h T hT).1 i
  have hc := mul_le_mul_of_nonneg_right (epsilon_add_rho_le_half_q q hq0.le hq1)
    (Nat.cast_nonneg (α := ℝ) (Fintype.card G))
  have hqn : 0 ≤ q*(Fintype.card G : ℝ) := by positivity
  have ha := abs_le.mp hs
  constructor <;> nlinarith

/-- The actual balanced target degree differs from d0=qm by at most 3rho*n,
exactly the diagonal-error estimate needed by the manuscript. -/
theorem fractionalRawEvent_target_diagonal_bound {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1/2)
    {s : OriginalSample G} (h : fractionalRawEvent q s) (T : PhysicalTarget G) (m : ℕ)
    (hm : ∀ i, (T i).card=m)
    (hT : editDistance T (rawTarget s) ≤ rho q*(Fintype.card G : ℝ))
    (i : Fin 3) (v : G) (hv : i=2 → v ≠ 0) :
    |targetDegree T i v-q*m| ≤ 3*rho q*(Fintype.card G : ℝ) := by
  have hs := (fractionalRawEvent_adaptive h T hT).1 (0 : Fin 3)
  rw [hm] at hs
  have hd := (fractionalRawEvent_adaptive h T hT).2 i v hv
  have hc := mul_le_mul_of_nonneg_right (q_mul_epsilon_add_rho_le_rho q hq0.le hq1)
    (Nat.cast_nonneg (α := ℝ) (Fintype.card G))
  have hsize : |q*(m : ℝ)-q^2*(Fintype.card G : ℝ)| ≤ rho q*(Fintype.card G : ℝ) := by
    calc
      _ = q*|(m : ℝ)-q*(Fintype.card G : ℝ)| := by
        have he : q*(m : ℝ)-q^2*(Fintype.card G : ℝ) =
            q*((m : ℝ)-q*(Fintype.card G : ℝ)) := by ring
        rw [he,abs_mul,abs_of_pos hq0]
      _ ≤ q*((epsilon q+rho q)*(Fintype.card G : ℝ)) :=
        mul_le_mul_of_nonneg_left hs hq0.le
      _ ≤ _ := by nlinarith [hc]
  have ha := abs_sub_le (targetDegree T i v) (q^2*(Fintype.card G : ℝ)) (q*m)
  rw [abs_sub_comm (q^2*(Fintype.card G : ℝ)) (q*m)] at ha
  linarith

end
end EndpointFractionalRawEvent
