import CorralFormalization.Results.SwitchFamily.Counting.Asymptotics

/-!
# Real recurrence estimate for the plastic-root contribution

This proves the spectral asymptotic from a *supplied* scalar recurrence and
its first three values. The independent combinatorial identification of
the cyclic layout count with that recurrence is not assumed to have been
proved in this file.
-/

open Filter Topology
open scoped Topology

namespace CorralFormalization.Results.SwitchFamily.LayoutAsymptotic

noncomputable section

/-- The positive real root relevant to the directed two/three state graph
exists strictly between one and two. -/
theorem exists_plastic_root : ∃ lam : ℝ, 1<lam ∧ lam<2 ∧ lam^3=lam+1 := by
  let f : ℝ → ℝ := fun x => x^3-x-1
  have hcont : Continuous f := by fun_prop
  have hinterval := intermediate_value_Icc (a:=(1:ℝ)) (b:=2) (by norm_num) hcont.continuousOn
  have hz : (0:ℝ) ∈ Set.Icc (f 1) (f 2) := by norm_num [f]
  obtain ⟨lam,⟨hlo,hhi⟩,hroot⟩ := hinterval hz
  have hr : lam^3=lam+1 := by dsimp [f] at hroot; linarith
  refine ⟨lam,?_,?_,hr⟩
  · by_contra h
    have he : lam=1 := by linarith
    subst lam
    norm_num at hr
  · by_contra h
    have he : lam=2 := by linarith
    subst lam
    norm_num at hr

/-- There is only one root above one, so this is exactly the λ named in
Proposition A.3. -/
theorem plastic_root_unique {x y : ℝ} (hx : 1<x) (hy : 1<y)
    (hxr : x^3=x+1) (hyr : y^3=y+1) : x=y := by
  have hf : (x-y)*(x^2+x*y+y^2-1)=0 := by nlinarith [hxr,hyr]
  have hp : 0<x^2+x*y+y^2-1 := by nlinarith [mul_pos (by linarith : 0<x) (by linarith : 0<y)]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_right (ne_of_gt hp))

def plasticRoot : ℝ := Classical.choose exists_plastic_root

theorem plasticRoot_bounds : 1<plasticRoot ∧ plasticRoot<2 ∧ plasticRoot^3=plasticRoot+1 :=
  Classical.choose_spec exists_plastic_root

def residual (f : ℕ → ℝ) (lam : ℝ) (n : ℕ) : ℝ := f n - lam^n

def energy (f : ℕ → ℝ) (lam : ℝ) (n : ℕ) : ℝ :=
  (lam^2-1)*(residual f lam n)^2 + lam*residual f lam n*residual f lam (n+1) +
    (residual f lam (n+1))^2

theorem root_coefficient {lam : ℝ} (hroot : lam^3=lam+1) :
    lam*(lam^2-1)=1 := by nlinarith

theorem residual_cubic (f : ℕ → ℝ) (lam : ℝ)
    (hroot : lam^3=lam+1) (hrec : ∀ n, f (n+3)=f (n+1)+f n) (n : ℕ) :
    residual f lam (n+3)=residual f lam (n+1)+residual f lam n := by
  have hpow : lam^(n+3)=lam^(n+1)+lam^n := by
    rw [pow_add,pow_add,hroot]
    ring
  simp only [residual,hrec,hpow]
  ring

/-- The two nonprincipal components satisfy the quadratic factor of
`x^3-x-1`; no complex roots are needed. -/
theorem residual_quadratic (f : ℕ → ℝ) (lam : ℝ)
    (hroot : lam^3=lam+1) (h0 : f 0=3) (h1 : f 1=0) (h2 : f 2=2)
    (hrec : ∀ n, f (n+3)=f (n+1)+f n) :
    ∀ n, residual f lam (n+2) =
      -lam*residual f lam (n+1)-(lam^2-1)*residual f lam n := by
  have hprod := root_coefficient hroot
  intro n
  induction n with
  | zero => simp [residual,h0,h1,h2]; ring
  | succ n ih =>
    have hr := residual_cubic f lam hroot hrec n
    have ht : (lam*(lam^2-1)-1)*residual f lam n=0 := by rw [hprod]; ring
    simp only [show n+1+2=n+3 by omega, show n+1+1=n+2 by omega] at ⊢
    rw [hr,ih]
    nlinarith [ht]

theorem energy_succ (f : ℕ → ℝ) (lam : ℝ)
    (hroot : lam^3=lam+1) (h0 : f 0=3) (h1 : f 1=0) (h2 : f 2=2)
    (hrec : ∀ n, f (n+3)=f (n+1)+f n) (n : ℕ) :
    energy f lam (n+1)=(lam^2-1)*energy f lam n := by
  unfold energy
  rw [show n+1+1=n+2 by omega,residual_quadratic f lam hroot h0 h1 h2 hrec n]
  ring

/-- For the positive root in (1,2), the quadratic coefficient lies in
(1/2,1). -/
theorem coefficient_bounds {lam : ℝ} (hlo : 1<lam) (hhi : lam<2)
    (hroot : lam^3=lam+1) : (1/2 : ℝ)<lam^2-1 ∧ lam^2-1<1 := by
  have hprod := root_coefficient hroot
  have hcpos : 0<lam^2-1 := by nlinarith
  have hupper : lam^2-1<1 := by
    by_contra hc
    have hp : 0<(lam-1)*(lam^2-1) := mul_pos (by linarith) hcpos
    nlinarith
  constructor
  · by_contra hc
    have hp : 0<(2-lam)*(lam^2-1) := mul_pos (by linarith) hcpos
    nlinarith
  · exact hupper

/-- The residual is bounded uniformly by four; dividing by `lam^n` then
proves convergence to the leading coefficient one. -/
theorem residual_bounded (f : ℕ → ℝ) (lam : ℝ)
    (hlo : 1<lam) (hhi : lam<2) (hroot : lam^3=lam+1)
    (h0 : f 0=3) (h1 : f 1=0) (h2 : f 2=2)
    (hrec : ∀ n, f (n+3)=f (n+1)+f n) (n : ℕ) :
    |residual f lam n| ≤ 4 := by
  obtain ⟨hclo,hchi⟩ := coefficient_bounds hlo hhi hroot
  have hc0 : 0 ≤ lam^2-1 := by linarith
  have hE : ∀ j, energy f lam j ≤ 2 := by
    intro j
    induction j with
    | zero =>
      simp [energy,residual,h0,h1]
      nlinarith
    | succ j ih =>
      rw [energy_succ f lam hroot h0 h1 h2 hrec j]
      have hm := mul_le_mul_of_nonneg_left ih hc0
      nlinarith
  have hcquad : (1/2 : ℝ) ≤ 4*(lam^2-1)-lam^2 := by nlinarith
  have hnonneg := mul_nonneg (sub_nonneg.mpr hcquad) (sq_nonneg (residual f lam n))
  have hsq := sq_nonneg (2*residual f lam (n+1)+lam*residual f lam n)
  have hres : (residual f lam n)^2 ≤ 8*energy f lam n := by
    unfold energy
    nlinarith [hnonneg,hsq]
  have hbound : (residual f lam n)^2 ≤ 16 := by nlinarith [hE n]
  rw [abs_le]
  constructor <;> nlinarith

theorem recurrence_absolute_upper (f : ℕ → ℝ) (lam : ℝ)
    (hlo : 1<lam) (hhi : lam<2) (hroot : lam^3=lam+1)
    (h0 : f 0=3) (h1 : f 1=0) (h2 : f 2=2)
    (hrec : ∀ n, f (n+3)=f (n+1)+f n) (n : ℕ) :
    |f n| ≤ 5*lam^n := by
  have hr := residual_bounded f lam hlo hhi hroot h0 h1 h2 hrec n
  have hp : 1 ≤ lam^n := one_le_pow₀ hlo.le
  have ha : |f n| ≤ |residual f lam n| + |lam^n| := by
    have h := abs_add_le (residual f lam n) (lam^n)
    simpa [residual] using h
  rw [abs_of_nonneg (by positivity : 0≤lam^n)] at ha
  nlinarith

theorem recurrence_ratio_tendsto_one (f : ℕ → ℝ) (lam : ℝ)
    (hlo : 1<lam) (hhi : lam<2) (hroot : lam^3=lam+1)
    (h0 : f 0=3) (h1 : f 1=0) (h2 : f 2=2)
    (hrec : ∀ n, f (n+3)=f (n+1)+f n) :
    Tendsto (fun n : ℕ => f n / lam^n) atTop (𝓝 1) := by
  have hzero : Tendsto (fun n : ℕ => residual f lam n / lam^n) atTop (𝓝 0) := by
    apply (tendsto_zero_iff_norm_tendsto_zero).mpr
    simp only [Real.norm_eq_abs]
    have ht : Tendsto (fun n : ℕ => (4 : ℝ)/lam^n) atTop (𝓝 0) := by
      have hg := (tendsto_pow_const_div_const_pow_of_one_lt 0 hlo).const_mul 4
      simpa [div_eq_mul_inv] using hg
    apply squeeze_zero (fun _ => abs_nonneg _) _ ht
    intro n
    rw [abs_div,abs_of_pos (pow_pos (by linarith : 0<lam) n)]
    exact div_le_div_of_nonneg_right (residual_bounded f lam hlo hhi hroot h0 h1 h2 hrec n)
      (le_of_lt (pow_pos (by linarith : 0<lam) n))
  have heq : (fun n : ℕ => f n / lam^n) =
      fun n => residual f lam n / lam^n + 1 := by
    funext n
    have hp : lam^n ≠ 0 := ne_of_gt (pow_pos (by linarith : 0<lam) n)
    unfold residual
    field_simp
    ring
  rw [heq]
  simpa using hzero.add (show Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) from tendsto_const_nhds)

/-- The directed state-transition matrix written in Appendix A. -/
def transitionMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => if (i.val=0 ∧ j.val=1) ∨ (i.val=1 ∧ j.val=0) ∨
      (i.val=1 ∧ j.val=2) ∨ (i.val=2 ∧ j.val=0)
    then 1 else 0

theorem transitionMatrix_cubic : transitionMatrix^3 = transitionMatrix+1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [transitionMatrix, pow_succ, Matrix.mul_apply, Fin.sum_univ_three] <;>
    simp_all [show (2 : Fin 3) ≠ 0 by decide]

def traceSequence (n : ℕ) : ℝ := Matrix.trace (transitionMatrix^n)

theorem traceSequence_zero : traceSequence 0=3 := by
  simp [traceSequence,Matrix.trace_one]

theorem traceSequence_one : traceSequence 1=0 := by
  simp only [traceSequence, pow_one, Matrix.trace, Matrix.diag_apply, Fin.sum_univ_three]
  norm_num [transitionMatrix]

theorem traceSequence_two : traceSequence 2=2 := by
  simp only [traceSequence, Matrix.trace, Matrix.diag_apply, Fin.sum_univ_three]
  norm_num [transitionMatrix, Matrix.mul_apply, Fin.sum_univ_three, pow_succ]

theorem traceSequence_recurrence (n : ℕ) :
    traceSequence (n+3)=traceSequence (n+1)+traceSequence n := by
  have hm : transitionMatrix^(n+3)=transitionMatrix^(n+1)+transitionMatrix^n := by
    rw [pow_add,transitionMatrix_cubic,mul_add,mul_one,pow_add,pow_one]
  simp only [traceSequence,hm,Matrix.trace_add]

theorem traceSequence_absolute_upper (n : ℕ) :
    |traceSequence n| ≤ 5*plasticRoot^n :=
  recurrence_absolute_upper traceSequence plasticRoot plasticRoot_bounds.1
    plasticRoot_bounds.2.1 plasticRoot_bounds.2.2 traceSequence_zero traceSequence_one
    traceSequence_two traceSequence_recurrence n

/-- The displayed matrix trace has the stated plastic-root leading term.
The separate equality with the number of cyclic tilings is not used here. -/
theorem traceSequence_ratio_tendsto_one :
    Tendsto (fun n : ℕ => traceSequence n / plasticRoot^n) atTop (𝓝 1) :=
  recurrence_ratio_tendsto_one traceSequence plasticRoot plasticRoot_bounds.1
    plasticRoot_bounds.2.1 plasticRoot_bounds.2.2 traceSequence_zero traceSequence_one
    traceSequence_two traceSequence_recurrence

end
end CorralFormalization.Results.SwitchFamily.LayoutAsymptotic
