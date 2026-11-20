import CorralFormalization.Results.SwitchFamily.LayoutAsymptotic
import CorralFormalization.Results.SwitchFamily.Counting.TraceBridge

/-!
# Actual cyclic layout asymptotics

Connect the count of marked local two/three-tile words to the transfer
matrix and its plastic-root asymptotic. The decorated-orbit result holds
uniformly for any height-dependent alphabet with at least one symbol.
This counts the abstract decorated layouts; the physical corral orbit
identification is a separate statement.
-/

open Filter Topology
open scoped Topology

namespace CorralFormalization.Results.SwitchFamily.LayoutAsymptotic

noncomputable section

open Counting

theorem transfer_matrix_cast :
    tileMatrix.map (Nat.castRingHom ℝ) = transitionMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tileMatrix, Transfer.adjacency, tileEdge, transitionMatrix,
      Matrix.map_apply, Fin.ext_iff]

theorem layoutCount_eq_traceSequence (j : ℕ) (hj : 0 < j) :
    (C j : ℝ) = traceSequence j := by
  letI : NeZero j := ⟨by omega⟩
  rw [C_eq_trace]
  calc
    ((Matrix.trace (tileMatrix ^ j) : ℕ) : ℝ) =
        Matrix.trace ((tileMatrix ^ j).map (Nat.castRingHom ℝ)) :=
      (AddMonoidHom.map_trace (Nat.castRingHom ℝ) (tileMatrix ^ j))
    _ = traceSequence j := by rw [Matrix.map_pow, transfer_matrix_cast, traceSequence]

theorem layoutCount_absolute_upper (j : ℕ) (hj : 0 < j) :
    |(C j : ℝ)| ≤ 5 * plasticRoot^j := by
  rw [layoutCount_eq_traceSequence j hj]
  exact traceSequence_absolute_upper j

theorem layoutCount_ratio_tendsto_one :
    Tendsto (fun j : ℕ => (C j : ℝ)/plasticRoot^j) atTop (𝓝 1) := by
  apply traceSequence_ratio_tendsto_one.congr'
  filter_upwards [Filter.eventually_ge_atTop 1] with j hj
  rw [layoutCount_eq_traceSequence j (by omega)]

/-- A.3's primitive-orbit asymptotic for the exact local-word model, with an
arbitrary varying decoration alphabet `Q h ≥ 1`. -/
theorem decorated_aperiodic_orbit_asymptotic (Q : ℕ → ℕ) (hQ : ∀ h, 1 ≤ Q h) :
    Tendsto (fun h : ℕ => ((aperiodicOrbitCount h (Q h) : ℝ)*h)/
      (plasticRoot*(Q h : ℝ))^h) atTop (𝓝 1) :=
  moving_aperiodic_orbit_asymptotic (K:=5) (by norm_num) plasticRoot_bounds.1
    layoutCount_absolute_upper layoutCount_ratio_tendsto_one Q hQ

end
end CorralFormalization.Results.SwitchFamily.LayoutAsymptotic
