import CorralFormalization.EndpointProof.Router.GlobalGeometry.Support
import CorralFormalization.EndpointProof.Factor.RouterBudget

/-! # Actual intermediate ports with the alternating legal-query restrictions -/
namespace EndpointRouter
open EndpointFactor EndpointLayeredSample
open scoped Classical
noncomputable section
universe u
variable {G : Type u} [AddCommGroup G] [Fintype G] [DecidableEq G]

private theorem edgeLabels_get {V C : Type*} (edge : V → V → C)
    (xs : List V) (i : ℕ) (hi : i+1 < xs.length) :
    (edgeLabels edge xs)[i]'(by rw [edgeLabels_length]; omega) =
      edge (xs[i]'(by omega)) (xs[i+1]'hi) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    cases xs with
    | nil => simp at hi
    | cons b xs =>
      cases i with
      | zero => rfl
      | succ i => exact ih i (by simpa using hi)

def externalPorts {n : ℕ} (input output : Fin n → G) : Finset G :=
  Finset.univ.image input ∪ Finset.univ.image output

theorem externalPorts_card {n : ℕ} (input output : Fin n → G) :
    (externalPorts input output).card ≤ 2*n := by
  have h := Finset.card_union_le (Finset.univ.image input) (Finset.univ.image output)
  have hx := Finset.card_image_le (s := Finset.univ) (f := input)
  have hz := Finset.card_image_le (s := Finset.univ) (f := output)
  simp only [Finset.card_univ,Fintype.card_fin] at hx hz
  dsimp [externalPorts]
  omega

/-- The dummy first difference costs at most two labels even for one track.
Every later difference is exactly the one required by §4.2. -/
def alternatingDelta {n : ℕ} (input output : Fin n → G) (j : Fin n) : G :=
  if hj : j.val = 0 then 0
  else if (j.val-1)%2 = 0 then input j - input ⟨j.val-1,by omega⟩
  else output j - output ⟨j.val-1,by omega⟩

/-- A function-indexed version of the already proved list port selection. -/
theorem choose_intermediate_function {n : ℕ} (RV F : Finset G)
    (input output : Fin n → G)
    (hcard : F.card + n + 2 < RV.card) :
    ∃ middle : Fin n → G,
      Function.Injective middle ∧ (∀ i, middle i ∈ RV ∧ middle i ∉ F) ∧
      (∀ i : Fin (n-1),
        let e := adjacentEdge n i
        let delta := if i.val%2 = 0 then input e.2 - input e.1 else output e.2 - output e.1
        middle e.2 - middle e.1 ≠ delta ∧ middle e.2 - middle e.1 ≠ -delta) := by
  let deltas := List.ofFn (alternatingDelta input output)
  obtain ⟨ports,hlen,hnd,havoid,hchain⟩ := choose_intermediate_ports RV F 0 deltas (by simpa [deltas] using hcard)
  have hp : ports.length = n := by simpa [deltas] using hlen
  let middle : Fin n → G := fun i => ports[i.val]'(by omega)
  refine ⟨middle,?_,?_,?_⟩
  · intro i j heq
    have hh := (List.nodup_iff_injective_get.mp hnd) (show ports.get ⟨i.val,by omega⟩ = ports.get ⟨j.val,by omega⟩ from heq)
    exact Fin.ext (congrArg (fun k : Fin ports.length => k.val) hh)
  · intro i
    exact havoid _ (List.getElem_mem _)
  · intro i
    let j : Fin n := ⟨i.val+1,by omega⟩
    have hleft : i.val+1 < (edgeLabels (fun a b : G => b-a) (0::ports)).length := by
      rw [edgeLabels_length]
      simp only [List.length_cons,hp]
      omega
    have hright : i.val+1 < deltas.length := by simp [deltas]; omega
    have h := hchain.get hleft hright
    have hedge := edgeLabels_get (fun a b : G => b-a) (0::ports) (i.val+1) (by simp [hp]; omega)
    simp only [List.get_eq_getElem] at h
    rw [hedge] at h
    simp only [List.getElem_cons_succ] at h
    have hsub : i.val+1-1 = i.val := by omega
    simpa [deltas,middle,alternatingDelta,j,adjacentEdge,hsub] using h

/-- The full original ledger pays the external-port exclusions as well as
all intermediate ports and the two extra labels at each greedy step. -/
theorem ReservoirEvent.choose_intermediate_ports {n : ℕ} (u : ℝ) (ω : Bool × G → Bool)
    (hu : 0 < u) (hu1 : u ≤ 1)
    (h : ReservoirEvent u (routerTrialBudget u (Fintype.card G)) ω)
    (F : Finset G) (input output : Fin n → G)
    (hledger : ((F.card + 22*n : ℕ) : ℝ) ≤ explicitRouterDensity u * (Fintype.card G : ℝ)/4)
    (hn : 8 ≤ u*(Fintype.card G : ℝ)) :
    ∃ middle : Fin n → G,
      Function.Injective middle ∧
      (∀ i, middle i ∈ vertexPool ω ∧ middle i ∉ F ∪ externalPorts input output) ∧
      (∀ i : Fin (n-1),
        let e := adjacentEdge n i
        let delta := if i.val%2 = 0 then input e.2 - input e.1 else output e.2 - output e.1
        middle e.2 - middle e.1 ≠ delta ∧ middle e.2 - middle e.1 ≠ -delta) := by
  apply choose_intermediate_function (vertexPool ω) (F ∪ externalPorts input output) input output
  have hF := Finset.card_union_le F (externalPorts input output)
  have hext := externalPorts_card input output
  have hb := (explicitRouterDensity_bounds u hu hu1).2
  have hbN := mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg (α := ℝ) (Fintype.card G))
  have hcard : (((F ∪ externalPorts input output).card + n + 2 : ℕ) : ℝ) < u*(Fintype.card G : ℝ)/2 := by
    push_cast at hledger ⊢
    have hFN : ((F ∪ externalPorts input output).card : ℝ) ≤ (F.card : ℝ) + 2*n := by exact_mod_cast (hF.trans (Nat.add_le_add_left hext _))
    have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    nlinarith
  exact_mod_cast hcard.trans_le h.2

end
end EndpointRouter
