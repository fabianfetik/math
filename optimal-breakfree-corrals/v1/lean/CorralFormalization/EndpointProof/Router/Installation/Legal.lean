import CorralFormalization.EndpointProof.Router.Installation.Tables
import CorralFormalization.EndpointProof.Router.Installation.Ports

/-! # The selected intermediate ports make every concrete query legal -/
namespace EndpointRouter
open scoped Classical
noncomputable section
universe u
variable {G : Type u} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Separate ordered external port sets and fresh distinct intermediate ports
produce the one injective port index required by geometric assembly. -/
theorem routerPort_injective_of_fresh {n : ℕ} (input middle output : Fin n → G)
    (hin : Function.Injective input) (hout : Function.Injective output)
    (hcross : ∀ i j, input i ≠ output j) (hmid : Function.Injective middle)
    (hfresh : ∀ i, middle i ∉ externalPorts input output) :
    Function.Injective (routerPort input middle output) := by
  have hmi (i j : Fin n) : middle i ≠ input j := by
    intro he
    apply hfresh i
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,he.symm⟩)
  have hmo (i j : Fin n) : middle i ≠ output j := by
    intro he
    apply hfresh i
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,he.symm⟩)
  rintro ⟨a,i⟩ ⟨b,j⟩ heq
  fin_cases a <;> fin_cases b
  · exact Prod.ext rfl (hin heq)
  · exact False.elim (hmi j i heq.symm)
  · exact False.elim (hcross i j heq)
  · exact False.elim (hmi i j heq)
  · exact Prod.ext rfl (hmid heq)
  · exact False.elim (hmo i j heq)
  · exact False.elim (hcross j i heq.symm)
  · exact False.elim (hmo j i heq.symm)
  · exact Prod.ext rfl (hout heq)

private theorem four_ports_nodup {n : ℕ} (input middle output : Fin n → G)
    (hports : Function.Injective (routerPort input middle output))
    (a b : Fin 3) (hab : a ≠ b) (i j : Fin n) (hij : i ≠ j) :
    [routerPort input middle output (a,i),routerPort input middle output (a,j),
      routerPort input middle output (b,i),routerPort input middle output (b,j)].Nodup := by
  have h : [(a,i),(a,j),(b,i),(b,j)].Nodup := by
    simp [List.nodup_cons,hab,hij]
  exact h.map hports

private theorem reverse_differences {a b c d : G}
    (h : b-a ≠ d-c ∧ b-a ≠ -(d-c)) :
    a-b ≠ c-d ∧ a-b ≠ -(c-d) := by
  constructor
  · intro he
    apply h.1
    simpa only [neg_sub] using congrArg Neg.neg he
  · intro he
    apply h.2
    simpa only [neg_sub,neg_neg] using congrArg Neg.neg he

/-- Every exchange and isolated idle query in both actual adjacent layers is
legal. The only difference restrictions are the ones already chosen in §4.2. -/
theorem alternating_queries_legal {n : ℕ} (input middle output : Fin n → G)
    (hports : Function.Injective (routerPort input middle output))
    (hdifference : ∀ i : Fin (n-1),
      let e := adjacentEdge n i
      let delta := if i.val%2 = 0 then input e.2-input e.1 else output e.2-output e.1
      middle e.2-middle e.1 ≠ delta ∧ middle e.2-middle e.1 ≠ -delta) :
    (∀ v, ((firstMatchingLayer n).unitQuery input middle v).Legal) ∧
    (∀ v, ((secondMatchingLayer n).unitQuery middle output v).Legal) := by
  constructor
  · rintro (e | i)
    · have he := e.property
      obtain ⟨j,hj,heq⟩ := List.mem_map.mp he
      have hp : j.val%2 = 0 := by simpa using (List.mem_filter.mp hj).2
      have hed := hdifference j
      have hne := (firstMatchingLayer n).no_loop e e.property
      have hnd := four_ports_nodup input middle output hports 0 1 (by decide) e.1.1 e.1.2 hne
      have hr : middle e.1.1-middle e.1.2 ≠ input e.1.1-input e.1.2 ∧
          middle e.1.1-middle e.1.2 ≠ -(input e.1.1-input e.1.2) := by
        apply reverse_differences
        simpa [heq,hp] using hed
      exact ⟨hnd,hr⟩
    · change input i ≠ middle i
      intro he
      have hh := hports (show routerPort input middle output (0,i) = routerPort input middle output (1,i) from he)
      have := congrArg (fun p : Fin 3 × Fin n => p.1.val) hh
      norm_num at this
  · rintro (e | i)
    · have he := e.property
      obtain ⟨j,hj,heq⟩ := List.mem_map.mp he
      have hp : j.val%2 ≠ 0 := by simpa using (List.mem_filter.mp hj).2
      have hed := hdifference j
      have hne := (secondMatchingLayer n).no_loop e e.property
      have hnd := four_ports_nodup input middle output hports 1 2 (by decide) e.1.1 e.1.2 hne
      have hr : middle e.1.1-middle e.1.2 ≠ output e.1.1-output e.1.2 ∧
          middle e.1.1-middle e.1.2 ≠ -(output e.1.1-output e.1.2) := by
        apply reverse_differences
        simpa [heq,hp] using hed
      refine ⟨hnd,Ne.symm hr.1,?_⟩
      intro he
      apply hr.2
      simpa only [neg_neg] using (congrArg Neg.neg he).symm
    · change middle i ≠ output i
      intro he
      have hh := hports (show routerPort input middle output (1,i) = routerPort input middle output (2,i) from he)
      have := congrArg (fun p : Fin 3 × Fin n => p.1.val) hh
      norm_num at this

end
end EndpointRouter
