import CorralFormalization.EndpointProof.Selector.Assembly.Splice

/-!
The deterministic quantifiers and support accounting of the coloured selector construction.

This file is explicitly a supplier theorem: `SmallSupply` and `HelperSupply`
are hypotheses. It proves the nontrivial recursive construction, rather than
assuming an already built large selector. To obtain unconditional selector these
two hypotheses must be discharged on the same primitive sample event.
-/

open scoped Classical

namespace EndpointSelector.Assembly

noncomputable section

variable {G : Type*} [CommRing G] [DecidableEq G]

def familySupport (R : Finset (Finset (Vertex G))) : Finset G :=
  numericalSupport (R.biUnion id)

theorem support_subset_family {R : Finset (Finset (Vertex G))}
    {T : Finset (Vertex G)} (hT : T ∈ R) : numericalSupport T ⊆ familySupport R := by
  apply numericalSupport_mono
  intro v hv
  exact Finset.mem_biUnion.mpr ⟨T,hT,hv⟩

theorem familySupport_card_le (R : Finset (Finset (Vertex G)))
    (hc : ∀ T ∈ R, T.card ≤ 2) : (familySupport R).card ≤ 4*R.card := by
  have hb : (R.biUnion id).card ≤ 2*R.card := by
    calc
      (R.biUnion id).card ≤ ∑ T ∈ R, T.card := Finset.card_biUnion_le
      _ ≤ ∑ _T ∈ R, 2 := Finset.sum_le_sum hc
      _ = 2*R.card := by simp [Nat.mul_comm]
  have hn := numericalSupport_card_le (R.biUnion id)
  change (numericalSupport (R.biUnion id)).card ≤ _
  omega

/-- The numerical-root part of the interface. Actual inverse pairs in a fixed
tag satisfy both fields. Distinctness is encoded by the finite family. -/
structure RootDomain (legal : Finset (Vertex G) → Prop) : Prop where
  nonempty : ∀ T, legal T → T.Nonempty
  card_le : ∀ T, legal T → T.card ≤ 2

/-- A local supplier for every one-, two-, or three-root query and every later
forbidden numerical support. All alternatives share the supplied interior. -/
def SmallSupply (P : Vertex G → Prop) (legal : Finset (Vertex G) → Prop)
    (budget : ℕ) : Prop :=
  ∀ (R : Finset (Finset (Vertex G))) (F : Finset G),
    R.Nonempty → R.card ≤ 3 → (∀ T ∈ R, legal T) → F.card+32 ≤ budget →
    ∃ S : SelectorOn P R, S.interior.card ≤ 16 ∧
      Disjoint (numericalSupport S.interior) F

/-- The same primitive event must also supply fresh P pairs. -/
def HelperSupply (P : Vertex G → Prop) (legal : Finset (Vertex G) → Prop)
    (budget : ℕ) : Prop :=
  ∀ (F : Finset G), F.card ≤ budget →
    ∃ H : Finset (Vertex G), legal H ∧ (∀ v ∈ H, P v) ∧
      Disjoint (numericalSupport H) F

/-- A new helper, a small module, then the recursive residual selector consume
at most 36 numerical coordinates per removed module: 32 interior signs and
four helper signs. The immutable original-root support is already in F. -/
theorem selectors_of_primitive_suppliers
    (P : Vertex G → Prop) (legal : Finset (Vertex G) → Prop)
    (D : RootDomain legal) (budget : ℕ)
    (small : SmallSupply P legal budget) (helper : HelperSupply P legal budget)
    (R : Finset (Finset (Vertex G))) (F : Finset G)
    (hne : R.Nonempty) (hlegal : ∀ T ∈ R, legal T)
    (hroots : familySupport R ⊆ F)
    (hbudget : F.card + 36*R.card-4 ≤ budget) :
    ∃ (S : SelectorOn P R) (m : ℕ), Built P S m ∧ m ≤ R.card ∧
      Disjoint (numericalSupport S.interior) F := by
  classical
  have main : ∀ n : ℕ, ∀ (R : Finset (Finset (Vertex G))) (F : Finset G),
      R.card = n → R.Nonempty → (∀ T ∈ R, legal T) → familySupport R ⊆ F →
      F.card + 36*n-4 ≤ budget →
      ∃ (S : SelectorOn P R) (m : ℕ), Built P S m ∧ m ≤ n ∧
        Disjoint (numericalSupport S.interior) F := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro R F hn hne hlegal hroots hbudget
      have hnpos : 1 ≤ n := by have := Finset.card_pos.mpr hne; omega
      have hFbudget : F.card ≤ budget := by omega
      by_cases hnsmall : n ≤ 3
      · obtain ⟨S,hS,hd⟩ := small R F hne (by omega) hlegal (by omega)
        exact ⟨S,1,Built.small S hS,hnpos,hd⟩
      · obtain ⟨a,ha⟩ := hne
        have herase : (R.erase a).Nonempty := by
          apply Finset.card_pos.mp
          rw [Finset.card_erase_of_mem ha]
          omega
        obtain ⟨b,hb⟩ := herase
        have hbR : b ∈ R := (Finset.mem_erase.mp hb).2
        have hba : b ≠ a := (Finset.mem_erase.mp hb).1
        let B := (R.erase a).erase b
        have hBsub : B ⊆ R := (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
        have hBcard : B.card = n-2 := by
          simp only [B,Finset.card_erase_of_mem hb,Finset.card_erase_of_mem ha,hn]
          omega
        obtain ⟨H,hH,hHP,hHF⟩ := helper F hFbudget
        have hHnot : H ∉ R := by
          intro hHR
          obtain ⟨v,hv⟩ := D.nonempty H hH
          exact Finset.disjoint_left.mp hHF (coordinate_mem_numericalSupport hv)
            (hroots (support_subset_family hHR (coordinate_mem_numericalSupport hv)))
        have hHa : H ≠ a := fun he ↦ hHnot (he ▸ ha)
        have hHb : H ≠ b := fun he ↦ hHnot (he ▸ hbR)
        let A : Finset (Finset (Vertex G)) := {a,b}
        let Q := insert H A
        let Fh := F ∪ numericalSupport H
        have hHsize : (numericalSupport H).card ≤ 4 := by
          have hc := D.card_le H hH
          have hs := numericalSupport_card_le H
          omega
        have hFhsize : Fh.card ≤ F.card+4 := by
          exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left hHsize _)
        have hQne : Q.Nonempty := Finset.insert_nonempty _ _
        have hQcard : Q.card ≤ 3 := by
          calc
            Q.card ≤ A.card+1 := Finset.card_insert_le _ _
            _ ≤ 3 := by have hc : A.card ≤ 2 := Finset.card_le_two; omega
        have hQlegal : ∀ T ∈ Q, legal T := by
          intro T hT
          simp only [Q,A,Finset.mem_insert,Finset.mem_singleton] at hT
          rcases hT with hT | hT | hT
          · simpa only [hT] using hH
          · simpa only [hT] using hlegal a ha
          · simpa only [hT] using hlegal b hbR
        obtain ⟨L,hLsize,hLFh⟩ := small Q Fh hQne hQcard hQlegal (by omega)
        let Fnext := Fh ∪ numericalSupport L.interior
        have hLI : (numericalSupport L.interior).card ≤ 32 := by
          have hs := numericalSupport_card_le L.interior
          omega
        have hFnext : Fnext.card ≤ F.card+36 := by
          have hc := Finset.card_union_le Fh (numericalSupport L.interior)
          change (Fh ∪ numericalSupport L.interior).card ≤ _
          omega
        let Rnext := insert H B
        have hRnextcard : Rnext.card = n-1 := by
          rw [Finset.card_insert_of_notMem (fun hh ↦ hHnot (hBsub hh)),hBcard]
          omega
        have hRnextlegal : ∀ T ∈ Rnext, legal T := by
          intro T hT
          rcases Finset.mem_insert.mp hT with rfl | hT
          · exact hH
          · exact hlegal T (hBsub hT)
        have hRnextroots : familySupport Rnext ⊆ Fnext := by
          intro x hx
          change x ∈ familySupport (insert H B) at hx
          simp only [familySupport,Finset.biUnion_insert,id_eq,numericalSupport_union,
            Finset.mem_union] at hx
          rcases hx with hx | hx
          · exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)
          · exact Finset.mem_union_left _ (Finset.mem_union_left _
              (hroots (numericalSupport_mono (by
                intro v hv
                obtain ⟨T,hT,hv⟩ := Finset.mem_biUnion.mp hv
                exact Finset.mem_biUnion.mpr ⟨T,hBsub hT,hv⟩) hx)))
        obtain ⟨S,m,hS,hm,hSF⟩ := ih (n-1) (by omega) Rnext Fnext hRnextcard
          (Finset.insert_nonempty _ _) hRnextlegal hRnextroots (by omega)
        have hLF : Disjoint (numericalSupport L.interior) F :=
          hLFh.mono_right Finset.subset_union_left
        have hSFold : Disjoint (numericalSupport S.interior) F :=
          hSF.mono_right (Finset.subset_union_left.trans Finset.subset_union_left)
        have hSFL : Disjoint (numericalSupport S.interior) (numericalSupport L.interior) :=
          hSF.mono_right Finset.subset_union_right
        have hSLtag : Disjoint L.interior S.interior :=
          (disjoint_of_numericalSupport hSFL).symm
        have hC : SpliceCompatible (A := A) (B := B) (H := H) L S := by
          refine ⟨hSLtag,?_,?_,?_,hHP⟩
          · intro T hT
            apply disjoint_of_numericalSupport
            exact hLF.mono_right ((support_subset_family (hBsub hT)).trans hroots)
          · intro T hT
            have hTR : T ∈ R := by
              simp only [A,Finset.mem_insert,Finset.mem_singleton] at hT
              rcases hT with rfl | rfl <;> assumption
            apply disjoint_of_numericalSupport
            exact hSFold.mono_right ((support_subset_family hTR).trans hroots)
          · intro T hT
            have hTR : T ∈ R := by
              rcases Finset.mem_union.mp hT with hT | hT
              · simp only [A,Finset.mem_insert,Finset.mem_singleton] at hT
                rcases hT with rfl | rfl <;> assumption
              · exact hBsub hT
            apply disjoint_of_numericalSupport
            exact hHF.mono_right ((support_subset_family hTR).trans hroots)
        have hAB : A ∪ B = R := by
          ext T
          simp only [A,B,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
            Finset.mem_erase]
          constructor
          · rintro ((rfl | rfl) | ⟨_,_,hT⟩)
            · exact ha
            · exact hbR
            · exact hT
          · intro hT
            by_cases hTa : T = a
            · exact Or.inl (Or.inl hTa)
            by_cases hTb : T = b
            · exact Or.inl (Or.inr hTb)
            exact Or.inr ⟨hTb,hTa,hT⟩
        let Z := splice L S hC
        have hZ : Built P Z (1+m) := Built.join L S hC (D.card_le H hH)
          (Built.small L hLsize) hS
        have hZF : Disjoint (numericalSupport Z.interior) F := by
          simp only [Z,splice,numericalSupport_union,Finset.disjoint_union_left]
          exact ⟨⟨hLF,hSFold⟩,hHF⟩
        have hout : ∃ (Z : SelectorOn P (A ∪ B)) (m : ℕ),
            Built P Z m ∧ m ≤ n ∧ Disjoint (numericalSupport Z.interior) F :=
          ⟨Z,1+m,hZ,by omega,hZF⟩
        exact Eq.mp (congrArg (fun Q ↦ ∃ (Z : SelectorOn P Q) (m : ℕ),
          Built P Z m ∧ m ≤ n ∧ Disjoint (numericalSupport Z.interior) F) hAB) hout
  exact main R.card R F rfl hne hlegal hroots hbudget

/-- Literal `1≤k≤100` quantitative consumer. `C+3996≤budget` pays every
intermediate primitive query, with one immutable external forbidden set. -/
theorem colouredSelector_of_primitive_suppliers
    (P : Vertex G → Prop) (legal : Finset (Vertex G) → Prop)
    (D : RootDomain legal) (budget C : ℕ)
    (small : SmallSupply P legal budget) (helper : HelperSupply P legal budget)
    (hmargin : C+3996 ≤ budget)
    (R : Finset (Finset (Vertex G))) (hne : R.Nonempty) (hk : R.card ≤ 100)
    (hlegal : ∀ T ∈ R, legal T) (F : Finset G) (hF : F.card ≤ C) :
    ∃ S : SelectorOn P R,
      S.interior.card ≤ 18*R.card-2 ∧
      Disjoint (numericalSupport S.interior) F ∧
      (numericalSupport (S.interior ∪ R.biUnion id)).card ≤ 3996 := by
  let F₀ := F ∪ familySupport R
  have hR : (familySupport R).card ≤ 4*R.card :=
    familySupport_card_le R (fun T hT ↦ D.card_le T (hlegal T hT))
  have hF₀ : F₀.card ≤ C+4*R.card := by
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add hF hR)
  have hnecard : 1 ≤ R.card := Finset.card_pos.mpr hne
  obtain ⟨S,m,hS,hm,hSF⟩ := selectors_of_primitive_suppliers P legal D budget small helper
    R F₀ hne hlegal Finset.subset_union_right (by omega)
  exact ⟨S,hS.selector_cardinality_bound hm,hSF.mono_right Finset.subset_union_left,
    hS.support_bound hm hk le_rfl (fun T hT ↦ D.card_le T (hlegal T hT))⟩

end
end EndpointSelector.Assembly
