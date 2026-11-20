import CorralFormalization.EndpointProof.Flow.AbelianTransport.Access

/-!
Finite ingredients for fixed-cardinality selectors on the actual tagged
zero-sum hypergraph. The eventual selection graph and probabilistic event
are separate inputs. In particular, a local selector is not itself a
fixed-cardinality selector.
-/

open scoped Classical BigOperators

namespace EndpointSelector.FixedCardinality

open EndpointFlow.AbelianTransport

noncomputable section

variable {G : Type*} [AddCommGroup G]

/-- A paired nonzero reservoir is enough to extract fresh helper pairs. -/
structure PairReservoir (P : Vertex G → Prop) : Prop where
  nonzero : ∀ v, P v → v.2 ≠ 0
  paired : ∀ v, P v → P (v.1, -v.2)

/-- Uniform actual local selector supply on one fixed reservoir. -/
def LocalSupply (P : Vertex G → Prop) (budget arity : ℕ) : Prop :=
  ∀ (part : Fin 3) (R : Finset (Finset (Vertex G))),
    R.Nonempty → R.card ≤ arity → (∀ T ∈ R, LegalPair part T) →
    ∀ F : Finset G, F.card ≤ budget →
      ∃ S : Selector P R,
        S.interior.card ≤ 18 * R.card - 2 ∧
        Disjoint (support S.interior) F

/-- The current sampled selector event implies the local contract. -/
theorem localSupply_of_colouredSelectors [Fintype G]
    (ω : EndpointFullProduct.FullSample G) (budget degree : ℕ)
    (hdegree : degree ≤ 100) (h : ColouredSelectors ω budget) :
    LocalSupply (ReservoirVertex ω false) budget degree := by
  intro part R hne hcard hlegal F hF
  obtain ⟨S, hsize, havoid, _⟩ :=
    h part R hne (hcard.trans hdegree) hlegal F hF
  exact ⟨S, hsize, havoid⟩

/-- Both signs of every actual P or Q child label occur on the same orbit,
and the orbit never contains zero. No additional sample event is needed. -/
theorem pairReservoir_of_reservoirVertex [Fintype G]
    (ω : EndpointFullProduct.FullSample G) (isQ : Bool) :
    PairReservoir (ReservoirVertex ω isQ) := by
  constructor
  · intro v hv
    obtain ⟨o, side, hcoord, _⟩ := hv
    rw [← hcoord]
    exact EndpointOriginalReservoir.orbitPlace_nonzero (o, side)
  · intro v hv
    obtain ⟨o, side, hcoord, hchild⟩ := hv
    refine ⟨o, !side, ?_, hchild⟩
    rw [EndpointOriginalReservoir.orbitPlace_neg, hcoord]

/-- Exactly one interior is selected before any later subfamily. -/
structure FixedSelector (P : Vertex G → Prop)
    (Y : Finset (Finset (Vertex G))) (s : ℕ) where
  interior : Finset (Vertex G)
  inside : ∀ v ∈ interior, P v
  roots_fresh : Disjoint (support interior) (support (Y.biUnion id))
  matching : ∀ Y₀ : Finset (Finset (Vertex G)), Y₀ ⊆ Y → Y₀.card = s →
    Nonempty (Matching (interior ∪ Y₀.biUnion id))

/-- Every hyperedge has a vertex in each part. -/
theorem hyperedge_has_part {E : Finset (Vertex G)} (hE : Hyperedge E)
    (p : Fin 3) : ∃ a : G, (p, a) ∈ E := by
  obtain ⟨x, y, z, _, rfl⟩ := hE
  fin_cases p
  · exact ⟨x, by simp⟩
  · exact ⟨y, by simp⟩
  · exact ⟨z, by simp⟩

/-- Local selectors themselves supply fresh helper pairs. No additional
sample count or independent helper supplier is assumed. -/
theorem fresh_pair_of_localSupply
    {P : Vertex G → Prop} {budget arity : ℕ}
    (hP : PairReservoir P) (hlocal : LocalSupply P budget arity)
    (harity : 1 ≤ arity) (a : G) (ha : a ≠ 0)
    (part : Fin 3) (F : Finset G) (hF : F.card ≤ budget) :
    ∃ H : Finset (Vertex G), LegalPair part H ∧
      (∀ v ∈ H, P v) ∧ Disjoint (support H) F := by
  classical
  let q : Fin 3 := if part = 0 then 1 else 0
  have hpq : part ≠ q := by
    fin_cases part <;> simp [q]
  let T : Finset (Vertex G) := {(q, a), (q, -a)}
  have hT : LegalPair q T := ⟨a, ha, rfl⟩
  obtain ⟨S, _, havoid⟩ :=
    hlocal q {T} (Finset.singleton_nonempty T) (by simpa using harity)
      (by simpa using hT) F hF
  obtain ⟨M⟩ := S.matching T (Finset.mem_singleton_self T)
  have hroot : (q, a) ∈ S.interior ∪ T := by simp [T]
  rw [← M.cover] at hroot
  obtain ⟨E, hEM, _⟩ := Finset.mem_biUnion.mp hroot
  obtain ⟨g, hgE⟩ := hyperedge_has_part (M.valid E hEM) part
  have hgI : (part, g) ∈ S.interior := by
    have hgcover : (part, g) ∈ S.interior ∪ T := by
      rw [← M.cover]
      exact Finset.mem_biUnion.mpr ⟨E, hEM, hgE⟩
    rcases Finset.mem_union.mp hgcover with hg | hg
    · exact hg
    · simp only [T, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hg
      rcases hg with hg | hg
      · exact (hpq hg.1).elim
      · exact (hpq hg.1).elim
  have hgP : P (part, g) := S.inside (part, g) hgI
  have hgn : g ≠ 0 := hP.nonzero (part, g) hgP
  refine ⟨{(part, g), (part, -g)}, ⟨g, hgn, rfl⟩, ?_, ?_⟩
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact hgP
    · exact hP.paired (part, g) hgP
  · apply Finset.disjoint_left.mpr
    intro x hx hxF
    have hxs : x = g ∨ x = -g := by
      simpa [support, or_comm] using hx
    have hg_support : g ∈ support S.interior := by
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(part, g), hgI, rfl⟩)
    have hng_support : -g ∈ support S.interior := by
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(part, g), hgI, rfl⟩)
    rcases hxs with rfl | rfl
    · exact Finset.disjoint_left.mp havoid hg_support hxF
    · exact Finset.disjoint_left.mp havoid hng_support hxF

/-- A local state retains actual matchings for every target pair. -/
def LocalState (P : Vertex G → Prop) (R : Finset (Finset (Vertex G)))
    (I : Finset (Vertex G)) : Prop :=
  (∀ v ∈ I, P v) ∧ I.card ≤ 18 * R.card - 2 ∧
    ∀ T ∈ R, Nonempty (Matching (I ∪ T))

theorem support_card_le (I : Finset (Vertex G)) :
    (support I).card ≤ 2 * I.card := by
  calc
    (support I).card ≤ (I.image Prod.snd).card +
        (I.image (fun v => -v.2)).card := Finset.card_union_le _ _
    _ ≤ I.card + I.card := Nat.add_le_add Finset.card_image_le Finset.card_image_le
    _ = 2 * I.card := by omega

/-- Install finitely many local selectors successively on one reservoir.
The single forbidden set F is retained at every stage, and each new local
interior also avoids the inverse supports of all earlier interiors. -/
theorem install_local_selectors {ι : Type*} [DecidableEq ι]
    {P : Vertex G → Prop} {budget arity : ℕ}
    (hlocal : LocalSupply P budget arity)
    (part : Fin 3) (D : Finset ι)
    (R : ι → Finset (Finset (Vertex G))) (F : Finset G)
    (hquery : ∀ i ∈ D, (R i).Nonempty ∧ (R i).card ≤ arity ∧
      ∀ T ∈ R i, LegalPair part T)
    (hbudget : F.card + ∑ i ∈ D, 2 * (18 * (R i).card - 2) ≤ budget) :
    ∃ I : ι → Finset (Vertex G),
      (∀ i ∈ D, LocalState P (R i) (I i)) ∧
      (∀ i ∈ D, Disjoint (support (I i)) F) ∧
      (∀ i ∈ D, ∀ j ∈ D, i ≠ j →
        Disjoint (support (I i)) (support (I j))) := by
  classical
  revert hquery hbudget
  induction D using Finset.induction_on with
  | empty =>
      intro _ _
      exact ⟨fun _ => ∅, by simp, by simp, by simp⟩
  | @insert i D hi ih =>
      intro hquery hbudget
      have hqueryD : ∀ j ∈ D, (R j).Nonempty ∧ (R j).card ≤ arity ∧
          ∀ T ∈ R j, LegalPair part T := by
        intro j hj
        exact hquery j (Finset.mem_insert_of_mem hj)
      have hbudgetD :
          F.card + ∑ j ∈ D, 2 * (18 * (R j).card - 2) ≤ budget := by
        simp only [Finset.sum_insert hi] at hbudget
        omega
      obtain ⟨I, hstate, havoid, hdis⟩ := ih hqueryD hbudgetD
      let F' := F ∪ D.biUnion (fun j => support (I j))
      have hsum :
          (D.biUnion (fun j => support (I j))).card ≤
            ∑ j ∈ D, 2 * (18 * (R j).card - 2) := by
        calc
          _ ≤ ∑ j ∈ D, (support (I j)).card := Finset.card_biUnion_le
          _ ≤ ∑ j ∈ D, 2 * (18 * (R j).card - 2) := by
            apply Finset.sum_le_sum
            intro j hj
            exact (support_card_le (I j)).trans
              (Nat.mul_le_mul_left 2 (hstate j hj).2.1)
      have hF' : F'.card ≤ budget := by
        have hcard := Finset.card_union_le F (D.biUnion (fun j => support (I j)))
        simp only [Finset.sum_insert hi] at hbudget
        dsimp [F']
        omega
      obtain ⟨hne, harity, hlegal⟩ := hquery i (Finset.mem_insert_self _ _)
      obtain ⟨S, hsize, hSavoid⟩ := hlocal part (R i) hne harity hlegal F' hF'
      let J := Function.update I i S.interior
      have hJi : J i = S.interior := by simp [J]
      have hJj {j : ι} (hj : j ∈ D) : J j = I j := by
        have hji : j ≠ i := by
          intro h
          subst j
          exact hi hj
        simp [J, hji]
      refine ⟨J, ?_, ?_, ?_⟩
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · rw [hJi]
          exact ⟨S.inside, hsize, S.matching⟩
        · rw [hJj hj]
          exact hstate j hj
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · rw [hJi]
          exact hSavoid.mono_right Finset.subset_union_left
        · rw [hJj hj]
          exact havoid j hj
      · intro j hj k hk hjk
        rcases Finset.mem_insert.mp hj with hjEq | hjD
        · subst j
          have hkD : k ∈ D := by
            rcases Finset.mem_insert.mp hk with he | he
            · exact (hjk he.symm).elim
            · exact he
          rw [hJi, hJj hkD]
          apply hSavoid.mono_right
          intro x hx
          exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨k, hkD, hx⟩)
        · rcases Finset.mem_insert.mp hk with hkEq | hkD
          · subst k
            rw [hJj hjD, hJi]
            apply (hSavoid.mono_right ?_).symm
            intro x hx
            exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j, hjD, hx⟩)
          · rw [hJj hjD, hJj hkD]
            exact hdis j hjD k hkD hjk
end
end EndpointSelector.FixedCardinality
