import CorralFormalization.EndpointProof.Router.ReservoirEvent
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Extracting the actual greedy installation at finite unit indices

The auxiliary labels carried by the installer are retained through `Forall₂`.
Consequently distinct unit indices obtain disjoint supports even when queries
happen to agree. No independent local or global supplier is assumed.
-/
namespace EndpointRouter
open scoped BigOperators Classical
noncomputable section
universe u v
variable {G : Type u} [AddCommGroup G] [DecidableEq G]

private theorem forall₂_witness {A B : Type*} {r : A → B → Prop}
    {as : List A} {bs : List B} (h : List.Forall₂ r as bs)
    {a : A} (ha : a ∈ as) : ∃ b ∈ bs, r a b := by
  induction h with
  | nil => simp at ha
  | @cons a' b as bs hab h ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨b, by simp, hab⟩
    · obtain ⟨b', hb', hr⟩ := ih ha
      exact ⟨b', by simp [hb'], hr⟩

/-- The existing concrete primitive installer, indexed by all actually used
units. The proof records which occurrence supplied every primitive. -/
theorem indexed_install {U : Type v} [Fintype U] [DecidableEq U]
    (RV RC : Set G) (budget : ℕ) (query : U → Query G) (F : Finset G)
    (hlegal : ∀ i, (query i).Legal)
    (hbudget : F.card + ∑ i, 9*(query i).arity ≤ budget)
    (havail : ∀ q : Query G, q.Legal → ∀ F' : Finset G, F'.card ≤ budget →
      ∃ P : Primitive G, P.Good RV RC q ∧ Disjoint P.support F') :
    ∃ primitive : U → Primitive G,
      (∀ i, (primitive i).Good RV RC (query i)) ∧
      Pairwise (fun i j => Disjoint (primitive i).support (primitive j).support) ∧
      (∀ i, Disjoint (primitive i).support F) := by
  let units := (Finset.univ : Finset U).toList
  let good : U → U × Primitive G → Prop := fun i p => p.1 = i ∧ p.2.Good RV RC (query i)
  let support : U × Primitive G → Finset G := fun p => p.2.support
  have hsize : ∀ i p, good i p → (support p).card ≤ 9*(query i).arity := by
    intro i p hp
    exact Primitive.good_support_card RV RC (query i) p.2 hp.2
  have hb : F.card + (units.map (fun i => 9*(query i).arity)).sum ≤ budget := by
    simpa only [units, Finset.sum_map_toList] using hbudget
  have hav : ∀ i ∈ units, ∀ F' : Finset G, F'.card ≤ budget →
      ∃ p, good i p ∧ Disjoint (support p) F' := by
    intro i _ F' hF'
    obtain ⟨P,hP,havoid⟩ := havail (query i) (hlegal i) F' hF'
    exact ⟨(i,P), ⟨rfl,hP⟩,havoid⟩
  obtain ⟨installed,hgood,hpair,havoid⟩ :=
    greedy_install good support (fun i => 9*(query i).arity) budget hsize units F hb hav
  have hex (i : U) : ∃ p ∈ installed, good i p :=
    forall₂_witness hgood (by simp [units])
  choose selected hmem hselected using hex
  refine ⟨fun i => (selected i).2, fun i => (hselected i).2, ?_, fun i => havoid _ (hmem i)⟩
  intro i j hij
  have hne : selected i ≠ selected j := by
    intro heq
    apply hij
    exact (hselected i).1.symm.trans ((congrArg Prod.fst heq).trans (hselected j).1)
  exact hpair.forall (hmem i) (hmem j) hne

/-- No universal supply event is imported as a new premise: this is the
actual good reservoir event already proved in `ReservoirEvent.lean`. -/
theorem ReservoirEvent.indexed_install [Fintype G] {U : Type v} [Fintype U] [DecidableEq U]
    (u : ℝ) (budget : ℕ) (ω : Bool × G → Bool) (h : ReservoirEvent u budget ω)
    (query : U → Query G) (F : Finset G)
    (hlegal : ∀ i, (query i).Legal)
    (hbudget : F.card + ∑ i, 9*(query i).arity ≤ budget) :
    ∃ primitive : U → Primitive G,
      (∀ i, (primitive i).Good (vertexReservoir ω) (colorReservoir ω) (query i)) ∧
      Pairwise (fun i j => Disjoint (primitive i).support (primitive j).support) ∧
      (∀ i, Disjoint (primitive i).support F) :=
  EndpointRouter.indexed_install _ _ budget query F hlegal hbudget h.1

end
end EndpointRouter
