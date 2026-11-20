import CorralFormalization.EndpointProof.Flow.Tetrahedron.Construction
open scoped Classical BigOperators
namespace EndpointMatching.Tetrahedron
open EndpointFlow.AbelianTransport
noncomputable section
variable {G : Type*} [AddCommGroup G]

/-- The missing random event supplies fresh parameters for the concrete
PC4 formulas, uniformly over all later admissible six-root queries. -/
def TetrahedronParametersAvailable (Q : Vertex G → Prop) (budget : ℕ) : Prop :=
  ∀ (a1 a2 b1 b2 c1 c2 : G),
    a1 ≠ a2 → b1 ≠ b2 → c1 ≠ c2 →
    a1 ≠ 0 → a2 ≠ 0 → b1 ≠ 0 → b2 ≠ 0 → c1 ≠ 0 → c2 ≠ 0 →
    ∀ F : Finset G, F.card ≤ budget →
    ∃ x y z : G,
      Function.Injective (place a1 a2 b1 b2 c1 c2 x y z) ∧
      (∀ v ∈ added a1 a2 b1 b2 c1 c2 x y z, Q v) ∧
      Disjoint (support (added a1 a2 b1 b2 c1 c2 x y z))
        (F ∪ support (roots a1 a2 b1 b2 c1 c2 x y z))

theorem fourPairSupplier_of_parameters (Q : Vertex G → Prop) (budget : ℕ)
    (hparams : TetrahedronParametersAvailable Q budget) : FourPairSupplier Q budget := by
  intro O X F hO hX hOX hOn hXn hF
  choose o ho hou using hO
  choose x hx hxu using hX
  have hdistinct (p : Fin 3) : o p ≠ x p := by
    intro h
    apply Finset.disjoint_left.mp hOX (ho p)
    simpa [← h] using hx p
  have hOf (p : Fin 3) (t : G) : (p,t) ∈ O ↔ t = o p := by
    constructor
    · exact hou p t
    · intro ht
      subst t
      exact ho p
  have hXf (p : Fin 3) (t : G) : (p,t) ∈ X ↔ t = x p := by
    constructor
    · exact hxu p t
    · intro ht
      subst t
      exact hx p
  obtain ⟨u,v,w,hinj,hQ,havoid⟩ :=
    hparams (o 0) (x 0) (o 1) (x 1) (o 2) (x 2)
      (hdistinct 0) (hdistinct 1) (hdistinct 2)
      (hOn (0,o 0) (ho 0)) (hXn (0,x 0) (hx 0))
      (hOn (1,o 1) (ho 1)) (hXn (1,x 1) (hx 1))
      (hOn (2,o 2) (ho 2)) (hXn (2,x 2) (hx 2)) F hF
  have hroots : O ∪ X = roots (o 0) (x 0) (o 1) (x 1) (o 2) (x 2) u v w := by
    rw [roots_formula]
    ext ⟨p,t⟩
    fin_cases p <;> simp [hOf, hXf]
  rw [hroots]
  exact ⟨tetrahedronMerge Q F (o 0) (x 0) (o 1) (x 1) (o 2) (x 2) u v w
    hinj hQ (havoid.mono_right Finset.subset_union_right)
    (havoid.mono_right Finset.subset_union_left)⟩

end
end EndpointMatching.Tetrahedron
