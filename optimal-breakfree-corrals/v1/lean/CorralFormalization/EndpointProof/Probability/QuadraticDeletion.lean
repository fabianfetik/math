import CorralFormalization.EndpointProof.Probability.JointAvailability
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
Deterministic numerical-deletion step in the quadratic absorbing core.

Unlike the older nine-orbit packed flow, the current tetrahedron uses a
cubic family of correlated candidates. Its quadratic numerical deletion
capacity follows from a lower bound for the total successful count and
upper bounds for coordinate sections. These hypotheses are counts, not
the desired robust availability event. The concentration estimates and
the construction of the twelve affine forms are not proved in this file.
-/

open MeasureTheory
open scoped BigOperators Classical

namespace CorralFormalization.EndpointProof.Probability.QuadraticDeletion

noncomputable section

variable {Candidate Coordinate : Type*}

/-- Successful candidates destroyed by a numerical forbidden set. -/
def destroyed (C : Finset Candidate) (support : Candidate → Finset Coordinate)
    (F : Finset Coordinate) : Finset Candidate :=
  C.filter (fun c ↦ ¬ Disjoint (support c) F)

/-- Successful candidates surviving a numerical forbidden set. -/
def surviving (C : Finset Candidate) (support : Candidate → Finset Coordinate)
    (F : Finset Coordinate) : Finset Candidate :=
  C.filter (fun c ↦ Disjoint (support c) F)

/-- A coordinate can destroy at most `L` successful candidates, so an
arbitrary later set destroys at most `|F| L`. Candidate supports may
overlap, and the forbidden set can depend on every sampled label. -/
theorem destroyed_card_le (C : Finset Candidate)
    (support : Candidate → Finset Coordinate) (L : ℝ)
    (hcoordinate : ∀ g, ((C.filter (fun c ↦ g ∈ support c)).card : ℝ) ≤ L)
    (F : Finset Coordinate) :
    ((destroyed C support F).card : ℝ) ≤ (F.card : ℝ) * L := by
  have hsub : destroyed C support F ⊆
      F.biUnion (fun g ↦ C.filter (fun c ↦ g ∈ support c)) := by
    intro c hc
    obtain ⟨hc, hhit⟩ := Finset.mem_filter.mp hc
    obtain ⟨g, hg, hgF⟩ := Finset.not_disjoint_iff.mp hhit
    exact Finset.mem_biUnion.mpr ⟨g, hgF, Finset.mem_filter.mpr ⟨hc, hg⟩⟩
  calc
    ((destroyed C support F).card : ℝ)
      ≤ ((F.biUnion (fun g ↦ C.filter (fun c ↦ g ∈ support c))).card : ℝ) :=
        Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ ≤ ∑ g ∈ F, ((C.filter (fun c ↦ g ∈ support c)).card : ℝ) := by
        exact_mod_cast (Finset.card_biUnion_le (s := F)
          (t := fun g ↦ C.filter (fun c ↦ g ∈ support c)))
    _ ≤ ∑ _g ∈ F, L := Finset.sum_le_sum (fun g _ ↦ hcoordinate g)
    _ = (F.card : ℝ) * L := by simp

/-- Quantitative deletion bound, retaining the number of surviving
successful candidates rather than merely asserting one exists. -/
theorem surviving_card_lower_bound (C : Finset Candidate)
    (support : Candidate → Finset Coordinate) (L : ℝ)
    (hcoordinate : ∀ g, ((C.filter (fun c ↦ g ∈ support c)).card : ℝ) ≤ L)
    (F : Finset Coordinate) :
    (C.card : ℝ) - (F.card : ℝ) * L ≤ ((surviving C support F).card : ℝ) := by
  have hpartition : (surviving C support F).card + (destroyed C support F).card =
      C.card := Finset.card_filter_add_card_filter_not _
  have hpartition' : ((surviving C support F).card : ℝ) +
      ((destroyed C support F).card : ℝ) = (C.card : ℝ) := by
    exact_mod_cast hpartition
  linarith [destroyed_card_le C support L hcoordinate F]

/-- The constants used by tetrahedron paired-cover: at least `τ^12 n^3 / 2`
successful triples, at most `48 τ^10 n^2` successes incident with any
numerical coordinate, and `|F| ≤ τ^2 n / 192` retain at least
`τ^12 n^3 / 4` candidates. All forbidden sets are quantified after the
count bounds, with no independence requirement and no union bound over F. -/
theorem tetrahedron_quadratic_capacity (τ n : ℝ) (hτ : 0 < τ) (hn : 0 < n)
    (C : Finset Candidate) (support : Candidate → Finset Coordinate)
    (htotal : τ^12 * n^3 / 2 ≤ (C.card : ℝ))
    (hcoordinate : ∀ g, ((C.filter (fun c ↦ g ∈ support c)).card : ℝ) ≤
      48 * τ^10 * n^2) :
    ∀ F : Finset Coordinate, (F.card : ℝ) ≤ τ^2 * n / 192 →
      τ^12 * n^3 / 4 ≤ ((surviving C support F).card : ℝ) ∧
        ∃ c ∈ C, Disjoint (support c) F := by
  intro F hF
  have hcapacity : (F.card : ℝ) * (48 * τ^10 * n^2) ≤ τ^12 * n^3 / 4 := by
    calc
      (F.card : ℝ) * (48 * τ^10 * n^2)
        ≤ (τ^2 * n / 192) * (48 * τ^10 * n^2) :=
          mul_le_mul_of_nonneg_right hF (by positivity)
      _ = τ^12 * n^3 / 4 := by ring
  have hsurv : τ^12 * n^3 / 4 ≤ ((surviving C support F).card : ℝ) := by
    linarith [surviving_card_lower_bound C support (48 * τ^10 * n^2) hcoordinate F]
  refine ⟨hsurv, ?_⟩
  have hpos : 0 < ((surviving C support F).card : ℝ) :=
    lt_of_lt_of_le (by positivity) hsurv
  have hnonempty : (surviving C support F).Nonempty :=
    Finset.card_pos.mp (by exact_mod_cast hpos)
  obtain ⟨c, hc⟩ := hnonempty
  exact ⟨c, (Finset.mem_filter.mp hc).1, (Finset.mem_filter.mp hc).2⟩

/-- Passing a coordinate through an injective map cannot increase the
largest fibre of a finite family. This pays affine translations and signs
without a field assumption on the finite abelian group. -/
theorem section_bound_of_injective {G H : Type*}
    (C : Finset Candidate) (direction : Candidate → G) (f : G → H)
    (hf : Function.Injective f) (L : ℝ) (hL : 0 ≤ L)
    (hsection : ∀ g, ((C.filter (fun c ↦ direction c = g)).card : ℝ) ≤ L) :
    ∀ g, ((C.filter (fun c ↦ f (direction c) = g)).card : ℝ) ≤ L := by
  intro g
  by_cases hne : (C.filter (fun c ↦ f (direction c) = g)).Nonempty
  · obtain ⟨c₀, hc₀⟩ := hne
    have hc₀' := (Finset.mem_filter.mp hc₀).2
    apply le_trans (Nat.cast_le.mpr (Finset.card_le_card ?_)) (hsection (direction c₀))
    intro c hc
    obtain ⟨hc, hcg⟩ := Finset.mem_filter.mp hc
    exact Finset.mem_filter.mpr ⟨hc, hf (hcg.trans hc₀'.symm)⟩
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simpa using hL

/-- Numerical support of twelve new inverse pairs, forgetting tags. -/
def twelvePairSupport {G : Type*} [Neg G]
    (representative : Fin 12 → Candidate → G) (c : Candidate) : Finset G :=
  Finset.univ.image (fun i : Fin 12 × Bool ↦
    if i.2 then -representative i.1 c else representative i.1 c)

/-- Twelve representatives, with both signs, create at most 24 fibres.
The coordinate sections need not be independent or disjoint. -/
theorem twelve_pair_incidence {G : Type*} [AddCommGroup G]
    (C : Finset Candidate) (representative : Fin 12 → Candidate → G)
    (L : ℝ) (hL : 0 ≤ L)
    (hsection : ∀ i g, ((C.filter (fun c ↦ representative i c = g)).card : ℝ) ≤ L) :
    ∀ g, ((C.filter (fun c ↦ g ∈ twelvePairSupport representative c)).card : ℝ) ≤
      24 * L := by
  intro g
  let hit (i : Fin 12 × Bool) : Finset Candidate :=
    C.filter (fun c ↦ (if i.2 then -representative i.1 c else representative i.1 c) = g)
  have hhit : ∀ i, ((hit i).card : ℝ) ≤ L := by
    rintro ⟨i, b⟩
    cases b with
    | false => exact hsection i g
    | true =>
      exact section_bound_of_injective C (representative i) (fun x ↦ -x)
        neg_injective L hL (hsection i) g
  have hsub : C.filter (fun c ↦ g ∈ twelvePairSupport representative c) ⊆
      Finset.univ.biUnion hit := by
    intro c hc
    obtain ⟨hc, hg⟩ := Finset.mem_filter.mp hc
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hg
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, Finset.mem_filter.mpr ⟨hc, hi⟩⟩
  calc
    ((C.filter (fun c ↦ g ∈ twelvePairSupport representative c)).card : ℝ)
      ≤ ((Finset.univ.biUnion hit).card : ℝ) :=
        Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ ≤ ∑ i : Fin 12 × Bool, ((hit i).card : ℝ) := by
        exact_mod_cast (Finset.card_biUnion_le (s := Finset.univ) (t := hit))
    _ ≤ ∑ _i : Fin 12 × Bool, L := Finset.sum_le_sum (fun i _ ↦ hhit i)
    _ = 24 * L := by norm_num

section Tetrahedron

variable {G : Type*} [AddCommGroup G]

/-- Root names and parameter order agree with the paired-cover numerical deletion condition. -/
structure TetrahedronRoots (G : Type*) where
  a₁ : G
  a₂ : G
  b₁ : G
  b₂ : G
  c₁ : G
  c₂ : G

abbrev TetrahedronParameters (G : Type*) := G × G × G

/-- The six section directions in the current paired-cover proof. -/
def tetrahedronDirection (i : Fin 6) (t : TetrahedronParameters G) : G :=
  ![t.1, t.2.1, t.2.2, t.1 + t.2.1, -t.1 + t.2.2, -t.2.1 - t.2.2] i

def tetrahedronDirectionIndex (i : Fin 12) : Fin 6 :=
  ![3, 4, 5, 0, 3, 4, 1, 2, 5, 0, 1, 2] i

def tetrahedronNegative (i : Fin 12) : Bool :=
  ![false, true, true, false, true, false, true, false, false, true, false, true] i

def tetrahedronOffset (r : TetrahedronRoots G) (i : Fin 12) : G :=
  ![r.c₁, -r.b₂, -r.a₁-r.a₂, 0, 0, r.c₂+r.b₂,
    r.a₁, 0, r.b₁+r.a₁+r.a₂, r.b₂, 0, r.a₂] i

/-- Order: h01, h20, h30, h12, h10, h02, h31, h23, h03, h21, h13, h32. -/
def tetrahedronRepresentative (r : TetrahedronRoots G) (i : Fin 12)
    (t : TetrahedronParameters G) : G :=
  (if tetrahedronNegative i then
    -tetrahedronDirection (tetrahedronDirectionIndex i) t else
    tetrahedronDirection (tetrahedronDirectionIndex i) t) + tetrahedronOffset r i

/-- Check the actual twelve affine representatives against the written
table; the six-direction decomposition is not an assumed correspondence. -/
theorem tetrahedron_representative_expanded (r : TetrahedronRoots G)
    (i : Fin 12) (t : TetrahedronParameters G) :
    tetrahedronRepresentative r i t =
      ![r.c₁+t.1+t.2.1, t.1-t.2.2-r.b₂, t.2.1+t.2.2-r.a₁-r.a₂, t.1,
        -t.1-t.2.1, r.c₂+r.b₂-t.1+t.2.2, r.a₁-t.2.1, t.2.2,
        r.b₁+r.a₁+r.a₂-t.2.1-t.2.2, r.b₂-t.1, t.2.1, r.a₂-t.2.2] i := by
  fin_cases i <;>
    simp [tetrahedronRepresentative, tetrahedronNegative, tetrahedronDirection,
      tetrahedronDirectionIndex, tetrahedronOffset] <;> abel

/-- Six numerical direction-section bounds imply the required pointwise
incidence bound 48 τ^10 n^2 for the actual twelve-pair gadget. It suffices
to bound successful candidates in a section; the proof's larger counts
obtained by dropping two reservoir-label requirements also suffice. -/
theorem tetrahedron_section_incidence (r : TetrahedronRoots G)
    (C : Finset (TetrahedronParameters G)) (τ n : ℝ)
    (hsection : ∀ i g,
      ((C.filter (fun t ↦ tetrahedronDirection i t = g)).card : ℝ) ≤
        2 * τ^10 * n^2) :
    ∀ g, ((C.filter (fun t ↦ g ∈
      twelvePairSupport (tetrahedronRepresentative r) t)).card : ℝ) ≤
        48 * τ^10 * n^2 := by
  have hrep : ∀ i g,
      ((C.filter (fun t ↦ tetrahedronRepresentative r i t = g)).card : ℝ) ≤
        2 * τ^10 * n^2 := by
    intro i g
    let f : G → G := fun x ↦
      (if tetrahedronNegative i then -x else x) + tetrahedronOffset r i
    have hf : Function.Injective f := by
      intro x y hxy
      have h : (if tetrahedronNegative i then -x else x) =
          (if tetrahedronNegative i then -y else y) := add_right_cancel hxy
      split_ifs at h with hi
      · exact neg_injective h
      · exact h
    exact section_bound_of_injective C
      (tetrahedronDirection (tetrahedronDirectionIndex i)) f hf
      (2 * τ^10 * n^2) (by positivity)
      (hsection (tetrahedronDirectionIndex i)) g
  have h := twelve_pair_incidence C (tetrahedronRepresentative r)
    (2 * τ^10 * n^2) (by positivity) hrep
  have heq : (24 : ℝ) * (2 * τ^10 * n^2) = 48 * τ^10 * n^2 := by ring
  simpa only [heq] using h

/-- The current tetrahedron's numerical exclusion capacity, conditional
only on the explicit total-count and six direction-section counts. -/
theorem tetrahedron_available_of_section_counts (r : TetrahedronRoots G)
    (C : Finset (TetrahedronParameters G)) (τ n : ℝ) (hτ : 0 < τ) (hn : 0 < n)
    (htotal : τ^12 * n^3 / 2 ≤ (C.card : ℝ))
    (hsection : ∀ i g,
      ((C.filter (fun t ↦ tetrahedronDirection i t = g)).card : ℝ) ≤
        2 * τ^10 * n^2) :
    ∀ F : Finset G, (F.card : ℝ) ≤ τ^2 * n / 192 →
      τ^12 * n^3 / 4 ≤
        ((surviving C (twelvePairSupport (tetrahedronRepresentative r)) F).card : ℝ) ∧
      ∃ t ∈ C, Disjoint (twelvePairSupport (tetrahedronRepresentative r) t) F :=
  tetrahedron_quadratic_capacity τ n hτ hn C
    (twelvePairSupport (tetrahedronRepresentative r)) htotal
    (tetrahedron_section_incidence r C τ n hsection)

/-- All root queries and all later numerical exclusions hold on the same
sample. The success set `C ω query` may be arbitrarily correlated across
queries and parameter triples. -/
def TetrahedronAvailable {Ω Query : Type*}
    (roots : Query → TetrahedronRoots G)
    (C : Ω → Query → Finset (TetrahedronParameters G)) (τ n : ℝ) (ω : Ω) : Prop :=
  ∀ query, ∀ F : Finset G, (F.card : ℝ) ≤ τ^2 * n / 192 →
    τ^12 * n^3 / 4 ≤
      ((surviving (C ω query) (twelvePairSupport (tetrahedronRepresentative (roots query)))
        F).card : ℝ) ∧
    ∃ t ∈ C ω query,
      Disjoint (twelvePairSupport (tetrahedronRepresentative (roots query)) t) F

/-- A union bound over root queries and the six direction sections gives
one event handling *every* later F. The only probability inputs are the
total-count and individual section-count tails; the theorem neither assumes
robust availability nor requires independence between event families.

For `n = |G|` and at most n^6 root queries this pays at most n^6 total
tails and 6 n^7 section tails, with no additional factor for forbidden sets.
The actual original-law concentration estimates remain separate obligations.
-/
theorem tetrahedron_common_event_probability {Ω Query : Type*}
    [MeasurableSpace Ω] [Fintype Query] [Fintype G]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (roots : Query → TetrahedronRoots G)
    (C : Ω → Query → Finset (TetrahedronParameters G))
    (τ n u v : ℝ) (hτ : 0 < τ) (hn : 0 < n)
    (htotal : ∀ query,
      μ.real {ω | ¬ τ^12 * n^3 / 2 ≤ ((C ω query).card : ℝ)} ≤ u)
    (hsection : ∀ query i g,
      μ.real {ω | ¬
        (((C ω query).filter (fun t ↦ tetrahedronDirection i t = g)).card : ℝ) ≤
          2 * τ^10 * n^2} ≤ v) :
    μ.real {ω | ¬ TetrahedronAvailable roots C τ n ω} ≤
      (Fintype.card Query : ℝ) * u +
        (Fintype.card Query : ℝ) * 6 * (Fintype.card G : ℝ) * v := by
  let totalBad : Set Ω :=
    ⋃ query, {ω | ¬ τ^12 * n^3 / 2 ≤ ((C ω query).card : ℝ)}
  let sectionBad : Set Ω :=
    ⋃ query, ⋃ i : Fin 6, ⋃ g : G,
      {ω | ¬ (((C ω query).filter (fun t ↦ tetrahedronDirection i t = g)).card : ℝ) ≤
        2 * τ^10 * n^2}
  have hsub : {ω | ¬ TetrahedronAvailable roots C τ n ω} ⊆ totalBad ∪ sectionBad := by
    intro ω hbad
    by_contra hnot
    have ht : ∀ query, τ^12 * n^3 / 2 ≤ ((C ω query).card : ℝ) := by
      intro query
      by_contra ht
      exact hnot (Or.inl (Set.mem_iUnion.mpr ⟨query, ht⟩))
    have hs : ∀ query i g,
        (((C ω query).filter (fun t ↦ tetrahedronDirection i t = g)).card : ℝ) ≤
          2 * τ^10 * n^2 := by
      intro query i g
      by_contra hs
      exact hnot (Or.inr (Set.mem_iUnion.mpr ⟨query,
        Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨g, hs⟩⟩⟩))
    apply hbad
    intro query
    exact tetrahedron_available_of_section_counts (roots query) (C ω query) τ n hτ hn
      (ht query) (hs query)
  have ht : μ.real totalBad ≤ (Fintype.card Query : ℝ) * u := by
    calc
      μ.real totalBad ≤ ∑ query, μ.real
          {ω | ¬ τ^12 * n^3 / 2 ≤ ((C ω query).card : ℝ)} :=
        measureReal_iUnion_fintype_le _
      _ ≤ ∑ _query : Query, u := Finset.sum_le_sum (fun query _ ↦ htotal query)
      _ = (Fintype.card Query : ℝ) * u := by simp
  have hs : μ.real sectionBad ≤
      (Fintype.card Query : ℝ) * 6 * (Fintype.card G : ℝ) * v := by
    calc
      μ.real sectionBad ≤ ∑ query, μ.real (⋃ i : Fin 6, ⋃ g : G,
          {ω | ¬ (((C ω query).filter
            (fun t ↦ tetrahedronDirection i t = g)).card : ℝ) ≤ 2 * τ^10 * n^2}) :=
        measureReal_iUnion_fintype_le _
      _ ≤ ∑ query, ∑ i : Fin 6, ∑ g : G,
          μ.real {ω | ¬ (((C ω query).filter
            (fun t ↦ tetrahedronDirection i t = g)).card : ℝ) ≤ 2 * τ^10 * n^2} := by
        apply Finset.sum_le_sum
        intro query _
        apply le_trans (measureReal_iUnion_fintype_le _)
        apply Finset.sum_le_sum
        intro i _
        exact measureReal_iUnion_fintype_le _
      _ ≤ ∑ _query : Query, ∑ _i : Fin 6, ∑ _g : G, v := by
        apply Finset.sum_le_sum
        intro query _
        apply Finset.sum_le_sum
        intro i _
        exact Finset.sum_le_sum (fun g _ ↦ hsection query i g)
      _ = (Fintype.card Query : ℝ) * 6 * (Fintype.card G : ℝ) * v := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
  exact (measureReal_mono hsub (measure_ne_top μ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add ht hs))

end Tetrahedron

end

end CorralFormalization.EndpointProof.Probability.QuadraticDeletion
