import CorralFormalization.EndpointProof.Router.Fibers
import Mathlib.Data.Fintype.BigOperators

/-!
# Fibres of affine forms in an arbitrary finite number of parameters

An actual coefficient `1`, `-1`, `2` or `-2` in one coordinate determines
that coordinate from all the others on a fixed-value fibre. Odd group order
makes doubling injective. No bound on a fibre is supplied as a hypothesis.
-/

namespace AbsorberInputs.GenericAffine

open Finset EndpointRouter
open scoped BigOperators

noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

def value {e : ℕ} (constant : G) (coefficient : Fin e → ℤ) (t : Fin e → G) : G :=
  constant + ∑ i, coefficient i • t i

abbrev freeIndex {e : ℕ} (k : Fin e) := ↥((Finset.univ : Finset (Fin e)).erase k)

def freeProjection {e : ℕ} (k : Fin e) (t : Fin e → G) : freeIndex k → G :=
  fun i => t i.1

/-- On a single fibre the free-coordinate projection is injective. -/
theorem fiber_projection_injective {e : ℕ} (hodd : Odd (Fintype.card G))
    (constant : G) (coefficient : Fin e → ℤ) (k : Fin e)
    (hk : Switch.SmallCoefficient (coefficient k)) (z : G) :
    Set.InjOn (freeProjection (G:=G) k)
      (↑((Finset.univ : Finset (Fin e → G)).filter
        (fun t => value constant coefficient t = z)) : Set (Fin e → G)) := by
  classical
  intro t ht u hu he
  have ht' := (Finset.mem_filter.mp ht).2
  have hu' := (Finset.mem_filter.mp hu).2
  have hv : value constant coefficient t = value constant coefficient u := ht'.trans hu'.symm
  have hfree : ∀ i : Fin e, i ≠ k → t i = u i := by
    intro i hi
    exact congrFun he ⟨i,Finset.mem_erase.mpr ⟨hi,Finset.mem_univ _⟩⟩
  have hsum : (∑ i ∈ (Finset.univ : Finset (Fin e)).erase k, coefficient i • t i) =
      ∑ i ∈ (Finset.univ : Finset (Fin e)).erase k, coefficient i • u i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hfree i (Finset.mem_erase.mp hi).1]
  have htk := Finset.sum_erase_add (Finset.univ : Finset (Fin e))
    (fun i => coefficient i • t i) (Finset.mem_univ k)
  have huk := Finset.sum_erase_add (Finset.univ : Finset (Fin e))
    (fun i => coefficient i • u i) (Finset.mem_univ k)
  unfold value at hv
  rw [← htk, ← huk, hsum] at hv
  have hkval : coefficient k • t k = coefficient k • u k :=
    add_left_cancel (add_left_cancel hv)
  have hkn := Affine.smallCoefficient_injective hodd (coefficient k) hk hkval
  funext i
  by_cases hi : i=k
  · subst i; exact hkn
  · exact hfree i hi

/-- An actual affine equation with a small invertible pivot has at most
`|G|^(e-1)` solutions, uniformly over its target and all coefficients. -/
theorem fiber_card_le {e : ℕ} (hodd : Odd (Fintype.card G))
    (constant : G) (coefficient : Fin e → ℤ) (k : Fin e)
    (hk : Switch.SmallCoefficient (coefficient k)) (z : G) :
    ((Finset.univ : Finset (Fin e → G)).filter
      (fun t => value constant coefficient t = z)).card ≤ (Fintype.card G)^(e-1) := by
  classical
  have hc := Finset.card_le_card_of_injOn
    (s := (Finset.univ : Finset (Fin e → G)).filter
      (fun t => value constant coefficient t = z))
    (t := (Finset.univ : Finset (freeIndex k → G))) (freeProjection k)
    (by intro t ht; simp) (fiber_projection_injective hodd constant coefficient k hk z)
  have hcard : Fintype.card (freeIndex k) = e-1 := by
    simp [freeIndex]
  simpa [Fintype.card_fun, hcard] using hc

omit [Fintype G] [DecidableEq G] in
theorem value_sub {e : ℕ} (a b : G) (p q : Fin e → ℤ) (t : Fin e → G) :
    value a p t - value b q t = value (a-b) (fun k => p k-q k) t := by
  have hs : (∑ i, (p i - q i) • t i) =
      (∑ i, p i • t i) - ∑ i, q i • t i := by
    simp only [sub_eq_add_neg, add_zsmul, neg_zsmul,
      Finset.sum_add_distrib, Finset.sum_neg_distrib]
  change (a + ∑ i, p i • t i) - (b + ∑ i, q i • t i) =
    (a-b) + ∑ i, (p i-q i) • t i
  rw [hs]
  abel

/-- A genuine affine equality is bounded by the invertible coefficient
in the difference of the two actual forms. -/
theorem equation_card_le {e : ℕ} (hodd : Odd (Fintype.card G))
    (a b : G) (p q : Fin e → ℤ) (k : Fin e)
    (hk : Switch.SmallCoefficient (p k-q k)) :
    ((Finset.univ : Finset (Fin e → G)).filter
      (fun t => value a p t = value b q t)).card ≤ (Fintype.card G)^(e-1) := by
  have heq : ((Finset.univ : Finset (Fin e → G)).filter
      (fun t => value a p t = value b q t)) =
      Finset.univ.filter (fun t => value (a-b) (fun k => p k-q k) t = 0) := by
    ext t
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,← value_sub,sub_eq_zero]
  rw [heq]
  exact fiber_card_le hodd _ _ k hk 0

private theorem biUnion_card_le_uniform {ι α : Type*} [DecidableEq α]
    (s : Finset ι) (f : ι → Finset α) (M : ℕ)
    (hf : ∀ i ∈ s, (f i).card ≤ M) :
    (s.biUnion f).card ≤ s.card * M := by
  classical
  calc
    _ ≤ ∑ i ∈ s, (f i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ s, M := Finset.sum_le_sum hf
    _ = s.card * M := by simp

/-- A finite list of actual affine collision equations. Equations already
excluded by root hypotheses need not be included in this list. -/
def collisionAssignments {e c : ℕ} (a : Fin c → G)
    (p : Fin c → Fin e → ℤ) (z : Fin c → G) : Finset (Fin e → G) :=
  Finset.univ.biUnion fun j =>
    Finset.univ.filter fun t => value (a j) (p j) t = z j

theorem collisionAssignments_card_le {e c : ℕ}
    (hodd : Odd (Fintype.card G)) (a : Fin c → G)
    (p : Fin c → Fin e → ℤ) (z : Fin c → G)
    (k : Fin c → Fin e) (hk : ∀ j, Switch.SmallCoefficient (p j (k j))) :
    (collisionAssignments a p z).card ≤ c * (Fintype.card G)^(e-1) := by
  classical
  unfold collisionAssignments
  simpa using biUnion_card_le_uniform (Finset.univ : Finset (Fin c))
    (fun j => (Finset.univ : Finset (Fin e → G)).filter
      (fun t => value (a j) (p j) t = z j))
    ((Fintype.card G)^(e-1))
    (by intro j _; exact fiber_card_le hodd (a j) (p j) (k j) (hk j) (z j))

/-- The quantitative first assertion of the packed availability lemma: the assignments avoiding
all listed collision equations are counted without assuming a packing. -/
theorem validAssignments_card_lower {e c : ℕ}
    (hodd : Odd (Fintype.card G)) (a : Fin c → G)
    (p : Fin c → Fin e → ℤ) (z : Fin c → G)
    (k : Fin c → Fin e) (hk : ∀ j, Switch.SmallCoefficient (p j (k j))) :
    (Fintype.card G)^e - c * (Fintype.card G)^(e-1) ≤
      ((Finset.univ : Finset (Fin e → G)) \ collisionAssignments a p z).card := by
  classical
  have hbad := collisionAssignments_card_le hodd a p z k hk
  have hcount := Finset.card_sdiff_add_card_inter
    (Finset.univ : Finset (Fin e → G)) (collisionAssignments a p z)
  have hint : ((Finset.univ : Finset (Fin e → G)) ∩
      collisionAssignments a p z).card ≤ (collisionAssignments a p z).card :=
    Finset.card_le_card (Finset.inter_subset_right)
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin] at hcount
  omega

def signedClosure (B : Finset G) : Finset G := B ∪ B.image (-·)

omit [Fintype G] in
theorem signedClosure_card_le (B : Finset G) : (signedClosure B).card ≤ 2*B.card := by
  calc
    _ ≤ B.card + (B.image (-·)).card := Finset.card_union_le _ _
    _ ≤ B.card + B.card := Nat.add_le_add_left Finset.card_image_le _
    _ = 2*B.card := by omega

/-- Assignments where one of `m` actual forms hits either sign of an
old representative. The original root query fixes these data before any
categorical labels are sampled. -/
def oldOrbitAssignments {e m : ℕ} (a : Fin m → G)
    (p : Fin m → Fin e → ℤ) (B : Finset G) : Finset (Fin e → G) :=
  Finset.univ.biUnion fun j => (signedClosure B).biUnion fun z =>
    Finset.univ.filter fun t => value (a j) (p j) t = z

theorem oldOrbitAssignments_card_le {e m : ℕ}
    (hodd : Odd (Fintype.card G)) (a : Fin m → G)
    (p : Fin m → Fin e → ℤ) (B : Finset G)
    (k : Fin m → Fin e) (hk : ∀ j, Switch.SmallCoefficient (p j (k j))) :
    (oldOrbitAssignments a p B).card ≤
      m * (2*B.card) * (Fintype.card G)^(e-1) := by
  classical
  let M := (Fintype.card G)^(e-1)
  have hinner (j : Fin m) :
      ((signedClosure B).biUnion fun z =>
        (Finset.univ : Finset (Fin e → G)).filter
          (fun t => value (a j) (p j) t = z)).card ≤ 2*B.card*M := by
    calc
      _ ≤ (signedClosure B).card*M := biUnion_card_le_uniform _ _ M
        (by intro z _; exact fiber_card_le hodd (a j) (p j) (k j) (hk j) z)
      _ ≤ (2*B.card)*M := Nat.mul_le_mul_right M (signedClosure_card_le B)
  unfold oldOrbitAssignments
  calc
    _ ≤ (Finset.univ : Finset (Fin m)).card * (2*B.card*M) :=
      biUnion_card_le_uniform _ _ _ (by intro j _; exact hinner j)
    _ = m*(2*B.card)*M := by simp [Nat.mul_assoc]

/-- After `i` prior gadgets, each with at most `m` representatives, the
additional exclusions are at most `2*m^2*i*|G|^(e-1)`. -/
theorem packedOldOrbitAssignments_card_le {e m : ℕ}
    (hodd : Odd (Fintype.card G)) (a : Fin m → G)
    (p : Fin m → Fin e → ℤ) (B : Finset G) (i : ℕ)
    (hB : B.card ≤ m*i) (k : Fin m → Fin e)
    (hk : ∀ j, Switch.SmallCoefficient (p j (k j))) :
    (oldOrbitAssignments a p B).card ≤
      (2*m*m*i) * (Fintype.card G)^(e-1) := by
  calc
    _ ≤ m * (2*B.card) * (Fintype.card G)^(e-1) :=
      oldOrbitAssignments_card_le hodd a p B k hk
    _ ≤ m * (2*(m*i)) * (Fintype.card G)^(e-1) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left m (Nat.mul_le_mul_left 2 hB))
    _ = (2*m*m*i) * (Fintype.card G)^(e-1) := by ring

/-- Whenever the explicit sum of the collision and old-orbit bounds is
strictly smaller than the number of assignments, an actual fresh assignment
exists. This is the selection step behind the greedy packing. -/
theorem fresh_assignment_exists {e c m : ℕ}
    (hodd : Odd (Fintype.card G))
    (ca : Fin c → G) (cp : Fin c → Fin e → ℤ) (cz : Fin c → G)
    (ck : Fin c → Fin e) (hck : ∀ j, Switch.SmallCoefficient (cp j (ck j)))
    (a : Fin m → G) (p : Fin m → Fin e → ℤ) (B : Finset G)
    (k : Fin m → Fin e) (hk : ∀ j, Switch.SmallCoefficient (p j (k j)))
    (hsize : c * (Fintype.card G)^(e-1) +
      m * (2*B.card) * (Fintype.card G)^(e-1) < (Fintype.card G)^e) :
    ∃ t : Fin e → G,
      t ∉ collisionAssignments ca cp cz ∧ t ∉ oldOrbitAssignments a p B := by
  classical
  have hc : (collisionAssignments ca cp cz ∪ oldOrbitAssignments a p B).card <
      (Finset.univ : Finset (Fin e → G)).card := by
    calc
      _ ≤ (collisionAssignments ca cp cz).card + (oldOrbitAssignments a p B).card :=
        Finset.card_union_le _ _
      _ ≤ c * (Fintype.card G)^(e-1) +
          m * (2*B.card) * (Fintype.card G)^(e-1) :=
        Nat.add_le_add (collisionAssignments_card_le hodd ca cp cz ck hck)
          (oldOrbitAssignments_card_le hodd a p B k hk)
      _ < (Finset.univ : Finset (Fin e → G)).card := by
        simpa [Fintype.card_fun] using hsize
  obtain ⟨t, _, ht⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  exact ⟨t, (fun h => ht (Finset.mem_union_left _ h)),
    (fun h => ht (Finset.mem_union_right _ h))⟩

def representatives {e m : ℕ} (a : Fin m → G) (p : Fin m → Fin e → ℤ)
    (t : Fin e → G) : Finset G :=
  Finset.univ.image fun j => value (a j) (p j) t

omit [Fintype G] in
theorem representatives_card_le {e m : ℕ} (a : Fin m → G)
    (p : Fin m → Fin e → ℤ) (t : Fin e → G) :
    (representatives a p t).card ≤ m := by
  simpa [representatives] using
    (Finset.card_image_le :
      ((Finset.univ : Finset (Fin m)).image (fun j => value (a j) (p j) t)).card ≤
        (Finset.univ : Finset (Fin m)).card)

omit [Fintype G] in
theorem mem_signedClosure_neg (B : Finset G) (z : G) :
    -z ∈ signedClosure B ↔ z ∈ signedClosure B := by
  simp only [signedClosure, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (hz | ⟨w, hw, hwz⟩)
    · exact Or.inr ⟨-z, hz, neg_neg z⟩
    · have : w = z := neg_injective hwz
      subst w
      exact Or.inl hw
  · rintro (hz | ⟨w, hw, hwz⟩)
    · exact Or.inr ⟨z, hz, rfl⟩
    · have : w = -z := by simpa using congrArg (fun x : G => -x) hwz
      subst w
      exact Or.inl hw

omit [Fintype G] in
theorem signedClosure_mono {A B : Finset G} (h : A ⊆ B) :
    signedClosure A ⊆ signedClosure B := by
  intro z hz
  rcases Finset.mem_union.mp hz with hz | hz
  · exact Finset.mem_union_left _ (h hz)
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v, h hv, rfl⟩)

omit [Fintype G] in
theorem signedClosure_disjoint {A B : Finset G}
    (h : Disjoint A (signedClosure B)) :
    Disjoint (signedClosure A) (signedClosure B) := by
  apply Finset.disjoint_left.mpr
  intro z hz hzB
  rcases Finset.mem_union.mp hz with hz | hz
  · exact Finset.disjoint_left.mp h hz hzB
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.disjoint_left.mp h hv ((mem_signedClosure_neg B v).mp hzB)

theorem fresh_representatives_disjoint {e m : ℕ}
    (a : Fin m → G) (p : Fin m → Fin e → ℤ) (B : Finset G) (t : Fin e → G)
    (ht : t ∉ oldOrbitAssignments a p B) :
    Disjoint (representatives a p t) (signedClosure B) := by
  classical
  apply Finset.disjoint_left.mpr
  intro z hz hzB
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hz
  apply ht
  apply Finset.mem_biUnion.mpr
  refine ⟨j, Finset.mem_univ _, ?_⟩
  apply Finset.mem_biUnion.mpr
  exact ⟨_, hzB, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩

/-- A deterministic packing of actual affine assignments. Its sets of
numerical representatives are pairwise disjoint even after both signs are
included. The only size condition is the explicit union-bound inequality. -/
theorem exists_affine_orbit_packing {e c m : ℕ}
    (hodd : Odd (Fintype.card G)) (hm : 0 < m)
    (ca : Fin c → G) (cp : Fin c → Fin e → ℤ) (cz : Fin c → G)
    (ck : Fin c → Fin e) (hck : ∀ j, Switch.SmallCoefficient (cp j (ck j)))
    (a : Fin m → G) (p : Fin m → Fin e → ℤ)
    (k : Fin m → Fin e) (hk : ∀ j, Switch.SmallCoefficient (p j (k j)))
    (M : ℕ) (hsize : c * (Fintype.card G)^(e-1) +
      (2*m*m*M) * (Fintype.card G)^(e-1) < (Fintype.card G)^e) :
    ∃ U : Finset (Fin e → G), U.card = M ∧
      (∀ t ∈ U, t ∉ collisionAssignments ca cp cz) ∧
      (U : Set (Fin e → G)).Pairwise
        (fun t u => Disjoint (signedClosure (representatives a p t))
          (signedClosure (representatives a p u))) := by
  classical
  induction M with
  | zero => exact ⟨∅, rfl, by simp, by simp⟩
  | succ M ih =>
    have hsizeM : c * (Fintype.card G)^(e-1) +
        (2*m*m*M) * (Fintype.card G)^(e-1) < (Fintype.card G)^e := by
      have hmM : (2*m*m*M) * (Fintype.card G)^(e-1) ≤
          (2*m*m*(M+1)) * (Fintype.card G)^(e-1) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.le_succ M))
      exact lt_of_le_of_lt (Nat.add_le_add_left hmM _) hsize
    obtain ⟨U, hU, hvalid, hpair⟩ := ih hsizeM
    let B := U.biUnion (representatives a p)
    have hB : B.card ≤ m*M := by
      calc
        _ ≤ U.card*m := biUnion_card_le_uniform _ _ _
          (by intro t _; exact representatives_card_le a p t)
        _ = m*M := by rw [hU]; exact Nat.mul_comm _ _
    have hcost : m*(2*B.card)*(Fintype.card G)^(e-1) ≤
        (2*m*m*(M+1))*(Fintype.card G)^(e-1) := by
      calc
        _ ≤ m*(2*(m*M))*(Fintype.card G)^(e-1) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left m (Nat.mul_le_mul_left 2 hB))
        _ ≤ m*(2*(m*(M+1)))*(Fintype.card G)^(e-1) := by
          gcongr
          omega
        _ = (2*m*m*(M+1))*(Fintype.card G)^(e-1) := by ring
    obtain ⟨t, htvalid, htfresh⟩ := fresh_assignment_exists hodd ca cp cz ck hck
      a p B k hk (lt_of_le_of_lt (Nat.add_le_add_left hcost _) hsize)
    have htB := fresh_representatives_disjoint a p B t htfresh
    have htU : t ∉ U := by
      intro htU
      let j : Fin m := ⟨0, hm⟩
      have hj : value (a j) (p j) t ∈ representatives a p t :=
        Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
      have hjB : value (a j) (p j) t ∈ B :=
        Finset.mem_biUnion.mpr ⟨t, htU, hj⟩
      exact Finset.disjoint_left.mp htB hj (Finset.mem_union_left _ hjB)
    have hdisj (u : Fin e → G) (hu : u ∈ U) :
        Disjoint (signedClosure (representatives a p t))
          (signedClosure (representatives a p u)) := by
      apply Finset.disjoint_of_subset_right _ (signedClosure_disjoint htB)
      apply signedClosure_mono
      intro z hz
      exact Finset.mem_biUnion.mpr ⟨u, hu, hz⟩
    refine ⟨insert t U, by simp [htU, hU], ?_, ?_⟩
    · intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact htvalid
      · exact hvalid u hu
    · intro u hu v hv huv
      rcases Finset.mem_insert.mp hu with huEq | huU
      · subst u
        rcases Finset.mem_insert.mp hv with hvEq | hvU
        · subst v
          exact False.elim (huv rfl)
        · exact hdisj v hvU
      · rcases Finset.mem_insert.mp hv with hvEq | hvU
        · subst v
          exact (hdisj u huU).symm
        · exact hpair huU hvU huv

/-- For fixed numbers of collision equations and coordinates, the packing
has linear size. The denominator is an explicit safe choice. -/
theorem exists_linear_affine_orbit_packing {e c m : ℕ}
    (hodd : Odd (Fintype.card G)) (he : 1 ≤ e) (hm : 0 < m)
    (hn : 2*c < Fintype.card G)
    (ca : Fin c → G) (cp : Fin c → Fin e → ℤ) (cz : Fin c → G)
    (ck : Fin c → Fin e) (hck : ∀ j, Switch.SmallCoefficient (cp j (ck j)))
    (a : Fin m → G) (p : Fin m → Fin e → ℤ)
    (k : Fin m → Fin e) (hk : ∀ j, Switch.SmallCoefficient (p j (k j))) :
    ∃ U : Finset (Fin e → G), U.card = (Fintype.card G)/(4*m*m) ∧
      (∀ t ∈ U, t ∉ collisionAssignments ca cp cz) ∧
      (U : Set (Fin e → G)).Pairwise
        (fun t u => Disjoint (signedClosure (representatives a p t))
          (signedClosure (representatives a p u))) := by
  let n := Fintype.card G
  let M := n/(4*m*m)
  have hdiv : (4*m*m)*M ≤ n := Nat.mul_div_le n (4*m*m)
  have hhalf : 2*(2*m*m*M) ≤ n := by
    calc
      _ = (4*m*m)*M := by ring
      _ ≤ n := hdiv
  have hsmall : c + 2*m*m*M < n := by
    change 2*c < n at hn
    omega
  have hp : 0 < n^(e-1) := pow_pos Fintype.card_pos _
  have hpow : n^e = n^(e-1)*n := by
    conv_lhs => rw [← Nat.sub_add_cancel he]
    rw [pow_succ]
  apply exists_affine_orbit_packing hodd hm ca cp cz ck hck a p k hk M
  rw [hpow]
  simpa only [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    Nat.mul_lt_mul_of_pos_left hsmall hp

end
end AbsorberInputs.GenericAffine
