import CorralFormalization.Results.DensityObstruction.Inventories

namespace CorralFormalization.Results.DensityObstruction

open scoped BigOperators
open CorralFormalization.LatinCompletion.TerraceCompletion

def height (a b : ℕ) : ℕ := 4*a+1+3*b

instance family_neZero (a b : ℕ) : NeZero (3 * height a b) :=
  ⟨by dsimp [height]; omega⟩

def start {h : ℕ} [NeZero (3*h)] (T : Finset (ZMod (3*h))) (y : ZMod (3*h)) :
    ZMod (3*h) := y - ∑ d ∈ colors T, d

theorem family_order_odd (a b : ℕ) (hb : Even b) : Odd (3 * height a b) := by
  obtain ⟨k, rfl⟩ := hb
  refine ⟨6*a+1+9*k, ?_⟩
  dsimp [height]
  omega

theorem family_colors_sum_residue (a b : ℕ)
    (T : Finset (ZMod (3 * height a b)))
    (hT : T ⊆ residueClass (height a b) 2) (hcard : T.card = a) :
    residue (height a b) (∑ d ∈ colors T, d) = 1 := by
  rw [colors_sum_residue T hT hcard]
  have h3 : (3 : ZMod 3) = 0 := by decide
  have h6 : (6 : ZMod 3) = 0 := by decide
  change ((4*a+1+3*b : ℕ) : ZMod 3) + 2*a = 1
  push_cast
  calc
    _ = (6 : ZMod 3) * a + 1 + 3*b := by ring
    _ = 1 := by rw [h6, h3]; ring

theorem family_start_residue (a b : ℕ)
    (T : Finset (ZMod (3 * height a b)))
    (hT : T ⊆ residueClass (height a b) 2) (hcard : T.card = a)
    (y : ZMod (3 * height a b)) (hy : y ∈ T) :
    residue (height a b) (start T y) = 1 := by
  rw [start, map_sub, family_colors_sum_residue a b T hT hcard,
    (mem_residueClass 2 y).mp (hT hy)]
  decide

theorem family_start_mem (a b : ℕ)
    (T : Finset (ZMod (3 * height a b)))
    (hT : T ⊆ residueClass (height a b) 2) (hcard : T.card = a)
    (y : ZMod (3 * height a b)) (hy : y ∈ T) :
    start T y ∈ vertices T := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact (mem_residueClass 1 _).mpr (family_start_residue a b T hT hcard y hy)

theorem family_start_ne_end (a b : ℕ)
    (T : Finset (ZMod (3 * height a b)))
    (hT : T ⊆ residueClass (height a b) 2) (hcard : T.card = a)
    (y : ZMod (3 * height a b)) (hy : y ∈ T) :
    start T y ≠ y := by
  intro he
  have h1 := family_start_residue a b T hT hcard y hy
  have h2 := (mem_residueClass 2 y).mp (hT hy)
  rw [he, h2] at h1
  exact (by decide : (2 : ZMod 3) ≠ 1) h1

theorem family_endpoint_sum {h : ℕ} [NeZero (3*h)]
    (T : Finset (ZMod (3*h))) (y : ZMod (3*h)) :
    (∑ d ∈ colors T, d) = y - start T y := by
  dsimp [start]
  abel

theorem family_no_endpointPath (a b : ℕ)
    (T : Finset (ZMod (3 * height a b)))
    (hT : T ⊆ residueClass (height a b) 2) (hcard : T.card = a)
    (y : ZMod (3 * height a b)) (hy : y ∈ T) :
    ¬ EndpointPathClaim (vertices T) (colors T) (start T y) y := by
  intro hp
  have hb := endpointPath_flow_bound (vertices T) (colors T) (start T y) y
    (residue (height a b)).toAddMonoidHom
    (family_start_residue a b T hT hcard y hy)
    ((mem_residueClass 2 y).mp (hT hy)) (zero_not_mem_colors T) hp
  change ((Finset.filter (fun d => residue (height a b) d = 1) (colors T)).card : ℤ) -
      (Finset.filter (fun d => residue (height a b) d = 2) (colors T)).card ≤
      3 * (Finset.filter (fun z => residue (height a b) z = 2) (vertices T)).card - 2 at hb
  rw [colors_filter_one T hT, colors_filter_two T hT, vertices_filter_two T hT,
    residueClass_card, hcard] at hb
  dsimp [height] at hb
  omega

/-- The printed finite family, with arbitrary `T` of the prescribed size and
arbitrary endpoint `y ∈ T`, in the pre-existing exact endpoint-path model. -/
theorem finite_density_obstruction (a b : ℕ) (_ha : 1 ≤ a) (hb : Even b)
    (T : Finset (ZMod (3 * height a b)))
    (hT : T ⊆ residueClass (height a b) 2) (hcard : T.card = a)
    (y : ZMod (3 * height a b)) (hy : y ∈ T) :
    Odd (3 * height a b) ∧
    (vertices T).card = 2 * height a b + a ∧
    (colors T).card + 1 = (vertices T).card ∧
    (colors T).card = 2 * height a b + a - 1 ∧
    residue (height a b) (∑ d ∈ colors T, d) = 1 ∧
    residue (height a b) (start T y) = 1 ∧
    start T y ∈ vertices T ∧ y ∈ vertices T ∧ start T y ≠ y ∧
    0 ∉ colors T ∧
    (∑ d ∈ colors T, d) = y - start T y ∧
    ¬ EndpointPathClaim (vertices T) (colors T) (start T y) y := by
  have hvc := vertices_card T hT hcard
  have hdc := colors_card_add_one T
  refine ⟨family_order_odd a b hb, hvc, hdc, ?_,
    family_colors_sum_residue a b T hT hcard,
    family_start_residue a b T hT hcard y hy,
    family_start_mem a b T hT hcard y hy, Finset.mem_union_right _ hy,
    family_start_ne_end a b T hT hcard y hy, zero_not_mem_colors T,
    family_endpoint_sum T y, family_no_endpointPath a b T hT hcard y hy⟩
  omega

end CorralFormalization.Results.DensityObstruction
