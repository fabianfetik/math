import CorralFormalization.EndpointProof.Factor.CycleCut

/-!
# Telescoping for actual path fragments

The exact closing call in the paper needs a checksum on the remaining
colours and the currently unused endpoints. The identities here use the
actual directed edge lists, not a hypothesized checksum for the remainder.
-/

open scoped BigOperators
namespace EndpointFactor.FragmentChecksum

variable {G : Type*} [AddCommGroup G]

/-- Empty fragments contribute zero; nonempty fragments use their real end. -/
def firstOrZero (p : List G) : G := p.head?.getD 0
def lastOrZero (p : List G) : G := p.getLast?.getD 0

theorem firstOrZero_mem {p : List G} (hne : p ≠ []) : firstOrZero p ∈ p := by
  unfold firstOrZero
  rw [List.head?_eq_some_head hne]
  exact List.head_mem hne

theorem lastOrZero_mem {p : List G} (hne : p ≠ []) : lastOrZero p ∈ p := by
  unfold lastOrZero
  rw [List.getLast?_eq_some_getLast hne]
  exact List.getLast_mem hne

omit [AddCommGroup G] in
/-- Choosing one actual vertex from each part of a disjoint path family
cannot produce repeated endpoints. -/
theorem selectedVertices_nodup (paths : List (List G)) (f : List G → G)
    (hflat : paths.flatten.Nodup) (hf : ∀ p ∈ paths, f p ∈ p) :
    (paths.map f).Nodup := by
  apply List.pairwise_map.mpr
  apply (List.nodup_flatten.mp hflat).2.imp_of_mem
  intro p q hp hq hdis heq
  have hpv := hf p hp
  have hqv := hf q hq
  exact (List.disjoint_left.mp hdis) hpv (by simpa [heq] using hqv)

theorem fragmentEndpoints_nodup (paths : List (List G))
    (hne : [] ∉ paths) (hflat : paths.flatten.Nodup) :
    (paths.map firstOrZero).Nodup ∧ (paths.map lastOrZero).Nodup := by
  constructor <;> apply selectedVertices_nodup paths _ hflat
  · intro p hp
    exact firstOrZero_mem (by intro he; subst p; exact hne hp)
  · intro p hp
    exact lastOrZero_mem (by intro he; subst p; exact hne hp)

theorem directedPath_sum (p : List G) :
    (edgeLabels (fun a b : G => b - a) p).sum = lastOrZero p - firstOrZero p := by
  induction p with
  | nil => simp [edgeLabels, firstOrZero, lastOrZero]
  | cons a rest ih =>
    cases rest with
    | nil => simp [edgeLabels, firstOrZero, lastOrZero]
    | cons b tail =>
      have htail := ih
      simp only [firstOrZero, List.head?_cons, Option.getD_some,
        lastOrZero, List.getLast?_cons_cons] at htail ⊢
      simp only [edgeLabels, List.sum_cons]
      rw [htail]
      abel

/-- Sum over a whole family of actual directed fragments, including empty
lists if supplied: intermediate vertices cancel in each fragment. -/
theorem fragmentFamily_sum (paths : List (List G)) :
    (paths.flatMap (edgeLabels (fun a b : G => b - a))).sum =
      (paths.map lastOrZero).sum - (paths.map firstOrZero).sum := by
  induction paths with
  | nil => simp
  | cons p paths ih =>
    simp only [List.flatMap_cons, List.sum_append, List.map_cons, List.sum_cons]
    rw [directedPath_sum, ih]
    abel

omit [AddCommGroup G] in
/-- Every nonempty fragment contributes one more vertex than real edges. -/
theorem fragmentFamily_edge_count {C : Type*} (edge : G → G → C)
    (paths : List (List G)) (hne : [] ∉ paths) :
    (paths.flatMap (edgeLabels edge)).length + paths.length = paths.flatten.length := by
  induction paths with
  | nil => simp
  | cons p paths ih =>
    have hpne : p ≠ [] := by
      intro hp
      subst p
      exact hne (by simp)
    have htne : [] ∉ paths := by
      intro hp
      exact hne (by simp [hp])
    have hp : (edgeLabels edge p).length + 1 = p.length := by
      rw [edgeLabels_length]
      have hpos : 0 < p.length := by cases p <;> simp_all
      omega
    have ht := ih htne
    simp only [List.flatMap_cons, List.length_append, List.length_cons, List.flatten_cons]
    omega

omit [AddCommGroup G] in
/-- If `j` consecutive ordinary transitions contribute `j*ℓ-h` edges and
their layers plus the leftover vertices contribute `(j+1)*ℓ+w` vertices,
the actual fragment family has exactly `ℓ+h+w` components. -/
theorem ordinaryFragment_count {C : Type*} (edge : G → G → C)
    (paths : List (List G)) (hne : [] ∉ paths) (j ℓ h w : ℕ)
    (hvertices : paths.flatten.length = (j+1)*ℓ+w)
    (hedges : (paths.flatMap (edgeLabels edge)).length + h = j*ℓ) :
    paths.length = ℓ+h+w := by
  have hcount := fragmentFamily_edge_count edge paths hne
  rw [hvertices, Nat.add_mul, Nat.one_mul] at hcount
  omega

/-- With actual duplicate-free vertex and colour inventories, the exact
cardinality identity is `used colours + fragments = used vertices`. -/
theorem fragmentFamily_inventory_card [DecidableEq G]
    (paths : List (List G)) (W used : Finset G)
    (hne : [] ∉ paths) (hflat : paths.flatten.Nodup)
    (hcolors : (paths.flatMap (edgeLabels (fun a b : G => b-a))).Nodup)
    (hW : paths.flatten.toFinset = W)
    (hused : (paths.flatMap (edgeLabels (fun a b : G => b-a))).toFinset = used) :
    used.card + paths.length = W.card := by
  have h := fragmentFamily_edge_count (fun a b : G => b-a) paths hne
  rw [← List.toFinset_card_of_nodup hcolors, hused,
    ← List.toFinset_card_of_nodup hflat, hW] at h
  exact h

/-- If the actual starts, ends and used colours have no repetitions, list
telescoping is exactly the identity between their physical finite sets. -/
theorem fragmentFamily_sum_finsets [DecidableEq G]
    (paths : List (List G)) (starts ends used : Finset G)
    (hstartnodup : (paths.map firstOrZero).Nodup)
    (hendnodup : (paths.map lastOrZero).Nodup)
    (hcolornodup : (paths.flatMap (edgeLabels (fun a b : G => b - a))).Nodup)
    (hstarts : (paths.map firstOrZero).toFinset = starts)
    (hends : (paths.map lastOrZero).toFinset = ends)
    (hused : (paths.flatMap (edgeLabels (fun a b : G => b - a))).toFinset = used) :
    (∑ c ∈ used, c) = (∑ y ∈ ends, y) - ∑ x ∈ starts, x := by
  have hs : (∑ x ∈ starts, x) = (paths.map firstOrZero).sum := by
    rw [← hstarts]
    simpa using (List.sum_toFinset (id : G → G) hstartnodup)
  have he : (∑ y ∈ ends, y) = (paths.map lastOrZero).sum := by
    rw [← hends]
    simpa using (List.sum_toFinset (id : G → G) hendnodup)
  have hu : (∑ c ∈ used, c) =
      (paths.flatMap (edgeLabels (fun a b : G => b - a))).sum := by
    rw [← hused]
    simpa using (List.sum_toFinset (id : G → G) hcolornodup)
  simpa only [hu, he, hs] using fragmentFamily_sum paths

/-- The exact-matching closing checksum follows from the original target checksum and
the actual disjoint colour/endpoint inventories of the fragment family. -/
theorem closing_checksum [DecidableEq G]
    (paths : List (List G)) (starts ends used D X Y H : Finset G)
    (hstartnodup : (paths.map firstOrZero).Nodup)
    (hendnodup : (paths.map lastOrZero).Nodup)
    (hcolornodup : (paths.flatMap (edgeLabels (fun a b : G => b - a))).Nodup)
    (hstarts : (paths.map firstOrZero).toFinset = starts)
    (hends : (paths.map lastOrZero).toFinset = ends)
    (hused : (paths.flatMap (edgeLabels (fun a b : G => b - a))).toFinset = used)
    (hX : X ⊆ starts) (hY : Y ⊆ ends) (hH : H ⊆ D)
    (husedD : used = D \ H)
    (htarget : (∑ d ∈ D, d) = (∑ y ∈ Y, y) - ∑ x ∈ X, x) :
    (∑ c ∈ H, c) = (∑ s ∈ starts \ X, s) - ∑ f ∈ ends \ Y, f := by
  have hfrag := fragmentFamily_sum_finsets paths starts ends used hstartnodup hendnodup
    hcolornodup hstarts hends hused
  have hd : (∑ c ∈ H, c) = (∑ d ∈ D, d) - ∑ c ∈ D \ H, c :=
    eq_sub_of_add_eq' (Finset.sum_sdiff (f := fun g : G => g) hH)
  have hs : (∑ s ∈ starts \ X, s) = (∑ s ∈ starts, s) - ∑ x ∈ X, x :=
    eq_sub_of_add_eq (Finset.sum_sdiff (f := fun g : G => g) hX)
  have he : (∑ f ∈ ends \ Y, f) = (∑ f ∈ ends, f) - ∑ y ∈ Y, y :=
    eq_sub_of_add_eq (Finset.sum_sdiff (f := fun g : G => g) hY)
  rw [hd, htarget, ← husedD, hfrag, hs, he]
  abel

end EndpointFactor.FragmentChecksum
