import CorralFormalization.EndpointProof.Selector.Assembly.FixedCardinality.LocalSupply

open scoped Classical BigOperators

namespace EndpointSelector.FixedCardinality

open EndpointFlow.AbelianTransport

noncomputable section

variable {G : Type*} [AddCommGroup G]

theorem support_mono {A B : Finset (Vertex G)} (h : A ⊆ B) :
    support A ⊆ support B := by
  exact Finset.union_subset_union (Finset.image_mono Prod.snd h)
    (Finset.image_mono (fun v : Vertex G => -v.2) h)

theorem support_union (A B : Finset (Vertex G)) :
    support (A ∪ B) = support A ∪ support B := by
  ext x
  simp only [support, Finset.image_union, Finset.mem_union]
  aesop

theorem support_biUnion {ι : Type*} (D : Finset ι) (I : ι → Finset (Vertex G)) :
    support (D.biUnion I) = D.biUnion (fun i => support (I i)) := by
  ext x
  simp only [support, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion]
  aesop

theorem disjoint_of_support {A B : Finset (Vertex G)}
    (h : Disjoint (support A) (support B)) : Disjoint A B := by
  apply Finset.disjoint_left.mpr
  intro v hvA hvB
  apply Finset.disjoint_left.mp h
  · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v, hvA, rfl⟩)
  · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v, hvB, rfl⟩)

/-- A legal inverse pair occupies at most two numerical coordinates. -/
theorem legalPair_support {part : Fin 3} {T : Finset (Vertex G)}
    (hT : LegalPair part T) :
    ∃ a : G, a ≠ 0 ∧ support T = {a, -a} := by
  obtain ⟨a, ha, rfl⟩ := hT
  refine ⟨a, ha, ?_⟩
  ext x
  simp [support, or_comm]

theorem legalPair_support_card_le {part : Fin 3} {T : Finset (Vertex G)}
    (hT : LegalPair part T) : (support T).card ≤ 2 := by
  obtain ⟨a, _, h⟩ := legalPair_support hT
  rw [h]
  exact (Finset.card_insert_le _ _).trans (by simp)

theorem legalPair_card_le {part : Fin 3} {T : Finset (Vertex G)}
    (hT : LegalPair part T) : T.card ≤ 2 := by
  obtain ⟨a, _, rfl⟩ := hT
  exact (Finset.card_insert_le _ _).trans (by simp)

theorem legalPair_support_nonempty {part : Fin 3} {T : Finset (Vertex G)}
    (hT : LegalPair part T) : (support T).Nonempty := by
  obtain ⟨a, _, h⟩ := legalPair_support hT
  rw [h]
  exact ⟨a, Finset.mem_insert_self _ _⟩

/-- Two different inverse pairs in one tagged part have disjoint numerical
inverse supports, even without an odd-order assumption. -/
theorem legalPair_support_disjoint {part : Fin 3} {T T' : Finset (Vertex G)}
    (hT : LegalPair part T) (hT' : LegalPair part T') (hne : T ≠ T') :
    Disjoint (support T) (support T') := by
  obtain ⟨a, ha, rfl⟩ := hT
  obtain ⟨b, hb, rfl⟩ := hT'
  apply Finset.disjoint_left.mpr
  intro x hxA hxB
  have hxA' : x = a ∨ x = -a := by simpa [support, or_comm] using hxA
  have hxB' : x = b ∨ x = -b := by simpa [support, or_comm] using hxB
  have hab : a = b ∨ a = -b := by
    rcases hxA' with ha' | ha' <;> rcases hxB' with hb' | hb'
    · exact Or.inl (ha'.symm.trans hb')
    · exact Or.inr (ha'.symm.trans hb')
    · apply Or.inr
      have h := congrArg Neg.neg (ha'.symm.trans hb')
      simpa using h
    · apply Or.inl
      have h := congrArg Neg.neg (ha'.symm.trans hb')
      simpa using h
  rcases hab with h | h
  · subst a
    exact hne rfl
  · subst a
    apply hne
    simpa only [neg_neg] using Finset.pair_comm (part, -b) (part, b)

/-- Greedy helper-pair supply on the same local event. The union of every
chosen pair's numerical inverse support avoids F. -/
theorem fresh_pair_family
    {P : Vertex G → Prop} {budget arity : ℕ}
    (hP : PairReservoir P) (hlocal : LocalSupply P budget arity)
    (harity : 1 ≤ arity) (a : G) (ha : a ≠ 0)
    (part : Fin 3) (F : Finset G) (k : ℕ)
    (hbudget : F.card + 2 * k ≤ budget) :
    ∃ H : Finset (Finset (Vertex G)), H.card = k ∧
      (∀ T ∈ H, LegalPair part T ∧ ∀ v ∈ T, P v) ∧
      Disjoint (support (H.biUnion id)) F ∧
      (∀ T ∈ H, ∀ T' ∈ H, T ≠ T' →
        Disjoint (support T) (support T')) := by
  classical
  induction k with
  | zero =>
      exact ⟨∅, by simp, by simp, by simp [support], by simp⟩
  | succ k ih =>
      have hbudget' : F.card + 2 * k ≤ budget := by omega
      obtain ⟨H, hcard, hlegal, havoid, hpair⟩ := ih hbudget'
      let F' := F ∪ support (H.biUnion id)
      have hsupport : (support (H.biUnion id)).card ≤ 2 * k := by
        rw [support_biUnion]
        calc
          _ ≤ ∑ T ∈ H, (support T).card := Finset.card_biUnion_le
          _ ≤ ∑ _T ∈ H, 2 := Finset.sum_le_sum (fun T hT =>
            legalPair_support_card_le (hlegal T hT).1)
          _ = 2 * k := by simp [hcard, Nat.mul_comm]
      have hF' : F'.card ≤ budget := by
        have hbound := Finset.card_union_le F (support (H.biUnion id))
        dsimp [F']
        omega
      obtain ⟨T, hTlegal, hTP, hTavoid⟩ :=
        fresh_pair_of_localSupply hP hlocal harity a ha part F' hF'
      have hTnew : T ∉ H := by
        intro hTH
        obtain ⟨x, hx⟩ := legalPair_support_nonempty hTlegal
        have hxF : x ∈ F' := Finset.mem_union_right _
          (by rw [support_biUnion]; exact Finset.mem_biUnion.mpr ⟨T, hTH, hx⟩)
        exact Finset.disjoint_left.mp hTavoid hx hxF
      refine ⟨insert T H, ?_, ?_, ?_, ?_⟩
      · simp [hTnew, hcard]
      · intro T' hT'
        rcases Finset.mem_insert.mp hT' with h | h
        · subst T'
          exact ⟨hTlegal, hTP⟩
        · exact hlegal T' h
      · rw [Finset.biUnion_insert, support_union]
        apply Finset.disjoint_union_left.mpr
        exact ⟨hTavoid.mono_right Finset.subset_union_left, havoid⟩
      · intro T₁ hT₁ T₂ hT₂ hne
        rcases Finset.mem_insert.mp hT₁ with h₁ | h₁
        · subst T₁
          have h₂ : T₂ ∈ H := by
            rcases Finset.mem_insert.mp hT₂ with he | he
            · exact (hne he.symm).elim
            · exact he
          apply hTavoid.mono_right
          intro x hx
          exact Finset.mem_union_right _ (by
            rw [support_biUnion]
            exact Finset.mem_biUnion.mpr ⟨T₂, h₂, hx⟩)
        · rcases Finset.mem_insert.mp hT₂ with h₂ | h₂
          · subst T₂
            apply (hTavoid.mono_right ?_).symm
            intro x hx
            exact Finset.mem_union_right _ (by
              rw [support_biUnion]
              exact Finset.mem_biUnion.mpr ⟨T₁, h₁, hx⟩)
          · exact hpair T₁ h₁ T₂ h₂ hne

/-- The physical pool used to label the fixed and variable graph ports. -/
structure PortPool (P : Vertex G → Prop) (Y : Finset (Finset (Vertex G)))
    (s : ℕ) (part : Fin 3) (U : Finset G) where
  fixed : Finset (Finset (Vertex G))
  varying : Finset (Finset (Vertex G))
  fixed_card : fixed.card = 2 * s
  varying_card : varying.card = 2 * s
  includes_targets : Y ⊆ varying
  disjoint : Disjoint fixed varying
  fixed_inside : ∀ T ∈ fixed, ∀ v ∈ T, P v
  fixed_avoids : Disjoint (support (fixed.biUnion id)) U
  legal : ∀ T ∈ fixed ∪ varying, LegalPair part T
  support_card : (support ((fixed ∪ varying).biUnion id)).card ≤ 8 * s

/-- A purely combinatorial selection graph: fixed ports are left injections,
variable ports are right injections, and every prescribed s-subset of the
variable ports can be routed together with all fixed ports. -/
structure SelectionGraph (s degree : ℕ) where
  neighbors : Fin (3 * s) → Finset (Sum (Fin (2 * s)) (Fin (2 * s)))
  nonempty : ∀ d, (neighbors d).Nonempty
  degree_le : ∀ d, (neighbors d).card ≤ degree
  route : ∀ W₀ : Finset (Fin (2 * s)), W₀.card = s →
    ∃ f : Fin (3 * s) → Sum (Fin (2 * s)) (Fin (2 * s)),
      Function.Injective f ∧ (∀ d, f d ∈ neighbors d) ∧
      Finset.univ.image f =
        (Finset.univ.image Sum.inl) ∪ W₀.image Sum.inr

/-- The complete graph supplies a nonvacuous finite check of the routing
contract for every positive s, but has degree 4s rather than a uniform
constant. It does not establish the degree-eight or degree-sixteen graph. -/
theorem complete_selectionGraph {s : ℕ} (hs : 1 ≤ s) :
    Nonempty (SelectionGraph s (4 * s)) := by
  classical
  refine ⟨⟨fun _ => Finset.univ, ?_, ?_, ?_⟩⟩
  · intro _
    exact ⟨Sum.inl ⟨0, by omega⟩, Finset.mem_univ _⟩
  · intro _
    simp only [Finset.card_univ, Fintype.card_sum, Fintype.card_fin]
    omega
  · intro W₀ hW
    let F : Finset (Sum (Fin (2 * s)) (Fin (2 * s))) :=
      Finset.univ.image Sum.inl
    let W : Finset (Sum (Fin (2 * s)) (Fin (2 * s))) := W₀.image Sum.inr
    have hFW : Disjoint F W := by
      apply Finset.disjoint_left.mpr
      intro x hxF hxW
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hxF
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hxW
      cases hj
    have hF : F.card = 2 * s := by
      dsimp [F]
      rw [Finset.card_image_of_injective _ Sum.inl_injective]
      simp
    have hW' : W.card = s := by
      dsimp [W]
      rw [Finset.card_image_of_injective _ Sum.inr_injective]
      exact hW
    let T := F ∪ W
    have hT : T.card = 3 * s := by
      dsimp [T]
      rw [Finset.card_union_of_disjoint hFW, hF, hW']
      omega
    let e : Fin (3 * s) ≃ {x // x ∈ T} :=
      (Fintype.equivFinOfCardEq (by simpa using hT)).symm
    let f := fun i => (e i).val
    have hf : Function.Injective f := by
      intro i j he
      exact e.injective (Subtype.ext he)
    have himage : Finset.univ.image f = T := by
      ext x
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, rfl⟩
        exact (e i).property
      · intro hx
        refine ⟨e.symm ⟨x, hx⟩, ?_⟩
        simp [f]
    exact ⟨f, hf, by simp, himage⟩

/-- The contiguous-index graph statement used in the returned written proof.
The first 2s indices are fixed ports and the remaining 2s are variable. -/
structure ContiguousSelectionGraph (s degree : ℕ) where
  neighbors : Fin (3 * s) → Finset (Fin (4 * s))
  nonempty : ∀ d, (neighbors d).Nonempty
  degree_le : ∀ d, (neighbors d).card ≤ degree
  route : ∀ W₀ : Finset (Fin (4 * s)),
    (∀ w ∈ W₀, 2 * s ≤ w.val) → W₀.card = s →
      ∃ f : Fin (3 * s) → Fin (4 * s), Function.Injective f ∧
        (∀ d, f d ∈ neighbors d) ∧
        Finset.univ.image f =
          (Finset.univ.filter (fun w : Fin (4 * s) => w.val < 2 * s)) ∪ W₀

/-- The sum-index graph used by the compiler has exactly the contiguous
port convention of the written graph theorem, up to a finite equivalence. -/
def selectionGraph_of_contiguous {s degree : ℕ}
    (graph : ContiguousSelectionGraph s degree) : SelectionGraph s degree := by
  classical
  have hsize : 2 * s + 2 * s = 4 * s := by omega
  let e : Sum (Fin (2 * s)) (Fin (2 * s)) ≃ Fin (4 * s) :=
    finSumFinEquiv.trans (finCongr hsize)
  have hleft (i : Fin (2 * s)) : (e (Sum.inl i)).val = i.val := by
    simp [e, Equiv.trans_apply, finCongr_apply, finSumFinEquiv]
  have hright (i : Fin (2 * s)) : (e (Sum.inr i)).val = 2 * s + i.val := by
    simp [e, Equiv.trans_apply, finCongr_apply, finSumFinEquiv, Nat.add_comm]
  let R := fun d => (graph.neighbors d).image e.symm
  refine ⟨R, ?_, ?_, ?_⟩
  · intro d
    exact Finset.image_nonempty.mpr (graph.nonempty d)
  · intro d
    exact Finset.card_image_le.trans (graph.degree_le d)
  · intro W₀ hcard
    let W := W₀.image (fun i => e (Sum.inr i))
    have hWinj : Function.Injective (fun i : Fin (2 * s) => e (Sum.inr i)) := by
      intro i j he
      exact Sum.inr.inj (e.injective he)
    have hWcard : W.card = s := by
      dsimp [W]
      rw [Finset.card_image_of_injective _ hWinj, hcard]
    have hWlower : ∀ w ∈ W, 2 * s ≤ w.val := by
      intro w hw
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
      rw [hright]
      omega
    obtain ⟨f, hfinj, hf, hfimage⟩ := graph.route W hWlower hWcard
    let g := fun d => e.symm (f d)
    have hfixedImage :
        (Finset.univ.filter (fun w : Fin (4 * s) => w.val < 2 * s)).image e.symm =
          Finset.univ.image Sum.inl := by
      ext u
      cases u with
      | inl i =>
          have hi : e (Sum.inl i) ∈
              Finset.univ.filter (fun w : Fin (4 * s) => w.val < 2 * s) := by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            rw [hleft]
            exact i.isLt
          have him : Sum.inl i ∈
              (Finset.univ.filter (fun w : Fin (4 * s) => w.val < 2 * s)).image e.symm :=
            Finset.mem_image.mpr ⟨e (Sum.inl i), hi, e.symm_apply_apply _⟩
          simp [him]
      | inr i =>
          have hnot : Sum.inr i ∉
              (Finset.univ.filter (fun w : Fin (4 * s) => w.val < 2 * s)).image e.symm := by
            intro hmem
            obtain ⟨w, hw, he⟩ := Finset.mem_image.mp hmem
            have hw' : w = e (Sum.inr i) := by
              apply e.symm.injective
              simpa using he
            have hlt := (Finset.mem_filter.mp hw).2
            rw [hw', hright] at hlt
            omega
          simp [hnot]
    have hWimage : W.image e.symm = W₀.image Sum.inr := by
      dsimp [W]
      rw [Finset.image_image]
      apply Finset.image_congr
      intro i _
      exact e.symm_apply_apply (Sum.inr i)
    refine ⟨g, e.symm.injective.comp hfinj, ?_, ?_⟩
    · intro d
      exact Finset.mem_image.mpr ⟨f d, hf d, rfl⟩
    · calc
        Finset.univ.image g = (Finset.univ.image f).image e.symm := by
          rw [Finset.image_image]
          rfl
        _ = ((Finset.univ.filter (fun w : Fin (4 * s) => w.val < 2 * s)) ∪ W).image
            e.symm := by rw [hfimage]
        _ = (Finset.univ.image Sum.inl) ∪ W₀.image Sum.inr := by
          rw [Finset.image_union, hfixedImage, hWimage]

/-- Relabel an abstract selection graph by two actual disjoint port pools.
Only the graph property is transported; no zero-sum matching is assumed. -/
theorem relabel_selectionGraph {α : Type*} [DecidableEq α]
    {s degree : ℕ} (fixed varying : Finset α)
    (hfixed : fixed.card = 2 * s) (hvarying : varying.card = 2 * s)
    (hdis : Disjoint fixed varying) (graph : SelectionGraph s degree) :
    ∃ R : Fin (3 * s) → Finset α,
      (∀ d, (R d).Nonempty ∧ (R d).card ≤ degree ∧ R d ⊆ fixed ∪ varying) ∧
      (∀ Y₀ : Finset α, Y₀ ⊆ varying → Y₀.card = s →
        ∃ f : Fin (3 * s) → α, (∀ d, f d ∈ R d) ∧ Function.Injective f ∧
          Finset.univ.image f = fixed ∪ Y₀) := by
  classical
  let eF : Fin (2 * s) ≃ {x // x ∈ fixed} :=
    (Fintype.equivFinOfCardEq (by simpa using hfixed)).symm
  let eV : Fin (2 * s) ≃ {x // x ∈ varying} :=
    (Fintype.equivFinOfCardEq (by simpa using hvarying)).symm
  let label : Sum (Fin (2 * s)) (Fin (2 * s)) → α :=
    Sum.elim (fun i => (eF i).val) (fun i => (eV i).val)
  have hlabel : Function.Injective label := by
    intro u v he
    cases u with
    | inl i =>
        cases v with
        | inl j =>
            have hij : eF i = eF j := Subtype.ext he
            exact congrArg Sum.inl (eF.injective hij)
        | inr j =>
            have hi : (eF i).val ∈ fixed := (eF i).property
            have hj : (eV j).val ∈ varying := (eV j).property
            have hv : (eF i).val ∈ varying := by
              change (eF i).val = (eV j).val at he
              exact he.symm ▸ hj
            exact (Finset.disjoint_left.mp hdis hi hv).elim
    | inr i =>
        cases v with
        | inl j =>
            have hi : (eV i).val ∈ varying := (eV i).property
            have hj : (eF j).val ∈ fixed := (eF j).property
            have hv : (eV i).val ∈ fixed := by
              change (eV i).val = (eF j).val at he
              exact he.symm ▸ hj
            exact (Finset.disjoint_left.mp hdis hv hi).elim
        | inr j =>
            have hij : eV i = eV j := Subtype.ext he
            exact congrArg Sum.inr (eV.injective hij)
  have hlabel_mem (u : Sum (Fin (2 * s)) (Fin (2 * s))) :
      label u ∈ fixed ∪ varying := by
    cases u with
    | inl i => exact Finset.mem_union_left _ (eF i).property
    | inr i => exact Finset.mem_union_right _ (eV i).property
  have hfixedImage : (Finset.univ.image (fun i : Fin (2 * s) => (eF i).val)) = fixed := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact (eF i).property
    · intro hx
      refine ⟨eF.symm ⟨x, hx⟩, ?_⟩
      simp
  let R := fun d => (graph.neighbors d).image label
  refine ⟨R, ?_, ?_⟩
  · intro d
    refine ⟨Finset.image_nonempty.mpr (graph.nonempty d),
      Finset.card_image_le.trans (graph.degree_le d), ?_⟩
    intro x hx
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hx
    exact hlabel_mem u
  · intro Y₀ hY₀ hs
    let W₀ := Finset.univ.filter (fun i : Fin (2 * s) => (eV i).val ∈ Y₀)
    have hVinject : Function.Injective (fun i : Fin (2 * s) => (eV i).val) := by
      intro i j he
      exact eV.injective (Subtype.ext he)
    have hWimage : W₀.image (fun i => (eV i).val) = Y₀ := by
      ext x
      simp only [Finset.mem_image, W₀, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact hi
      · intro hx
        have hxv := hY₀ hx
        refine ⟨eV.symm ⟨x, hxv⟩, ?_, ?_⟩
        · simpa using hx
        · simp
    have hWcard : W₀.card = s := by
      have h := Finset.card_image_of_injective W₀ hVinject
      rw [hWimage, hs] at h
      omega
    obtain ⟨f, hfinj, hf, hfimage⟩ := graph.route W₀ hWcard
    let g := fun d => label (f d)
    refine ⟨g, ?_, hlabel.comp hfinj, ?_⟩
    · intro d
      exact Finset.mem_image.mpr ⟨f d, hf d, rfl⟩
    · calc
        Finset.univ.image g = (Finset.univ.image f).image label := by
          rw [Finset.image_image]
          rfl
        _ = ((Finset.univ.image Sum.inl) ∪ W₀.image Sum.inr).image label := by
          rw [hfimage]
        _ = fixed ∪ Y₀ := by
          simp only [Finset.image_union, Finset.image_image, Function.comp_def,
            label, Sum.elim_inl, Sum.elim_inr, hfixedImage, hWimage]

/-- Reserve all fixed and dummy ports before the later subfamily is known.
Their existence is derived from the actual local selectors. -/
theorem portPool_of_localSupply
    {P : Vertex G → Prop} {budget arity s : ℕ}
    (hP : PairReservoir P) (hlocal : LocalSupply P budget arity)
    (harity : 1 ≤ arity) (part : Fin 3)
    (Y : Finset (Finset (Vertex G))) (U : Finset G)
    (hs : 1 ≤ s) (hsize₁ : s ≤ Y.card) (hsize₂ : Y.card ≤ 2 * s)
    (hYlegal : ∀ T ∈ Y, LegalPair part T)
    (hbudget : U.card + 8 * s ≤ budget) :
    Nonempty (PortPool P Y s part U) := by
  classical
  have hYne : Y.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨T₀, hT₀⟩ := hYne
  obtain ⟨a, ha, _⟩ := hYlegal T₀ hT₀
  let F := U ∪ support (Y.biUnion id)
  have hYsupport : (support (Y.biUnion id)).card ≤ 2 * Y.card := by
    rw [support_biUnion]
    calc
      _ ≤ ∑ T ∈ Y, (support T).card := Finset.card_biUnion_le
      _ ≤ ∑ _T ∈ Y, 2 := Finset.sum_le_sum (fun T hT =>
        legalPair_support_card_le (hYlegal T hT))
      _ = 2 * Y.card := by simp [Nat.mul_comm]
  have hFbudget : F.card + 2 * (4 * s - Y.card) ≤ budget := by
    have hbound := Finset.card_union_le U (support (Y.biUnion id))
    dsimp [F]
    omega
  obtain ⟨H, hHcard, hHlegal, hHavoid, _⟩ :=
    fresh_pair_family hP hlocal harity a ha part F (4 * s - Y.card) hFbudget
  have hHY : Disjoint H Y := by
    apply Finset.disjoint_left.mpr
    intro T hTH hTY
    obtain ⟨x, hx⟩ := legalPair_support_nonempty (hYlegal T hTY)
    have hxH : x ∈ support (H.biUnion id) := by
      rw [support_biUnion]
      exact Finset.mem_biUnion.mpr ⟨T, hTH, hx⟩
    have hxY : x ∈ F := Finset.mem_union_right _ (by
      rw [support_biUnion]
      exact Finset.mem_biUnion.mpr ⟨T, hTY, hx⟩)
    exact Finset.disjoint_left.mp hHavoid hxH hxY
  have hfixed_exists : 2 * s ≤ H.card := by omega
  obtain ⟨fixed, hfixedH, hfixedCard⟩ := Finset.exists_subset_card_eq hfixed_exists
  let dummy := H \ fixed
  let varying := Y ∪ dummy
  have hfixedY : Disjoint fixed Y := hHY.mono_left hfixedH
  have hYdummy : Disjoint Y dummy := by
    apply hHY.symm.mono_right
    exact Finset.sdiff_subset
  have hfixedDummy : Disjoint fixed dummy := by
    apply Finset.disjoint_left.mpr
    intro T hTf hTd
    exact (Finset.mem_sdiff.mp hTd).2 hTf
  have hdummyCard : dummy.card = 2 * s - Y.card := by
    dsimp [dummy]
    rw [Finset.card_sdiff_of_subset hfixedH, hHcard, hfixedCard]
    omega
  have hvaryCard : varying.card = 2 * s := by
    dsimp [varying]
    rw [Finset.card_union_of_disjoint hYdummy, hdummyCard]
    omega
  have hfixedAvoid : Disjoint (support (fixed.biUnion id)) U := by
    have hsub : fixed.biUnion id ⊆ H.biUnion id := by
      intro v hv
      obtain ⟨T, hT, hv⟩ := Finset.mem_biUnion.mp hv
      exact Finset.mem_biUnion.mpr ⟨T, hfixedH hT, hv⟩
    exact (hHavoid.mono_left (support_mono hsub)).mono_right Finset.subset_union_left
  have hpoolLegal : ∀ T ∈ fixed ∪ varying, LegalPair part T := by
    intro T hT
    rcases Finset.mem_union.mp hT with hT | hT
    · exact (hHlegal T (hfixedH hT)).1
    · rcases Finset.mem_union.mp hT with hT | hT
      · exact hYlegal T hT
      · exact (hHlegal T (Finset.mem_sdiff.mp hT).1).1
  have hpoolCard : (fixed ∪ varying).card = 4 * s := by
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_right.mpr
      ⟨hfixedY, hfixedDummy⟩), hfixedCard, hvaryCard]
    omega
  have hpoolSupport : (support ((fixed ∪ varying).biUnion id)).card ≤ 8 * s := by
    rw [support_biUnion]
    calc
      _ ≤ ∑ T ∈ fixed ∪ varying, (support T).card := Finset.card_biUnion_le
      _ ≤ ∑ _T ∈ fixed ∪ varying, 2 := Finset.sum_le_sum (fun T hT =>
        legalPair_support_card_le (hpoolLegal T hT))
      _ = 8 * s := by simp [hpoolCard, Nat.mul_comm]; omega
  refine ⟨⟨fixed, varying, hfixedCard, hvaryCard, Finset.subset_union_left,
    Finset.disjoint_union_right.mpr ⟨hfixedY, hfixedDummy⟩, ?_,
    hfixedAvoid, hpoolLegal, hpoolSupport⟩⟩
  intro T hT
  exact (hHlegal T (hfixedH hT)).2
end
end EndpointSelector.FixedCardinality
