import CorralFormalization.EndpointProof.Flow.Cover.Supplier
import CorralFormalization.EndpointProof.Flow.LayoutSelection
import CorralFormalization.EndpointProof.Flow.AffineAvailability
import CorralFormalization.EndpointProof.Flow.Results

/-!
The concrete affine-event supplier for the paired-cover iteration. Input
triples are converted to actual legal root coordinates before choosing the
regular layout or the genuine three-torsion exceptional construction.
-/

open scoped Classical BigOperators

namespace EndpointFlow.Cover

set_option maxHeartbeats 1500000
set_option maxRecDepth 2048

open EndpointSelector EndpointSelector.Assembly

noncomputable section

variable {G : Type*} [CommRing G] [Fintype G]

/-- Two disjoint nonzero one-per-part triples are exactly one legal two-root
query. Numerical coincidences in different tagged parts remain unrestricted. -/
theorem roots_of_two_triples (O X : Finset (Vertex G))
    (hO : OnePerPart O) (hX : OnePerPart X) (hdis : Disjoint O X)
    (hOn : ∀ v ∈ O, v.2 ≠ 0) (hXn : ∀ v ∈ X, v.2 ≠ 0) :
    ∃ f : Part → Fin 2 → G, PairLegal f ∧ pairSet f = O ∪ X := by
  choose a ha hua using hO
  choose b hb hub using hX
  let f : Part → Fin 2 → G := fun p ↦ ![a p,b p]
  refine ⟨f,⟨?_,?_⟩,?_⟩
  · intro p i
    fin_cases i
    · exact hOn (p,a p) (ha p)
    · exact hXn (p,b p) (hb p)
  · intro p he
    change a p = b p at he
    exact Finset.disjoint_left.mp hdis (ha p) (he.symm ▸ hb p)
  · ext ⟨p,x⟩
    simp only [mem_pairSet,Finset.mem_union]
    change (x=a p ∨ x=b p) ↔ (p,x) ∈ O ∨ (p,x) ∈ X
    constructor
    · rintro (he | he)
      · exact Or.inl (he.symm ▸ ha p)
      · exact Or.inr (he.symm ▸ hb p)
    · rintro (hx | hx)
      · exact Or.inl (hua p x hx)
      · exact Or.inr (hub p x hx)

theorem rotate_sdiff (σ : Equiv.Perm Part) (S T : Finset (Vertex G)) :
    rotate σ (S \ T) = rotate σ S \ rotate σ T :=
  Finset.image_sdiff S T (tagEquiv σ).injective

theorem numericalSupport_subset_of_paired
    (S : Finset (Vertex G)) (F : Finset G)
    (hp : ∀ v ∈ S, (v.1,-v.2) ∈ S) (hc : ∀ v ∈ S, v.2 ∈ F) :
    numericalSupport S ⊆ F := by
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx
    exact hc v hv
  · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx
    exact hc (v.1,-v.2) (hp v hv)

theorem regular_numericalSupport_subset (L : Layout) (r : Fin 6 → G) (xy : G × G) :
    numericalSupport (augmentation L r xy) ⊆ orbitSupport L r xy :=
  numericalSupport_subset_of_paired _ _ (augmentation_paired L r xy)
    (augmentation_numerical_mem L r xy)

theorem roots_numericalSupport_subset (L : Layout) (r : Fin 6 → G) :
    numericalSupport (roots L r) ⊆ rootSupport r := by
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
    exact rootSupport_mem r i
  · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_image.mpr ⟨(i,true),Finset.mem_univ _,rfl⟩

theorem rotate_paired (σ : Equiv.Perm Part) (S : Finset (Vertex G))
    (hS : ∀ v ∈ S, (v.1,-v.2) ∈ S) :
    ∀ v ∈ rotate σ S, (v.1,-v.2) ∈ rotate σ S := by
  intro v hv
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
  exact Finset.mem_image.mpr ⟨(w.1,-w.2),hS w hw,rfl⟩

theorem exceptional_numericalSupport_subset (a : G) (h3 : a+a+a=0) (xy : G × G) :
    numericalSupport (exceptionalAugmentation xy) ⊆ orbitSupport .first (dummyRoots a) xy :=
  numericalSupport_subset_of_paired _ _ (exceptional_paired xy)
    (exceptional_support_subset a h3 xy)

theorem exceptional_roots_numericalSupport_subset (a : G) :
    numericalSupport (exceptionalRoots a) ⊆ rootSupport (dummyRoots a) := by
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨⟨p,b⟩,_,rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_image.mpr ⟨(0,b),Finset.mem_univ _,rfl⟩
  · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨⟨p,b⟩,_,rfl⟩ := Finset.mem_image.mp hv
    refine Finset.mem_image.mpr ⟨(0,!b),Finset.mem_univ _,?_⟩
    cases b <;> simp [dummyRoots]

theorem exceptional_subset_candidate (a : G) (h3 : a+a+a=0) (xy : G × G) :
    exceptionalAugmentation xy ⊆ augmentation .first (dummyRoots a) xy := by
  intro v hv
  obtain ⟨pb,_,rfl⟩ := Finset.mem_image.mp hv
  exact Finset.mem_image.mpr ⟨(exceptionalSlot pb.1,pb.2),Finset.mem_univ _,
    (exceptionalVertex_eq a h3 xy pb).symm⟩

/-- One actual regular layout, including the tag permutation chosen from the
input. Freshness is numerical and includes every sign of every root. -/
theorem regular_output_of_affine_event
    (hodd : Odd (Fintype.card G)) (hn : 1000 ≤ Fintype.card G)
    (budget : ℕ) (ω : EndpointFullProduct.FullSample G)
    (hgood : affineFlowEvent hodd hn budget ω)
    (O X : Finset (Vertex G)) (F : Finset G) (hF : F.card ≤ budget)
    (σ : Equiv.Perm Part) (L : Layout) (r : Fin 6 → G)
    (hr : RootLegal L r) (hoff : OffsetDistinct L r)
    (hroots : rotate σ (roots L r) = O ∪ X) :
    Nonempty (SixRootOutput (QVertex ω) O X F) := by
  let rq : AffineQuery G := ⟨(σ,L,r),hoff⟩
  obtain ⟨xy,hv,hd,hQ⟩ := successful_affine_candidate hodd hn budget ω hgood rq F hF
  have hv' : Valid L r xy := hv
  have hsupport : numericalSupport (rotate σ (augmentation L r xy)) = orbitSupport L r xy := by
    rw [numericalSupport_rotate,augmentation_numericalSupport]
  have hrootSupport : numericalSupport (O ∪ X) = rootSupport r := by
    rw [← hroots,numericalSupport_rotate,roots_numericalSupport]
  refine ⟨{
    added := rotate σ (augmentation L r xy)
    output := rotate σ (outputs L r xy)
    added_Q := hQ
    added_paired := rotate_paired σ _ (augmentation_paired L r xy)
    added_nonzero := ?_
    added_balanced := rotate_balanced σ _ (regular_augmentation_balanced hodd L r xy hv')
    added_card_le := by simpa using (augmentation_card hodd L r xy hv').le
    output_subset := Finset.image_subset_image (outputs_subset_augmentation L r xy)
    output_onePerPart := rotate_regular_outputs_onePerPart hodd σ L r xy hv'
    roots_fresh := by rw [hsupport,hrootSupport]; exact hv'.2.2
    avoids := by rw [hsupport]; exact hd
    matching := ?_ }⟩
  · intro v hvInterior
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hvInterior
    exact augmentation_nonzero L r xy hv' w hw
  · have hm := (regularMatchingOn hodd L r xy hr hv').rotated σ
    rw [rotate_sdiff,rotate_union,hroots] at hm
    exact hm

/-- Case IV uses only the three initial inverse pairs of the nine-orbit
candidate. The artificial root list is used solely for packing and labels;
the actual matching is `exceptionalMatchingOn` on the real six roots. -/
theorem exceptional_output_of_affine_event
    (hodd : Odd (Fintype.card G)) (hn : 1000 ≤ Fintype.card G)
    (budget : ℕ) (ω : EndpointFullProduct.FullSample G)
    (hgood : affineFlowEvent hodd hn budget ω)
    (O X : Finset (Vertex G)) (F : Finset G) (hF : F.card ≤ budget)
    (a : G) (ha : a ≠ 0) (h3 : a+a+a=0)
    (hroots : exceptionalRoots a = O ∪ X) :
    Nonempty (SixRootOutput (QVertex ω) O X F) := by
  let rq : AffineQuery G := exceptionalAffine hodd ⟨a,ha,h3⟩
  obtain ⟨xy,hv,hd,hQ⟩ := successful_affine_candidate hodd hn budget ω hgood rq F hF
  have hv' : Valid .first (dummyRoots a) xy := hv
  have hQ' : ∀ v ∈ augmentation .first (dummyRoots a) xy, QVertex ω v := by
    simpa [rq,exceptionalAffine,rotate_refl] using hQ
  have hs := exceptional_numericalSupport_subset a h3 xy
  refine ⟨{
    added := exceptionalAugmentation xy
    output := exceptionalOutputs xy
    added_Q := fun v hv ↦ hQ' v (exceptional_subset_candidate a h3 xy hv)
    added_paired := exceptional_paired xy
    added_nonzero := exceptional_augmentation_nonzero a h3 xy hv'
    added_balanced := exceptional_augmentation_balanced hodd a h3 xy hv'
    added_card_le := (exceptionalAugmentation_card_le xy).trans (by decide)
    output_subset := exceptional_outputs_subset xy
    output_onePerPart := exceptional_outputs_onePerPart xy
    roots_fresh := ?_
    avoids := hd.mono_left hs
    matching := ?_ }⟩
  · rw [← hroots]
    exact hv'.2.2.mono hs (exceptional_roots_numericalSupport_subset a)
  · have hm := exceptionalMatchingOn hodd a ha h3 xy hv'
    rw [hroots] at hm
    exact hm

/-- The actual common affine Q event is a complete six-root supplier. All
input triples and all later forbidden supports are queried after one ω. -/
theorem sixRootSupplier_of_affine_event
    (hodd : Odd (Fintype.card G)) (hn : 1000 ≤ Fintype.card G)
    (budget : ℕ) (ω : EndpointFullProduct.FullSample G)
    (hgood : affineFlowEvent hodd hn budget ω) :
    SixRootSupplier (QVertex ω) budget := by
  intro O X F hO hX hdis hOn hXn hF
  obtain ⟨f,hf,hset⟩ := roots_of_two_triples O X hO hX hdis hOn hXn
  rcases choose_layout hodd f hf with hregular | hexceptional
  · obtain ⟨σ,L,r,hr,hoff,hroots⟩ := hregular
    exact regular_output_of_affine_event hodd hn budget ω hgood O X F hF
      σ L r hr hoff (hroots.trans hset)
  · obtain ⟨a,ha,h3,hroots⟩ := hexceptional
    exact exceptional_output_of_affine_event hodd hn budget ω hgood O X F hF
      a ha h3 (hroots.trans hset)

end
end EndpointFlow.Cover
