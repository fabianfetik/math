import CorralFormalization.EndpointProof.Flow.UniversalSupply

/-! Selection of the actual regular layout or the genuine three-torsion case. -/

open scoped Classical BigOperators

namespace EndpointFlow

set_option maxHeartbeats 2500000
set_option maxRecDepth 2048

open EndpointSelector.Assembly

noncomputable section

variable {G : Type*} [CommRing G] [Fintype G]

def pairSet (f : Part → Fin 2 → G) : Finset (Vertex G) :=
  Finset.univ.image (fun pi : Part × Fin 2 ↦ (pi.1,f pi.1 pi.2))

def PairLegal (f : Part → Fin 2 → G) : Prop :=
  (∀ p i, f p i ≠ 0) ∧ ∀ p, f p 0 ≠ f p 1

def sixRoots (a a' b b' c c' : G) : Finset (Vertex G) :=
  {(0,a),(0,a'),(1,b),(1,b'),(2,c),(2,c')}

@[simp] theorem mem_exceptionalRoots (a : G) (p : Part) (x : G) :
    (p,x) ∈ exceptionalRoots a ↔ x=a ∨ x=-a := by
  simp only [exceptionalRoots,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨⟨q,b⟩,he⟩
    have hx := congrArg Prod.snd he
    cases b
    · exact Or.inl hx.symm
    · exact Or.inr hx.symm
  · rintro (he|he)
    · exact ⟨(p,false),by simpa using congrArg (fun y ↦ (p,y)) he.symm⟩
    · exact ⟨(p,true),by simpa using congrArg (fun y ↦ (p,y)) he.symm⟩

@[simp] theorem mem_pairSet (f : Part → Fin 2 → G) (p : Part) (x : G) :
    (p,x) ∈ pairSet f ↔ x=f p 0 ∨ x=f p 1 := by
  simp [pairSet,Fin.exists_fin_succ,eq_comm]

theorem pairSet_congr {f g : Part → Fin 2 → G}
    (h : ∀ p x, (x=f p 0 ∨ x=f p 1) ↔ (x=g p 0 ∨ x=g p 1)) : pairSet f = pairSet g := by
  ext ⟨p,x⟩
  simpa only [mem_pairSet] using h p x

@[simp] theorem rotate_refl (S : Finset (Vertex G)) : rotate (Equiv.refl Part) S = S := by
  change S.image id = S
  exact Finset.image_id

theorem pairSet_rotate (σ : Equiv.Perm Part) (f : Part → Fin 2 → G) :
    rotate σ (pairSet (fun p i ↦ f (σ p) i)) = pairSet f := by
  simp only [rotate,pairSet,Finset.image_image]
  ext v
  simp only [Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨⟨p,i⟩,rfl⟩
    exact ⟨(σ p,i),rfl⟩
  · rintro ⟨⟨p,i⟩,rfl⟩
    refine ⟨(σ.symm p,i),?_⟩
    simp [tagEquiv]

theorem sixRoots_eq_pairSet (a a' b b' c c' : G) :
    sixRoots a a' b b' c c' = pairSet ![![a,a'],![b,b'],![c,c']] := by
  ext v
  simp [sixRoots,pairSet,Fin.exists_fin_succ,eq_comm]
  tauto

theorem first_roots_eq (r : Fin 6 → G) :
    roots .first r = sixRoots (r 0) (r 1) (r 2) (r 3) (r 4) (r 5) := by
  ext v
  simp [roots,rootVertex,rootPart,sixRoots,Fin.exists_fin_succ,eq_comm]

theorem second_roots_eq (a b b' c c' : G) :
    roots .second ![a,b,b',c,c',-a] = sixRoots a (-a) b b' c c' := by
  ext v
  simp [roots,rootVertex,rootPart,sixRoots,Fin.exists_fin_succ,eq_comm]
  tauto

theorem third_roots_eq (a : G) : roots .third (thirdRoots a) = exceptionalRoots a := by
  ext ⟨p,x⟩
  rw [mem_exceptionalRoots]
  fin_cases p <;> simp [roots,rootVertex,rootPart,thirdRoots,Fin.exists_fin_succ,eq_comm]
  all_goals tauto

theorem exists_perm_01 (i j : Part) (hij : i ≠ j) :
    ∃ σ : Equiv.Perm Part, σ 0=i ∧ σ 1=j := by
  fin_cases i <;> fin_cases j
  all_goals try exact False.elim (hij rfl)
  all_goals first
    | exact ⟨Equiv.refl _,rfl,rfl⟩
    | exact ⟨Equiv.swap 1 2,rfl,rfl⟩
    | exact ⟨Equiv.swap 0 1,rfl,rfl⟩
    | exact ⟨(Equiv.swap 0 1).trans (Equiv.swap 0 2),rfl,rfl⟩
    | exact ⟨(Equiv.swap 0 2).trans (Equiv.swap 0 1),rfl,rfl⟩
    | exact ⟨Equiv.swap 0 2,rfl,rfl⟩

/-- The two choices in the written case-II argument, including both signs
of a and the possible interchange of the two C roots. -/
theorem choose_second_normalized (hodd : Odd (Fintype.card G))
    (a b b' c c' : G) (ha : a ≠ 0) (hb : b ≠ 0) (hb' : b' ≠ 0)
    (hc : c ≠ 0) (hc' : c' ≠ 0) (hbb' : b ≠ b') (hcc' : c ≠ c')
    (hba : b ≠ a) (hbna : b ≠ -a) :
    ∃ r : Fin 6 → G, RootLegal .second r ∧ OffsetDistinct .second r ∧
      roots .second r = sixRoots a (-a) b b' c c' := by
  have hchooseC : ∃ d e, ((d=c ∧ e=c') ∨ (d=c' ∧ e=c)) ∧ b'+d ≠ 0 := by
    by_cases hbc : b'+c ≠ 0
    · exact ⟨c,c',Or.inl ⟨rfl,rfl⟩,hbc⟩
    · refine ⟨c',c,Or.inr ⟨rfl,rfl⟩,?_⟩
      intro hbc'
      apply hcc'
      have hh : b'+c=0 := by tauto
      linear_combination hh-hbc'
  obtain ⟨d,e,hde,hbd⟩ := hchooseC
  have hdn : d ≠ 0 := by rcases hde with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> assumption
  have hen : e ≠ 0 := by rcases hde with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> assumption
  have hdene : d ≠ e := by
    rcases hde with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact hcc'
    · exact hcc'.symm
  have han := EndpointSelector.ne_neg_of_odd hodd ha
  have hchooseA : ∃ α, (α=a ∨ α=-a) ∧ α ≠ e := by
    by_cases hae : a ≠ e
    · exact ⟨a,Or.inl rfl,hae⟩
    · refine ⟨-a,Or.inr rfl,?_⟩
      intro he
      apply han
      have hh : a=e := by tauto
      exact hh.trans he.symm
  obtain ⟨α,hα,hαe⟩ := hchooseA
  have hαn : α ≠ 0 := by rcases hα with rfl|rfl <;> simpa using ha
  have hαb : α+b ≠ 0 := by
    intro he
    rcases hα with rfl|rfl
    · apply hbna; linear_combination he
    · apply hba; linear_combination he
  have heα : e+(-α) ≠ 0 := by
    intro he
    apply hαe
    linear_combination -he
  let r : Fin 6 → G := ![α,b,b',d,e,-α]
  have hrn : ∀ i, r i ≠ 0 := by
    intro i; fin_cases i <;> simp [r,hαn,hb,hb',hdn,hen]
  refine ⟨r,second_rootLegal r hrn ?_ ?_ ?_,
    two_block_offsetDistinct .second (by decide) r hrn ?_ ?_ ?_,?_⟩
  · simpa [r] using EndpointSelector.ne_neg_of_odd hodd hαn
  · simpa [r] using hbb'
  · simpa [r] using hdene
  · simpa [r] using hαb
  · simpa [r] using hbd
  · simpa [r] using heα
  · change roots .second ![α,b,b',d,e,-α] = _
    rw [second_roots_eq]
    rcases hα with rfl|rfl <;> rcases hde with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    all_goals ext v; simp [sixRoots] <;> tauto

/-- All six-root inputs are classified, allowing a common permutation of
the tagged parts. Cross-part numerical coincidences are unrestricted. -/
theorem choose_layout (hodd : Odd (Fintype.card G))
    (f : Part → Fin 2 → G) (hq : PairLegal f) :
    (∃ (σ : Equiv.Perm Part) (L : Layout) (r : Fin 6 → G),
      RootLegal L r ∧ OffsetDistinct L r ∧ rotate σ (roots L r) = pairSet f) ∨
    (∃ a : G, a ≠ 0 ∧ a+a+a=0 ∧ exceptionalRoots a = pairSet f) := by
  by_cases hp : ∀ p, f p 0+f p 1 ≠ 0
  · let r : Fin 6 → G := ![f 0 0,f 0 1,f 1 0,f 1 1,f 2 0,f 2 1]
    have hrn : ∀ i, r i ≠ 0 := by
      intro i; fin_cases i <;> simpa [r] using hq.1 _ _
    have hrl : RootLegal .first r := first_rootLegal r hrn
      (by simpa [r] using hq.2 0) (by simpa [r] using hq.2 1)
      (by simpa [r] using hq.2 2)
    have hrd : OffsetDistinct .first r := two_block_offsetDistinct .first (by decide) r hrn
      (by simpa [r] using hp 0) (by simpa [r] using hp 1) (by simpa [r] using hp 2)
    left
    refine ⟨Equiv.refl _,.first,r,hrl,hrd,?_⟩
    rw [rotate_refl]
    rw [first_roots_eq,sixRoots_eq_pairSet]
    apply pairSet_congr
    intro p x
    fin_cases p <;> rfl
  · have hex : ∃ i, f i 0+f i 1=0 := by simpa only [not_forall,ne_eq,not_not] using hp
    obtain ⟨i,hi⟩ := hex
    let a : G := f i 0
    have ha : a ≠ 0 := hq.1 i 0
    have hi1 : f i 1 = -a := by dsimp [a]; linear_combination hi
    by_cases hout : ∃ j k, f j k ≠ a ∧ f j k ≠ -a
    · obtain ⟨j,k,hja,hjna⟩ := hout
      have hji : i ≠ j := by
        intro he
        subst j
        fin_cases k
        · exact hja rfl
        · exact hjna hi1
      obtain ⟨σ,hσ0,hσ1⟩ := exists_perm_01 i j hji
      have hbb : f j k ≠ f j k.rev := by
        fin_cases k
        · simpa using hq.2 j
        · simpa using (hq.2 j).symm
      obtain ⟨r,hrl,hrd,hrset⟩ := choose_second_normalized hodd
        a (f j k) (f j k.rev) (f (σ 2) 0) (f (σ 2) 1)
        ha (hq.1 j k) (hq.1 j k.rev) (hq.1 (σ 2) 0) (hq.1 (σ 2) 1)
        hbb (hq.2 (σ 2)) hja hjna
      left
      refine ⟨σ,.second,r,hrl,hrd,?_⟩
      rw [hrset,sixRoots_eq_pairSet]
      have heq : pairSet ![![a,-a],![f j k,f j k.rev],![f (σ 2) 0,f (σ 2) 1]] =
          pairSet (fun p z ↦ f (σ p) z) := by
        apply pairSet_congr
        intro p x
        fin_cases p
        · change (x=a ∨ x=-a) ↔ (x=f (σ 0) 0 ∨ x=f (σ 0) 1)
          rw [hσ0,hi1]
        · change (x=f j k ∨ x=f j k.rev) ↔ (x=f (σ 1) 0 ∨ x=f (σ 1) 1)
          rw [hσ1]
          fin_cases k <;> simp <;> tauto
        · rfl
      rw [heq,pairSet_rotate]
    · have hsign (p : Part) (z : Fin 2) : f p z=a ∨ f p z=-a := by
        by_contra hs
        exact hout ⟨p,z,by tauto⟩
      have hpair (p : Part) :
          (f p 0=a ∧ f p 1=-a) ∨ (f p 0=-a ∧ f p 1=a) := by
        rcases hsign p 0 with h0|h0 <;> rcases hsign p 1 with h1|h1
        · exact False.elim ((hq.2 p) (h0.trans h1.symm))
        · exact Or.inl ⟨h0,h1⟩
        · exact Or.inr ⟨h0,h1⟩
        · exact False.elim ((hq.2 p) (h0.trans h1.symm))
      have hset : exceptionalRoots a = pairSet f := by
        ext ⟨p,x⟩
        rw [mem_exceptionalRoots,mem_pairSet]
        rcases hpair p with ⟨h0,h1⟩|⟨h0,h1⟩ <;> rw [h0,h1] <;> tauto
      by_cases h3 : a+a+a=0
      · exact Or.inr ⟨a,ha,h3,hset⟩
      · left
        refine ⟨Equiv.refl _,.third,thirdRoots a,third_rootLegal hodd a ha,
          third_offsetDistinct hodd a ha h3,?_⟩
        rw [rotate_refl,third_roots_eq,hset]

end

end EndpointFlow
