import CorralFormalization.Results.SwitchFamily.LayoutPhysicalBridge

/-!
# Actual phase bits and actual physical site-pair choices

The alphabet Fin (2^m) is decoded by the explicit binary finite-function
bijection. The physical pairs are precisely the concrete `sitePair` values;
their injectivity and the complete image of the actual switch layer are
proved, not assumed as an abstract choice correspondence.
-/

namespace CorralFormalization.Results.SwitchFamily.Counting.DecoratedPhysicalCode

open CorralFormalization.LatinCompletion.TerraceLift
open CorralFormalization.Results.SwitchFamily
open CorralFormalization.Results.SwitchFamily.Physical
open CorralFormalization.Results.SwitchFamily.LayoutPhysicalBridge

noncomputable section

variable {h n m : ℕ} [NeZero h] [NeZero n] [NeZero (h*n)]

/-- Explicit binary digits, indexed by the actual local switch coordinate. -/
def colorBitsEquiv (m : ℕ) : Fin (2^m) ≃ (Fin m → Bool) :=
  (finFunctionFinEquiv (m:=2) (n:=m)).symm.trans
    (Equiv.piCongrRight (fun _ => finTwoEquiv))

/-- The same m-bit alphabet at every phase, with no divisor-height
recomputation of m. -/
def phaseBitsEquiv (h m : ℕ) : (ZMod h → Fin (2^m)) ≃ (Bit m h → Bool) where
  toFun b k := colorBitsEquiv m (b k.2) k.1
  invFun b q := (colorBitsEquiv m).symm (fun i => b (i,q))
  left_inv b := by
    funext q
    exact (colorBitsEquiv m).symm_apply_apply (b q)
  right_inv b := by
    funext k
    exact congrFun ((colorBitsEquiv m).apply_symm_apply (fun i => b (i,k.2))) k.1

abbrev PairChoice (hsize : (5*m+8)^2 ≤ n) :=
  ↥((switchLayer (h:=h) hsize).edges.toFinset.powerset)

/-- Complete actual image of the physical site-pair index map. -/
theorem layer_pair_mem_iff (hsize : (5*m+8)^2 ≤ n)
    (e : ZMod (h*n) × ZMod (h*n)) :
    e ∈ (switchLayer (h:=h) hsize).edges.toFinset ↔
      ∃ k : Bit m h, sitePair (n:=n) k = e := by
  classical
  simp [switchLayer]

/-- The pair indices are a proved bijection onto the actual physical layer. -/
def sitePairIndexEquiv (hsize : (5*m+8)^2 ≤ n) :
    Bit m h ≃ ↥((switchLayer (h:=h) hsize).edges.toFinset) :=
  Equiv.ofBijective (fun k => ⟨sitePair (n:=n) k,
    (layer_pair_mem_iff hsize _).mpr ⟨k,rfl⟩⟩) (by
      constructor
      · intro k l he
        exact sitePair_injective hsize (congrArg Subtype.val he)
      · intro e
        obtain ⟨k,hk⟩ := (layer_pair_mem_iff hsize e.1).mp e.2
        exact ⟨k,Subtype.ext hk⟩)

/-- The concrete selected pair set of an actual bit function. -/
def selectedPairs (b : Bit m h → Bool) : Finset (ZMod (h*n) × ZMod (h*n)) :=
  (Finset.univ.filter (fun k => b k = true)).image (sitePair (n:=n))

theorem selectedPairs_mem_iff (hsize : (5*m+8)^2 ≤ n)
    (b : Bit m h → Bool) (k : Bit m h) :
    sitePair (n:=n) k ∈ selectedPairs b ↔ b k = true := by
  classical
  simp only [selectedPairs,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨l,hl,he⟩
    exact (sitePair_injective hsize he) ▸ hl
  · intro hk
    exact ⟨k,hk,rfl⟩

theorem selectedPairs_subset (hsize : (5*m+8)^2 ≤ n) (b : Bit m h → Bool) :
    selectedPairs b ⊆ (switchLayer (h:=h) hsize).edges.toFinset := by
  classical
  intro e he
  obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp he
  exact (layer_pair_mem_iff hsize _).mpr ⟨k,rfl⟩

/-- Every actual subset is represented and every bit is recovered by testing
its own actual physical pair. -/
def bitsChoiceEquiv (hsize : (5*m+8)^2 ≤ n) :
    (Bit m h → Bool) ≃ PairChoice (h:=h) hsize where
  toFun b := ⟨selectedPairs b,Finset.mem_powerset.mpr (selectedPairs_subset hsize b)⟩
  invFun U k := decide (sitePair (n:=n) k ∈ U.1)
  left_inv b := by
    funext k
    have he := selectedPairs_mem_iff hsize b k
    cases hb : b k <;> simp_all
  right_inv U := by
    apply Subtype.ext
    ext e
    constructor
    · intro he
      obtain ⟨k,hk,hke⟩ := Finset.mem_image.mp he
      have hkU : sitePair (n:=n) k ∈ U.1 := by
        simpa using (Finset.mem_filter.mp hk).2
      simpa only [hke] using hkU
    · intro he
      have heLayer := (Finset.mem_powerset.mp U.2) he
      obtain ⟨k,hke⟩ := (layer_pair_mem_iff hsize e).mp heLayer
      apply Finset.mem_image.mpr
      refine ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,hke⟩
      simpa only [hke,decide_eq_true_eq] using he

/-- Its decoding is literal membership in the indexed concrete pair. -/
@[simp] theorem bitsChoiceEquiv_decode (hsize : (5*m+8)^2 ≤ n)
    (U : PairChoice (h:=h) hsize) (k : Bit m h) :
    (bitsChoiceEquiv hsize).symm U k = decide (sitePair (n:=n) k ∈ U.1) := rfl

/-- The geometric translation of a concrete pair by an actual whole phase. -/
def pairShift (a : ZMod h) (e : ZMod (h*n) × ZMod (h*n)) :=
  (e.1+zeroSite h n a,e.2+zeroSite h n a)

theorem sitePair_shift (a : ZMod h) (k : Bit m h) :
    sitePair (n:=n) (k.1,k.2+a) = pairShift a (sitePair (n:=n) k) := by
  ext <;> simp [sitePair,endpoint,pairShift,zeroSite_add] <;> ring

/-- A geometric phase shift carries an actual pair choice to an actual pair
choice. Layer preservation follows from complete indexing by sitePair. -/
def shiftChoice (hsize : (5*m+8)^2 ≤ n) (a : ZMod h)
    (U : PairChoice (h:=h) hsize) : PairChoice (h:=h) hsize := by
  refine ⟨U.1.image (pairShift a),Finset.mem_powerset.mpr ?_⟩
  intro e he
  obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp he
  obtain ⟨k,rfl⟩ := (layer_pair_mem_iff hsize d).mp ((Finset.mem_powerset.mp U.2) hd)
  apply (layer_pair_mem_iff hsize _).mpr
  exact ⟨(k.1,k.2+a),sitePair_shift a k⟩

/-- Index-level action of a geometric phase shift; bits are moved, never
complemented. -/
def bitShift (a : ZMod h) (b : Bit m h → Bool) : Bit m h → Bool :=
  fun k => b (k.1,k.2-a)

/-- Actual equivariance of the bit/subset encoding with physical pair
translation, proved through the concrete sitePair indices. -/
theorem bitsChoiceEquiv_shift (hsize : (5*m+8)^2 ≤ n) (a : ZMod h)
    (b : Bit m h → Bool) :
    bitsChoiceEquiv hsize (bitShift a b) = shiftChoice hsize a (bitsChoiceEquiv hsize b) := by
  apply Subtype.ext
  ext e
  constructor
  · intro he
    obtain ⟨k,hk,hke⟩ := Finset.mem_image.mp he
    have hkbit : b (k.1,k.2-a) = true := (Finset.mem_filter.mp hk).2
    apply Finset.mem_image.mpr
    refine ⟨sitePair (n:=n) (k.1,k.2-a),?_,?_⟩
    · exact (selectedPairs_mem_iff hsize b _).mpr hkbit
    · rw [← sitePair_shift]
      simpa only [sub_add_cancel] using hke
  · intro he
    obtain ⟨d,hd,hde⟩ := Finset.mem_image.mp he
    obtain ⟨k,hk,hkd⟩ := Finset.mem_image.mp hd
    have hkbit : b k = true := (Finset.mem_filter.mp hk).2
    apply Finset.mem_image.mpr
    refine ⟨(k.1,k.2+a),Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,?_⟩
    · simpa [bitShift] using hkbit
    · rw [sitePair_shift,hkd]
      exact hde

end
end CorralFormalization.Results.SwitchFamily.Counting.DecoratedPhysicalCode
