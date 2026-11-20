import CorralFormalization.DiversityCompletion.LatinCorralConstruction

namespace CorralFormalization.LatinCompletion

open LatinTransfer
open PhysicalCorral

/-- The paper's original symbols s_(j,u)=(j+u) mod r. -/
def cyclicLatinSquare (r : ℕ) [NeZero r] : LatinSquare r where
  entry j u := j + u
  row_bijective j := (Equiv.addLeft j).bijective
  column_bijective u := (Equiv.addRight u).bijective

def cyclicLatinFamily (h r : ℕ) [NeZero r] : Family h r := fun _ => cyclicLatinSquare r

theorem cyclicLatinSquare_entry {r : ℕ} [NeZero r] (j u : Fin r) :
    ((cyclicLatinSquare r).entry j u).val = (j.val + u.val) % r := by
  rfl

def phaseIndex {h : ℕ} [NeZero h] (q : ZMod h) : Fin h := ⟨q.val, q.val_lt⟩

theorem phaseIndex_natCast {h : ℕ} [NeZero h] (i : Fin h) :
    phaseIndex (i.val : ZMod h) = i := by
  apply Fin.ext
  exact ZMod.val_natCast_of_lt i.isLt

theorem corralRows_natural_partition {h n : ℕ} [NeZero (width n)]
    (R : CorralRows h n) (hwidth : width n = h * n) (x : ℕ) (hx : x < width n) :
    ∃! i, x ∈ R.sites i := by
  have hm : (x : ZMod (width n)) ∈ Finset.univ.biUnion
      (fun i => physicalSites (width n) (R.sites i)) := by
    rw [corralRows_physical_full R hwidth]
    exact Finset.mem_univ _
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hm
  have hinat : x ∈ R.sites i := by
    have ht := (physicalSites_mem_iff _ (R.bounded i) (x : ZMod (width n))).mp hi
    simpa [ZMod.val_natCast_of_lt hx] using ht
  refine ⟨i, hinat, ?_⟩
  intro j hj
  by_contra hji
  exact Finset.disjoint_left.mp (R.disjoint j i hji) hj hinat

namespace PhysicalFrame

variable {h n r : ℕ} [NeZero h] [NeZero (h * n)]

/-- A real `CorralRows` baseline supplies the full physical baseline once
its rows are identified with the frame's positive one-turn gap words.
Only this initial row identification is assumed, not any modified inventory. -/
def fromCorralRows (G : PhysicalFrame h n r) (R : CorralRows h n)
    (hwidth : width n = h * n) (L₀ : Family h r)
    (hrows : ∀ q : ZMod h, (G.row L₀ q).image ZMod.val = R.sites (phaseIndex q)) :
    FullBaseline G := by
  letI : NeZero (width n) := ⟨by rw [hwidth]; exact NeZero.ne _⟩
  refine { latin := L₀, partition := ?_, palette := ?_ }
  · intro x
    obtain ⟨i, hi, huniq⟩ := corralRows_natural_partition R hwidth x.val
      (by simpa [hwidth] using x.val_lt)
    let q : ZMod h := (i.val : ZMod h)
    have hq : phaseIndex q = i := phaseIndex_natCast i
    have hx : x ∈ G.row L₀ q := by
      have him : x.val ∈ (G.row L₀ q).image ZMod.val := by rw [hrows q, hq]; exact hi
      obtain ⟨y, hy, he⟩ := Finset.mem_image.mp him
      have hyx : y = x := ZMod.val_injective _ he
      simpa [hyx] using hy
    refine ⟨q, hx, ?_⟩
    intro t ht
    have htnat : x.val ∈ R.sites (phaseIndex t) := by
      rw [← hrows t]
      exact Finset.mem_image.mpr ⟨x, ht, rfl⟩
    have hidx := huniq (phaseIndex t) htnat
    apply ZMod.val_injective h
    have hv := congrArg Fin.val hidx
    change t.val = i.val at hv
    simpa [q, ZMod.val_natCast_of_lt i.isLt] using hv
  · intro q
    rw [hrows q, ← hwidth]
    exact R.gaps (phaseIndex q)

/-- Uniform genuine-corral output and absolute unordered physical
injectivity. The hypotheses are one local frame, one actual baseline and
its initial geometric identification. No `FixedSkeleton` or
`CyclicEdgeCertificate` is supplied by the caller. -/
theorem latin_corrals_from_baseline (G : PhysicalFrame h n r)
    (hr : 2 ≤ r) (hn : n = 2 * h - 1) (hlarge : 100 * r * r ≤ n)
    (R : CorralRows h n) (L₀ : Family h r)
    (hrows : ∀ q : ZMod h, (G.row L₀ q).image ZMod.val = R.sites (phaseIndex q)) :
    ∃ C : Family h r → CorralRows h n,
      (∀ L q, (C L).sites q = naturalRows (G.row L) q) ∧
      (∀ L x, x < width n → ∃! q, x ∈ (C L).sites q) ∧
      Function.Injective G.unlabelled := by
  obtain ⟨hres, hh⟩ := connectorPrefix_numeric_bounds hr hn hlarge
  let T := G.fromCorralRows R (optimal_width (NeZero.pos h) hn) L₀ hrows
  refine ⟨G.completed hr hlarge hres T hn, ?_, ?_, ?_⟩
  · exact G.completed_sites hr hlarge hres T hn
  · exact G.completed_full_occupancy hr hlarge hres T hn
  · exact G.unlabelled_injective hr hlarge hres T hh

theorem latin_corrals_from_cyclic_baseline [NeZero r] (G : PhysicalFrame h n r)
    (hr : 2 ≤ r) (hn : n = 2 * h - 1) (hlarge : 100 * r * r ≤ n)
    (R : CorralRows h n)
    (hrows : ∀ q : ZMod h,
      (G.row (cyclicLatinFamily h r) q).image ZMod.val = R.sites (phaseIndex q)) :
    ∃ C : Family h r → CorralRows h n,
      (∀ L q, (C L).sites q = naturalRows (G.row L) q) ∧
      (∀ L x, x < width n → ∃! q, x ∈ (C L).sites q) ∧
      Function.Injective G.unlabelled :=
  G.latin_corrals_from_baseline hr hn hlarge R (cyclicLatinFamily h r) hrows

end PhysicalFrame

end CorralFormalization.LatinCompletion
