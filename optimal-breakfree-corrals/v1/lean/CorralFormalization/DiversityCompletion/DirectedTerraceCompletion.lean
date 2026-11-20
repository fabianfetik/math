import CorralFormalization.DiversityCompletion.LatinConnectorPrefix
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.List.Rotate
import Mathlib.Data.List.FinRange

namespace CorralFormalization.LatinCompletion.TerraceCompletion

open LatinTransfer TerraceLift LatinPrefix LatinPrefixSupply

/-- An actual directed rotational terrace. Its vertices enumerate every
nonzero residue once. The positive representatives of its actual cyclic
successor differences enumerate `[1,...,n-1]` once, including the final
edge back to the initial vertex. No lift, physical partition or partial-sum
representation is an input. -/
structure DirectedTerrace (n : ℕ) where
  vertices : Fin (n-1) ≃ {x : ZMod n // x ≠ 0}
  rainbow : (List.ofFn (fun i : Fin (n-1) =>
    ((vertices (finRotate (n-1) i)).val - (vertices i).val).val)).Perm
      (fullGapList (n-1))

namespace DirectedTerrace

def gap {n : ℕ} (D : DirectedTerrace n) (i : Fin (n-1)) : ℕ :=
  ((D.vertices (finRotate (n-1) i)).val - (D.vertices i).val).val

def word {n : ℕ} (D : DirectedTerrace n) : List ℕ := List.ofFn D.gap

theorem word_perm {n : ℕ} (D : DirectedTerrace n) :
    D.word.Perm (fullGapList (n-1)) := D.rainbow

theorem step {n : ℕ} [NeZero n] (D : DirectedTerrace n) (i : Fin (n-1)) :
    (D.vertices (finRotate (n-1) i)).val = (D.vertices i).val + (D.gap i : ZMod n) := by
  rw [gap,ZMod.natCast_zmod_val]
  abel

/-- Change the distinguished first vertex by one actual cyclic edge. -/
def rotate {n : ℕ} (D : DirectedTerrace n) : DirectedTerrace n where
  vertices := (finRotate (n-1)).trans D.vertices
  rainbow := by
    change (List.ofFn (D.gap ∘ finRotate (n-1))).Perm (fullGapList (n-1))
    exact ((finRotate (n-1)).ofFn_comp_perm D.gap).trans D.rainbow

theorem ofFn_rotate {N : ℕ} (f : Fin N → ℕ) :
    List.ofFn (f ∘ finRotate N) = (List.ofFn f).rotate 1 := by
  apply List.ext_getElem
  · simp
  · intro k hk hk'
    have hkN : k < N := by simpa using hk
    have : NeZero N := ⟨by omega⟩
    simp only [List.getElem_ofFn,List.getElem_rotate,List.length_ofFn,
      Function.comp_apply]
    congr 1
    apply Fin.ext
    simp only [finRotate_apply,Fin.val_add]
    simp

theorem rotate_word {n : ℕ} (D : DirectedTerrace n) :
    D.rotate.word = D.word.rotate 1 := by
  exact ofFn_rotate D.gap

/-- Consecutive actual differences telescope to the positive-lift partial
sums at every vertex before the cyclic return. -/
theorem vertex_partialSum {n : ℕ} [NeZero n] (D : DirectedTerrace n)
    (hpos : 0 < n-1) (t : Fin (n-1)) :
    (D.vertices t).val = (D.vertices ⟨0,hpos⟩).val +
      (((D.word.take t.val).sum : ℕ) : ZMod n) := by
  suffices hh : ∀ k (hk : k < n-1),
      (D.vertices ⟨k,hk⟩).val = (D.vertices ⟨0,hpos⟩).val +
        (((D.word.take k).sum : ℕ) : ZMod n) by
    exact hh t.val t.isLt
  intro k
  induction k with
  | zero => intro hk; simp [word]
  | succ k ih =>
    intro hk
    have hk' : k < n-1 := by omega
    have hnext : finRotate (n-1) (⟨k,hk'⟩ : Fin (n-1)) = ⟨k+1,hk⟩ := by
      have : NeZero (n-1) := ⟨by omega⟩
      apply Fin.ext
      simp only [finRotate_apply,Fin.val_add]
      simp [Nat.mod_eq_of_lt hk]
    rw [← hnext,D.step,ih hk']
    rw [List.sum_take_succ _ _ (by simpa [word] using hk')]
    simp only [word,List.getElem_ofFn,Nat.cast_add]
    abel

end DirectedTerrace

/-- Convert the original orientation beginning at `n-3` into the genuine
completed-terrace input used by the physical construction. The concrete
calendar hypothesis is an equality for the terrace's *actual* positive
successor differences, not a desired lift or corral assertion. -/
def completedOfDirected {n : ℕ} [NeZero n] (D : DirectedTerrace n)
    (hn : 15 ≤ n) (body : List ℕ)
    (hstart : (D.vertices ⟨0,by omega⟩).val = ((n-3 : ℕ) : ZMod n))
    (hcalendar : D.word = [2,3,10,n-14,12] ++ body) : CompletedTerrace n := by
  have hg : D.gap ⟨0,by omega⟩ = 2 := by
    have hh := congrArg (fun w : List ℕ => w[0]?) hcalendar
    simpa [DirectedTerrace.word,show 1 < n by omega] using hh
  have hs : (D.rotate.vertices ⟨0,by omega⟩).val = ((n-1 : ℕ) : ZMod n) := by
    change (D.vertices (finRotate (n-1) ⟨0,by omega⟩)).val = _
    rw [D.step,hstart,hg,← Nat.cast_add]
    congr 1
    omega
  have hw : D.rotate.word = TileGapWords.cycle n body := by
    rw [D.rotate_word,hcalendar]
    simp [List.rotate_cons_succ,TileGapWords.cycle]
  exact {
    body := body
    differences := hw ▸ D.rotate.word_perm
    vertices := D.rotate.vertices
    vertex_at := fun t => by
      rw [D.rotate.vertex_partialSum (by omega),hs,hw]
      simp only [Nat.cast_add]
  }

theorem completedOfDirected_body {n : ℕ} [NeZero n] (D : DirectedTerrace n)
    (hn : 15 ≤ n) (body : List ℕ)
    (hstart : (D.vertices ⟨0,by omega⟩).val = ((n-3 : ℕ) : ZMod n))
    (hcalendar : D.word = [2,3,10,n-14,12] ++ body) :
    (completedOfDirected D hn body hstart hcalendar).body = body := rfl

/-- The exact continuation contract needed after the concrete connector-prefix chain:
the actual directed terrace starts at `n-3` and preserves the prescribed
positive difference prefix; the remaining suffix is arbitrary. -/
def completedOfConnectorPrefix {n r : ℕ} [NeZero n] [NeZero r]
    (D : DirectedTerrace n) (hn : 15 ≤ n) (y : Cell r → ℕ) (suffix : List ℕ)
    (hstart : (D.vertices ⟨0,by omega⟩).val = ((n-3 : ℕ) : ZMod n))
    (hcalendar : D.word = [2,3,10,n-14,12] ++ connectorPrefixGaps n y ++ suffix) :
    CompletedTerrace n :=
  completedOfDirected D hn (connectorPrefixGaps n y ++ suffix) hstart
    (by simpa only [List.append_assoc] using hcalendar)

theorem completedOfConnectorPrefix_body {n r : ℕ} [NeZero n] [NeZero r]
    (D : DirectedTerrace n) (hn : 15 ≤ n) (y : Cell r → ℕ) (suffix : List ℕ)
    (hstart : (D.vertices ⟨0,by omega⟩).val = ((n-3 : ℕ) : ZMod n))
    (hcalendar : D.word = [2,3,10,n-14,12] ++ connectorPrefixGaps n y ++ suffix) :
    (completedOfConnectorPrefix D hn y suffix hstart hcalendar).body = connectorPrefixGaps n y ++ suffix := rfl

/-- In particular no independent H2/location input is required for the
completed terrace converted from such an actual directed connector-prefix terrace. -/
def bodyInputOfDirectedConnectorPrefix {n r : ℕ} [NeZero n] [NeZero r]
    (D : DirectedTerrace n) (hr : 2 ≤ r) (hlarge : 100*r*r ≤ n)
    (y : Cell r → ℕ) (hy : ∀ i, 30*r*r ≤ y i ∧ y i < 40*r*r)
    (suffix : List ℕ)
    (hstart : (D.vertices ⟨0,by
      have : 15 ≤ n := by nlinarith
      omega⟩).val =
      ((n-3 : ℕ) : ZMod n))
    (hcalendar : D.word = [2,3,10,n-14,12] ++ connectorPrefixGaps n y ++ suffix) :
    BodyInput (completedOfConnectorPrefix D (by nlinarith) y suffix hstart hcalendar) r :=
  bodyInputOfConnectorPrefix _ hr hlarge y hy suffix rfl

end CorralFormalization.LatinCompletion.TerraceCompletion
