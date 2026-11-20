import CorralFormalization.Results.GeneralTiles.LocalTails
import CorralFormalization.DiversityCompletion.DirectedTerraceCompletion

/-!
# From the printed eight-vertex prefix to the physical tile input
-/

namespace CorralFormalization.LatinCompletion.GeneralTiles

open TerraceLift TerraceCompletion

def explicitPrefix (n : ℕ) : List (ZMod n) :=
  [((n-3 : ℕ) : ZMod n),((n-1 : ℕ) : ZMod n),2,12,
    ((n-2 : ℕ) : ZMod n),10,17,18]

def HasSpecifiedPrefix {n : ℕ} (D : DirectedTerrace n) : Prop :=
  (List.ofFn (fun i : Fin (n-1) => (D.vertices i).val)).take 8=explicitPrefix n

theorem explicitPrefix_vertex {n : ℕ} (D : DirectedTerrace n) (hn : 65≤n)
    (hp : HasSpecifiedPrefix D) (k : ℕ) (hk : k<8) :
    (D.vertices ⟨k,by omega⟩).val = (explicitPrefix n)[k]'(by simp [explicitPrefix]; omega) := by
  have he := congrArg (fun xs : List (ZMod n) => xs[k]?) hp
  have hpLen : k<(explicitPrefix n).length := by simpa [explicitPrefix] using hk
  rw [List.getElem?_eq_getElem hpLen] at he
  have he' : some (D.vertices ⟨k,by omega⟩).val =
      some ((explicitPrefix n)[k]'hpLen) := by
    simpa [HasSpecifiedPrefix,List.getElem?_take,List.getElem?_ofFn,hk,
      show k<n-1 by omega] using he
  exact Option.some.inj he'

def explicitGapPrefix (n : ℕ) : List ℕ := [2,3,10,n-14,12,7,1]

theorem explicitPrefix_gap {n : ℕ} [NeZero n] (D : DirectedTerrace n) (hn : 65≤n)
    (hp : HasSpecifiedPrefix D) (k : Fin 7) :
    D.gap ⟨k.val,by have := k.isLt; omega⟩ =
      (explicitGapPrefix n)[k.val]'(by simpa [explicitGapPrefix] using k.isLt) := by
  have hk := k.isLt
  have hnext : finRotate (n-1) (⟨k.val,by omega⟩ : Fin (n-1)) = ⟨k.val+1,by omega⟩ := by
    let : NeZero (n-1) := ⟨by omega⟩
    apply Fin.ext
    simp only [finRotate_apply,Fin.val_add]
    simp [Nat.mod_eq_of_lt (by omega : k.val+1<n-1)]
  rw [DirectedTerrace.gap,hnext,explicitPrefix_vertex D hn hp _ (by omega),
    explicitPrefix_vertex D hn hp _ (by omega)]
  have hs1 : ((n-1 : ℕ) : ZMod n)= -1 := by
    rw [Nat.cast_sub (by omega : 1≤n),ZMod.natCast_self,Nat.cast_one]
    simp
  have hs2 : ((n-2 : ℕ) : ZMod n)= -2 := by
    rw [Nat.cast_sub (by omega : 2≤n),ZMod.natCast_self,Nat.cast_ofNat]
    simp
  have hs3 : ((n-3 : ℕ) : ZMod n)= -3 := by
    rw [Nat.cast_sub (by omega : 3≤n),ZMod.natCast_self,Nat.cast_ofNat]
    simp
  have hs14 : (-14 : ZMod n)=((n-14 : ℕ) : ZMod n) := by
    rw [Nat.cast_sub (by omega : 14≤n),ZMod.natCast_self,Nat.cast_ofNat]
    simp
  have hv1 : (1 : ZMod n).val=1 := by
    simpa only [Nat.cast_one] using (ZMod.val_natCast_of_lt (by omega : 1<n))
  have hv2 : (2 : ZMod n).val=2 := ZMod.val_natCast_of_lt (by omega : 2<n)
  have hv3 : (3 : ZMod n).val=3 := ZMod.val_natCast_of_lt (by omega : 3<n)
  have hv7 : (7 : ZMod n).val=7 := ZMod.val_natCast_of_lt (by omega : 7<n)
  have hv10 : (10 : ZMod n).val=10 := ZMod.val_natCast_of_lt (by omega : 10<n)
  have hv12 : (12 : ZMod n).val=12 := ZMod.val_natCast_of_lt (by omega : 12<n)
  have hv14 : ((n-14 : ℕ) : ZMod n).val=n-14 := ZMod.val_natCast_of_lt (by omega : n-14<n)
  fin_cases k <;> simp [explicitPrefix,explicitGapPrefix,hs1,hs2,hs3] <;> norm_num1
  all_goals
    first
    | exact hv1
    | exact hv2
    | exact hv3
    | exact hv7
    | exact hv10
    | exact hv12
    | rw [hs14]; exact hv14

/-- The actual positive difference calendar follows from the literal
eight-vertex prefix; it is a conclusion rather than an extra hypothesis. -/
theorem explicitPrefix_calendar {n : ℕ} [NeZero n] (D : DirectedTerrace n) (hn : 65≤n)
    (hp : HasSpecifiedPrefix D) :
    D.word=explicitGapPrefix n++D.word.drop 7 := by
  have ht : D.word.take 7=explicitGapPrefix n := by
    apply List.ext_getElem
    · simp [DirectedTerrace.word,explicitGapPrefix]
      omega
    · intro k hk hk'
      have hk7 : k<7 := by simpa [explicitGapPrefix] using hk'
      simp only [List.getElem_take,DirectedTerrace.word,List.getElem_ofFn]
      exact explicitPrefix_gap D hn hp ⟨k,hk7⟩
  calc
    D.word = D.word.take 7++D.word.drop 7 := (List.take_append_drop 7 D.word).symm
    _ = _ := by rw [ht]

theorem explicitPrefix_start {n : ℕ} (D : DirectedTerrace n) (hn : 65≤n)
    (hp : HasSpecifiedPrefix D) :
    (D.vertices ⟨0,by omega⟩).val=((n-3 : ℕ) : ZMod n) := by
  simpa [explicitPrefix] using explicitPrefix_vertex D hn hp 0 (by decide)

/-- A fully constructed completed-terrace input from exactly the printed
directed terrace and vertex prefix. The suffix is its actual drop-7 gap
calendar. No body, physical partition or marker formulas are supplied. -/
def completedOfSpecifiedPrefix {n : ℕ} [NeZero n] (D : DirectedTerrace n)
    (hn : 65≤n) (hp : HasSpecifiedPrefix D) : CompletedTerrace n :=
  completedOfDirected D (by omega) ([7,1]++D.word.drop 7)
    (explicitPrefix_start D hn hp)
    (by simpa [explicitGapPrefix] using explicitPrefix_calendar D hn hp)

theorem completedOfSpecifiedPrefix_body {n : ℕ} [NeZero n] (D : DirectedTerrace n)
    (hn : 65≤n) (hp : HasSpecifiedPrefix D) :
    (completedOfSpecifiedPrefix D hn hp).body=[7,1]++D.word.drop 7 := rfl

end CorralFormalization.LatinCompletion.GeneralTiles
