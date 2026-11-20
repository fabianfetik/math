import CorralFormalization.Results.SwitchFamily.Counting.TileSemantics
import CorralFormalization.Results.GeneralTiles.LayoutTails

/-!
# Every actual cyclic two/three tiling has its local-word representation

The state at a phase is its internal position in the unique original tile.
This constructs the local word directly from an arbitrary actual interval
partition; no word representation or desired start-set equality is assumed.
-/

namespace CorralFormalization.Results.SwitchFamily.LayoutCompleteness

open CorralFormalization.LatinCompletion
open TerraceLift GeneralTiles
open CorralFormalization.Results.SwitchFamily.Counting

noncomputable section

variable {h : ℕ} [NeZero h]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def leftStart (L : CyclicTiling h ι) (i : ι) : ZMod h :=
  match L.size i with
  | .two => L.start i-1
  | .three => L.start i-2

theorem mem_block (L : CyclicTiling h ι) (i : ι) (q : ZMod h) :
    q∈(L.size i).block (L.start i) ↔
      q=leftStart L i ∨ q=leftStart L i+1 ∨
        (L.size i=.three ∧ q=leftStart L i+2) := by
  cases hs : L.size i
  · simp [TileSize.block,leftStart,hs,or_comm]
  · have h1 : L.start i-2+1=L.start i-1 := by ring
    simp [TileSize.block,leftStart,hs,h1,or_comm,or_left_comm,or_assoc]

theorem leftStart_mem (L : CyclicTiling h ι) (i : ι) :
    leftStart L i∈(L.size i).block (L.start i) :=
  (mem_block L i _).mpr (Or.inl rfl)

theorem leftStart_one_mem (L : CyclicTiling h ι) (i : ι) :
    leftStart L i+1∈(L.size i).block (L.start i) :=
  (mem_block L i _).mpr (Or.inr (Or.inl rfl))

theorem leftStart_two_mem (L : CyclicTiling h ι) (i : ι) (hi : L.size i=.three) :
    leftStart L i+2∈(L.size i).block (L.start i) :=
  (mem_block L i _).mpr (Or.inr (Or.inr ⟨hi,rfl⟩))

theorem start_mem (L : CyclicTiling h ι) (i : ι) :
    L.start i∈(L.size i).block (L.start i) := by
  cases hs : L.size i <;> simp [TileSize.block,hs]

def owner (L : CyclicTiling h ι) (q : ZMod h) : ι := (L.partition q).choose

theorem owner_mem (L : CyclicTiling h ι) (q : ZMod h) :
    q∈(L.size (owner L q)).block (L.start (owner L q)) :=
  (L.partition q).choose_spec.1

theorem owner_eq (L : CyclicTiling h ι) (q : ZMod h) (i : ι)
    (hi : q∈(L.size i).block (L.start i)) : owner L q=i :=
  ((L.partition q).choose_spec.2 i hi).symm

theorem same_owner (L : CyclicTiling h ι) (q : ZMod h) (i j : ι)
    (hi : q∈(L.size i).block (L.start i))
    (hj : q∈(L.size j).block (L.start j)) : i=j :=
  (owner_eq L q i hi).symm.trans (owner_eq L q j hj)

theorem internal_position_lt (L : CyclicTiling h ι) (hh : 3≤h) (q : ZMod h) :
    (q-leftStart L (owner L q)).val<3 := by
  let i := owner L q
  have hi := owner_mem L q
  change q∈(L.size i).block (L.start i) at hi
  change (q-leftStart L i).val<3
  rcases (mem_block L i q).mp hi with hq|hq|⟨_,hq⟩
  · rw [hq,sub_self,ZMod.val_zero]
    omega
  · rw [hq,add_sub_cancel_left]
    have he : (1 : ZMod h).val=1 := by
      simpa only [Nat.cast_one] using (ZMod.val_natCast_of_lt (by omega : 1<h))
    omega
  · rw [hq,add_sub_cancel_left]
    have he : (2 : ZMod h).val=2 := ZMod.val_natCast_of_lt (by omega : 2<h)
    omega

def state (L : CyclicTiling h ι) (hh : 3≤h) (q : ZMod h) : Fin 3 :=
  ⟨(q-leftStart L (owner L q)).val,internal_position_lt L hh q⟩

theorem state_left (L : CyclicTiling h ι) (hh : 3≤h) (i : ι) :
    state L hh (leftStart L i)=0 := by
  apply Fin.ext
  simp only [state,owner_eq L _ i (leftStart_mem L i),sub_self,ZMod.val_zero,Fin.val_zero]

theorem state_one (L : CyclicTiling h ι) (hh : 3≤h) (i : ι) :
    state L hh (leftStart L i+1)=1 := by
  apply Fin.ext
  simp only [state,owner_eq L _ i (leftStart_one_mem L i),add_sub_cancel_left]
  simpa only [Nat.cast_one,Fin.val_one] using
    (ZMod.val_natCast_of_lt (by omega : 1<h))

theorem state_two (L : CyclicTiling h ι) (hh : 3≤h) (i : ι) (hi : L.size i=.three) :
    state L hh (leftStart L i+2)=2 := by
  apply Fin.ext
  simp only [state,owner_eq L _ i (leftStart_two_mem L i hi),add_sub_cancel_left]
  exact ZMod.val_natCast_of_lt (by omega : 2<h)

theorem state_endpoint_two (L : CyclicTiling h ι) (hh : 3≤h) (i : ι) (hi : L.size i=.two) :
    state L hh (L.start i)=1 := by
  have he : leftStart L i+1=L.start i := by simp [leftStart,hi]
  rw [← he]
  exact state_one L hh i

theorem state_endpoint_three (L : CyclicTiling h ι) (hh : 3≤h) (i : ι) (hi : L.size i=.three) :
    state L hh (L.start i)=2 := by
  have he : leftStart L i+2=L.start i := by simp [leftStart,hi]
  rw [← he]
  exact state_two L hh i hi

theorem state_endpoint_ne_zero (L : CyclicTiling h ι) (hh : 3≤h) (i : ι) :
    state L hh (L.start i)≠0 := by
  cases hs : L.size i
  · rw [state_endpoint_two L hh i hs]
    decide
  · rw [state_endpoint_three L hh i hs]
    decide

theorem state_after_endpoint (L : CyclicTiling h ι) (hh : 3≤h) (i : ι) :
    state L hh (L.start i+1)=0 := by
  let j := owner L (L.start i+1)
  have hj := owner_mem L (L.start i+1)
  change L.start i+1∈(L.size j).block (L.start j) at hj
  rcases (mem_block L j _).mp hj with he|he|⟨hs,he⟩
  · rw [he,state_left L hh j]
  · have hp : L.start i=leftStart L j := add_right_cancel he
    have hij : i=j := same_owner L (L.start i) i j (start_mem L i)
      (hp ▸ leftStart_mem L j)
    have hz := state_left L hh j
    rw [← hp] at hz
    exact False.elim (state_endpoint_ne_zero L hh i hz)
  · have hp : L.start i=leftStart L j+1 := by linear_combination he
    have hij : i=j := same_owner L (L.start i) i j (start_mem L i)
      (hp ▸ leftStart_one_mem L j)
    have h1 := state_one L hh j
    have h2 := state_endpoint_three L hh i (hij ▸ hs)
    rw [← hp] at h1
    rw [h1] at h2
    exact False.elim (by have := congrArg Fin.val h2; norm_num at this)

/-- A canonical local-word representation of every actual cyclic tiling.
The three states are the actual internal positions, not arbitrary colors. -/
def ofCyclicTiling (L : CyclicTiling h ι) (hh : 3≤h) : Layout h := by
  refine ⟨state L hh,?_⟩
  intro q
  let i := owner L q
  have hi := owner_mem L q
  change q∈(L.size i).block (L.start i) at hi
  rcases (mem_block L i q).mp hi with hq|hq|⟨hs,hq⟩
  · rw [hq,state_left L hh i,state_one L hh i]
    decide
  · rw [hq,state_one L hh i]
    cases hs : L.size i
    · have he : leftStart L i+1=L.start i := by simp [leftStart,hs]
      rw [he,state_after_endpoint L hh i]
      decide
    · have he : leftStart L i+1+1=leftStart L i+2 := by ring
      rw [he,state_two L hh i hs]
      decide
  · rw [hq,state_two L hh i hs]
    have he : leftStart L i+2=L.start i := by simp [leftStart,hs]
    rw [he,state_after_endpoint L hh i]
    decide

@[simp] theorem ofCyclicTiling_apply (L : CyclicTiling h ι) (hh : 3≤h) (q : ZMod h) :
    ofCyclicTiling L hh q=state L hh q := rfl

def tileMap (L : CyclicTiling h ι) (hh : 3≤h) (i : ι) : (ofCyclicTiling L hh).Tile :=
  ⟨leftStart L i,state_left L hh i⟩

theorem tileMap_data (L : CyclicTiling h ι) (hh : 3≤h) (i : ι) :
    (ofCyclicTiling L hh).tileEndpoint (tileMap L hh i)=L.start i ∧
      (ofCyclicTiling L hh).tileSize (tileMap L hh i)=L.size i := by
  change (if ofCyclicTiling L hh (leftStart L i+2)=2 then leftStart L i+2
    else leftStart L i+1)=L.start i ∧
    (if ofCyclicTiling L hh (leftStart L i+2)=2 then TileSize.three
    else TileSize.two)=L.size i
  cases hs : L.size i
  · have hnext : ofCyclicTiling L hh (leftStart L i+2)=0 := by
      have he : leftStart L i+2=L.start i+1 := by simp [leftStart,hs]; ring
      rw [he,ofCyclicTiling_apply,state_after_endpoint L hh i]
    rw [hnext]
    simp [leftStart,hs]
  · have hnext : ofCyclicTiling L hh (leftStart L i+2)=2 := state_two L hh i hs
    rw [hnext]
    simp [leftStart,hs]

theorem tileMap_injective (L : CyclicTiling h ι) (hh : 3≤h) :
    Function.Injective (tileMap L hh) := by
  intro i j he
  have hp : leftStart L i=leftStart L j := congrArg Subtype.val he
  exact same_owner L (leftStart L i) i j (leftStart_mem L i) (hp ▸ leftStart_mem L j)

theorem tileMap_surjective (L : CyclicTiling h ι) (hh : 3≤h) :
    Function.Surjective (tileMap L hh) := by
  intro p
  let i := owner L p.val
  have hi := owner_mem L p.val
  change p.val∈(L.size i).block (L.start i) at hi
  have hp : state L hh p.val=0 := p.property
  rcases (mem_block L i p.val).mp hi with hq|hq|⟨hs,hq⟩
  · exact ⟨i,Subtype.ext hq.symm⟩
  · rw [hq,state_one L hh i] at hp
    have hc := congrArg Fin.val hp
    norm_num at hc
  · rw [hq,state_two L hh i hs] at hp
    have hc := congrArg Fin.val hp
    norm_num at hc

/-- Original tile labels and the canonical zero-state labels describe
exactly the same intervals, up to their unique relabelling. -/
def tileEquiv (L : CyclicTiling h ι) (hh : 3≤h) : ι≃(ofCyclicTiling L hh).Tile :=
  Equiv.ofBijective (tileMap L hh) ⟨tileMap_injective L hh,tileMap_surjective L hh⟩

theorem tileEquiv_data (L : CyclicTiling h ι) (hh : 3≤h) (i : ι) :
    (ofCyclicTiling L hh).tileEndpoint (tileEquiv L hh i)=L.start i ∧
      (ofCyclicTiling L hh).tileSize (tileEquiv L hh i)=L.size i :=
  tileMap_data L hh i

theorem start_sets_eq (L : CyclicTiling h ι) (hh : 3≤h) (s : TileSize) :
    (Finset.univ.filter (fun p : (ofCyclicTiling L hh).Tile =>
      (ofCyclicTiling L hh).tileSize p=s)).image (ofCyclicTiling L hh).tileEndpoint=
        (Finset.univ.filter (fun i => L.size i=s)).image L.start := by
  ext q
  simp only [Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨p,hps,hpq⟩
    obtain ⟨i,rfl⟩ := tileMap_surjective L hh p
    exact ⟨i,(tileMap_data L hh i).2.symm.trans hps,
      (tileMap_data L hh i).1.symm.trans hpq⟩
  · rintro ⟨i,his,hiq⟩
    exact ⟨tileMap L hh i,(tileMap_data L hh i).2.trans his,
      (tileMap_data L hh i).1.trans hiq⟩

theorem twoStarts_eq (L : CyclicTiling h ι) (hh : 3≤h) :
    (Layout.toCyclicTiling (ofCyclicTiling L hh)).twoStarts=L.twoStarts :=
  start_sets_eq L hh .two

theorem threeStarts_eq (L : CyclicTiling h ι) (hh : 3≤h) :
    (Layout.toCyclicTiling (ofCyclicTiling L hh)).threeStarts=L.threeStarts :=
  start_sets_eq L hh .three

theorem rows_tileMap {n : ℕ} [NeZero n] [NeZero (h*n)]
    (L : CyclicTiling h ι) (hh : 3≤h) (T : CompletedTerrace n) (i : ι) :
    (Layout.toCyclicTiling (ofCyclicTiling L hh)).rows T (tileMap L hh i)=L.rows T i := by
  change (match (ofCyclicTiling L hh).tileSize (tileMap L hh i) with
    | .two => {T.tileFirst ((ofCyclicTiling L hh).tileEndpoint (tileMap L hh i)),
        T.tileTwoSecond ((ofCyclicTiling L hh).tileEndpoint (tileMap L hh i))}
    | .three => {T.tileFirst ((ofCyclicTiling L hh).tileEndpoint (tileMap L hh i)),
        T.tileThreeSecond ((ofCyclicTiling L hh).tileEndpoint (tileMap L hh i)),
        T.tileThreeThird ((ofCyclicTiling L hh).tileEndpoint (tileMap L hh i))})=L.rows T i
  rw [(tileMap_data L hh i).1,(tileMap_data L hh i).2]
  rfl

/-- Every original physical tile-row family is exactly represented by
the constructed word; equality holds for every actual terrace. -/
theorem family_eq {n : ℕ} [NeZero n] [NeZero (h*n)]
    (L : CyclicTiling h ι) (hh : 3≤h) (T : CompletedTerrace n) :
    (Layout.toCyclicTiling (ofCyclicTiling L hh)).family T=L.family T := by
  ext R
  simp only [CyclicTiling.family,Finset.mem_biUnion,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨p,hp⟩
    obtain ⟨i,rfl⟩ := tileMap_surjective L hh p
    rw [rows_tileMap L hh T i] at hp
    exact ⟨i,hp⟩
  · rintro ⟨i,hi⟩
    refine ⟨tileMap L hh i,?_⟩
    rw [rows_tileMap L hh T i]
    exact hi

/-- Thus the local-word model covers every two/three interval partition
in particular throughout the paper range h≥33. -/
theorem every_tiling_represented (L : CyclicTiling h ι) (hh : 3≤h) :
    ∃ u : Layout h, ∃ e : ι≃u.Tile,
      (∀ i,u.tileEndpoint (e i)=L.start i ∧ u.tileSize (e i)=L.size i) ∧
      u.toCyclicTiling.twoStarts=L.twoStarts ∧ u.toCyclicTiling.threeStarts=L.threeStarts :=
  ⟨ofCyclicTiling L hh,tileEquiv L hh,tileEquiv_data L hh,twoStarts_eq L hh,threeStarts_eq L hh⟩

end
end CorralFormalization.Results.SwitchFamily.LayoutCompleteness
