import CorralFormalization.Results.SwitchFamily.Counting.CyclicWords
import CorralFormalization.Results.GeneralTiles.CyclicTiling

/-!
# The local words really are cyclic directed two/three layouts

A 0-state starts a tile; the states along it are 0,1 or 0,1,2.
The displayed map gives an actual partition by the existing physical
phase-block intervals. It includes tiles crossing the marked cut and
never quotients their internal positions into sets at a shorter period.
-/

namespace CorralFormalization.Results.SwitchFamily.Counting

open CorralFormalization.LatinCompletion.GeneralTiles

namespace Layout

variable {h : ℕ} [NeZero h]

theorem zero_next (u : Layout h) {p : ZMod h} (hp : u p = 0) : u (p+1) = 1 := by
  have he := u.2 p
  simpa [tileEdge, hp] using he

theorem one_prev (u : Layout h) {p : ZMod h} (hp : u p = 1) : u (p-1) = 0 := by
  have he := u.2 (p-1)
  simpa [tileEdge, hp] using he

theorem two_prev (u : Layout h) {p : ZMod h} (hp : u p = 2) : u (p-1) = 1 := by
  have he := u.2 (p-1)
  simpa [tileEdge, hp] using he

theorem two_next (u : Layout h) {p : ZMod h} (hp : u p = 2) : u (p+1) = 0 := by
  have he := u.2 p
  simpa [tileEdge, hp] using he

theorem one_next (u : Layout h) {p : ZMod h} (hp : u p = 1) :
    u (p+1) = 0 ∨ u (p+1) = 2 := by
  have he := u.2 p
  simpa [tileEdge, hp] using he

/-- Tiles have canonical finite labels: their 0-state positions. -/
abbrev Tile (u : Layout h) := {p : ZMod h // u p = 0}

/-- The existing block convention runs backwards from its endpoint. -/
def tileSize (u : Layout h) (p : u.Tile) : TileSize :=
  if u (p.1+2) = 2 then .three else .two

def tileEndpoint (u : Layout h) (p : u.Tile) : ZMod h :=
  if u (p.1+2) = 2 then p.1+2 else p.1+1

/-- Exact support membership with the start and internal positions retained. -/
theorem mem_tileBlock (u : Layout h) (p : u.Tile) (q : ZMod h) :
    q ∈ (u.tileSize p).block (u.tileEndpoint p) ↔
      q = p.1 ∨ q = p.1+1 ∨ (u (p.1+2) = 2 ∧ q = p.1+2) := by
  by_cases ht : u (p.1+2) = 2
  · simp only [tileSize, tileEndpoint, if_pos ht, TileSize.block,
      Finset.mem_insert, Finset.mem_singleton]
    have h1 : p.1+2-1 = p.1+1 := by ring
    have h2 : p.1+2-2 = p.1 := by ring
    rw [h1,h2]
    simp [ht, or_comm, or_assoc]
  · simp only [tileSize, tileEndpoint, if_neg ht, TileSize.block,
      Finset.mem_insert, Finset.mem_singleton]
    have h1 : p.1+1-1 = p.1 := by ring
    rw [h1]
    simp [ht, or_comm]

/-- The unique tile start owning a phase is q minus its internal state. -/
theorem tile_owner (u : Layout h) (p : u.Tile) (q : ZMod h)
    (hq : q ∈ (u.tileSize p).block (u.tileEndpoint p)) :
    p.1 = q - ((u q).val : ZMod h) := by
  rcases (u.mem_tileBlock p q).mp hq with hq | hq | ⟨hp,hq⟩
  · rw [hq,p.2]
    simp
  · have he := u.zero_next p.2
    rw [hq,he]
    simp
  · rw [hq,hp]
    simp

/-- A genuine actual directed interval partition, including the cut edge. -/
def toCyclicTiling (u : Layout h) : CyclicTiling h u.Tile where
  start := u.tileEndpoint
  size := u.tileSize
  partition q := by
    have hex : ∃ p : u.Tile, q ∈ (u.tileSize p).block (u.tileEndpoint p) := by
      have hq := (u q).isLt
      match hs : u q with
      | 0 =>
        refine ⟨⟨q,hs⟩, (u.mem_tileBlock _ _).mpr (Or.inl rfl)⟩
      | 1 =>
        have hp : u (q-1) = 0 := u.one_prev hs
        refine ⟨⟨q-1,hp⟩, (u.mem_tileBlock _ _).mpr (Or.inr (Or.inl ?_))⟩
        simp
      | 2 =>
        have hp1 : u (q-1) = 1 := u.two_prev hs
        have hp0 : u (q-2) = 0 := by
          have he := u.one_prev hp1
          have hpos : (q-1)-1 = q-2 := by ring
          simpa only [hpos] using he
        refine ⟨⟨q-2,hp0⟩, (u.mem_tileBlock _ _).mpr (Or.inr (Or.inr ⟨?_,?_⟩))⟩
        · simpa using hs
        · simp
      | ⟨k+3,hk⟩ => omega
    obtain ⟨p,hp⟩ := hex
    refine ⟨p,hp,?_⟩
    intro r hr
    apply Subtype.ext
    exact (u.tile_owner r q hr).trans (u.tile_owner p q hp).symm

/-- For this actual partition, every internal tile position has the state
specified by the local word. -/
theorem start_states (u : Layout h) (p : u.Tile) :
    u p.1 = 0 ∧ u (p.1+1) = 1 ∧
      ((u.tileSize p = .two ∧ u (p.1+2) = 0) ∨
       (u.tileSize p = .three ∧ u (p.1+2) = 2 ∧ u (p.1+3) = 0)) := by
  refine ⟨p.2,u.zero_next p.2,?_⟩
  by_cases ht : u (p.1+2) = 2
  · refine Or.inr ⟨by simp [tileSize,ht], ht, ?_⟩
    have he := u.two_next ht
    have hpos : p.1+2+1 = p.1+3 := by ring
    simpa only [hpos] using he
  · refine Or.inl ⟨by simp [tileSize,ht], ?_⟩
    have he := u.one_next (u.zero_next p.2)
    have hpos : p.1+1+1 = p.1+2 := by ring
    rw [hpos] at he
    exact he.resolve_right ht

/-- The unlabelled physical phase-layout data: endpoint and tile size. -/
def tileData (u : Layout h) : Finset (ZMod h × TileSize) :=
  Finset.univ.image (fun p : u.Tile => (u.tileEndpoint p,u.tileSize p))

private def leftEnd (e : ZMod h) (s : TileSize) : ZMod h :=
  match s with
  | .two => e-1
  | .three => e-2

private theorem leftEnd_data (u : Layout h) (p : u.Tile) :
    leftEnd (u.tileEndpoint p) (u.tileSize p) = p.1 := by
  by_cases ht : u (p.1+2) = 2 <;> simp [leftEnd,tileEndpoint,tileSize,ht]

/-- There is no collapse of marked word layouts in the actual unlabelled
phase-interval data once h >= 3. -/
theorem tileData_injective (hh : 3 ≤ h) :
    Function.Injective (tileData : Layout h → Finset (ZMod h × TileSize)) := by
  intro u v huv
  apply LocalWord.ext
  intro q
  obtain ⟨p,hp,_⟩ := u.toCyclicTiling.partition q
  have hpd : (u.tileEndpoint p,u.tileSize p) ∈ v.tileData := by
    rw [← huv]
    exact Finset.mem_image.mpr ⟨p,Finset.mem_univ _,rfl⟩
  obtain ⟨r,_,hr⟩ := Finset.mem_image.mp hpd
  have he : v.tileEndpoint r = u.tileEndpoint p := congrArg Prod.fst hr
  have hs : v.tileSize r = u.tileSize p := congrArg Prod.snd hr
  have hrq : q ∈ (v.tileSize r).block (v.tileEndpoint r) := by
    rw [he,hs]
    exact hp
  have hpr : p.1 = r.1 := by
    rw [← u.leftEnd_data p, ← v.leftEnd_data r,he,hs]
  have hcast : ((u q).val : ZMod h) = ((v q).val : ZMod h) := by
    have hou := u.tile_owner p q hp
    have hov := v.tile_owner r q hrq
    rw [hpr,hov] at hou
    exact (sub_right_inj).mp hou.symm
  apply Fin.ext
  have huq : (u q).val < h := lt_of_lt_of_le (u q).isLt hh
  have hvq : (v q).val < h := lt_of_lt_of_le (v q).isLt hh
  have hv := congrArg ZMod.val hcast
  simpa [ZMod.val_natCast,Nat.mod_eq_of_lt huq,Nat.mod_eq_of_lt hvq] using hv

/-- Phase translation is a genuine permutation of unlabelled tile data.
Our precomposition convention rotates the geometric layout by minus t. -/
theorem tileData_rotate (u : Layout h) (t : ZMod h) :
    tileData (LocalWord.rotate t u) =
      u.tileData.image (fun a => (a.1-t,a.2)) := by
  ext a
  constructor
  · intro ha
    obtain ⟨p,_,hp⟩ := Finset.mem_image.mp ha
    let r : u.Tile := ⟨p.1+t,p.2⟩
    apply Finset.mem_image.mpr
    refine ⟨(u.tileEndpoint r,u.tileSize r),Finset.mem_image.mpr
      ⟨r,Finset.mem_univ _,rfl⟩,?_⟩
    rw [← hp]
    dsimp [r,tileEndpoint,tileSize,LocalWord.rotate]
    have had : p.1+2+t = p.1+t+2 := by ring
    simp only [had]
    split_ifs <;> ext <;> simp <;> ring
  · intro ha
    obtain ⟨b,hb,hba⟩ := Finset.mem_image.mp ha
    obtain ⟨r,_,hr⟩ := Finset.mem_image.mp hb
    let p : Tile (LocalWord.rotate t u) := ⟨r.1-t,by simpa using r.2⟩
    apply Finset.mem_image.mpr
    refine ⟨p,Finset.mem_univ _,?_⟩
    rw [← hba,← hr]
    dsimp [p,tileEndpoint,tileSize,LocalWord.rotate]
    have had : r.1-t+2+t = r.1+2 := by ring
    simp only [had]
    split_ifs <;> ext <;> simp <;> ring

end Layout
end CorralFormalization.Results.SwitchFamily.Counting
