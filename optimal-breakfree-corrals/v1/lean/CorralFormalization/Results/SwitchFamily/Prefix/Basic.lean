import CorralFormalization.Results.PathTerraceCompletion
import CorralFormalization.Results.GeneralTiles.DirectedInput

/-!
# The literal Appendix A switch prefix

The natural representatives below are precisely (A1)--(A3).  They are
constructed before any endpoint-completion theorem is used.
-/

namespace CorralFormalization.Results.SwitchFamily.Prefix

open CorralFormalization.LatinCompletion.TerraceCompletion
open CorralFormalization.LatinCompletion.GeneralTiles

/-- The natural floor parameter in Appendix A. -/
def count (n : ℕ) : ℕ := (Nat.sqrt n - 8) / 5

def parity (i : ℕ) : ℕ := i % 2
def alpha (i : ℕ) : ℕ := 8*i+20
def beta (i : ℕ) : ℕ := 8*i+23+parity i
def center (i : ℕ) : ℕ := 8*i^2+44*i+38+i/2

def backward (i : ℕ) : ℕ := center i-beta i
def ending (i : ℕ) : ℕ := center i+beta i+1

def blockNaturals (i : ℕ) : List ℕ :=
  [center i, center i+alpha i+1, backward i, center i+1, ending i]

def initialNaturals (n : ℕ) : List ℕ := [n-3,n-1,2,12,n-2,10,17,18]

def naturals (n m : ℕ) : List ℕ :=
  initialNaturals n ++ (List.range m).flatMap blockNaturals

def blockVertices (n i : ℕ) : List (ZMod n) := (blockNaturals i).map Nat.cast

def vertices (n m : ℕ) : List (ZMod n) := (naturals n m).map Nat.cast

def blockColors (n i : ℕ) : List ℕ :=
  [alpha i, alpha i+1, n-(alpha i+beta i+1), beta i+1, beta i]

def colors (n m : ℕ) : List ℕ :=
  explicitGapPrefix n ++ (List.range m).flatMap (blockColors n)

@[simp] theorem parity_lt (i : ℕ) : parity i < 2 := Nat.mod_lt _ (by decide)

theorem parity_succ (i : ℕ) : parity (i+1)+parity i=1 := by
  simp only [parity]
  omega

theorem center_succ (i : ℕ) :
    center (i+1)=center i+16*i+52+parity i := by
  have hf : (i+1)/2=i/2+i%2 := by omega
  simp only [center, parity, hf]
  ring

theorem beta_alpha (i : ℕ) : beta i=alpha i+3+parity i := by
  simp [beta,alpha]

theorem beta_lt_center (i : ℕ) : beta i<center i := by
  have hp := parity_lt i
  simp only [beta,center]
  nlinarith [Nat.zero_le (i/2), Nat.zero_le (i^2)]

theorem backward_add_beta (i : ℕ) : backward i+beta i=center i :=
  Nat.sub_add_cancel (beta_lt_center i).le

theorem predecessor (i : ℕ) : center (i+1)=ending i+alpha (i+1) := by
  rw [center_succ]
  simp [ending,alpha,beta]
  omega

@[simp] theorem predecessor_zero : center 0=18+alpha 0 := by decide

theorem backward_next (i : ℕ) :
    backward (i+1)+3+parity (i+1)=ending i := by
  have h := backward_add_beta (i+1)
  rw [predecessor] at h
  have hb := beta_alpha (i+1)
  omega

theorem ending_above (i : ℕ) : center i+alpha i+1<ending i := by
  have h := beta_alpha i
  simp only [ending]
  omega

theorem block_bounds {i x : ℕ} (hx : x ∈ blockNaturals i) :
    backward i ≤ x ∧ x ≤ ending i := by
  have hbc := backward_add_beta i
  have hba := beta_alpha i
  simp only [blockNaturals,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl <;> simp only [ending] <;> omega

theorem backward_strictMono : StrictMono backward := by
  apply strictMono_nat_of_lt_succ
  intro i
  have hn := backward_next i
  have hb := backward_add_beta i
  have hp := parity_lt (i+1)
  have hbp := beta_alpha i
  have ha : 20≤alpha i := by dsimp [alpha]; omega
  simp only [ending] at hn
  omega

theorem ending_strictMono : StrictMono ending := by
  apply strictMono_nat_of_lt_succ
  intro i
  have h := predecessor i
  simp only [ending] at *
  have : 20≤alpha (i+1) := by dsimp [alpha]; omega
  omega

theorem ending_lt_backward_two (i : ℕ) : ending i<backward (i+2) := by
  have h := backward_next (i+1)
  have hp := predecessor i
  have hb : 23≤beta (i+1) := by dsimp [beta]; omega
  have ha : 20≤alpha (i+1) := by dsimp [alpha]; omega
  have he := parity_lt (i+2)
  have hnorm : i+1+1=i+2 := by omega
  rw [hnorm] at h
  simp only [ending] at h
  omega

theorem block_nodup (i : ℕ) : (blockNaturals i).Nodup := by
  have hbc := backward_add_beta i
  have hba := beta_alpha i
  have ha : 20≤alpha i := by dsimp [alpha]; omega
  simp only [blockNaturals,List.nodup_cons,List.mem_cons,List.not_mem_nil,
    or_false,not_or,List.nodup_nil,not_false_eq_true,and_true]
  simp only [ending] at *
  omega

theorem adjacent_blocks_disjoint (i : ℕ) :
    List.Disjoint (blockNaturals i) (blockNaturals (i+1)) := by
  have hbc := backward_add_beta i
  have hbc' := backward_add_beta (i+1)
  have hba := beta_alpha i
  have hba' := beta_alpha (i+1)
  have ha : 20≤alpha i := by dsimp [alpha]; omega
  have ha' : 20≤alpha (i+1) := by dsimp [alpha]; omega
  have hc := predecessor i
  have he := backward_next i
  have hp := parity_succ i
  have hpl := parity_lt i
  have hpl' := parity_lt (i+1)
  rw [List.disjoint_left]
  intro x hx hy
  simp only [blockNaturals,List.mem_cons,List.not_mem_nil,or_false] at hx hy
  simp only [ending] at *
  rcases hx with rfl|rfl|rfl|rfl|rfl <;>
    rcases hy with hy|hy|hy|hy|hy <;> omega

theorem blocks_disjoint {i j : ℕ} (hij : i<j) :
    List.Disjoint (blockNaturals i) (blockNaturals j) := by
  by_cases heq : j=i+1
  · simpa [heq] using adjacent_blocks_disjoint i
  · have hg : i+2≤j := by omega
    have hsep : ending i<backward j :=
      (ending_lt_backward_two i).trans_le (backward_strictMono.monotone hg)
    rw [List.disjoint_left]
    intro x hx hy
    have hb := block_bounds hx
    have hb' := block_bounds hy
    omega

theorem all_blocks_nodup (m : ℕ) : ((List.range m).flatMap blockNaturals).Nodup := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ,List.flatMap_append]
    simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]
    rw [List.nodup_append]
    refine ⟨ih, block_nodup m, ?_⟩
    intro x hx y hy hxy
    subst y
    obtain ⟨i,hi,hx⟩ := List.mem_flatMap.mp hx
    have him : i < m := List.mem_range.mp hi
    exact (List.disjoint_left.mp (blocks_disjoint him)) hx hy

@[simp] theorem vertices_length (n m : ℕ) : (vertices n m).length=5*m+8 := by
  simp [vertices,naturals,initialNaturals,blockNaturals,List.length_flatMap]
  omega

@[simp] theorem vertices_initial (n m : ℕ) :
    vertices n m=explicitPrefix n ++ (List.range m).flatMap (blockVertices n) := by
  simp only [vertices,naturals,List.map_append,List.map_flatMap]
  rfl

/-- The printed expression for the greatest appended representative. -/
theorem ending_formula (i : ℕ) :
    ending i=8*(i+1)^2+36*(i+1)+18+(i+1)/2 := by
  have hf : (i+1)/2=i/2+i%2 := by omega
  simp only [ending,center,beta,parity,hf]
  ring

theorem block_values {n m i x : ℕ} (hsize : (5*m+8)^2 ≤ n)
    (hi : i < m) (hx : x ∈ blockNaturals i) : 0 < x ∧ x < n-3 := by
  have hb := block_bounds hx
  have hl : 15 ≤ backward i := by
    simpa [backward,center,beta,parity] using backward_strictMono.monotone (Nat.zero_le i)
  have hpow : (i+1)^2 ≤ m^2 := Nat.pow_le_pow_left (by omega) 2
  have hdiv := Nat.div_le_self (i+1) 2
  have hend := ending_formula i
  have hn : 3 ≤ n := by nlinarith
  constructor
  · omega
  · have : ending i+3 < n := by nlinarith
    omega

theorem initial_nodup {n : ℕ} (hn : 65 ≤ n) : (initialNaturals n).Nodup := by
  simp [initialNaturals,List.nodup_cons]
  omega

theorem initial_blocks_disjoint {n m : ℕ} (hn : 65 ≤ n)
    (hsize : (5*m+8)^2 ≤ n) :
    List.Disjoint (initialNaturals n) ((List.range m).flatMap blockNaturals) := by
  rw [List.disjoint_left]
  intro x hx hy
  obtain ⟨i,hi,hy⟩ := List.mem_flatMap.mp hy
  have him : i < m := List.mem_range.mp hi
  have hb := block_values hsize him hy
  have hlow : x≠2 ∧ x≠12 ∧ x≠10 ∧ x≠17 ∧ x≠18 := by
    by_cases hi0 : i=0
    · subst i
      simp only [blockNaturals,center,alpha,beta,parity,backward,ending,
        List.mem_cons,List.not_mem_nil,or_false] at hy
      norm_num at hy
      omega
    · have hone : 1 ≤ i := by omega
      have hmin : 58 ≤ backward i := by
        simpa [backward,center,beta,parity] using backward_strictMono.monotone hone
      have hxlow := block_bounds hy
      omega
  simp only [initialNaturals,List.mem_cons,List.not_mem_nil,or_false] at hx
  omega

theorem naturals_nodup {n m : ℕ} (hn : 65 ≤ n) (hsize : (5*m+8)^2 ≤ n) :
    (naturals n m).Nodup := by
  rw [naturals,List.nodup_append]
  exact ⟨initial_nodup hn, all_blocks_nodup m,
    fun _ hx _ hy hxy => (List.disjoint_left.mp (initial_blocks_disjoint hn hsize))
      hx (hxy ▸ hy)⟩

theorem natural_values {n m x : ℕ} (hn : 65 ≤ n) (hsize : (5*m+8)^2 ≤ n)
    (hx : x ∈ naturals n m) : 0 < x ∧ x < n := by
  simp only [naturals,List.mem_append] at hx
  rcases hx with hx|hx
  · simp only [initialNaturals,List.mem_cons,List.not_mem_nil,or_false] at hx
    omega
  · obtain ⟨i,hi,hx⟩ := List.mem_flatMap.mp hx
    have hb := block_values hsize (List.mem_range.mp hi) hx
    omega

theorem vertices_nodup {n m : ℕ} [NeZero n] (hn : 65 ≤ n)
    (hsize : (5*m+8)^2 ≤ n) : (vertices n m).Nodup := by
  rw [vertices]
  apply List.Nodup.map_on _ (naturals_nodup hn hsize)
  intro x hx y hy heq
  have hxl := (natural_values hn hsize hx).2
  have hyl := (natural_values hn hsize hy).2
  have hh := congrArg ZMod.val heq
  simpa only [ZMod.val_natCast_of_lt hxl,ZMod.val_natCast_of_lt hyl] using hh

theorem vertices_nonzero {n m : ℕ} [NeZero n] (hn : 65 ≤ n)
    (hsize : (5*m+8)^2 ≤ n) : ∀ x ∈ vertices n m, x ≠ 0 := by
  intro x hx hzero
  change x ∈ (naturals n m).map Nat.cast at hx
  obtain ⟨y,hy,hxy⟩ := List.mem_map.mp hx
  have hbounds := natural_values hn hsize hy
  have hh := congrArg ZMod.val (hxy.trans hzero)
  rw [ZMod.val_natCast_of_lt hbounds.2,ZMod.val_zero] at hh
  omega

end CorralFormalization.Results.SwitchFamily.Prefix
