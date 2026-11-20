import CorralFormalization.Results.SwitchFamily.Physical.AppendixWords
import CorralFormalization.Results.SwitchFamily.FamilySwitches

/-! The actual h*m adjacent physical site pairs in Appendix A.3. -/

namespace CorralFormalization.Results.SwitchFamily.Physical

open CorralFormalization CorralFormalization.LatinCompletion
open LatinTransfer PhysicalCorral DiversitySymmetry TerraceLift GeneralTiles LatinPrefix
open scoped Classical

abbrev Bit (m h : ℕ) := Fin m × ZMod h

def endpoint {h n m : ℕ} (k : Bit m h) (s : Bool) : ZMod (h*n) :=
  zeroSite h n k.2+((Prefix.center k.1.val+s.toNat : ℕ) : ZMod (h*n))

def sitePair {h n m : ℕ} (k : Bit m h) : ZMod (h*n) × ZMod (h*n) :=
  (endpoint (n:=n) k false,endpoint (n:=n) k true)

@[simp] theorem endpoint_right {h n m : ℕ} (k : Bit m h) :
    endpoint (n:=n) k true=endpoint (n:=n) k false+1 := by
  simp [endpoint]
  ring

theorem center_strictMono : StrictMono Prefix.center := by
  apply strictMono_nat_of_lt_succ
  intro i
  rw [Prefix.center_succ]
  omega

theorem centers_separated {i j : ℕ} (hij : i<j) : Prefix.center i+1<Prefix.center j := by
  have hc := center_strictMono.monotone (by omega : i+1≤j)
  rw [Prefix.center_succ] at hc
  omega

theorem center_value_bounds {n m : ℕ} (hsize : (5*m+8)^2≤n) (i : Fin m) (s : Bool) :
    0<Prefix.center i.val+s.toNat ∧ Prefix.center i.val+s.toNat<n := by
  cases s
  · have h := Prefix.block_values hsize i.isLt
      (show Prefix.center i.val∈Prefix.blockNaturals i.val by simp [Prefix.blockNaturals])
    simpa using And.intro h.1 (by omega : Prefix.center i.val<n)
  · have h := Prefix.block_values hsize i.isLt (show Prefix.center i.val+1∈Prefix.blockNaturals i.val by
      simp [Prefix.blockNaturals])
    simpa only [Bool.toNat_true] using And.intro h.1 (by omega : Prefix.center i.val+1<n)

theorem endpoint_residue {h n m : ℕ} (k : Bit m h) (s : Bool) :
    residueMap h n (endpoint (n:=n) k s)=
      ((Prefix.center k.1.val+s.toNat : ℕ) : ZMod n) := by
  simp [endpoint,map_add,zeroSite_residue,map_natCast]

/-- Disjointness of all physical switch endpoints is derived from their
natural representatives and the phase embedding; it is not an input. -/
theorem endpoint_injective {h n m : ℕ} [NeZero h] [NeZero n] [NeZero (h*n)]
    (hsize : (5*m+8)^2≤n) :
    Function.Injective (fun c : Bit m h × Bool => endpoint (n:=n) c.1 c.2) := by
  rintro ⟨⟨i,q⟩,s⟩ ⟨⟨j,t⟩,u⟩ he
  have hv := congrArg (residueMap h n) he
  simp only [endpoint_residue] at hv
  have hv' := congrArg ZMod.val hv
  rw [ZMod.val_natCast_of_lt (center_value_bounds hsize i s).2,
    ZMod.val_natCast_of_lt (center_value_bounds hsize j u).2] at hv'
  have hs := Bool.toNat_le s
  have hu := Bool.toNat_le u
  have hij : i=j := by
    apply Fin.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with hij|hji
    · have := centers_separated hij
      omega
    · have := centers_separated hji
      omega
  subst j
  have hsu : s=u := by
    cases s <;> cases u <;> simp_all
  subst u
  have hqt : q=t := zeroSite_injective (NeZero.pos n) (add_right_cancel he)
  subst t
  rfl

theorem sitePair_injective {h n m : ℕ} [NeZero h] [NeZero n] [NeZero (h*n)]
    (hsize : (5*m+8)^2≤n) : Function.Injective (sitePair (h:=h) (n:=n) (m:=m)) := by
  intro i j he
  have h := endpoint_injective hsize (a₁:=(i,false)) (a₂:=(j,false)) (congrArg Prod.fst he)
  exact congrArg Prod.fst h

noncomputable def switchLayer {h n m : ℕ} [NeZero h] [NeZero n] [NeZero (h*n)]
    (hsize : (5*m+8)^2≤n) : EndpointRouter.MatchingLayer (ZMod (h*n)) where
  edges := (Finset.univ : Finset (Bit m h)).toList.map (sitePair (n:=n))
  nodup := (Finset.nodup_toList (Finset.univ : Finset (Bit m h))).map
    (sitePair_injective hsize)
  no_loop := by
    intro e he
    obtain ⟨k,_,rfl⟩ := List.mem_map.mp he
    intro heq
    have h := endpoint_injective hsize (a₁:=(k,false)) (a₂:=(k,true)) heq
    exact Bool.false_ne_true (congrArg Prod.snd h)
  separate := by
    intro e he d hd hed
    obtain ⟨k,_,rfl⟩ := List.mem_map.mp he
    obtain ⟨l,_,rfl⟩ := List.mem_map.mp hd
    have hkl : k≠l := by intro h; exact hed (congrArg sitePair h)
    have hdomain : ([(k,false),(k,true),(l,false),(l,true)] : List (Bit m h × Bool)).Nodup := by
      simp [List.nodup_cons,hkl,Ne.symm hkl]
    exact hdomain.map (endpoint_injective hsize)

theorem switchLayer_mem {h n m : ℕ} [NeZero h] [NeZero n] [NeZero (h*n)]
    (hsize : (5*m+8)^2≤n) (k : Bit m h) :
    sitePair (n:=n) k∈(switchLayer hsize).edges := by
  exact List.mem_map.mpr ⟨k,by simp,rfl⟩

theorem switchLayer_length {h n m : ℕ} [NeZero h] [NeZero n] [NeZero (h*n)]
    (hsize : (5*m+8)^2≤n) : (switchLayer (h:=h) hsize).edges.length=h*m := by
  simp [switchLayer,Fintype.card_prod,ZMod.card,Nat.mul_comm]

theorem switchLayer_isolated_iff {h n m : ℕ} [NeZero h] [NeZero n] [NeZero (h*n)]
    (hsize : (5*m+8)^2≤n) (x : ZMod (h*n)) :
    (switchLayer hsize).Isolated x ↔ ∀ (k : Bit m h) (s : Bool),endpoint (n:=n) k s≠x := by
  simp only [EndpointRouter.MatchingLayer.Isolated,EndpointRouter.MatchingLayer.Incident]
  constructor
  · intro hx k s he
    apply hx
    refine ⟨sitePair k,switchLayer_mem hsize k,?_⟩
    cases s
    · exact Or.inl he.symm
    · exact Or.inr he.symm
  · intro hx ⟨e,he,hi⟩
    obtain ⟨k,_,rfl⟩ := List.mem_map.mp he
    rcases hi with hi|hi
    · exact hx k false hi.symm
    · exact hx k true hi.symm

end CorralFormalization.Results.SwitchFamily.Physical
