import CorralFormalization.EndpointProof.Selector.TwoPairSwitch

/-!
# The three regular six-root flow layouts

Every coordinate below is the actual oriented flow on one of the nine
graph edges in the paired cover construction.  Layout IV (the three-torsion exception) is separate.
No group division, and in particular no division by three, is used.
-/

open scoped BigOperators

namespace EndpointFlow

set_option maxHeartbeats 1500000
set_option maxRecDepth 2048

abbrev Part := Fin 3
abbrev Vertex (G : Type*) := Part × G
abbrev Atom := Sum (Fin 6) (Fin 9 × Bool)

inductive Layout where
  | first | second | third
  deriving DecidableEq

instance : Fintype Layout where
  elems := {.first,.second,.third}
  complete := by intro L; cases L <;> simp

def path (L : Layout) : Fin 9 → Fin 3 :=
  match L with
  | .first | .second => ![0,0,0,1,1,1,2,2,2]
  | .third => ![0,0,0,0,1,1,1,2,2]

def part (L : Layout) : Fin 9 → Part :=
  match L with
  | .first => ![1,2,1,2,0,2,0,1,0]
  | .second => ![1,2,0,2,0,1,0,1,2]
  | .third => ![1,2,0,1,2,1,0,0,2]

def rootPart (L : Layout) : Fin 6 → Part :=
  match L with
  | .first => ![0,0,1,1,2,2]
  | .second => ![0,1,1,2,2,0]
  | .third => ![0,1,2,0,2,1]

def incoming (L : Layout) : Fin 6 → Fin 9 :=
  match L with
  | .first | .second => ![0,1,3,4,6,7]
  | .third => ![0,1,2,4,5,7]

def outgoing (L : Layout) : Fin 6 → Fin 9 :=
  match L with
  | .first | .second => ![1,2,4,5,7,8]
  | .third => ![1,2,3,5,6,8]

def initial (L : Layout) : Fin 3 → Fin 9 :=
  match L with
  | .first | .second => ![0,3,6]
  | .third => ![0,4,7]

def terminal (L : Layout) : Fin 3 → Fin 9 :=
  match L with
  | .first | .second => ![2,5,8]
  | .third => ![3,6,8]

def nodeAtoms (L : Layout) (k : Fin 7) : Finset Atom :=
  if h : k.val < 6 then
    let i : Fin 6 := ⟨k.val,h⟩
    {Sum.inl i, Sum.inr (incoming L i,true), Sum.inr (outgoing L i,false)}
  else Finset.univ.image (fun p : Fin 3 ↦ Sum.inr (terminal L p,true))

def outputAtoms (L : Layout) : Finset Atom :=
  Finset.univ.image (fun p : Fin 3 ↦ Sum.inr (initial L p,false))

theorem nodeAtoms_disjoint (L : Layout) :
    Pairwise (fun i j ↦ Disjoint (nodeAtoms L i) (nodeAtoms L j)) := by
  change ∀ i j : Fin 7, i ≠ j → Disjoint (nodeAtoms L i) (nodeAtoms L j)
  cases L <;> decide

theorem nodeAtoms_disjoint_outputAtoms (L : Layout) (i : Fin 7) :
    Disjoint (nodeAtoms L i) (outputAtoms L) := by
  cases L <;> fin_cases i <;> decide

theorem nodeAtoms_cover (L : Layout) :
    Finset.univ.biUnion (nodeAtoms L) ∪ outputAtoms L = Finset.univ := by
  cases L <;> decide

theorem outputAtoms_card (L : Layout) : (outputAtoms L).card = 3 := by
  cases L <;> decide

theorem part_count (L : Layout) (p : Part) :
    (Finset.univ.filter (fun j ↦ part L j = p)).card = 3 := by
  cases L <;> fin_cases p <;> decide

section Coordinates

variable {G : Type*} [CommRing G] [DecidableEq G]

def rootSum (r : Fin 6 → G) : G := ∑ i, r i

def base (s : G) (p : Fin 3) (xy : G × G) : G := ![xy.1,xy.2,s-xy.1-xy.2] p

def offset (L : Layout) (r : Fin 6 → G) : Fin 9 → G :=
  match L with
  | .first | .second => ![0,r 0,r 0+r 1,0,r 2,r 2+r 3,0,r 4,r 4+r 5]
  | .third => ![0,r 0,r 0+r 1,r 0+r 1+r 2,0,r 3,r 3+r 4,0,r 5]

def flow (L : Layout) (r : Fin 6 → G) (xy : G × G) (j : Fin 9) : G :=
  base (rootSum r) (path L j) xy - offset L r j

def rootVertex (L : Layout) (r : Fin 6 → G) (i : Fin 6) : Vertex G :=
  (rootPart L i,r i)

def signedFlow (L : Layout) (r : Fin 6 → G) (xy : G × G)
    (jb : Fin 9 × Bool) : G :=
  if jb.2 then -flow L r xy jb.1 else flow L r xy jb.1

def newVertex (L : Layout) (r : Fin 6 → G) (xy : G × G)
    (jb : Fin 9 × Bool) : Vertex G := (part L jb.1,signedFlow L r xy jb)

def atomVertex (L : Layout) (r : Fin 6 → G) (xy : G × G) : Atom → Vertex G
  | Sum.inl i => rootVertex L r i
  | Sum.inr jb => newVertex L r xy jb

def roots (L : Layout) (r : Fin 6 → G) : Finset (Vertex G) :=
  Finset.univ.image (rootVertex L r)

def augmentation (L : Layout) (r : Fin 6 → G) (xy : G × G) : Finset (Vertex G) :=
  Finset.univ.image (newVertex L r xy)

def outputs (L : Layout) (r : Fin 6 → G) (xy : G × G) : Finset (Vertex G) :=
  (outputAtoms L).image (atomVertex L r xy)

def state (L : Layout) (r : Fin 6 → G) (xy : G × G) (i : Fin 7) :
    Finset (Vertex G) := (nodeAtoms L i).image (atomVertex L r xy)

def orbitSupport (L : Layout) (r : Fin 6 → G) (xy : G × G) : Finset G :=
  Finset.univ.image (signedFlow L r xy)

def rootSupport (r : Fin 6 → G) : Finset G :=
  Finset.univ.image (fun ib : Fin 6 × Bool ↦ if ib.2 then -r ib.1 else r ib.1)

def RootLegal (L : Layout) (r : Fin 6 → G) : Prop :=
  (∀ i, r i ≠ 0) ∧ Function.Injective (rootVertex L r)

def OffsetDistinct (L : Layout) (r : Fin 6 → G) : Prop :=
  ∀ i j, i ≠ j → path L i = path L j → offset L r i ≠ offset L r j

def Valid (L : Layout) (r : Fin 6 → G) (xy : G × G) : Prop :=
  (∀ j, flow L r xy j ≠ 0) ∧
  (∀ i j, i ≠ j → flow L r xy i ≠ flow L r xy j ∧
    flow L r xy i ≠ -flow L r xy j) ∧
  Disjoint (orbitSupport L r xy) (rootSupport r)

@[simp] theorem mem_orbitSupport (L : Layout) (r : Fin 6 → G) (xy : G × G) (x : G) :
    x ∈ orbitSupport L r xy ↔ ∃ j, x = flow L r xy j ∨ x = -flow L r xy j := by
  simp only [orbitSupport,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨⟨j,b⟩,h⟩
    cases b
    · exact ⟨j,Or.inl (by simpa [signedFlow] using h.symm)⟩
    · exact ⟨j,Or.inr (by simpa [signedFlow] using h.symm)⟩
  · rintro ⟨j,h|h⟩
    · exact ⟨(j,false),by simpa [signedFlow] using h.symm⟩
    · exact ⟨(j,true),by simpa [signedFlow] using h.symm⟩

@[simp] theorem flow_mem_orbitSupport (L : Layout) (r : Fin 6 → G)
    (xy : G × G) (j : Fin 9) : flow L r xy j ∈ orbitSupport L r xy := by
  exact Finset.mem_image.mpr ⟨(j,false),Finset.mem_univ _,rfl⟩

theorem orbitSupport_card_le (L : Layout) (r : Fin 6 → G) (xy : G × G) :
    (orbitSupport L r xy).card ≤ 18 :=
  Finset.card_image_le.trans (by simp)

theorem rootSupport_mem (r : Fin 6 → G) (i : Fin 6) : r i ∈ rootSupport r := by
  exact Finset.mem_image.mpr ⟨(i,false),Finset.mem_univ _,rfl⟩

theorem flow_step (L : Layout) (r : Fin 6 → G) (xy : G × G) (i : Fin 6) :
    -flow L r xy (incoming L i) + flow L r xy (outgoing L i) + r i = 0 := by
  cases L <;> fin_cases i <;> simp [flow,incoming,outgoing,path,offset,base] <;> ring

theorem terminal_sum (L : Layout) (r : Fin 6 → G) (xy : G × G) :
    (∑ p, -flow L r xy (terminal L p)) = 0 := by
  cases L <;> simp [flow,terminal,path,offset,base,rootSum,Fin.sum_univ_succ] <;> ring

theorem output_sum (L : Layout) (r : Fin 6 → G) (xy : G × G) :
    (∑ p, flow L r xy (initial L p)) = rootSum r := by
  cases L <;> simp [flow,initial,path,offset,base,Fin.sum_univ_succ] <;> ring

end Coordinates

end EndpointFlow
