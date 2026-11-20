import CorralFormalization.DiversityCompletion.LatinPrefixFrame

namespace CorralFormalization.LatinCompletion.LatinPrefixSupply

open LatinTransfer TerraceLift LatinPrefix

/-- Actual two positive representatives of the connecting edges
`N -> y -> P` when both edges wrap in the residue cycle. -/
def wrapOut (n y N : ℕ) : ℕ := n+y-N
def wrapIn (n y P : ℕ) : ℕ := n+P-y

theorem two_wrap_geometry (n P N y : ℕ)
    (hP : P < y) (hy : y < N) (hN : N < n) :
    0 < wrapOut n y N ∧ wrapOut n y N < n ∧
    0 < wrapIn n y P ∧ wrapIn n y P < n ∧
    N + wrapOut n y N + wrapIn n y P = P+2*n ∧
    (N : ZMod n) + (wrapOut n y N : ℕ) = (y : ZMod n) ∧
    (y : ZMod n) + (wrapIn n y P : ℕ) = (P : ZMod n) := by
  have ho : N + wrapOut n y N = n+y := by dsimp [wrapOut]; omega
  have hi : y + wrapIn n y P = n+P := by dsimp [wrapIn]; omega
  refine ⟨by dsimp [wrapOut]; omega, by dsimp [wrapOut]; omega,
    by dsimp [wrapIn]; omega, by dsimp [wrapIn]; omega, by omega, ?_, ?_⟩
  · have h := congrArg (fun z : ℕ => (z : ZMod n)) ho
    simpa only [Nat.cast_add, ZMod.natCast_self, zero_add] using h
  · have h := congrArg (fun z : ℕ => (z : ZMod n)) hi
    simpa only [Nat.cast_add, ZMod.natCast_self, zero_add] using h

/-- The genuine word-piece chain: a cell is followed by the two explicit
wrap gaps before the next cell, with no connector after the final cell. -/
def cellChain {I : Type*} (n : ℕ) (P N y : I → ℕ) (first : I) :
    List I → List (Piece I)
  | [] => [Piece.cell first]
  | next :: rest => Piece.cell first ::
      Piece.fixed (wrapOut n (y first) (N first)) ::
      Piece.fixed (wrapIn n (y first) (P next)) :: cellChain n P N y next rest

theorem cellChain_cells {I : Type*} (n : ℕ) (P N y : I → ℕ)
    (first : I) (rest : List I) :
    cells (cellChain n P N y first rest) = first :: rest := by
  induction rest generalizing first with
  | nil => rfl
  | cons next rest ih => simpa [cellChain,cells] using congrArg (List.cons first) (ih next)

/-- A parametric positive-lift theorem. Its only geometric inputs are the
literal cell displacement and the ordinary connector ordering. The factor
`2*t` is a conclusion of the actual two-edge connector sums. -/
theorem cellChain_location {I : Type*} (n : ℕ) (A B P N y : I → ℕ)
    (hcell : ∀ i, P i + (A i+B i) = N i)
    (horder : ∀ i j, P j < y i ∧ y i < N i ∧ N i < n)
    (first : I) (rest : List I) (i : I) (p : ℕ)
    (hp : (i,p) ∈ locatedCells A B (cellChain n P N y first rest)) :
    ∃ t : Fin (first :: rest).length,
      (first :: rest)[t.val] = i ∧ P first+p = P i+2*t.val*n := by
  induction rest generalizing first i p with
  | nil =>
    have he : (i,p) = (first,0) := by simpa [cellChain,locatedCells] using hp
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
    exact ⟨⟨0,by simp⟩,rfl,by simp⟩
  | cons next rest ih =>
    simp only [cellChain, locatedCells, List.map_map, Function.comp_def,
      List.mem_cons, List.mem_map] at hp
    rcases hp with he | ⟨⟨j,q⟩,hq,he⟩
    · obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
      exact ⟨⟨0,by simp⟩,rfl,by simp⟩
    · have hji : j=i := congrArg Prod.fst he
      have hqp := congrArg Prod.snd he
      dsimp at hji hqp
      subst j
      obtain ⟨t,hti,ht⟩ := ih next i q hq
      obtain ⟨hP,hy,hN⟩ := horder first next
      have hwrap := (two_wrap_geometry n (P next) (N first) (y first) hP hy hN).2.2.2.2.1
      have hstep : P first+(A first+B first+
          (wrapOut n (y first) (N first)+(wrapIn n (y first) (P next)))) = P next+2*n := by
        rw [← Nat.add_assoc, hcell]
        omega
      refine ⟨⟨t.val+1,by simpa only [List.length_cons] using Nat.succ_lt_succ t.isLt⟩, ?_, ?_⟩
      · simpa using hti
      · rw [← hqp]
        calc
          P first+(A first+B first+(wrapOut n (y first) (N first)+
              (wrapIn n (y first) (P next)+q))) =
              P first+(A first+B first+
                (wrapOut n (y first) (N first)+wrapIn n (y first) (P next)))+q := by omega
          _ = P next+2*n+q := by rw [hstep]
          _ = (P next+q)+2*n := by omega
          _ = (P i+2*t.val*n)+2*n := by rw [ht]
          _ = P i+2*(t.val+1)*n := by ring

/-- Lexicographic connector-prefix order, using the exact finite-product equivalence:
the index of `(j,u)` is `u+r*j`. -/
def lexCells (r : ℕ) : List (Cell r) :=
  List.ofFn (fun t : Fin (r*r) => finProdFinEquiv.symm t)

def firstCell (r : ℕ) [NeZero r] : Cell r :=
  (⟨0,NeZero.pos r⟩, ⟨0,NeZero.pos r⟩)

theorem lexCells_length (r : ℕ) : (lexCells r).length = r*r := by
  simp [lexCells]

theorem lexCells_rank (r : ℕ) (t : ℕ) (ht : t < (lexCells r).length) :
    (finProdFinEquiv ((lexCells r)[t])).val = t := by
  simpa [lexCells, Nat.mul_comm] using Nat.mod_add_div t r

theorem lexCells_perm (r : ℕ) :
    (lexCells r).Perm (Finset.univ : Finset (Cell r)).toList := by
  apply (List.perm_ext_iff_of_nodup
    (List.nodup_ofFn.mpr finProdFinEquiv.symm.injective) (Finset.nodup_toList _)).mpr
  intro i
  simp only [Finset.mem_toList, Finset.mem_univ, iff_true]
  exact List.mem_ofFn.mpr ⟨finProdFinEquiv i, finProdFinEquiv.symm_apply_apply i⟩

theorem lexCells_cons (r : ℕ) [NeZero r] :
    lexCells r = firstCell r :: (lexCells r).tail := by
  have hnon : lexCells r ≠ [] := by
    intro h
    have hlen := lexCells_length r
    rw [h] at hlen
    have hr := NeZero.pos r
    simp only [List.length_nil] at hlen
    nlinarith
  have hhead : (lexCells r).head hnon = firstCell r := by
    rw [List.head_eq_getElem_zero hnon]
    apply finProdFinEquiv.injective
    apply Fin.ext
    rw [lexCells_rank]
    simp [firstCell,finProdFinEquiv]
  exact (hhead ▸ List.cons_head_tail hnon).symm

/-- The connector-prefix bands imply the connector ordering uniformly for
every possible pair of connector-prefix cells. These are ordinary integer inequalities. -/
theorem connectorPrefix_connector_order {r n : ℕ} (hr : 2 ≤ r) (hn : 100*r*r ≤ n)
    (y : Cell r → ℕ) (hy : ∀ i, 30*r*r ≤ y i ∧ y i < 40*r*r)
    (i j : Cell r) :
    predecessor j.1 j.2 < y i ∧ y i < successor i.1 i.2 ∧ successor i.1 i.2 < n := by
  have hsq : r ≤ r*r := by nlinarith
  have hji := j.1.isLt
  have hju := j.2.isLt
  have hii := i.1.isLt
  have hiu := i.2.isLt
  have hmulju := Nat.mul_lt_mul_of_pos_left hju (by omega : 0 < r+1)
  have hmuliu := Nat.mul_lt_mul_of_pos_left hiu (by omega : 0 < r+1)
  have hmulii := Nat.mul_lt_mul_of_pos_left hii (by omega : 0 < r)
  obtain ⟨hylo,hyhi⟩ := hy i
  dsimp [predecessor,successor,centerBase,incomingBase,outgoingBase]
  refine ⟨?_,?_,?_⟩ <;>
    nlinarith [Nat.sub_le (20*r*r+(r+1)*j.2.val) (10*r*r+r*j.1.val)]

theorem connectorPrefix_cell_displacement {r : ℕ} (hr : 2 ≤ r) (i : Cell r) :
    predecessor i.1 i.2 + (cellA i+cellB i) = successor i.1 i.2 := by
  have hii := i.1.isLt
  have hsq : r ≤ r*r := by nlinarith
  have hm := Nat.mul_lt_mul_of_pos_left hii (by omega : 0 < r)
  have hle : incomingBase i.1 ≤ centerBase i.2 := by
    dsimp [incomingBase,centerBase]
    nlinarith
  dsimp [predecessor,successor,cellA,cellB]
  omega

theorem connectorPrefix_predecessor_large {r : ℕ} (hr : 2 ≤ r) (i : Cell r) :
    18 < predecessor i.1 i.2 := by
  have hii := i.1.isLt
  have hsq : r ≤ r*r := by nlinarith
  have hm := Nat.mul_lt_mul_of_pos_left hii (by omega : 0 < r)
  have hle : incomingBase i.1 ≤ centerBase i.2 := by
    dsimp [incomingBase,centerBase]
    nlinarith
  have hsub := Nat.sub_add_cancel hle
  dsimp [predecessor,centerBase,incomingBase]
  dsimp [centerBase,incomingBase] at hsub
  nlinarith

def connectorPrefixChain {r : ℕ} [NeZero r] (n : ℕ) (y : Cell r → ℕ) : List (Piece (Cell r)) :=
  cellChain n (fun i => predecessor i.1 i.2) (fun i => successor i.1 i.2)
    y (firstCell r) (lexCells r).tail

/-- The literal body prefix after the initial calendar reaches residue 10:
`10 -> 17 -> 18 -> P_00`, followed by connector-prefix triples and their connectors. -/
def connectorPrefixGaps {r : ℕ} [NeZero r] (n : ℕ) (y : Cell r → ℕ) : List ℕ :=
  [7,1,predecessor (firstCell r).1 (firstCell r).2-18] ++
    word cellA cellB canonicalSymbol (connectorPrefixChain n y)

def connectorPrefixPieces {r : ℕ} [NeZero r] (n : ℕ) (y : Cell r → ℕ) (suffix : List ℕ) :
    List (Piece (Cell r)) :=
  fixedPieces [7,1,predecessor (firstCell r).1 (firstCell r).2-18] ++
    connectorPrefixChain n y ++ fixedPieces suffix

theorem connectorPrefixPieces_word {r : ℕ} [NeZero r] (n : ℕ) (y : Cell r → ℕ) (suffix : List ℕ) :
    word cellA cellB canonicalSymbol (connectorPrefixPieces n y suffix) = connectorPrefixGaps n y ++ suffix := by
  simp only [connectorPrefixPieces,word_append,word_fixedPieces,connectorPrefixGaps,List.append_assoc]

theorem connectorPrefixPieces_cells {r : ℕ} [NeZero r] (n : ℕ) (y : Cell r → ℕ) (suffix : List ℕ) :
    (cells (connectorPrefixPieces n y suffix)).Perm (Finset.univ : Finset (Cell r)).toList := by
  simpa only [connectorPrefixPieces,cells_append,cells_fixedPieces,List.nil_append,List.append_nil,
    connectorPrefixChain,cellChain_cells,← lexCells_cons] using lexCells_perm r

/-- Concrete predecessor positions from the actual connector-prefix chain. No additional
position, lifted-prefix identity or completed frame is assumed. -/
theorem connectorPrefixPieces_position {r n : ℕ} [NeZero r] (hr : 2 ≤ r) (hn : 100*r*r ≤ n)
    (y : Cell r → ℕ) (hy : ∀ i, 30*r*r ≤ y i ∧ y i < 40*r*r)
    (suffix : List ℕ) (i : Cell r) (p : ℕ)
    (hp : (i,p) ∈ locatedCells cellA cellB (connectorPrefixPieces n y suffix)) :
    2*n+10+p = predecessor i.1 i.2+(2+2*r*i.1.val+2*i.2.val)*n := by
  simp only [connectorPrefixPieces,locatedCells_append,locatedCells_fixedPieces,List.nil_append,
    List.map_nil,List.append_nil,weights_fixedPieces,List.sum_cons,List.sum_nil,
    Nat.add_zero] at hp
  obtain ⟨⟨j,q⟩,hq,he⟩ := List.mem_map.mp hp
  have hji : j=i := congrArg Prod.fst he
  have hqp := congrArg Prod.snd he
  dsimp at hji hqp
  subst j
  obtain ⟨t,hti,ht⟩ := cellChain_location n cellA cellB
    (fun i : Cell r => predecessor i.1 i.2) (fun i => successor i.1 i.2) y
    (connectorPrefix_cell_displacement hr) (connectorPrefix_connector_order hr hn y hy) (firstCell r) (lexCells r).tail i q hq
  have htbound : t.val < (lexCells r).length := by
    exact t.isLt.trans_eq (congrArg List.length (lexCells_cons r).symm)
  have hti' : (lexCells r)[t.val] = i := by
    simpa only [(lexCells_cons r).symm] using hti
  have hrank : t.val = i.2.val+r*i.1.val := by
    have hh := lexCells_rank r t.val htbound
    rw [hti'] at hh
    exact hh.symm
  have hlarge := connectorPrefix_predecessor_large hr (firstCell r)
  calc
    2*n+10+p = predecessor (firstCell r).1 (firstCell r).2+q+2*n := by omega
    _ = (predecessor i.1 i.2+2*t.val*n)+2*n := by rw [ht]
    _ = predecessor i.1 i.2+(2+2*r*i.1.val+2*i.2.val)*n := by rw [hrank]; ring

theorem completed_body_positive {n : ℕ} (T : CompletedTerrace n) (d : ℕ)
    (hd : d ∈ T.body) : 0 < d := by
  have hm : d ∈ TileGapWords.cycle n T.body := by simp [TileGapWords.cycle,hd]
  exact ((fullGapList_mem (n-1) d).mp (T.differences.mem_iff.mp hm)).1

/-- connector-prefix/calendar supplier for the existing frame construction. The only
calendar input says that the completed terrace retains the explicitly
constructed connector-prefix difference prefix and some completion suffix. Connector
existence and completed-terrace existence are not asserted by this definition. -/
def bodyInputOfConnectorPrefix {n r : ℕ} [NeZero r] (T : CompletedTerrace n)
    (hr : 2 ≤ r) (hn : 100*r*r ≤ n) (y : Cell r → ℕ)
    (hy : ∀ i, 30*r*r ≤ y i ∧ y i < 40*r*r) (suffix : List ℕ)
    (hcalendar : T.body = connectorPrefixGaps n y ++ suffix) : BodyInput T r where
  pieces := connectorPrefixPieces n y suffix
  fixed_positive d hd := by
    have hm : d ∈ word cellA cellB canonicalSymbol (connectorPrefixPieces n y suffix) :=
      List.mem_flatMap.mpr ⟨Piece.fixed d,hd,by simp [Piece.gaps]⟩
    rw [connectorPrefixPieces_word, ← hcalendar] at hm
    exact completed_body_positive T d hm
  cells_complete := connectorPrefixPieces_cells n y suffix
  calendar := by rw [connectorPrefixPieces_word,hcalendar]
  position := connectorPrefixPieces_position hr hn y hy suffix

end CorralFormalization.LatinCompletion.LatinPrefixSupply
