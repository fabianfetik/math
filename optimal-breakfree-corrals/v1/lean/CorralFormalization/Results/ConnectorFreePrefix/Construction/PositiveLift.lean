import CorralFormalization.Results.ConnectorFreePrefix.Construction.PrefixChain

/-! The three ordinary positive-lift coordinates (L14), together.
The predecessor location is derived from the actual direct-join chain;
the next two locations follow from the actual positive centre-edge gaps. -/

namespace CorralFormalization.LatinCompletion.TerraceCompletion.ConnectorFreePrefix.Construction

open LatinTransfer TerraceLift LatinPrefix LatinPrefixSupply

variable {r n : ℕ} [NeZero r]

/-- All three vertices of every concrete cell occupy the exact locations
printed in L14, with common level `2+r*j+t`. -/
theorem prefixPieces_triple_position (hr : 3 ≤ r) (hn : 200*r*r≤n)
    (suffix : List ℕ) (i : Cell r) (p : ℕ)
    (hp : (i,p) ∈ locatedCells prefixA prefixB (prefixPieces n r suffix)) :
    2*n+10+p=prefixPredecessor i+(2+r*i.1.val+i.2.val)*n ∧
    2*n+10+p+(prefixA i+canonicalSymbol i)=
      prefixCenter i+(2+r*i.1.val+i.2.val)*n ∧
    2*n+10+p+(prefixA i+canonicalSymbol i)+(prefixB i-canonicalSymbol i)=
      prefixSuccessor i+(2+r*i.1.val+i.2.val)*n := by
  have hP := prefixPieces_position hr hn suffix i p hp
  obtain ⟨_,_,hPA,hA,hB,_,_,_,_⟩ :=
    (waleckiCoordinates r).local_gap_geometry hr hn i.1 i.2 ((cyclicLatinSquare r).entry i.1 i.2)
  have hPC : prefixPredecessor i+(prefixA i+canonicalSymbol i)=prefixCenter i := by
    dsimp [prefixPredecessor,prefixA,prefixCenter,canonicalSymbol]
    omega
  have hCN : prefixCenter i+(prefixB i-canonicalSymbol i)=prefixSuccessor i := by
    dsimp [prefixCenter,prefixB,prefixSuccessor,canonicalSymbol]
    have hs := (waleckiCoordinates r).local_gap_geometry hr hn i.1 i.2 ((cyclicLatinSquare r).entry i.1 i.2)
    omega
  exact ⟨hP,by omega,by omega⟩

end CorralFormalization.LatinCompletion.TerraceCompletion.ConnectorFreePrefix.Construction
