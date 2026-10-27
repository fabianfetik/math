import Pinwheel.Basic

/-! Literal catalogue from the R021 finite-cover certificate.

The order of every vector is the order in the frozen JSON evidence.
No generated declaration asserts a coverage fact; these definitions
only expose the words, caps, stream cycles, and load rows to the proof.
-/

namespace RealPinwheel
namespace Catalogue

def words : Fin 84 → List (Fin 5)
  | 0 => [0, 0, 1, 0, 0, 4, 0, 2, 0, 1, 0, 0, 3, 0, 0, 1, 0, 2]
  | 1 => [0, 0, 0, 3, 0, 2, 0, 1, 0, 0, 4, 0, 0, 3, 0, 2, 0, 1]
  | 2 => [0, 0, 1, 0, 2, 0, 0, 3, 0, 1, 0, 4, 0, 0, 2, 0, 1, 0, 3]
  | 3 => [0, 0, 1, 0, 2, 0, 3, 0, 1, 0, 0, 4, 0, 2, 0, 1, 0, 3]
  | 4 => [0, 0, 2, 0, 1, 0, 0, 2, 0, 1, 0, 0, 2, 0, 1, 0, 3, 0, 2, 0, 1, 0, 0, 4, 0, 1, 0, 2, 0, 1, 0, 0, 2, 0, 1, 0, 0, 3, 0, 1, 0, 2, 0, 1]
  | 5 => [0, 0, 0, 1, 0, 2, 0, 1, 0, 0, 3, 0, 1, 0, 2, 0, 1, 0, 0, 4, 0, 1, 0, 2, 0, 3, 0, 1]
  | 6 => [0, 0, 1, 0, 2, 0, 4, 0, 1, 0, 3, 0, 2, 0, 1]
  | 7 => [0, 0, 2, 0, 1, 0, 0, 2, 0, 1, 0, 3, 0, 2, 0, 1, 0, 0, 2, 0, 1, 0, 4, 0, 2, 0, 1, 0, 3, 0, 2, 0, 1]
  | 8 => [0, 0, 0, 1, 0, 3, 0, 2, 0, 1, 0, 4, 0, 1, 0, 3, 0, 2, 0, 1]
  | 9 => [0, 0, 2, 0, 3, 0, 1, 0, 2, 0, 4, 0, 1, 0, 3, 0, 2, 0, 1]
  | 10 => [0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1]
  | 11 => [0, 1, 0, 2, 0, 3, 0, 1, 0, 2, 0, 4, 0, 1, 0, 3, 0, 2]
  | 12 => [0, 0, 1, 0, 2, 0, 1, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1, 0, 3, 1]
  | 13 => [0, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 1]
  | 14 => [0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 2, 1, 0, 0, 4, 0, 2, 1, 0, 0, 3, 0, 1, 2]
  | 15 => [0, 0, 1, 0, 1, 0, 2, 0, 1, 0, 3, 1, 0, 0, 1, 0, 2, 0, 1, 0, 4, 1, 0, 0, 1, 0, 2, 0, 1, 3, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 2, 1]
  | 16 => [0, 1, 0, 2, 0, 3, 0, 1, 0, 2, 0, 4, 0, 1, 3, 0, 2]
  | 17 => [0, 1, 0, 3, 0, 2, 0, 1, 4, 0, 3, 0, 2]
  | 18 => [0, 0, 1, 0, 3, 1, 0, 2, 0, 1, 0, 1, 0, 4, 1, 0, 2, 0, 1, 0, 1, 0, 3, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 1]
  | 19 => [0, 0, 1, 0, 1, 0, 3, 1, 0, 2, 0, 1, 0, 1, 0, 4, 1, 0, 2, 0, 1, 0, 3, 1, 0, 0, 1, 0, 2, 1]
  | 20 => [0, 1, 0, 2, 0, 1, 4, 0, 1, 0, 3, 0, 1, 2, 0, 1, 0, 3]
  | 21 => [0, 1, 0, 2, 0, 1, 0, 3, 0, 2, 1, 0, 4, 0, 1, 0, 2, 3]
  | 22 => [0, 1, 0, 2, 0, 3, 1, 0, 4, 0, 2, 0, 1, 3, 0, 2, 0, 1, 0, 3, 0, 1, 2, 0, 3, 0, 1, 0, 2, 3]
  | 23 => [0, 1, 0, 1, 0, 2, 1, 0, 1, 0, 1, 0, 2, 1, 0, 1, 0, 3, 1, 0, 2, 0, 1, 0, 1, 0, 2, 1, 0, 4, 0, 1, 0, 2, 1, 0, 1, 0, 3, 1, 0, 2]
  | 24 => [0, 1, 0, 2, 0, 1, 0, 3, 0, 2, 1, 0, 1, 0, 2, 0, 1, 0, 3, 0, 2, 1, 0, 4, 0, 1, 2, 0, 1, 0, 3, 0, 2, 1]
  | 25 => [0, 1, 0, 3, 1, 0, 2, 0, 1, 0, 3, 1, 0, 2, 0, 1, 0, 4, 1, 0, 3, 0, 1, 2]
  | 26 => [0, 1, 2, 0, 3, 0, 1, 4, 0, 2, 0, 1, 3, 0, 4]
  | 27 => [0, 1, 2, 0, 3, 0, 1, 2, 0, 3, 0, 1, 2, 0, 3, 0, 1, 2, 0, 4, 0, 3, 1, 0, 2, 0, 1, 3, 0, 2, 0, 1, 3, 0, 2, 0, 1, 3, 0, 2, 0, 1, 3, 0, 4, 0, 2, 1, 0, 3]
  | 28 => [0, 1, 0, 1, 0, 3, 1, 0, 2, 1, 0, 4, 0, 1, 0, 3, 1, 0, 2, 1]
  | 29 => [0, 1, 0, 2, 1, 0, 1, 0, 2, 1, 0, 3, 1, 0, 2, 0, 1, 0, 2, 1, 0, 4, 1, 0, 2, 0, 1, 0, 2, 1, 0, 3, 1, 0, 2]
  | 30 => [0, 1, 0, 1, 2, 0, 3, 1, 0, 4, 0, 1, 2, 0, 1, 0, 3, 1, 0, 2]
  | 31 => [0, 1, 0, 2, 1, 0, 4, 0, 1, 2, 0, 3, 1, 0, 2]
  | 32 => [0, 1, 0, 2, 0, 1, 3, 0, 4, 1, 0, 2, 0, 1, 3]
  | 33 => [0, 1, 0, 3, 0, 1, 2, 0, 4, 1, 0, 3, 0, 2, 1, 0, 3, 0, 1, 2]
  | 34 => [0, 1, 0, 1, 0, 2, 1, 0, 1, 0, 2, 1, 0, 3, 1, 0, 2, 0, 1, 0, 1, 0, 2, 1, 0, 4, 1, 0, 2, 0, 1, 3, 0, 1, 0, 2, 1, 0, 1, 0, 2, 1, 0, 1, 0, 2, 1, 0, 3, 1, 0, 2]
  | 35 => [0, 1, 2, 0, 4, 1, 0, 3, 0, 2, 1, 0, 3]
  | 36 => [0, 1, 0, 2, 0, 1, 2, 0, 1, 0, 2, 0, 1, 2, 0, 3, 1, 0, 2, 0, 1, 2, 0, 4, 1, 0, 2, 0, 1, 2, 0, 1, 0, 2, 0, 1, 2, 0, 3, 1, 0, 2, 0, 1, 2]
  | 37 => [0, 1, 0, 2, 0, 1, 2, 0, 3, 1, 0, 2, 0, 1, 2, 0, 1, 0, 2, 0, 1, 2, 0, 3, 1, 0, 2, 0, 1, 2, 0, 4, 1, 0, 2, 0, 1, 2, 0, 3, 1, 0, 2, 0, 1, 2]
  | 38 => [0, 1, 0, 3, 1, 0, 2, 1, 0, 1, 0, 3, 1, 0, 2, 1, 0, 1, 0, 3, 1, 0, 2, 1, 0, 4, 0, 1, 3, 0, 1, 2]
  | 39 => [0, 1, 0, 2, 1, 0, 1, 0, 2, 1, 0, 3, 1, 0, 2, 1, 0, 4, 0, 1, 2, 0, 1, 0, 2, 1, 0, 3, 1, 0, 2, 1]
  | 40 => [0, 1, 0, 2, 1, 0, 2, 0, 1, 3, 0, 2, 1, 0, 4, 2, 0, 1, 0, 2, 1, 0, 3, 2]
  | 41 => [0, 1, 0, 2, 1, 0, 3, 0, 1, 2, 0, 4, 1, 0, 3, 2]
  | 42 => [0, 1, 2, 0, 1, 3, 0, 2, 1, 0, 4, 0, 1, 2, 0, 3, 1, 0, 2, 1, 0, 3]
  | 43 => [0, 1, 2, 0, 3, 1, 0, 2, 0, 3, 1, 0, 4, 2, 0, 1, 3, 0, 2, 1, 0, 3]
  | 44 => [0, 1, 0, 2, 3, 0, 1, 2, 0, 3, 1, 0, 2, 0, 1, 3, 0, 2, 1, 0, 3, 2, 0, 1, 0, 2, 3, 0, 1, 2, 0, 4, 1, 0, 3, 2]
  | 45 => [0, 1, 2, 0, 1, 3, 0, 1, 4, 0, 2, 1, 0, 3]
  | 46 => [0, 1, 3, 0, 2, 1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 0, 2, 0, 1, 4, 0, 2, 1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 0, 2]
  | 47 => [0, 1, 0, 2, 1, 0, 1, 2, 0, 1, 3, 0, 2, 1, 0, 4, 1, 0, 2, 1, 0, 1, 2, 0, 1, 0, 2, 1, 0, 3, 1, 0, 2, 1, 0, 1, 2]
  | 48 => [0, 1, 3, 0, 2, 1, 0, 3, 4, 0, 2, 1, 0, 3, 2]
  | 49 => [0, 0, 1, 2, 0, 1, 2, 0, 3, 1, 0, 2, 1, 0, 2, 1, 4, 0, 2, 1, 0, 0, 1, 2, 3, 0, 1, 2, 0, 1, 0, 2, 1, 0, 2, 1, 0, 3, 2, 1, 0, 0, 1, 2, 0, 1, 4, 2, 0, 1, 0, 2, 1, 3, 0, 2, 1, 0, 2, 1]
  | 50 => [0, 1, 2, 0, 1, 2, 0, 3, 1, 0, 2, 1, 0, 4, 2, 1, 0, 2, 0, 1, 3, 0, 2, 1, 0, 2, 1, 0, 2, 1, 0, 3, 2, 1, 0, 2]
  | 51 => [0, 1, 0, 2, 3, 1, 0, 2, 0, 1, 4, 0, 2, 1, 3, 0, 1, 2]
  | 52 => [0, 1, 0, 2, 1, 0, 3, 2, 1, 0, 4, 0, 1, 2, 3]
  | 53 => [0, 1, 2, 0, 3, 1, 0, 2, 0, 1, 3, 0, 2, 1, 0, 3, 2, 1, 0, 4, 0, 2, 1, 3]
  | 54 => [0, 1, 0, 3, 2, 1, 0, 1, 2, 0, 3, 1, 0, 2, 0, 1, 3, 0, 2, 1, 0, 3, 1, 2, 0, 4, 1, 0, 3, 2]
  | 55 => [0, 1, 2, 0, 4, 3, 1, 0, 2, 0, 1, 3, 0, 4, 2, 1, 0, 3]
  | 56 => [0, 1, 0, 3, 2, 0, 1, 4, 0, 2, 3, 1, 0, 2, 0, 1, 3, 0, 2, 4, 1, 0, 3, 2]
  | 57 => [0, 1, 2, 0, 3, 1, 0, 2, 3, 0, 1, 2, 0, 3, 1, 0, 2, 3, 0, 1, 4, 2, 0, 3, 1, 0, 2, 3]
  | 58 => [0, 1, 2, 0, 1, 2, 0, 3, 1, 0, 2, 4, 1, 0, 2, 3]
  | 59 => [0, 1, 2, 0, 1, 3, 0, 2, 1, 0, 1, 3, 2, 0, 1, 4, 0, 1, 2, 3]
  | 60 => [0, 1, 2, 0, 3, 1, 0, 4, 2, 1, 0, 3, 1, 0, 2, 3, 1, 0, 4, 2, 0, 1, 3]
  | 61 => [0, 1, 2, 0, 3, 1, 0, 2, 1, 3, 0, 4, 1, 2, 0, 3, 1, 0, 2, 1, 3]
  | 62 => [0, 1, 2, 0, 1, 3, 0, 2, 1, 4, 0, 3, 2, 1, 0, 2, 1, 0, 3, 2, 1, 0, 2, 3]
  | 63 => [0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 4, 2, 0, 3, 1, 0, 2, 3]
  | 64 => [0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 4, 2, 0, 3, 1, 0, 2, 1, 3]
  | 65 => [0, 2, 3, 1, 0, 2, 4, 1, 0, 3, 2, 1]
  | 66 => [0, 0, 0, 1, 0, 2, 0, 0, 1, 0, 1, 0, 2, 0, 0, 1, 0, 0, 2, 0, 1, 0, 0, 2, 0, 1, 0, 0, 2, 0, 1, 0, 0, 1, 0, 2, 0, 0, 1, 0, 2, 0, 3, 0, 1, 0, 0, 2, 0, 1, 0, 0, 0, 1, 0, 2, 0, 0, 1, 0, 1, 0, 2, 0, 0, 1, 0, 0, 2, 0, 1, 0, 0, 2, 0, 1, 0, 0, 2, 0, 1, 0, 0, 1, 0, 2, 0, 0, 1, 0, 2, 0, 4, 0, 1, 0, 0, 2, 0, 1]
  | 67 => [0, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1]
  | 68 => [0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 0, 1, 0, 2, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1]
  | 69 => [0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 4]
  | 70 => [0, 0, 1, 2, 0, 1, 0, 1, 2, 0, 1, 0, 2, 0, 1, 2, 0, 1, 2, 0, 1, 3, 0, 2, 1, 0, 0, 1, 2, 0, 1, 0, 1, 2, 0, 1, 0, 2, 0, 1, 2, 0, 1, 2, 0, 1, 4, 0, 2, 1]
  | 71 => [0, 1, 0, 1, 0, 2, 0, 1, 3, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 4, 0, 1, 0, 2]
  | 72 => [0, 1, 0, 2, 0, 1, 0, 3, 4, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 4, 0, 3]
  | 73 => [0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 3, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 4]
  | 74 => [0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 4, 0, 1, 0, 2]
  | 75 => [0, 0, 1, 2, 0, 1, 0, 1, 0, 2, 1, 0, 0, 2, 1, 0, 3, 0, 1, 2, 0, 1, 0, 2, 1, 0, 0, 1, 2, 0, 1, 0, 1, 0, 2, 1, 0, 0, 2, 1, 0, 4, 0, 1, 2, 0, 1, 0, 2, 1]
  | 76 => [0, 0, 1, 0, 1, 0, 0, 3, 0, 1, 0, 0, 1, 0, 2, 0, 0, 1, 0, 1, 0, 0, 4, 0, 1, 0, 0, 1, 0, 2]
  | 77 => [0, 0, 1, 0, 2, 0, 1, 0, 1, 0, 3, 0, 1, 0, 0, 1, 0, 2, 0, 1, 0, 1, 0, 4, 0, 1]
  | 78 => [0, 1, 0, 2, 1, 0, 1, 2, 0, 3, 1, 0, 2, 0, 1, 0, 2, 1, 0, 1, 2, 0, 4, 1, 0, 2]
  | 79 => [0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 4]
  | 80 => [0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 4]
  | 81 => [0, 0, 1, 0, 3, 0, 2, 0, 0, 1, 0, 4]
  | 82 => [0, 0, 2, 0, 1, 0, 0, 2, 0, 3, 0, 1, 0, 0, 2, 0, 1, 0, 0, 2, 0, 4, 0, 1]
  | 83 => [0, 0, 1, 0, 1, 0, 0, 1, 0, 2, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 3, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 2, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 4, 0, 1]
  | _ => []

def wordCaps : Fin 84 → Fin 5 → RateCap
  | 0 => fun
      | 0 => { bound := (3/5 : ℚ), closed := false }
      | 1 => { bound := (1/6 : ℚ), closed := false }
      | 2 => { bound := (1/9 : ℚ), closed := false }
      | 3 => { bound := (1/18 : ℚ), closed := true }
      | 4 => { bound := (1/18 : ℚ), closed := true }
  | 1 => fun
      | 0 => { bound := (3/5 : ℚ), closed := false }
      | 1 => { bound := (1/9 : ℚ), closed := false }
      | 2 => { bound := (1/9 : ℚ), closed := false }
      | 3 => { bound := (1/9 : ℚ), closed := false }
      | 4 => { bound := (1/18 : ℚ), closed := true }
  | 2 => fun
      | 0 => { bound := (11/19 : ℚ), closed := true }
      | 1 => { bound := (2/13 : ℚ), closed := false }
      | 2 => { bound := (2/19 : ℚ), closed := true }
      | 3 => { bound := (1/10 : ℚ), closed := false }
      | 4 => { bound := (1/19 : ℚ), closed := true }
  | 3 => fun
      | 0 => { bound := (5/9 : ℚ), closed := true }
      | 1 => { bound := (1/6 : ℚ), closed := false }
      | 2 => { bound := (1/9 : ℚ), closed := true }
      | 3 => { bound := (1/10 : ℚ), closed := false }
      | 4 => { bound := (1/18 : ℚ), closed := true }
  | 4 => fun
      | 0 => { bound := (5/9 : ℚ), closed := false }
      | 1 => { bound := (1/5 : ℚ), closed := false }
      | 2 => { bound := (1/8 : ℚ), closed := false }
      | 3 => { bound := (1/22 : ℚ), closed := false }
      | 4 => { bound := (1/44 : ℚ), closed := true }
  | 5 => fun
      | 0 => { bound := (5/9 : ℚ), closed := false }
      | 1 => { bound := (1/5 : ℚ), closed := false }
      | 2 => { bound := (3/28 : ℚ), closed := true }
      | 3 => { bound := (1/14 : ℚ), closed := false }
      | 4 => { bound := (1/28 : ℚ), closed := true }
  | 6 => fun
      | 0 => { bound := (8/15 : ℚ), closed := true }
      | 1 => { bound := (2/11 : ℚ), closed := false }
      | 2 => { bound := (2/15 : ℚ), closed := true }
      | 3 => { bound := (1/15 : ℚ), closed := true }
      | 4 => { bound := (1/15 : ℚ), closed := true }
  | 7 => fun
      | 0 => { bound := (8/15 : ℚ), closed := false }
      | 1 => { bound := (2/11 : ℚ), closed := false }
      | 2 => { bound := (2/11 : ℚ), closed := false }
      | 3 => { bound := (2/33 : ℚ), closed := true }
      | 4 => { bound := (1/33 : ℚ), closed := true }
  | 8 => fun
      | 0 => { bound := (9/17 : ℚ), closed := false }
      | 1 => { bound := (1/5 : ℚ), closed := false }
      | 2 => { bound := (1/10 : ℚ), closed := true }
      | 3 => { bound := (1/10 : ℚ), closed := true }
      | 4 => { bound := (1/20 : ℚ), closed := true }
  | 9 => fun
      | 0 => { bound := (10/19 : ℚ), closed := true }
      | 1 => { bound := (3/19 : ℚ), closed := true }
      | 2 => { bound := (1/7 : ℚ), closed := false }
      | 3 => { bound := (2/19 : ℚ), closed := true }
      | 4 => { bound := (1/19 : ℚ), closed := true }
  | 10 => fun
      | 0 => { bound := (13/25 : ℚ), closed := false }
      | 1 => { bound := (6/23 : ℚ), closed := false }
      | 2 => { bound := (1/11 : ℚ), closed := false }
      | 3 => { bound := (2/29 : ℚ), closed := false }
      | 4 => { bound := (1/42 : ℚ), closed := true }
  | 11 => fun
      | 0 => { bound := (1/2 : ℚ), closed := true }
      | 1 => { bound := (1/6 : ℚ), closed := true }
      | 2 => { bound := (1/7 : ℚ), closed := false }
      | 3 => { bound := (1/9 : ℚ), closed := false }
      | 4 => { bound := (1/18 : ℚ), closed := true }
  | 12 => fun
      | 0 => { bound := (1/2 : ℚ), closed := false }
      | 1 => { bound := (2/7 : ℚ), closed := false }
      | 2 => { bound := (1/10 : ℚ), closed := true }
      | 3 => { bound := (1/20 : ℚ), closed := true }
      | 4 => { bound := (1/20 : ℚ), closed := true }
  | 13 => fun
      | 0 => { bound := (1/2 : ℚ), closed := false }
      | 1 => { bound := (3/11 : ℚ), closed := false }
      | 2 => { bound := (1/9 : ℚ), closed := false }
      | 3 => { bound := (1/18 : ℚ), closed := true }
      | 4 => { bound := (1/18 : ℚ), closed := true }
  | 14 => fun
      | 0 => { bound := (1/2 : ℚ), closed := false }
      | 1 => { bound := (1/5 : ℚ), closed := false }
      | 2 => { bound := (1/6 : ℚ), closed := false }
      | 3 => { bound := (1/12 : ℚ), closed := true }
      | 4 => { bound := (1/24 : ℚ), closed := true }
  | 15 => fun
      | 0 => { bound := (10/21 : ℚ), closed := false }
      | 1 => { bound := (7/23 : ℚ), closed := false }
      | 2 => { bound := (1/11 : ℚ), closed := false }
      | 3 => { bound := (1/18 : ℚ), closed := false }
      | 4 => { bound := (1/49 : ℚ), closed := true }
  | 16 => fun
      | 0 => { bound := (8/17 : ℚ), closed := true }
      | 1 => { bound := (3/17 : ℚ), closed := true }
      | 2 => { bound := (1/6 : ℚ), closed := false }
      | 3 => { bound := (2/17 : ℚ), closed := true }
      | 4 => { bound := (1/17 : ℚ), closed := true }
  | 17 => fun
      | 0 => { bound := (6/13 : ℚ), closed := true }
      | 1 => { bound := (2/13 : ℚ), closed := true }
      | 2 => { bound := (2/13 : ℚ), closed := true }
      | 3 => { bound := (2/13 : ℚ), closed := true }
      | 4 => { bound := (1/13 : ℚ), closed := true }
  | 18 => fun
      | 0 => { bound := (9/20 : ℚ), closed := false }
      | 1 => { bound := (1/3 : ℚ), closed := false }
      | 2 => { bound := (4/35 : ℚ), closed := true }
      | 3 => { bound := (2/35 : ℚ), closed := true }
      | 4 => { bound := (1/35 : ℚ), closed := true }
  | 19 => fun
      | 0 => { bound := (4/9 : ℚ), closed := false }
      | 1 => { bound := (1/3 : ℚ), closed := false }
      | 2 => { bound := (1/10 : ℚ), closed := false }
      | 3 => { bound := (1/15 : ℚ), closed := false }
      | 4 => { bound := (1/30 : ℚ), closed := true }
  | 20 => fun
      | 0 => { bound := (4/9 : ℚ), closed := false }
      | 1 => { bound := (5/18 : ℚ), closed := true }
      | 2 => { bound := (1/9 : ℚ), closed := false }
      | 3 => { bound := (1/10 : ℚ), closed := false }
      | 4 => { bound := (1/18 : ℚ), closed := true }
  | 21 => fun
      | 0 => { bound := (4/9 : ℚ), closed := false }
      | 1 => { bound := (2/9 : ℚ), closed := true }
      | 2 => { bound := (1/6 : ℚ), closed := false }
      | 3 => { bound := (1/9 : ℚ), closed := false }
      | 4 => { bound := (1/18 : ℚ), closed := true }
  | 22 => fun
      | 0 => { bound := (13/30 : ℚ), closed := true }
      | 1 => { bound := (1/5 : ℚ), closed := false }
      | 2 => { bound := (1/6 : ℚ), closed := false }
      | 3 => { bound := (1/7 : ℚ), closed := false }
      | 4 => { bound := (1/30 : ℚ), closed := true }
  | 23 => fun
      | 0 => { bound := (3/7 : ℚ), closed := false }
      | 1 => { bound := (1/3 : ℚ), closed := false }
      | 2 => { bound := (1/7 : ℚ), closed := false }
      | 3 => { bound := (1/21 : ℚ), closed := true }
      | 4 => { bound := (1/42 : ℚ), closed := true }
  | 24 => fun
      | 0 => { bound := (3/7 : ℚ), closed := false }
      | 1 => { bound := (1/4 : ℚ), closed := false }
      | 2 => { bound := (3/17 : ℚ), closed := false }
      | 3 => { bound := (3/34 : ℚ), closed := true }
      | 4 => { bound := (1/34 : ℚ), closed := true }
  | 25 => fun
      | 0 => { bound := (5/12 : ℚ), closed := false }
      | 1 => { bound := (7/24 : ℚ), closed := true }
      | 2 => { bound := (1/9 : ℚ), closed := false }
      | 3 => { bound := (1/9 : ℚ), closed := false }
      | 4 => { bound := (1/24 : ℚ), closed := true }
  | 26 => fun
      | 0 => { bound := (2/5 : ℚ), closed := true }
      | 1 => { bound := (1/5 : ℚ), closed := true }
      | 2 => { bound := (2/15 : ℚ), closed := true }
      | 3 => { bound := (2/15 : ℚ), closed := true }
      | 4 => { bound := (2/15 : ℚ), closed := true }
  | 27 => fun
      | 0 => { bound := (2/5 : ℚ), closed := true }
      | 1 => { bound := (1/5 : ℚ), closed := false }
      | 2 => { bound := (1/6 : ℚ), closed := false }
      | 3 => { bound := (1/6 : ℚ), closed := false }
      | 4 => { bound := (1/25 : ℚ), closed := true }
  | 28 => fun
      | 0 => { bound := (2/5 : ℚ), closed := false }
      | 1 => { bound := (1/3 : ℚ), closed := false }
      | 2 => { bound := (1/10 : ℚ), closed := true }
      | 3 => { bound := (1/10 : ℚ), closed := true }
      | 4 => { bound := (1/20 : ℚ), closed := true }
  | 29 => fun
      | 0 => { bound := (2/5 : ℚ), closed := false }
      | 1 => { bound := (7/23 : ℚ), closed := false }
      | 2 => { bound := (1/5 : ℚ), closed := false }
      | 3 => { bound := (1/19 : ℚ), closed := false }
      | 4 => { bound := (1/35 : ℚ), closed := true }
  | 30 => fun
      | 0 => { bound := (2/5 : ℚ), closed := false }
      | 1 => { bound := (2/7 : ℚ), closed := false }
      | 2 => { bound := (1/7 : ℚ), closed := false }
      | 3 => { bound := (1/10 : ℚ), closed := true }
      | 4 => { bound := (1/20 : ℚ), closed := true }
  | 31 => fun
      | 0 => { bound := (2/5 : ℚ), closed := false }
      | 1 => { bound := (4/15 : ℚ), closed := true }
      | 2 => { bound := (1/5 : ℚ), closed := false }
      | 3 => { bound := (1/15 : ℚ), closed := true }
      | 4 => { bound := (1/15 : ℚ), closed := true }
  | 32 => fun
      | 0 => { bound := (2/5 : ℚ), closed := false }
      | 1 => { bound := (4/15 : ℚ), closed := true }
      | 2 => { bound := (2/15 : ℚ), closed := true }
      | 3 => { bound := (2/15 : ℚ), closed := true }
      | 4 => { bound := (1/15 : ℚ), closed := true }
  | 33 => fun
      | 0 => { bound := (2/5 : ℚ), closed := false }
      | 1 => { bound := (1/4 : ℚ), closed := false }
      | 2 => { bound := (3/20 : ℚ), closed := true }
      | 3 => { bound := (1/7 : ℚ), closed := false }
      | 4 => { bound := (1/20 : ℚ), closed := true }
  | 34 => fun
      | 0 => { bound := (11/28 : ℚ), closed := false }
      | 1 => { bound := (1/3 : ℚ), closed := false }
      | 2 => { bound := (1/6 : ℚ), closed := false }
      | 3 => { bound := (3/52 : ℚ), closed := true }
      | 4 => { bound := (1/52 : ℚ), closed := true }
  | 35 => fun
      | 0 => { bound := (5/13 : ℚ), closed := true }
      | 1 => { bound := (3/13 : ℚ), closed := true }
      | 2 => { bound := (2/13 : ℚ), closed := true }
      | 3 => { bound := (1/7 : ℚ), closed := false }
      | 4 => { bound := (1/13 : ℚ), closed := true }
  | 36 => fun
      | 0 => { bound := (5/13 : ℚ), closed := false }
      | 1 => { bound := (5/19 : ℚ), closed := false }
      | 2 => { bound := (1/4 : ℚ), closed := false }
      | 3 => { bound := (2/45 : ℚ), closed := true }
      | 4 => { bound := (1/45 : ℚ), closed := true }
  | 37 => fun
      | 0 => { bound := (8/21 : ℚ), closed := false }
      | 1 => { bound := (7/27 : ℚ), closed := false }
      | 2 => { bound := (1/4 : ℚ), closed := false }
      | 3 => { bound := (3/46 : ℚ), closed := true }
      | 4 => { bound := (1/46 : ℚ), closed := true }
  | 38 => fun
      | 0 => { bound := (3/8 : ℚ), closed := true }
      | 1 => { bound := (1/3 : ℚ), closed := false }
      | 2 => { bound := (1/8 : ℚ), closed := false }
      | 3 => { bound := (1/8 : ℚ), closed := false }
      | 4 => { bound := (1/32 : ℚ), closed := true }
  | 39 => fun
      | 0 => { bound := (3/8 : ℚ), closed := false }
      | 1 => { bound := (1/3 : ℚ), closed := false }
      | 2 => { bound := (2/11 : ℚ), closed := false }
      | 3 => { bound := (1/16 : ℚ), closed := true }
      | 4 => { bound := (1/32 : ℚ), closed := true }
  | 40 => fun
      | 0 => { bound := (3/8 : ℚ), closed := false }
      | 1 => { bound := (1/4 : ℚ), closed := false }
      | 2 => { bound := (1/4 : ℚ), closed := false }
      | 3 => { bound := (1/12 : ℚ), closed := false }
      | 4 => { bound := (1/24 : ℚ), closed := true }
  | 41 => fun
      | 0 => { bound := (3/8 : ℚ), closed := false }
      | 1 => { bound := (1/4 : ℚ), closed := false }
      | 2 => { bound := (2/11 : ℚ), closed := false }
      | 3 => { bound := (1/8 : ℚ), closed := true }
      | 4 => { bound := (1/16 : ℚ), closed := true }
  | 42 => fun
      | 0 => { bound := (4/11 : ℚ), closed := true }
      | 1 => { bound := (3/11 : ℚ), closed := false }
      | 2 => { bound := (2/11 : ℚ), closed := true }
      | 3 => { bound := (1/9 : ℚ), closed := false }
      | 4 => { bound := (1/22 : ℚ), closed := true }
  | 43 => fun
      | 0 => { bound := (4/11 : ℚ), closed := false }
      | 1 => { bound := (2/9 : ℚ), closed := false }
      | 2 => { bound := (2/11 : ℚ), closed := true }
      | 3 => { bound := (1/6 : ℚ), closed := false }
      | 4 => { bound := (1/22 : ℚ), closed := true }
  | 44 => fun
      | 0 => { bound := (13/36 : ℚ), closed := true }
      | 1 => { bound := (5/23 : ℚ), closed := false }
      | 2 => { bound := (1/5 : ℚ), closed := false }
      | 3 => { bound := (1/7 : ℚ), closed := false }
      | 4 => { bound := (1/36 : ℚ), closed := true }
  | 45 => fun
      | 0 => { bound := (5/14 : ℚ), closed := true }
      | 1 => { bound := (2/7 : ℚ), closed := false }
      | 2 => { bound := (1/7 : ℚ), closed := false }
      | 3 => { bound := (1/7 : ℚ), closed := false }
      | 4 => { bound := (1/14 : ℚ), closed := true }
  | 46 => fun
      | 0 => { bound := (6/17 : ℚ), closed := true }
      | 1 => { bound := (2/7 : ℚ), closed := false }
      | 2 => { bound := (1/4 : ℚ), closed := false }
      | 3 => { bound := (1/34 : ℚ), closed := true }
      | 4 => { bound := (1/34 : ℚ), closed := true }
  | 47 => fun
      | 0 => { bound := (7/20 : ℚ), closed := false }
      | 1 => { bound := (1/3 : ℚ), closed := false }
      | 2 => { bound := (1/5 : ℚ), closed := false }
      | 3 => { bound := (2/37 : ℚ), closed := true }
      | 4 => { bound := (1/37 : ℚ), closed := true }
  | 48 => fun
      | 0 => { bound := (1/3 : ℚ), closed := true }
      | 1 => { bound := (1/5 : ℚ), closed := false }
      | 2 => { bound := (1/5 : ℚ), closed := false }
      | 3 => { bound := (1/5 : ℚ), closed := false }
      | 4 => { bound := (1/15 : ℚ), closed := true }
  | 49 => fun
      | 0 => { bound := (1/3 : ℚ), closed := false }
      | 1 => { bound := (3/10 : ℚ), closed := false }
      | 2 => { bound := (1/4 : ℚ), closed := false }
      | 3 => { bound := (3/46 : ℚ), closed := false }
      | 4 => { bound := (1/30 : ℚ), closed := true }
  | 50 => fun
      | 0 => { bound := (1/3 : ℚ), closed := false }
      | 1 => { bound := (3/11 : ℚ), closed := false }
      | 2 => { bound := (1/4 : ℚ), closed := false }
      | 3 => { bound := (1/12 : ℚ), closed := false }
      | 4 => { bound := (1/36 : ℚ), closed := true }
  | 51 => fun
      | 0 => { bound := (1/3 : ℚ), closed := false }
      | 1 => { bound := (3/11 : ℚ), closed := false }
      | 2 => { bound := (2/9 : ℚ), closed := false }
      | 3 => { bound := (1/9 : ℚ), closed := false }
      | 4 => { bound := (1/18 : ℚ), closed := true }
  | 52 => fun
      | 0 => { bound := (1/3 : ℚ), closed := false }
      | 1 => { bound := (4/15 : ℚ), closed := true }
      | 2 => { bound := (1/5 : ℚ), closed := false }
      | 3 => { bound := (2/15 : ℚ), closed := true }
      | 4 => { bound := (1/15 : ℚ), closed := true }
  | 53 => fun
      | 0 => { bound := (1/3 : ℚ), closed := false }
      | 1 => { bound := (1/4 : ℚ), closed := false }
      | 2 => { bound := (5/24 : ℚ), closed := true }
      | 3 => { bound := (1/7 : ℚ), closed := false }
      | 4 => { bound := (1/24 : ℚ), closed := true }
  | 54 => fun
      | 0 => { bound := (1/3 : ℚ), closed := false }
      | 1 => { bound := (1/4 : ℚ), closed := false }
      | 2 => { bound := (1/5 : ℚ), closed := false }
      | 3 => { bound := (1/6 : ℚ), closed := false }
      | 4 => { bound := (1/30 : ℚ), closed := true }
  | 55 => fun
      | 0 => { bound := (1/3 : ℚ), closed := false }
      | 1 => { bound := (2/9 : ℚ), closed := true }
      | 2 => { bound := (1/6 : ℚ), closed := true }
      | 3 => { bound := (1/6 : ℚ), closed := true }
      | 4 => { bound := (1/9 : ℚ), closed := true }
  | 56 => fun
      | 0 => { bound := (1/3 : ℚ), closed := false }
      | 1 => { bound := (5/24 : ℚ), closed := true }
      | 2 => { bound := (5/24 : ℚ), closed := true }
      | 3 => { bound := (1/6 : ℚ), closed := false }
      | 4 => { bound := (1/12 : ℚ), closed := true }
  | 57 => fun
      | 0 => { bound := (9/28 : ℚ), closed := true }
      | 1 => { bound := (3/14 : ℚ), closed := false }
      | 2 => { bound := (3/14 : ℚ), closed := false }
      | 3 => { bound := (1/5 : ℚ), closed := false }
      | 4 => { bound := (1/28 : ℚ), closed := true }
  | 58 => fun
      | 0 => { bound := (5/16 : ℚ), closed := true }
      | 1 => { bound := (1/4 : ℚ), closed := false }
      | 2 => { bound := (1/4 : ℚ), closed := false }
      | 3 => { bound := (1/8 : ℚ), closed := true }
      | 4 => { bound := (1/16 : ℚ), closed := true }
  | 59 => fun
      | 0 => { bound := (3/10 : ℚ), closed := false }
      | 1 => { bound := (5/17 : ℚ), closed := false }
      | 2 => { bound := (1/5 : ℚ), closed := false }
      | 3 => { bound := (1/7 : ℚ), closed := false }
      | 4 => { bound := (1/20 : ℚ), closed := true }
  | 60 => fun
      | 0 => { bound := (3/10 : ℚ), closed := false }
      | 1 => { bound := (1/4 : ℚ), closed := false }
      | 2 => { bound := (4/23 : ℚ), closed := true }
      | 3 => { bound := (1/6 : ℚ), closed := false }
      | 4 => { bound := (2/23 : ℚ), closed := true }
  | 61 => fun
      | 0 => { bound := (2/7 : ℚ), closed := false }
      | 1 => { bound := (2/7 : ℚ), closed := false }
      | 2 => { bound := (4/21 : ℚ), closed := true }
      | 3 => { bound := (4/21 : ℚ), closed := true }
      | 4 => { bound := (1/21 : ℚ), closed := true }
  | 62 => fun
      | 0 => { bound := (2/7 : ℚ), closed := false }
      | 1 => { bound := (1/4 : ℚ), closed := false }
      | 2 => { bound := (2/9 : ℚ), closed := false }
      | 3 => { bound := (1/6 : ℚ), closed := false }
      | 4 => { bound := (1/24 : ℚ), closed := true }
  | 63 => fun
      | 0 => { bound := (3/11 : ℚ), closed := false }
      | 1 => { bound := (2/9 : ℚ), closed := false }
      | 2 => { bound := (2/9 : ℚ), closed := false }
      | 3 => { bound := (1/5 : ℚ), closed := false }
      | 4 => { bound := (1/18 : ℚ), closed := true }
  | 64 => fun
      | 0 => { bound := (5/19 : ℚ), closed := true }
      | 1 => { bound := (1/4 : ℚ), closed := false }
      | 2 => { bound := (4/19 : ℚ), closed := true }
      | 3 => { bound := (1/5 : ℚ), closed := false }
      | 4 => { bound := (1/19 : ℚ), closed := true }
  | 65 => fun
      | 0 => { bound := (1/4 : ℚ), closed := true }
      | 1 => { bound := (1/4 : ℚ), closed := true }
      | 2 => { bound := (1/4 : ℚ), closed := false }
      | 3 => { bound := (1/6 : ℚ), closed := false }
      | 4 => { bound := (1/12 : ℚ), closed := true }
  | 66 => fun
      | 0 => { bound := (4/7 : ℚ), closed := false }
      | 1 => { bound := (1/5 : ℚ), closed := false }
      | 2 => { bound := (1/7 : ℚ), closed := false }
      | 3 => { bound := (1/100 : ℚ), closed := true }
      | 4 => { bound := (1/100 : ℚ), closed := true }
  | 67 => fun
      | 0 => { bound := (6/11 : ℚ), closed := true }
      | 1 => { bound := (3/11 : ℚ), closed := true }
      | 2 => { bound := (1/11 : ℚ), closed := true }
      | 3 => { bound := (1/22 : ℚ), closed := true }
      | 4 => { bound := (1/22 : ℚ), closed := true }
  | 68 => fun
      | 0 => { bound := (8/15 : ℚ), closed := true }
      | 1 => { bound := (4/15 : ℚ), closed := true }
      | 2 => { bound := (2/15 : ℚ), closed := true }
      | 3 => { bound := (1/30 : ℚ), closed := true }
      | 4 => { bound := (1/30 : ℚ), closed := true }
  | 69 => fun
      | 0 => { bound := (1/2 : ℚ), closed := true }
      | 1 => { bound := (1/3 : ℚ), closed := false }
      | 2 => { bound := (1/12 : ℚ), closed := true }
      | 3 => { bound := (1/24 : ℚ), closed := true }
      | 4 => { bound := (1/24 : ℚ), closed := true }
  | 70 => fun
      | 0 => { bound := (4/11 : ℚ), closed := false }
      | 1 => { bound := (4/13 : ℚ), closed := false }
      | 2 => { bound := (3/14 : ℚ), closed := false }
      | 3 => { bound := (1/50 : ℚ), closed := true }
      | 4 => { bound := (1/50 : ℚ), closed := true }
  | 71 => fun
      | 0 => { bound := (6/13 : ℚ), closed := true }
      | 1 => { bound := (3/10 : ℚ), closed := false }
      | 2 => { bound := (2/13 : ℚ), closed := true }
      | 3 => { bound := (1/26 : ℚ), closed := true }
      | 4 => { bound := (1/26 : ℚ), closed := true }
  | 72 => fun
      | 0 => { bound := (5/11 : ℚ), closed := true }
      | 1 => { bound := (1/6 : ℚ), closed := false }
      | 2 => { bound := (3/22 : ℚ), closed := true }
      | 3 => { bound := (3/22 : ℚ), closed := true }
      | 4 => { bound := (1/11 : ℚ), closed := true }
  | 73 => fun
      | 0 => { bound := (5/11 : ℚ), closed := true }
      | 1 => { bound := (3/11 : ℚ), closed := true }
      | 2 => { bound := (1/6 : ℚ), closed := false }
      | 3 => { bound := (1/22 : ℚ), closed := true }
      | 4 => { bound := (1/22 : ℚ), closed := true }
  | 74 => fun
      | 0 => { bound := (13/25 : ℚ), closed := true }
      | 1 => { bound := (1/5 : ℚ), closed := false }
      | 2 => { bound := (3/16 : ℚ), closed := false }
      | 3 => { bound := (1/25 : ℚ), closed := true }
      | 4 => { bound := (1/25 : ℚ), closed := true }
  | 75 => fun
      | 0 => { bound := (5/12 : ℚ), closed := false }
      | 1 => { bound := (2/7 : ℚ), closed := false }
      | 2 => { bound := (1/5 : ℚ), closed := false }
      | 3 => { bound := (1/50 : ℚ), closed := true }
      | 4 => { bound := (1/50 : ℚ), closed := true }
  | 76 => fun
      | 0 => { bound := (3/5 : ℚ), closed := true }
      | 1 => { bound := (1/4 : ℚ), closed := false }
      | 2 => { bound := (1/15 : ℚ), closed := true }
      | 3 => { bound := (1/30 : ℚ), closed := true }
      | 4 => { bound := (1/30 : ℚ), closed := true }
  | 77 => fun
      | 0 => { bound := (7/13 : ℚ), closed := true }
      | 1 => { bound := (3/10 : ℚ), closed := false }
      | 2 => { bound := (1/13 : ℚ), closed := true }
      | 3 => { bound := (1/26 : ℚ), closed := true }
      | 4 => { bound := (1/26 : ℚ), closed := true }
  | 78 => fun
      | 0 => { bound := (3/8 : ℚ), closed := false }
      | 1 => { bound := (2/7 : ℚ), closed := false }
      | 2 => { bound := (3/13 : ℚ), closed := true }
      | 3 => { bound := (1/26 : ℚ), closed := true }
      | 4 => { bound := (1/26 : ℚ), closed := true }
  | 79 => fun
      | 0 => { bound := (2/3 : ℚ), closed := true }
      | 1 => { bound := (1/5 : ℚ), closed := false }
      | 2 => { bound := (1/18 : ℚ), closed := true }
      | 3 => { bound := (1/36 : ℚ), closed := true }
      | 4 => { bound := (1/36 : ℚ), closed := true }
  | 80 => fun
      | 0 => { bound := (7/11 : ℚ), closed := true }
      | 1 => { bound := (1/4 : ℚ), closed := false }
      | 2 => { bound := (1/22 : ℚ), closed := true }
      | 3 => { bound := (1/44 : ℚ), closed := true }
      | 4 => { bound := (1/44 : ℚ), closed := true }
  | 81 => fun
      | 0 => { bound := (7/12 : ℚ), closed := true }
      | 1 => { bound := (1/6 : ℚ), closed := false }
      | 2 => { bound := (1/12 : ℚ), closed := true }
      | 3 => { bound := (1/12 : ℚ), closed := true }
      | 4 => { bound := (1/12 : ℚ), closed := true }
  | 82 => fun
      | 0 => { bound := (7/12 : ℚ), closed := true }
      | 1 => { bound := (1/6 : ℚ), closed := false }
      | 2 => { bound := (1/6 : ℚ), closed := false }
      | 3 => { bound := (1/24 : ℚ), closed := true }
      | 4 => { bound := (1/24 : ℚ), closed := true }
  | 83 => fun
      | 0 => { bound := (7/12 : ℚ), closed := true }
      | 1 => { bound := (1/3 : ℚ), closed := false }
      | 2 => { bound := (1/24 : ℚ), closed := true }
      | 3 => { bound := (1/48 : ℚ), closed := true }
      | 4 => { bound := (1/48 : ℚ), closed := true }
  | _ => fun _ => { bound := 0, closed := false }

def streamLeft : Fin 13 → List (Fin 5)
  | 0 => [0]
  | 1 => [4]
  | 2 => [0]
  | 3 => [1]
  | 4 => [4]
  | 5 => [0]
  | 6 => [2]
  | 7 => [4]
  | 8 => [0, 1]
  | 9 => [1, 2]
  | 10 => [3, 4]
  | 11 => [0, 1]
  | 12 => [3, 4]
  | _ => []

def streamRight : Fin 13 → List (Fin 5)
  | 0 => [1, 2, 3, 4]
  | 1 => [0, 1, 2, 3]
  | 2 => [1, 2, 1, 3, 1, 2, 1, 4]
  | 3 => [0, 2, 0, 3, 0, 2, 0, 4]
  | 4 => [0, 1, 0, 2, 0, 1, 0, 3]
  | 5 => [1, 2, 3, 1, 2, 4]
  | 6 => [0, 1, 3, 0, 1, 4]
  | 7 => [0, 1, 2, 0, 1, 3]
  | 8 => [2, 3, 2, 4]
  | 9 => [0, 3, 0, 4]
  | 10 => [0, 1, 0, 2]
  | 11 => [2, 3, 4]
  | 12 => [0, 1, 2]
  | _ => []

def streamLoads : Fin 13 → List (Fin 5 → ℚ)
  | 0 => [
      fun
                  | 0 => (1 : ℚ)
                  | 1 => (4 : ℚ)
                  | 2 => (0 : ℚ)
                  | 3 => (0 : ℚ)
                  | 4 => (0 : ℚ)
    ]
  | 1 => [
      fun
                  | 0 => (4 : ℚ)
                  | 1 => (0 : ℚ)
                  | 2 => (0 : ℚ)
                  | 3 => (0 : ℚ)
                  | 4 => (1 : ℚ)
    ]
  | 2 => [
      fun
                  | 0 => (1 : ℚ)
                  | 1 => (2 : ℚ)
                  | 2 => (0 : ℚ)
                  | 3 => (0 : ℚ)
                  | 4 => (0 : ℚ),
      fun
                  | 0 => (1 : ℚ)
                  | 1 => (0 : ℚ)
                  | 2 => (4 : ℚ)
                  | 3 => (0 : ℚ)
                  | 4 => (0 : ℚ),
      fun
                  | 0 => (1 : ℚ)
                  | 1 => (0 : ℚ)
                  | 2 => (0 : ℚ)
                  | 3 => (8 : ℚ)
                  | 4 => (0 : ℚ)
    ]
  | 3 => [
      fun
                  | 0 => (2 : ℚ)
                  | 1 => (1 : ℚ)
                  | 2 => (0 : ℚ)
                  | 3 => (0 : ℚ)
                  | 4 => (0 : ℚ),
      fun
                  | 0 => (0 : ℚ)
                  | 1 => (1 : ℚ)
                  | 2 => (4 : ℚ)
                  | 3 => (0 : ℚ)
                  | 4 => (0 : ℚ),
      fun
                  | 0 => (0 : ℚ)
                  | 1 => (1 : ℚ)
                  | 2 => (0 : ℚ)
                  | 3 => (8 : ℚ)
                  | 4 => (0 : ℚ)
    ]
  | 4 => [
      fun
                  | 0 => (2 : ℚ)
                  | 1 => (0 : ℚ)
                  | 2 => (0 : ℚ)
                  | 3 => (0 : ℚ)
                  | 4 => (1 : ℚ),
      fun
                  | 0 => (0 : ℚ)
                  | 1 => (4 : ℚ)
                  | 2 => (0 : ℚ)
                  | 3 => (0 : ℚ)
                  | 4 => (1 : ℚ),
      fun
                  | 0 => (0 : ℚ)
                  | 1 => (0 : ℚ)
                  | 2 => (8 : ℚ)
                  | 3 => (0 : ℚ)
                  | 4 => (1 : ℚ)
    ]
  | 5 => [
      fun
                  | 0 => (1 : ℚ)
                  | 1 => (3 : ℚ)
                  | 2 => (0 : ℚ)
                  | 3 => (0 : ℚ)
                  | 4 => (0 : ℚ),
      fun
                  | 0 => (1 : ℚ)
                  | 1 => (0 : ℚ)
                  | 2 => (0 : ℚ)
                  | 3 => (6 : ℚ)
                  | 4 => (0 : ℚ)
    ]
  | 6 => [
      fun
                  | 0 => (3 : ℚ)
                  | 1 => (0 : ℚ)
                  | 2 => (1 : ℚ)
                  | 3 => (0 : ℚ)
                  | 4 => (0 : ℚ),
      fun
                  | 0 => (0 : ℚ)
                  | 1 => (0 : ℚ)
                  | 2 => (1 : ℚ)
                  | 3 => (6 : ℚ)
                  | 4 => (0 : ℚ)
    ]
  | 7 => [
      fun
                  | 0 => (3 : ℚ)
                  | 1 => (0 : ℚ)
                  | 2 => (0 : ℚ)
                  | 3 => (0 : ℚ)
                  | 4 => (1 : ℚ),
      fun
                  | 0 => (0 : ℚ)
                  | 1 => (0 : ℚ)
                  | 2 => (6 : ℚ)
                  | 3 => (0 : ℚ)
                  | 4 => (1 : ℚ)
    ]
  | 8 => [
      fun
                  | 0 => (2 : ℚ)
                  | 1 => (0 : ℚ)
                  | 2 => (2 : ℚ)
                  | 3 => (0 : ℚ)
                  | 4 => (0 : ℚ),
      fun
                  | 0 => (2 : ℚ)
                  | 1 => (0 : ℚ)
                  | 2 => (0 : ℚ)
                  | 3 => (4 : ℚ)
                  | 4 => (0 : ℚ)
    ]
  | 9 => [
      fun
                  | 0 => (2 : ℚ)
                  | 1 => (2 : ℚ)
                  | 2 => (0 : ℚ)
                  | 3 => (0 : ℚ)
                  | 4 => (0 : ℚ),
      fun
                  | 0 => (0 : ℚ)
                  | 1 => (2 : ℚ)
                  | 2 => (0 : ℚ)
                  | 3 => (4 : ℚ)
                  | 4 => (0 : ℚ)
    ]
  | 10 => [
      fun
                  | 0 => (2 : ℚ)
                  | 1 => (0 : ℚ)
                  | 2 => (0 : ℚ)
                  | 3 => (2 : ℚ)
                  | 4 => (0 : ℚ),
      fun
                  | 0 => (0 : ℚ)
                  | 1 => (4 : ℚ)
                  | 2 => (0 : ℚ)
                  | 3 => (2 : ℚ)
                  | 4 => (0 : ℚ)
    ]
  | 11 => [
      fun
                  | 0 => (2 : ℚ)
                  | 1 => (0 : ℚ)
                  | 2 => (3 : ℚ)
                  | 3 => (0 : ℚ)
                  | 4 => (0 : ℚ)
    ]
  | 12 => [
      fun
                  | 0 => (3 : ℚ)
                  | 1 => (0 : ℚ)
                  | 2 => (0 : ℚ)
                  | 3 => (2 : ℚ)
                  | 4 => (0 : ℚ)
    ]
  | _ => []

end Catalogue
end RealPinwheel
