import CorralFormalization.Constructions.Optimal.Odd.Theorem
import CorralFormalization.Constructions.Optimal.Even.Theorem

namespace CorralFormalization

/-- At every positive height the original corral predicate holds at the
optimal order. The odd-height proof currently uses the earlier two-swap
construction and separate small cases; it does not by itself formalize the
one-swap construction printed in the manuscript. -/
theorem optimalCorral_exists (height : ℕ) (hpos : 0 < height) :
    OriginalCorral height (2 * height - 1) := by
  by_cases hodd : height % 2 = 1
  · exact OptimalOdd.all_heights height hpos hodd
  · let k := height / 2
    have hk : 1 ≤ k := by dsimp [k]; omega
    have hheight : height = 2 * k := by dsimp [k]; omega
    have horder : 2 * height - 1 = 4 * k - 1 := by omega
    rw [horder, hheight]
    exact OptimalEven.exists_corral k hk

end CorralFormalization
