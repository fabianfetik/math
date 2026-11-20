import CorralFormalization.Optimal
import CorralFormalization.Counting
import CorralFormalization.OrderExtension

namespace CorralFormalization

/-- The complete original existence assertion: every admissible positive
height and order, obtained by extending the optimal construction. -/
theorem originalTarget_proved : OriginalTarget := by
  intro h n hh hn hbound
  exact originalCorral_mono_order h (2 * h - 1) n hh (by omega)
    (optimalCorral_exists h hh) hbound

/-- Exact existence criterion for ordinary breakfree corrals, including the
counting necessity and all larger orders. -/
theorem originalCorral_iff_order_bound (h n : ℕ) (hh : 0 < h) (hn : 0 < n) :
    OriginalCorral h n ↔ 2 * h - 1 ≤ n := by
  constructor
  · exact originalCorral_order_lower_bound h n hn
  · intro hbound
    exact originalTarget_proved h n hh hn hbound

end CorralFormalization
