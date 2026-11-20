import CorralFormalization.Results.PrimeHeight.ModelBridges
import CorralFormalization.Optimal

namespace CorralFormalization.Results.PrimeHeight

open PhysicalCorral

/-- The universal prime-height theorem applies to an inhabited physical
corral domain at every odd prime height, using the maintained existence proof. -/
theorem odd_prime_optimal_asymmetric_models_exist (h : ℕ)
    (hp : Nat.Prime h) (hodd : Odd h) :
    ∃ R : CorralRows h (2*h-1), PhysicallyAsymmetric (physicalFamily R) := by
  obtain ⟨R⟩ := originalCorral_nonempty_rows (by have := hp.two_le; omega : 0 < 2*h-1)
    (optimalCorral_exists h hp.pos)
  exact ⟨R, every_odd_prime_optimal_corralRows_asymmetric h hp hodd R⟩

end CorralFormalization.Results.PrimeHeight
