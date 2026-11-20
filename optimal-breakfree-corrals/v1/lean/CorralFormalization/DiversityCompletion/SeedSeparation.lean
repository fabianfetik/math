import CorralFormalization.DiversityCompletion.SeedMarker

namespace CorralFormalization.DiversitySymmetry

open Finset
open CorralFormalization.PhysicalCorral

/-- A different exhibited gap-neighbor pair prevents physical isometry
with the concrete seed. The two rows may be moved independently. No
validity, rigidity, or unique-maximum hypothesis on `S` is required. -/
theorem evenConstructionSeed_separation_of_marker (k : ℕ) (hk : 2 ≤ k)
    (S : Finset (ZMod (evenConstructionClock k))) (pair : Finset ℕ)
    (hpair : pair ≠ {1, 2 * k - 2})
    (hmarker : HasGapNeighborPair S (4 * k - 1) pair)
    (f g : Motion (evenConstructionClock k)) :
    f.onRow (evenConstructionSeed k) ≠ g.onRow S := by
  let : NeZero (evenConstructionClock k) :=
    ⟨Nat.ne_of_gt (evenConstructionClock_pos k (by omega))⟩
  intro heq
  have hnew : HasGapNeighborPair (evenConstructionSeed k) (4 * k - 1) pair := by
    apply (hasGapNeighborPair_motion_iff f (evenConstructionSeed k) (4 * k - 1) pair).mp
    rw [heq]
    exact (hasGapNeighborPair_motion_iff g S (4 * k - 1) pair).mpr hmarker
  exact hpair ((evenConstructionSeed_marker_iff k hk pair).mp hnew)

theorem evenConstructionSeed_pair_ne_upper (k : ℕ) (hk : 2 ≤ k) :
    ({2 * k, 2 * k + 1} : Finset ℕ) ≠ {1, 2 * k - 2} := by
  have hnot : 1 ∉ ({2 * k, 2 * k + 1} : Finset ℕ) := by
    simp only [mem_insert, mem_singleton]
    omega
  intro heq
  apply hnot
  rw [heq]
  simp

theorem evenConstructionSeed_pair_ne_mixed (k : ℕ) (hk : 2 ≤ k) :
    ({2 * k - 2, 2 * k + 3} : Finset ℕ) ≠ {1, 2 * k - 2} := by
  have hnot : 1 ∉ ({2 * k - 2, 2 * k + 3} : Finset ℕ) := by
    simp only [mem_insert, mem_singleton]
    omega
  intro heq
  apply hnot
  rw [heq]
  simp

/-- The two concrete new-row markers in manuscript §6.4 are both
physically separated from the actual seed, under every motion. -/
theorem evenConstructionSeed_separation (k : ℕ) (hk : 2 ≤ k)
    (S : Finset (ZMod (evenConstructionClock k)))
    (hmarker : HasGapNeighborPair S (4 * k - 1) {2 * k, 2 * k + 1} ∨
      HasGapNeighborPair S (4 * k - 1) {2 * k - 2, 2 * k + 3})
    (f g : Motion (evenConstructionClock k)) :
    f.onRow (evenConstructionSeed k) ≠ g.onRow S := by
  rcases hmarker with hupper | hmixed
  · exact evenConstructionSeed_separation_of_marker k hk S _ (evenConstructionSeed_pair_ne_upper k hk) hupper f g
  · exact evenConstructionSeed_separation_of_marker k hk S _ (evenConstructionSeed_pair_ne_mixed k hk) hmixed f g

/-- A combined local supplier for the existing seed-reduction theorem:
the seed is rigid and lies in neither physical orbit of the new markers. -/
theorem evenConstructionSeed_rigid_and_separated (k : ℕ) (hk : 2 ≤ k)
    (S : Finset (ZMod (evenConstructionClock k)))
    (hmarker : HasGapNeighborPair S (4 * k - 1) {2 * k, 2 * k + 1} ∨
      HasGapNeighborPair S (4 * k - 1) {2 * k - 2, 2 * k + 3}) :
    RigidRow (evenConstructionSeed k) ∧
      ∀ f g : Motion (evenConstructionClock k), f.onRow (evenConstructionSeed k) ≠ g.onRow S :=
  ⟨evenConstructionSeed_rigid k hk, evenConstructionSeed_separation k hk S hmarker⟩

/-- Literal m-parameterization, including m=1: h=4m+2, n=8m+3. -/
theorem evenSwitchFamily_seed_separation (m : ℕ) (hm : 1 ≤ m)
    (S : Finset (ZMod (evenConstructionClock (2 * m + 1))))
    (hmarker : HasGapNeighborPair S (8 * m + 3) {4 * m + 2, 4 * m + 3} ∨
      HasGapNeighborPair S (8 * m + 3) {4 * m, 4 * m + 5})
    (f g : Motion (evenConstructionClock (2 * m + 1))) :
    f.onRow (evenConstructionSeed (2 * m + 1)) ≠ g.onRow S := by
  have hn : 4 * (2 * m + 1) - 1 = 8 * m + 3 := by
    have h : 4 * (2 * m + 1) = 8 * m + 4 := by ring
    omega
  have hh : 2 * (2 * m + 1) = 4 * m + 2 := by ring
  have hp : 2 * (2 * m + 1) - 2 = 4 * m := by
    omega
  apply evenConstructionSeed_separation (2 * m + 1) (by omega) S _ f g
  simpa [hn, hh, hp, Nat.add_assoc] using hmarker

end CorralFormalization.DiversitySymmetry
