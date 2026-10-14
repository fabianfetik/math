import Pinwheel.Streams

namespace RealPinwheel

theorem listCycle_mem {w : List (Fin 5)} (hw : w ≠ []) (n : ℤ) :
    listCycle w n ∈ w := by
  have hlen : 0 < (w.length : ℤ) := by
    exact_mod_cast List.length_pos_of_ne_nil hw
  have hidx : (n % (w.length : ℤ)).toNat < w.length := by
    apply (Int.toNat_lt (Int.emod_nonneg n hlen.ne')).mpr
    exact Int.emod_lt_of_pos n hlen
  rw [listCycle_eq_get hw n hidx]
  exact List.get_mem _ _

theorem listCycle_ne_of_disjoint {u v : List (Fin 5)}
    (hu : u ≠ []) (hv : v ≠ []) (h : List.Disjoint u v) (n m : ℤ) :
    listCycle u n ≠ listCycle v m := by
  intro heq
  have hleft := listCycle_mem hu n
  have hright := listCycle_mem hv m
  rw [← heq] at hright
  exact List.disjoint_left.mp h hleft hright

end RealPinwheel
