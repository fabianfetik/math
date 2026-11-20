import CorralFormalization.DiversityCompletion.CarrierPartition

namespace CorralFormalization.EvenSupportPartition

open Finset EvenSwitches PhysicalCorral DiversitySymmetry

/-- Integer translations by one full maintained even-construction period. -/
def periodIntMap (k : ℕ) : ℤ →+ ZMod (evenConstructionClock k) where
  toFun z := (z : ZMod (evenConstructionClock k)) * (evenConstructionPeriod k : ℕ)
  map_zero' := by simp
  map_add' x y := by simp [add_mul]

theorem periodIntMap_period (k : ℕ) : periodIntMap k k = 0 := by
  have h : ((k * evenConstructionPeriod k : ℕ) : ZMod (evenConstructionClock k)) = 0 :=
    ZMod.natCast_self _
  simpa [periodIntMap, Nat.cast_mul] using h

/-- The physical period-stride homomorphism. Its domain is the support-phase
cycle, rather than the full physical clock. -/
def periodStride (k : ℕ) : ZMod k →+ ZMod (evenConstructionClock k) :=
  ZMod.lift k ⟨periodIntMap k, periodIntMap_period k⟩

theorem periodStride_natCast (k j : ℕ) :
    periodStride k (j : ZMod k) = ((evenConstructionPeriod k * j : ℕ) : ZMod (evenConstructionClock k)) := by
  have h := ZMod.lift_coe k ⟨periodIntMap k, periodIntMap_period k⟩ (j : ℤ)
  simpa [periodStride, periodIntMap, Nat.cast_mul, mul_comm] using h

theorem periodStride_val (k : ℕ) [NeZero k] (j : ZMod k) :
    periodStride k j = ((evenConstructionPeriod k * j.val : ℕ) : ZMod (evenConstructionClock k)) := by
  simpa only [ZMod.natCast_zmod_val] using periodStride_natCast k j.val

theorem finEquiv_natCast (k : ℕ) [NeZero k] (i : Fin k) :
    ZMod.finEquiv k i = (i.val : ZMod k) := by
  cases k with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ k => exact (ZMod.natCast_zmod_val (ZMod.finEquiv (k+1) i)).symm

theorem periodStride_fin (k : ℕ) [NeZero k] (i : Fin k) :
    periodStride k (ZMod.finEquiv k i) =
      ((evenConstructionPeriod k * i.val : ℕ) : ZMod (evenConstructionClock k)) := by
  rw [finEquiv_natCast, periodStride_natCast]

instance phaseNeZero (m : ℕ) : NeZero (2*m+1) := ⟨by omega⟩

def midPhase (m : ℕ) : Fin (2*m+1) := ⟨m, by omega⟩

/-- The actual half-period re-pairing of the two maintained source families. -/
def supportShift (m : ℕ) : Equiv.Perm (Fin (2*m+1)) :=
  Equiv.addRight (midPhase m)

theorem supportShift_phase (m : ℕ) (i : Fin (2*m+1)) :
    ZMod.finEquiv (2*m+1) (supportShift m i) =
      ZMod.finEquiv (2*m+1) i + ZMod.finEquiv (2*m+1) (midPhase m) := by
  exact (ZMod.finEquiv (2*m+1)).map_add i (midPhase m)

/-- The literal seed/reflected-seed carrier on the maintained construction's
clock. `switchClock_eq_evenConstructionClock` identifies it with `oldCarrier`. -/
def evenSupportCarrier (m : ℕ) : Finset (ZMod (evenConstructionClock (2*m+1))) :=
  evenConstructionSeed (2*m+1) ∪
    (Motion.reflection (((height m)^2-1 : ℕ) : ZMod (evenConstructionClock (2*m+1)))).onRow
      (evenConstructionSeed (2*m+1))

/-- The actual physical carrier at support phase `j`. -/
def supportAt (m : ℕ) (j : ZMod (2*m+1)) :
    Finset (ZMod (evenConstructionClock (2*m+1))) :=
  (Motion.rotation (periodStride (2*m+1) j)).onRow (evenSupportCarrier m)

theorem zero_source (m : ℕ) :
    physicalSites (evenConstructionClock (2*m+1)) (evenConstructionRowSource (2*m+1) 0) =
      evenConstructionSeed (2*m+1) := by
  simp [evenConstructionRowSource, evenConstructionSeed]

/-- Equation (D2) identifies the reflected half-shifted maintained row
with the literal physical reflection used by the new A/B switches. -/
theorem reflected_source_mid (m : ℕ) :
    evenPhysicalRow (2*m+1) 1 (midPhase m) =
      (Motion.reflection (((height m)^2-1 : ℕ) : ZMod (evenConstructionClock (2*m+1)))).onRow
        (evenConstructionSeed (2*m+1)) := by
  have hk : 1 ≤ 2*m+1 := by omega
  have hheight : height m = 2*(2*m+1) := by unfold height; ring
  have hnat : evenConstructionPeriod (2*m+1)*m + evenConstructionShift (2*m+1) = (height m)^2-1 := by
    rw [hheight, diversity_reflection_parameter]
    ring
  rw [evenPhysicalRow_translation]
  simp only [evenConstructionRowSource, Fin.val_one, one_ne_zero, if_false, midPhase]
  rw [evenPhysical_reflection _ hk, ← Motion.onRow_compose]
  change (Motion.reflection (((evenConstructionPeriod (2*m+1)*m : ℕ) : ZMod (evenConstructionClock (2*m+1))) +
    (evenConstructionShift (2*m+1) : ZMod (evenConstructionClock (2*m+1))))).onRow (evenConstructionSeed (2*m+1)) = _
  rw [← Nat.cast_add, hnat]

theorem translate_evenPhysicalRow (k : ℕ) [NeZero k] (b : Fin 2)
    (i j : Fin k) :
    (Motion.rotation (periodStride k (ZMod.finEquiv k i))).onRow (evenPhysicalRow k b j) =
      evenPhysicalRow k b (i+j) := by
  rw [evenPhysicalRow_translation k b j, evenPhysicalRow_translation k b (i+j),
    ← Motion.onRow_compose]
  change (Motion.rotation (periodStride k (ZMod.finEquiv k i) +
    ((evenConstructionPeriod k*j.val : ℕ) : ZMod (evenConstructionClock k)))).onRow _ = _
  rw [← periodStride_fin, ← map_add, ← map_add, periodStride_fin]

/-- Exact identification with the pre-existing complete partition. The
permutation is paid, namely addition of `m` in the `2m+1` phase cycle. -/
theorem supportAt_eq_evenSupport (m : ℕ) (j : ZMod (2*m+1)) :
    supportAt m j = evenSupport (2*m+1) (supportShift m) ((ZMod.finEquiv (2*m+1)).symm j) := by
  let i := (ZMod.finEquiv (2*m+1)).symm j
  have hi : ZMod.finEquiv (2*m+1) i = j := (ZMod.finEquiv _).apply_symm_apply j
  have hzero : evenPhysicalRow (2*m+1) 0 (0 : Fin (2*m+1)) = evenConstructionSeed (2*m+1) := by
    rw [evenPhysicalRow_translation, zero_source]
    simp
  rw [supportAt, evenSupportCarrier]
  simp only [Motion.onRow, image_union]
  change (Motion.rotation (periodStride (2*m+1) j)).onRow (evenConstructionSeed (2*m+1)) ∪
    (Motion.rotation (periodStride (2*m+1) j)).onRow
      ((Motion.reflection (((height m)^2-1 : ℕ) : ZMod (evenConstructionClock (2*m+1)))).onRow
        (evenConstructionSeed (2*m+1))) = _
  rw [← reflected_source_mid, ← hzero, ← hi,
    translate_evenPhysicalRow, translate_evenPhysicalRow]
  simp [evenSupport, supportShift, Equiv.addRight, i]

theorem supportAt_zero (m : ℕ) : supportAt m 0 = evenSupportCarrier m := by
  simp [supportAt]

theorem supportAt_period_translation (m : ℕ) (j : ZMod (2*m+1)) :
    supportAt m j =
      (Motion.rotation ((evenConstructionPeriod (2*m+1)*j.val : ℕ) : ZMod (evenConstructionClock (2*m+1)))).onRow
        (evenSupportCarrier m) := by
  rw [supportAt, periodStride_val]

theorem evenSupportCarrier_reflection (m : ℕ) :
    (Motion.reflection (((height m)^2-1 : ℕ) : ZMod (evenConstructionClock (2*m+1)))).onRow
      (evenSupportCarrier m) = evenSupportCarrier m := by
  rw [evenSupportCarrier]
  simp only [Motion.onRow, image_union]
  change (Motion.reflection (((height m)^2-1 : ℕ) : ZMod (evenConstructionClock (2*m+1)))).onRow
      (evenConstructionSeed (2*m+1)) ∪
    (Motion.reflection (((height m)^2-1 : ℕ) : ZMod (evenConstructionClock (2*m+1)))).onRow
      ((Motion.reflection (((height m)^2-1 : ℕ) : ZMod (evenConstructionClock (2*m+1)))).onRow
        (evenConstructionSeed (2*m+1))) = _
  rw [Motion.reflection_onRow_involutive]
  exact union_comm _ _

/-- Literal physical reflection sends the support at phase `j` to the
support at phase `-j`; no abstract phase-action hypothesis is assumed. -/
theorem supportAt_reflection (m : ℕ) (j : ZMod (2*m+1)) :
    (Motion.reflection (((height m)^2-1 : ℕ) : ZMod (evenConstructionClock (2*m+1)))).onRow
      (supportAt m j) = supportAt m (-j) := by
  rw [supportAt, supportAt, map_neg, ← Motion.onRow_compose]
  have hmotion : (Motion.reflection (((height m)^2-1 : ℕ) : ZMod (evenConstructionClock (2*m+1)))).compose
      (Motion.rotation (periodStride (2*m+1) j)) =
    (Motion.rotation (-(periodStride (2*m+1) j))).compose
      (Motion.reflection (((height m)^2-1 : ℕ) : ZMod (evenConstructionClock (2*m+1)))) := by
    simp only [Motion.compose]
    congr 1
    ring
  rw [hmotion, Motion.onRow_compose, evenSupportCarrier_reflection]

theorem supportAt_translation (m : ℕ) (i j : ZMod (2*m+1)) :
    (Motion.rotation (periodStride (2*m+1) i)).onRow (supportAt m j) = supportAt m (i+j) := by
  rw [supportAt, supportAt, map_add, ← Motion.onRow_compose]
  rfl

/-- Each physical point has exactly one concrete shifted carrier phase. -/
theorem supportAt_partition (m : ℕ) (x : ZMod (evenConstructionClock (2*m+1))) :
    ∃! j : ZMod (2*m+1), x ∈ supportAt m j := by
  obtain ⟨i, hi, huniq⟩ := evenSupport_partition (2*m+1) (by omega) (supportShift m) x
  refine ⟨ZMod.finEquiv (2*m+1) i, ?_, ?_⟩
  · simpa only [supportAt_eq_evenSupport, RingEquiv.symm_apply_apply] using hi
  · intro j hj
    rw [supportAt_eq_evenSupport] at hj
    have hij := huniq ((ZMod.finEquiv (2*m+1)).symm j) hj
    simpa only [RingEquiv.apply_symm_apply] using congrArg (ZMod.finEquiv (2*m+1)) hij

theorem supportAt_disjoint (m : ℕ) (i j : ZMod (2*m+1)) (hij : i ≠ j) :
    Disjoint (supportAt m i) (supportAt m j) := by
  rw [supportAt_eq_evenSupport, supportAt_eq_evenSupport]
  apply evenSupport_disjoint _ (by omega)
  exact fun h => hij ((ZMod.finEquiv _).symm.injective h)

instance explicitClockNeZero (m : ℕ) : NeZero (evenConstructionClock (2*m+1)) :=
  ⟨Nat.ne_of_gt (evenConstructionClock_pos _ (by omega))⟩

theorem supportAt_coverage (m : ℕ) :
    Finset.univ.biUnion (supportAt m) = (Finset.univ : Finset (ZMod (evenConstructionClock (2*m+1)))) := by
  ext x
  simp only [mem_biUnion, mem_univ, true_and, iff_true]
  obtain ⟨j, hj, _⟩ := supportAt_partition m x
  exact ⟨j, hj⟩

/-- The literal A/B rows disjointly fill the zero-phase carrier, on the
maintained construction's clock. The parameter range includes `m=1`. -/
theorem physical_rows_partition_explicitCarrier (m : ℕ) (hm : 1 ≤ m) (a : Choices m) :
    Disjoint (physicalSites (evenConstructionClock (2*m+1)) (rowA m a))
      (physicalSites (evenConstructionClock (2*m+1)) (rowB m a)) ∧
    physicalSites (evenConstructionClock (2*m+1)) (rowA m a) ∪
      physicalSites (evenConstructionClock (2*m+1)) (rowB m a) = evenSupportCarrier m := by
  have h := physical_rows_partition_old m hm a
  unfold oldCarrier baseRow at h
  rw [switchClock_eq_evenConstructionClock m] at h
  exact h

/-- Concrete translated A/B rows fill precisely the old maintained support
with the half-period re-pairing. No support identity is an input. -/
theorem physical_rows_partition_supportAt (m : ℕ) (hm : 1 ≤ m) (a : Choices m)
    (j : ZMod (2*m+1)) :
    Disjoint
      ((Motion.rotation (periodStride (2*m+1) j)).onRow
        (physicalSites (evenConstructionClock (2*m+1)) (rowA m a)))
      ((Motion.rotation (periodStride (2*m+1) j)).onRow
        (physicalSites (evenConstructionClock (2*m+1)) (rowB m a))) ∧
    (Motion.rotation (periodStride (2*m+1) j)).onRow
        (physicalSites (evenConstructionClock (2*m+1)) (rowA m a)) ∪
      (Motion.rotation (periodStride (2*m+1) j)).onRow
        (physicalSites (evenConstructionClock (2*m+1)) (rowB m a)) = supportAt m j := by
  obtain ⟨hd, hu⟩ := physical_rows_partition_explicitCarrier m hm a
  constructor
  · exact (Finset.disjoint_image (Motion.act_injective _)).mpr hd
  · rw [supportAt, ← hu]
    exact (Finset.image_union _ _).symm

end CorralFormalization.EvenSupportPartition
