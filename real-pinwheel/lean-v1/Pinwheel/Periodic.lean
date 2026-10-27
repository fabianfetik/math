import Pinwheel.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.NormNum

open Finset

namespace RealPinwheel

def phase (P : ℕ) (hP : 0 < P) (t : ℤ) : Fin P :=
  ⟨(t % (P : ℤ)).toNat, by
    apply (Int.toNat_lt (Int.emod_nonneg t (by omega))).mpr
    exact Int.emod_lt_of_pos t (by omega)⟩

def periodic {α : Type*} (P : ℕ) (hP : 0 < P) (w : Fin P → α) (t : ℤ) : α :=
  w (phase P hP t)

abbrev phaseIndex (P : ℕ) (hP : 0 < P) (s : Fin P) (k : ℕ) : Fin P :=
  ⟨(s.val + k) % P, Nat.mod_lt _ hP⟩

abbrev cyclicCount (P : ℕ) (hP : 0 < P) (w : Fin P → Fin 5)
    (i : Fin 5) (s : Fin P) (h : ℕ) : ℕ :=
  (List.range h).countP (fun k => decide (w (phaseIndex P hP s k) = i))

lemma card_filter_range_eq_cyclicCount (P : ℕ) (hP : 0 < P)
    (w : Fin P → Fin 5) (i : Fin 5) (s : Fin P) (h : ℕ) :
    ((Finset.range h).filter (fun k => w (phaseIndex P hP s k) = i)).card =
      cyclicCount P hP w i s h := by
  let p : ℕ → Bool := fun k => decide (w (phaseIndex P hP s k) = i)
  have hset : (List.range h).toFinset = Finset.range h := by
    ext k
    simp
  have hfilter :
      ((List.filter p (List.range h)).toFinset) =
        (Finset.range h).filter (fun k => w (phaseIndex P hP s k) = i) := by
    rw [List.toFinset_filter, hset]
    ext k
    simp [p, decide_eq_true_eq]
  have hnodup : (List.range h).Nodup := List.nodup_range
  have hnodup' : (List.filter p (List.range h)).Nodup := hnodup.filter _
  have hcard := List.toFinset_card_of_nodup hnodup'
  rw [hfilter] at hcard
  rw [cyclicCount, List.countP_eq_length_filter]
  exact hcard.symm

lemma phase_nat_add (P : ℕ) (hP : 0 < P) (s : Fin P) (k : ℕ) :
    phase P hP ((s.val + k : ℕ) : ℤ) = phaseIndex P hP s k := by
  apply Fin.ext
  change (((s.val + k : ℕ) : ℤ) % (P : ℤ)).toNat = (s.val + k) % P
  have hrem : 0 ≤ ((s.val + k : ℕ) : ℤ) % (P : ℤ) :=
    Int.emod_nonneg _ (by omega)
  have hcast : (((s.val + k) % P : ℕ) : ℤ) =
      ((s.val + k : ℕ) : ℤ) % (P : ℤ) := by
    exact Int.natCast_emod _ _
  apply Int.natCast_inj.mp
  exact (Int.toNat_of_nonneg hrem).trans hcast.symm

def natAddIntEmbedding (s : Fin P) : ℕ ↪ ℤ where
  toFun k := (s.val : ℤ) + (k : ℤ)
  inj' := by
    intro a b h
    change (s.val : ℤ) + (a : ℤ) = (s.val : ℤ) + (b : ℤ) at h
    have h' : (a : ℤ) = (b : ℤ) := by
      calc
        (a : ℤ) = ((s.val : ℤ) + (a : ℤ)) - (s.val : ℤ) := by ring
        _ = ((s.val : ℤ) + (b : ℤ)) - (s.val : ℤ) := by rw [h]
        _ = (b : ℤ) := by ring
    exact Int.natCast_inj.mp h'

lemma map_range_natAddInt (s : Fin P) (h : ℕ) :
  (range h).map (natAddIntEmbedding s) =
      Ico (s.val : ℤ) ((s.val : ℤ) + (h : ℤ)) := by
  ext x
  simp only [mem_map, mem_range, mem_Ico]
  constructor
  · rintro ⟨k, hk, rfl⟩
    change (s.val : ℤ) ≤ (natAddIntEmbedding s) k ∧
      (natAddIntEmbedding s) k < (s.val : ℤ) + (h : ℤ)
    change (s.val : ℤ) ≤ (s.val : ℤ) + (k : ℤ) ∧
      (s.val : ℤ) + (k : ℤ) < (s.val : ℤ) + (h : ℤ)
    omega
  · intro hx
    have hnonneg : 0 ≤ x - (s.val : ℤ) := by omega
    let k : ℕ := (x - (s.val : ℤ)).toNat
    have hkcast : (k : ℤ) = x - (s.val : ℤ) := by
      dsimp [k]
      exact Int.toNat_of_nonneg hnonneg
    refine ⟨k, ?_, ?_⟩
    · omega
    · change (s.val : ℤ) + (k : ℤ) = x
      omega

lemma serviceCount_phase_eq_cyclicCount
    (P : ℕ) (hP : 0 < P) (w : Fin P → Fin 5) (i : Fin 5) (s : Fin P) (h : ℕ) :
    serviceCount (periodic P hP w) i (s.val : ℤ) (h : ℤ) =
      cyclicCount P hP w i s h := by
  classical
  let e := natAddIntEmbedding s
  have he := map_range_natAddInt s h
  unfold serviceCount RealPinwheel.windowCount
  have hfilter :
      @Finset.filter ℤ (fun t => periodic P hP w t = i)
          (fun t => Classical.propDecidable _) (Finset.Ico (s.val : ℤ)
            ((s.val : ℤ) + (h : ℤ))) =
        Finset.map e (@Finset.filter ℕ (fun k => w (phaseIndex P hP s k) = i)
          (inferInstance) (Finset.range h)) := by
    rw [← he]
    ext x
    constructor
    · intro hx
      have hx' := (@Finset.mem_filter ℤ (fun t => periodic P hP w t = i)
        (fun t => Classical.propDecidable _) _ _).mp hx
      rcases hx' with ⟨hxmap, hxi⟩
      rcases Finset.mem_map.mp hxmap with ⟨k, hk, rfl⟩
      have hphase : phase P hP ((e k)) = phaseIndex P hP s k := by
        change phase P hP ((s.val : ℤ) + (k : ℤ)) = _
        rw [← Int.natCast_add]
        exact phase_nat_add P hP s k
      refine Finset.mem_map.mpr ⟨k, ?_, rfl⟩
      apply Finset.mem_filter.mpr
      refine ⟨hk, ?_⟩
      change w (phase P hP (e k)) = i at hxi
      rw [hphase] at hxi
      exact hxi
    · intro hx
      rcases Finset.mem_map.mp hx with ⟨k, hk, rfl⟩
      have hk' := Finset.mem_filter.mp hk
      rcases hk' with ⟨hk, hki⟩
      apply (@Finset.mem_filter ℤ (fun t => periodic P hP w t = i)
        (fun t => Classical.propDecidable _) _ _).mpr
      refine ⟨Finset.mem_map.mpr ⟨k, hk, rfl⟩, ?_⟩
      · have hphase : phase P hP ((e k)) = phaseIndex P hP s k := by
          change phase P hP ((s.val : ℤ) + (k : ℤ)) = _
          rw [← Int.natCast_add]
          exact phase_nat_add P hP s k
        change w (phase P hP (e k)) = i
        rw [hphase]
        exact hki
  have hc := congrArg Finset.card hfilter
  rw [Finset.card_map] at hc
  rw [cyclicCount]
  exact hc.trans (card_filter_range_eq_cyclicCount P hP w i s h)

lemma phase_add_mul_period (P : ℕ) (hP : 0 < P) (t q : ℤ) :
    phase P hP (t + q * (P : ℤ)) = phase P hP t := by
  have hdiv : (P : ℤ) ∣ q * (P : ℤ) := by
    refine ⟨q, ?_⟩
    ring
  have hzero : q * (P : ℤ) % (P : ℤ) = 0 :=
    Int.emod_eq_zero_of_dvd hdiv
  have hrem : (t + q * (P : ℤ)) % (P : ℤ) = t % (P : ℤ) := by
    rw [Int.add_emod, hzero]
    simp
  apply Fin.ext
  simp [phase, hrem]

lemma periodic_add_mul_period {α : Type*} (P : ℕ) (hP : 0 < P)
    (w : Fin P → α) (t q : ℤ) :
    periodic P hP w (t + q * (P : ℤ)) = periodic P hP w t := by
  unfold periodic
  rw [phase_add_mul_period]

def intShiftEmbedding (d : ℤ) : ℤ ↪ ℤ where
  toFun x := x + d
  inj' := by
    intro a b h
    change a + d = b + d at h
    omega

lemma map_Ico_intShift (m L d : ℤ) :
    (Ico m (m + L)).map (intShiftEmbedding d) =
      Ico (m + d) (m + L + d) := by
  ext x
  simp only [mem_map, mem_Ico]
  constructor
  · rintro ⟨y, hy, rfl⟩
    change (m + d ≤ y + d) ∧ (y + d < m + L + d)
    omega
  · intro hx
    refine ⟨x - d, ?_, ?_⟩
    · omega
    · change (x - d) + d = x
      omega

lemma serviceCount_shift_periodic
    {α : Type*} [DecidableEq α]
    (P : ℕ) (hP : 0 < P) (w : Fin P → α) (i : α)
    (m L q : ℤ) :
    serviceCount (periodic P hP w) i (m + q * (P : ℤ)) L =
      serviceCount (periodic P hP w) i m L := by
  classical
  let e := intShiftEmbedding (q * (P : ℤ))
  have he := map_Ico_intShift m L (q * (P : ℤ))
  unfold serviceCount RealPinwheel.windowCount
  have hfilter :
      @Finset.filter ℤ (fun t => periodic P hP w t = i)
          (fun t => Classical.propDecidable _) (Finset.Ico
            (m + q * (P : ℤ)) ((m + q * (P : ℤ)) + L)) =
        Finset.map e (@Finset.filter ℤ (fun t => periodic P hP w t = i)
          (fun t => Classical.propDecidable _) (Finset.Ico m (m + L))) := by
    rw [show (m + q * (P : ℤ)) + L = m + L + q * (P : ℤ) by ring]
    rw [← he]
    ext x
    constructor
    · intro hx
      have hx' := (@Finset.mem_filter ℤ (fun t => periodic P hP w t = i)
        (fun t => Classical.propDecidable _) _ _).mp hx
      rcases hx' with ⟨hxmap, hxi⟩
      rcases Finset.mem_map.mp hxmap with ⟨y, hy, rfl⟩
      change periodic P hP w (y + q * (P : ℤ)) = i at hxi
      rw [periodic_add_mul_period P hP w y q] at hxi
      refine Finset.mem_map.mpr ⟨y, ?_, rfl⟩
      apply (@Finset.mem_filter ℤ (fun t => periodic P hP w t = i)
        (fun t => Classical.propDecidable _) _ _).mpr
      exact ⟨hy, hxi⟩
    · intro hx
      rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩
      have hy' := (@Finset.mem_filter ℤ (fun t => periodic P hP w t = i)
        (fun t => Classical.propDecidable _) _ _).mp hy
      rcases hy' with ⟨hy, hyi⟩
      apply (@Finset.mem_filter ℤ (fun t => periodic P hP w t = i)
        (fun t => Classical.propDecidable _) _ _).mpr
      refine ⟨Finset.mem_map.mpr ⟨y, hy, rfl⟩, ?_⟩
      change periodic P hP w (y + q * (P : ℤ)) = i
      rw [periodic_add_mul_period P hP w y q]
      exact hyi
  have hc := congrArg Finset.card hfilter
  rw [Finset.card_map] at hc
  exact hc

lemma windowCount_add
    (p : ℤ → Prop) (m a b : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    windowCount p m (a + b) =
      windowCount p m a + windowCount p (m + a) b := by
  classical
  have h₁ : m ≤ m + a := by omega
  have h₂ : m + a ≤ m + a + b := by omega
  have hset : Ico m (m + a + b) = Ico m (m + a) ∪ Ico (m + a) (m + a + b) := by
    symm
    exact Finset.Ico_union_Ico_eq_Ico h₁ h₂
  unfold windowCount
  rw [show m + (a + b) = m + a + b by ring, hset, Finset.filter_union]
  rw [Finset.card_union_of_disjoint]
  apply Finset.disjoint_filter_filter
  apply Finset.disjoint_left.mpr
  intro x hx₁ hx₂
  simp only [mem_Ico] at hx₁ hx₂
  omega

lemma serviceCount_add
    {α : Type*} [DecidableEq α] (S : ℤ → α) (i : α)
    (m a b : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    serviceCount S i m (a + b) =
      serviceCount S i m a + serviceCount S i (m + a) b := by
  exact windowCount_add (fun t => S t = i) m a b ha hb

lemma serviceCount_nat_add
    {α : Type*} [DecidableEq α] (S : ℤ → α) (i : α)
    (m : ℤ) (a b : ℕ) :
    serviceCount S i m ((a + b : ℕ) : ℤ) =
      serviceCount S i m (a : ℤ) + serviceCount S i (m + (a : ℤ)) (b : ℤ) := by
  have := serviceCount_add S i (m : ℤ) (a : ℤ) (b : ℤ) (by omega) (by omega)
  simpa [Nat.cast_add] using this

lemma serviceCount_periodic_blocks
    {α : Type*} [DecidableEq α]
    (P : ℕ) (hP : 0 < P) (w : Fin P → α) (i : α)
    (m : ℤ) (q h : ℕ) :
    serviceCount (periodic P hP w) i m ((q * P + h : ℕ) : ℤ) =
      q * serviceCount (periodic P hP w) i m (P : ℤ) +
        serviceCount (periodic P hP w) i (m + (q * P : ℤ)) (h : ℤ) := by
  induction q generalizing m with
  | zero => simp
  | succ q ih =>
      calc
        serviceCount (periodic P hP w) i m ((Nat.succ q * P + h : ℕ) : ℤ) =
            serviceCount (periodic P hP w) i m
              ((P + (q * P + h) : ℕ) : ℤ) := by
                congr 2
                simp [Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        _ = serviceCount (periodic P hP w) i m (P : ℤ) +
              serviceCount (periodic P hP w) i (m + (P : ℤ))
                ((q * P + h : ℕ) : ℤ) := by
                simpa [Nat.cast_add] using
                  (serviceCount_nat_add (periodic P hP w) i m P (q * P + h))
        _ = serviceCount (periodic P hP w) i m (P : ℤ) +
              (q * serviceCount (periodic P hP w) i (m + (P : ℤ)) (P : ℤ) +
                serviceCount (periodic P hP w) i
                  (m + (P : ℤ) + (q * P : ℤ)) (h : ℤ)) := by
                rw [ih (m + (P : ℤ))]
        _ = (Nat.succ q) * serviceCount (periodic P hP w) i m (P : ℤ) +
              serviceCount (periodic P hP w) i
                (m + (Nat.succ q * P : ℤ)) (h : ℤ) := by
                have hs := serviceCount_shift_periodic P hP w i m (P : ℤ) 1
                rw [show m + 1 * (P : ℤ) = m + (P : ℤ) by ring] at hs
                rw [hs]
                have hstart : m + (P : ℤ) + (q * P : ℤ) =
                    m + (Nat.succ q * P : ℤ) := by
                  norm_num [Nat.cast_mul, Nat.succ_mul]
                  ring
                rw [hstart]
                simp [Nat.succ_eq_add_one, Nat.add_mul, Nat.add_assoc,
                  Nat.add_left_comm, Nat.add_comm]

lemma phase_val_eq_emod (P : ℕ) (hP : 0 < P) (m : ℤ) :
    ((phase P hP m).val : ℤ) = m % (P : ℤ) := by
  change (((m % (P : ℤ)).toNat : ℕ) : ℤ) = m % (P : ℤ)
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))

lemma int_eq_phase_add_quotient_period (P : ℕ) (hP : 0 < P) (m : ℤ) :
    m = (phase P hP m).val + (m / (P : ℤ)) * (P : ℤ) := by
  have hdiv := Int.ediv_mul_add_emod m (P : ℤ)
  rw [phase_val_eq_emod P hP m]
  omega

lemma serviceCount_periodic_blocks_phase
    (P : ℕ) (hP : 0 < P) (w : Fin P → Fin 5) (i : Fin 5)
    (m : ℤ) (q h : ℕ) :
    serviceCount (periodic P hP w) i m ((q * P + h : ℕ) : ℤ) =
      q * cyclicCount P hP w i (phase P hP m) P +
        cyclicCount P hP w i (phase P hP m) h := by
  let s : Fin P := phase P hP m
  have hblocks := serviceCount_periodic_blocks P hP w i m q h
  have hm : m = (s.val : ℤ) + (m / (P : ℤ)) * (P : ℤ) := by
    dsimp [s]
    exact int_eq_phase_add_quotient_period P hP m
  have hfull :
      serviceCount (periodic P hP w) i m (P : ℤ) =
        cyclicCount P hP w i s P := by
    calc
      serviceCount (periodic P hP w) i m (P : ℤ) =
          serviceCount (periodic P hP w) i
            ((s.val : ℤ) + (m / (P : ℤ)) * (P : ℤ)) (P : ℤ) := by
              exact congrArg (fun x =>
                serviceCount (periodic P hP w) i x (P : ℤ)) hm
      _ = serviceCount (periodic P hP w) i (s.val : ℤ) (P : ℤ) :=
        serviceCount_shift_periodic P hP w i (s.val : ℤ) (P : ℤ)
          (m / (P : ℤ))
      _ = cyclicCount P hP w i s P :=
        serviceCount_phase_eq_cyclicCount P hP w i s P
  have hres :
      serviceCount (periodic P hP w) i (m + (q * P : ℤ)) (h : ℤ) =
        cyclicCount P hP w i s h := by
    have hm' : m + (q * P : ℤ) =
        (s.val : ℤ) + ((m / (P : ℤ)) + (q : ℤ)) * (P : ℤ) := by
      calc
        m + (q * P : ℤ) =
            ((s.val : ℤ) + (m / (P : ℤ)) * (P : ℤ)) + (q * P : ℤ) := by
              exact congrArg (fun x => x + (q * P : ℤ)) hm
        _ = (s.val : ℤ) + ((m / (P : ℤ)) + (q : ℤ)) * (P : ℤ) := by
              push_cast
              ring
    calc
      serviceCount (periodic P hP w) i (m + (q * P : ℤ)) (h : ℤ) =
          serviceCount (periodic P hP w) i
            ((s.val : ℤ) + ((m / (P : ℤ)) + (q : ℤ)) * (P : ℤ)) (h : ℤ) := by
              exact congrArg (fun x =>
                serviceCount (periodic P hP w) i x (h : ℤ)) hm'
      _ = serviceCount (periodic P hP w) i (s.val : ℤ) (h : ℤ) :=
        serviceCount_shift_periodic P hP w i (s.val : ℤ) (h : ℤ)
          ((m / (P : ℤ)) + (q : ℤ))
      _ = cyclicCount P hP w i s h :=
        serviceCount_phase_eq_cyclicCount P hP w i s h
  change serviceCount (periodic P hP w) i m ((q * P + h : ℕ) : ℤ) =
      q * cyclicCount P hP w i s P + cyclicCount P hP w i s h
  rw [hblocks, hfull, hres]

abbrev MeanCap (c : RateCap) (P n : ℕ) : Prop :=
  c.bound * (P : ℚ) ≤ (n : ℚ)

abbrev ResidualCap (c : RateCap) (h n : ℕ) : Prop :=
  if c.closed then c.bound * (h : ℚ) < ((n + 1 : ℕ) : ℚ)
  else c.bound * (h : ℚ) ≤ ((n + 1 : ℕ) : ℚ)

abbrev WordCertificate (P : ℕ) (hP : 0 < P) (w : Fin P → Fin 5)
    (caps : Fin 5 → RateCap) : Prop :=
  ∀ (i : Fin 5) (s : Fin P),
    MeanCap (caps i) P (cyclicCount P hP w i s P) ∧
      ∀ h : Fin P, 0 < h.val →
        ResidualCap (caps i) h.val (cyclicCount P hP w i s h.val)

lemma rateCap_holds_le {c : RateCap} {x : ℝ} (h : c.Holds x) :
    x ≤ (c.bound : ℝ) := by
  by_cases hc : c.closed
  · simpa [RateCap.Holds, hc] using h
  · have hlt : x < (c.bound : ℝ) := by
      simpa [RateCap.Holds, hc] using h
    exact hlt.le

lemma rateCap_holds_lt_of_open {c : RateCap} {x : ℝ}
    (hc : ¬ c.closed) (h : c.Holds x) : x < (c.bound : ℝ) := by
  simpa [RateCap.Holds, hc] using h

lemma meanCap_real {c : RateCap} {P n : ℕ} (h : MeanCap c P n) :
    (c.bound : ℝ) * (P : ℝ) ≤ (n : ℝ) := by
  exact_mod_cast h

lemma residualCap_real_closed {c : RateCap} {h n : ℕ}
    (hc : c.closed) (hh : ResidualCap c h n) :
    (c.bound : ℝ) * (h : ℝ) < (n : ℝ) + 1 := by
  have hh' : c.bound * (h : ℚ) < ((n + 1 : ℕ) : ℚ) := by
    simpa [ResidualCap, hc] using hh
  exact_mod_cast hh'

lemma residualCap_real_open {c : RateCap} {h n : ℕ}
    (hc : ¬ c.closed) (hh : ResidualCap c h n) :
    (c.bound : ℝ) * (h : ℝ) ≤ (n : ℝ) + 1 := by
  have hh' : c.bound * (h : ℚ) ≤ ((n + 1 : ℕ) : ℚ) := by
    simpa [ResidualCap, hc] using hh
  exact_mod_cast hh'

lemma wordCertificate_mean_real
    {P : ℕ} {hP : 0 < P} {w : Fin P → Fin 5}
    {caps : Fin 5 → RateCap} (hcert : WordCertificate P hP w caps)
    (i : Fin 5) (s : Fin P) (r : Fin 5 → ℝ)
    (hr : CapsHold caps r) :
    (P : ℝ) * r i ≤ (cyclicCount P hP w i s P : ℝ) := by
  have hmean := (hcert i s).1
  have hmeanR := meanCap_real hmean
  have hbound : r i ≤ (caps i).bound := rateCap_holds_le (hr i)
  have hmul := mul_le_mul_of_nonneg_left hbound (by positivity : (0 : ℝ) ≤ P)
  calc
    (P : ℝ) * r i ≤ (P : ℝ) * (caps i).bound := hmul
    _ = (caps i).bound * (P : ℝ) := by ring
    _ ≤ (cyclicCount P hP w i s P : ℝ) := hmeanR

lemma wordCertificate_residual_real
    {P : ℕ} {hP : 0 < P} {w : Fin P → Fin 5}
    {caps : Fin 5 → RateCap} (hcert : WordCertificate P hP w caps)
    (i : Fin 5) (s : Fin P) (h : ℕ) (hh : 0 < h) (hlt : h < P)
    (r : Fin 5 → ℝ) (hr : CapsHold caps r) :
    (h : ℝ) * r i < (cyclicCount P hP w i s h : ℝ) + 1 := by
  have hres := (hcert i s).2 ⟨h, hlt⟩ hh
  by_cases hc : (caps i).closed
  · have hbound : r i ≤ (caps i).bound := rateCap_holds_le (hr i)
    have hmul := mul_le_mul_of_nonneg_left hbound
      (by exact_mod_cast (Nat.zero_le h) : (0 : ℝ) ≤ (h : ℝ))
    have hcap := residualCap_real_closed hc hres
    linarith
  · have hbound : r i < (caps i).bound :=
      rateCap_holds_lt_of_open hc (hr i)
    have hpos : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
    have hmul := mul_lt_mul_of_pos_left hbound hpos
    have hcap := residualCap_real_open hc hres
    linarith

theorem validRates_periodic_of_wordCertificate
    {P : ℕ} (hP : 0 < P) (w : Fin P → Fin 5)
    {caps : Fin 5 → RateCap} (hcert : WordCertificate P hP w caps)
    {r : Fin 5 → ℝ} (hr : CapsHold caps r) :
    ValidRates r (periodic P hP w) := by
  intro i m L
  let q : ℕ := L / P
  let h : ℕ := L % P
  let s : Fin P := phase P hP m
  have hlt : h < P := by
    dsimp [h]
    exact Nat.mod_lt L hP
  have hdecomp : q * P + h = L := by
    dsimp [q, h]
    exact Nat.div_add_mod' L P
  have hcount := serviceCount_periodic_blocks_phase P hP w i m q h
  have hcount' : serviceCount (periodic P hP w) i m (L : ℤ) =
      q * cyclicCount P hP w i s P + cyclicCount P hP w i s h := by
    rw [← hdecomp]
    simpa [s] using hcount
  have hmean := wordCertificate_mean_real hcert i s r hr
  by_cases hh : h = 0
  · have hL : (L : ℝ) = (q : ℝ) * (P : ℝ) := by
      have : L = q * P := by omega
      exact_mod_cast this
    have hq := mul_le_mul_of_nonneg_left hmean
      (by exact_mod_cast (Nat.zero_le q) : (0 : ℝ) ≤ (q : ℝ))
    rw [hcount', hh] at *
    push_cast at hq ⊢
    rw [hL]
    have hq' : (q : ℝ) * (P : ℝ) * r i ≤
        (q : ℝ) * (cyclicCount P hP w i s P : ℝ) := by
      simpa [mul_assoc] using hq
    norm_num
    linarith
  · have hres := wordCertificate_residual_real hcert i s h
      (by omega) hlt r hr
    have hL : (L : ℝ) = (q : ℝ) * (P : ℝ) + (h : ℝ) := by
      exact_mod_cast hdecomp.symm
    have hq := mul_le_mul_of_nonneg_left hmean
      (by exact_mod_cast (Nat.zero_le q) : (0 : ℝ) ≤ (q : ℝ))
    rw [hcount']
    push_cast at hq ⊢
    rw [hL]
    have hq' : (q : ℝ) * (P : ℝ) * r i ≤
        (q : ℝ) * (cyclicCount P hP w i s P : ℝ) := by
      simpa [mul_assoc] using hq
    linarith

end RealPinwheel
