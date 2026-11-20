import CorralFormalization.EndpointProof.Matching.Fractional.RawEvent.RowSum
import CorralFormalization.EndpointProof.Matching.Fractional.RawEvent.Candidates
import CorralFormalization.EndpointProof.Matching.Fractional.RobustWeights.PhysicalCoordinates

/-!
Raw-event estimates for the actual target matrices. Every sum is transported
through the existing balanced chart of the unchanged tagged target. Signed
roles 0 and 2 are reflected and role 1 is unchanged.
-/
open scoped Classical BigOperators Matrix Matrix.Norms.Operator symmDiff

namespace EndpointFractionalRawEvent
open EndpointOriginalReservoir EndpointFullProduct
open EndpointFlow.AbelianTransport EndpointMatching.AbsorptionAssembly
open EndpointMatching.UniversalCore EndpointMatching.Fractional.ActualRemainder
open EndpointMatching.Fractional.RobustWeights
noncomputable section
set_option maxHeartbeats 1500000
variable {G : Type*} [Fintype G] [AddCommGroup G]

/-- The balanced chart enumerates each actual signed role-coordinate set
exactly once; no surrogate or padded vertex set is used. -/
theorem actualCoordinate_image (W : Finset (Vertex G)) (hW : Balanced W) (r : Fin 3) :
    Finset.univ.image (fun j => actualCoordinate W hW (r,j)) = signedCoordinateSet W r := by
  ext g
  constructor
  · rintro hg
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hg
    apply (signedCoordinateSet_mem W r _).mpr
    let w := (balancedChart W hW).symm (r,j)
    have he : w.val = (r,actualCoordinate W hW (r,j)) :=
      Prod.ext (actualChart_part W hW (r,j)) rfl
    rw [← he]
    exact w.property
  · intro hg
    have hmem := (signedCoordinateSet_mem W r g).mp hg
    let w : W := ⟨(r,g),hmem⟩
    let j := (balancedChart W hW w).2
    have he : (r,j) = balancedChart W hW w := by
      apply Prod.ext
      · simp [w]
      · rfl
    refine Finset.mem_image.mpr ⟨j,Finset.mem_univ _,?_⟩
    unfold actualCoordinate
    rw [he,Equiv.symm_apply_apply]

/-- Sum transport through the actual balanced chart and rolewise physical
reflection. The two signs are applied once, including the colour role. -/
theorem actualCoordinate_sum_physical (W : Finset (Vertex G)) (hW : Balanced W)
    (T : PhysicalTarget G) (hT : signedCoordinateSet W = signedSets T)
    (r : Fin 3) (f : G → ℝ) :
    (∑ j, f (actualCoordinate W hW (r,j))) = ∑ g ∈ T r, f (signCoordinate r g) := by
  calc
    _ = ∑ g ∈ Finset.univ.image (fun j => actualCoordinate W hW (r,j)), f g :=
      (Finset.sum_image (fun i _ j _ hij => actualCoordinate_injective W hW r hij)).symm
    _ = ∑ g ∈ signedCoordinateSet W r, f g := by rw [actualCoordinate_image]
    _ = ∑ g ∈ signedSets T r, f g := by rw [hT]
    _ = _ := by
      unfold signedSets
      rw [Finset.sum_image]
      intro i _ j _ hij
      exact signCoordinate_injective r hij

/-- The actual raw matrix's complete row sum is exactly the previously
proved two-block raw-mask sum on the actual physical target columns. -/
theorem actualRawMatrix_row_sum_eq (W : Finset (Vertex G)) (hW : Balanced W)
    (T : PhysicalTarget G) (hT : signedCoordinateSet W = signedSets T)
    (s : OriginalSample G) (q : ℝ) (v : Fin 3 × CommonIndex W) :
    (∑ u, |actualRawMatrix W hW (signedSets (rawTarget s)) q v u|) =
      targetRawRowSum q s T v.1 (signCoordinate v.1 (actualCoordinate W hW v)) := by
  rw [Fintype.sum_prod_type]
  have hb (r : Fin 3) :
      (∑ j, |actualRawMatrix W hW (signedSets (rawTarget s)) q v (r,j)|) =
      if v.1=r then 0 else
        ∑ g ∈ T r, |setBit (rawTarget s (thirdRole v.1 r))
          (signCoordinate (thirdRole v.1 r) (-(actualCoordinate W hW v+signCoordinate r g)))-q| := by
    by_cases hr : v.1=r
    · simp [actualRawMatrix,offDiagonal,hr]
    · simp only [actualRawMatrix,offDiagonal,hr,if_false,requiredCoordinate]
      rw [actualCoordinate_sum_physical W hW T hT r
        (fun g => |setBit (signedSets (rawTarget s) (thirdRole v.1 r))
          (-(actualCoordinate W hW v+g))-q|)]
      simp_rw [signedSets_bit]
  simp_rw [hb]
  rcases v with ⟨r,j⟩
  fin_cases r <;>
    simp [targetRawRowSum,blockRowSum,partnerFirst,partnerSecond,partnerPerm,
      signCoordinate,thirdRole,Fin.sum_univ_succ,rawTarget,sub_eq_add_neg,
      neg_add_rev,add_comm,add_left_comm,add_assoc]

private theorem setBit_mul_sum (S : Finset G) (f : G → ℝ) :
    (∑ g, setBit S g*f g) = ∑ g ∈ S, f g := by
  simp only [setBit,ite_mul,one_mul,zero_mul]
  exact Finset.sum_ite_mem_eq S f

private theorem targetDegree_partner_sum (T : PhysicalTarget G) (r : Fin 3) (v : G) :
    targetDegree T r v = ∑ g ∈ T (partnerFirst r),
      setBit (T (partnerSecond r)) (partnerPerm r v g) := by
  fin_cases r <;> simp [targetDegree,partnerFirst,partnerSecond,partnerPerm,setBit_mul_sum]

/-- Any one partner role counts the actual degree exactly once. This is a
proved incidence identity and does not take degree correctness as input. -/
theorem familyDegree_eq_cross_sum {I E : Type*} [Fintype I] [DecidableEq I]
    [Fintype E] [DecidableEq E] (edge : E → Fin 3 → I) (v : Fin 3 × I) (r : Fin 3) :
    (familyDegree edge Finset.univ v : ℝ) = ∑ j, gram edge v (r,j) := by
  rw [← sum_family_incidence]
  simp only [gram,Matrix.mul_apply,Matrix.transpose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [← Finset.mul_sum]
  simp [incidence]

/-- The canonical actual edge type and balanced reindexing have exactly the
physical target degree used in the raw-event edit estimate. -/
theorem actualFamilyDegree_eq_targetDegree (W : Finset (Vertex G)) (hW : Balanced W)
    (T : PhysicalTarget G) (hT : signedCoordinateSet W = signedSets T)
    (v : Fin 3 × CommonIndex W) :
    (familyDegree (allowedEdgeIndex W hW ∅) Finset.univ v : ℝ) =
      targetDegree T v.1 (signCoordinate v.1 (actualCoordinate W hW v)) := by
  rw [familyDegree_eq_cross_sum _ v (partnerFirst v.1)]
  have hr : v.1 ≠ partnerFirst v.1 := by
    rcases v with ⟨r,j⟩
    fin_cases r <;> simp [partnerFirst]
  have hc (j : CommonIndex W) := actual_gram_cross W hW v (partnerFirst v.1,j) hr
  simp_rw [hc]
  simp only [requiredCoordinate]
  rw [actualCoordinate_sum_physical W hW T hT (partnerFirst v.1)
    (fun g => setBit (signedCoordinateSet W (thirdRole v.1 (partnerFirst v.1)))
      (-(actualCoordinate W hW v+g)))]
  simp_rw [hT,signedSets_bit]
  rw [targetDegree_partner_sum]
  rcases v with ⟨r,j⟩
  fin_cases r <;>
    simp [partnerFirst,partnerSecond,partnerPerm,signCoordinate,thirdRole,
      sub_eq_add_neg,neg_add_rev,add_comm,add_left_comm,add_assoc]

/-- The chart root is an actual member of the unchanged tagged target. -/
theorem actualCoordinate_mem (W : Finset (Vertex G)) (hW : Balanced W)
    (v : Fin 3 × CommonIndex W) : (v.1,actualCoordinate W hW v) ∈ W := by
  rcases v with ⟨r,j⟩
  apply (signedCoordinateSet_mem W r _).mp
  rw [← actualCoordinate_image W hW r]
  exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩

/-- A target with no colour zero has every chart root in the valid raw-degree
domain, including when an endpoint coordinate is zero. -/
theorem actualPhysicalRoot_valid (W : Finset (Vertex G)) (hW : Balanced W)
    (hC : (2,(0:G)) ∉ W) (v : Fin 3 × CommonIndex W) :
    v.1=2 → signCoordinate v.1 (actualCoordinate W hW v) ≠ 0 := by
  intro hr hz
  have hcoord : actualCoordinate W hW v = 0 := by simpa [signCoordinate,hr] using hz
  have hm := actualCoordinate_mem W hW v
  exact hC (by simpa [hr,hcoord] using hm)

/-- Decoding/reflection preserves every actual role size. -/
theorem physicalSets_card (W : Finset (Vertex G)) (r : Fin 3) :
    (physicalSets W r).card = (slice W r).card := by
  unfold physicalSets signedSets
  rw [Finset.card_image_of_injective _ (signCoordinate_injective r)]
  unfold signedCoordinateSet
  apply Finset.card_image_of_injOn
  intro v hv u hu hcoord
  apply Prod.ext
  · exact (Finset.mem_filter.mp hv).2.trans (Finset.mem_filter.mp hu).2.symm
  · exact hcoord

theorem physicalSets_balanced_card (W : Finset (Vertex G)) (hW : Balanced W) (r : Fin 3) :
    (physicalSets W r).card = Fintype.card (CommonIndex W) := by
  rw [physicalSets_card]
  simpa [CommonIndex,PartIndex] using hW r

/-- The raw-mask infinity norm is proved for the actual restricted matrix,
with its exact tagged target and the original signed raw masks. -/
theorem fractionalRawEvent_actualRawMatrix_norm_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2)
    {s : OriginalSample G} (hraw : fractionalRawEvent q s)
    (W : Finset (Vertex G)) (hW : Balanced W) (hC : (2,(0:G)) ∉ W)
    (hdist : (taggedDistance (signedRawTarget s) W : ℝ) ≤ rho q*(Fintype.card G : ℝ)) :
    ‖actualRawMatrix W hW (signedSets (rawTarget s)) q‖ ≤ 5*q^2*(Fintype.card G : ℝ) := by
  have hed : editDistance (physicalSets W) (rawTarget s) ≤ rho q*(Fintype.card G : ℝ) := by
    rw [physicalSets_taggedDistance]
    exact hdist
  apply matrix_norm_le_of_row_sum_le _ _ (by positivity)
  intro v
  rw [actualRawMatrix_row_sum_eq W hW (physicalSets W) (signedSets_physicalSets W).symm]
  exact fractionalRawEvent_targetRawRowSum_le hq0 hq1 hraw (physicalSets W) hed v.1
    (signCoordinate v.1 (actualCoordinate W hW v)) (actualPhysicalRoot_valid W hW hC v)

/-- The degree premise of the robust weights theorem now follows from the
raw event on the canonical actual edge family. No degree formula is assumed. -/
theorem fractionalRawEvent_actual_hdegree {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1/2)
    {s : OriginalSample G} (hraw : fractionalRawEvent q s)
    (W : Finset (Vertex G)) (hW : Balanced W) (hC : (2,(0:G)) ∉ W)
    (hdist : (taggedDistance (signedRawTarget s) W : ℝ) ≤ rho q*(Fintype.card G : ℝ)) :
    ∀ v : Fin 3 × CommonIndex W,
      |(familyDegree (allowedEdgeIndex W hW ∅) Finset.univ v : ℝ)-
        q*(Fintype.card (CommonIndex W) : ℝ)| ≤ 3*q^2*(Fintype.card G : ℝ)/10000 := by
  intro v
  have hed : editDistance (physicalSets W) (rawTarget s) ≤ rho q*(Fintype.card G : ℝ) := by
    rw [physicalSets_taggedDistance]
    exact hdist
  rw [actualFamilyDegree_eq_targetDegree W hW (physicalSets W) (signedSets_physicalSets W).symm]
  have h := fractionalRawEvent_target_diagonal_bound hq0 hq1 hraw (physicalSets W)
    (Fintype.card (CommonIndex W)) (physicalSets_balanced_card W hW) hed v.1
    (signCoordinate v.1 (actualCoordinate W hW v)) (actualPhysicalRoot_valid W hW hC v)
  unfold rho at h
  convert h using 1 <;> ring

/-- The constructed actual diagonal error matrix inherits the same paid
bound, in precisely the maximum absolute row-sum norm. -/
theorem fractionalRawEvent_actualDegreeMatrix_norm_le {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1/2)
    {s : OriginalSample G} (hraw : fractionalRawEvent q s)
    (W : Finset (Vertex G)) (hW : Balanced W) (hC : (2,(0:G)) ∉ W)
    (hdist : (taggedDistance (signedRawTarget s) W : ℝ) ≤ rho q*(Fintype.card G : ℝ)) :
    ‖actualDegreeMatrix W hW (q*(Fintype.card (CommonIndex W) : ℝ))‖ ≤
      3*q^2*(Fintype.card G : ℝ)/10000 := by
  apply degreeDiagonal_norm_le _ _ _ (by positivity)
  exact fractionalRawEvent_actual_hdegree hq0 hq1 hraw W hW hC hdist

/-- The actual membership edit norm is paid by the very same tagged distance.
This wrapper uses the existing constructive edit-matrix theorem. -/
theorem fractionalRawEvent_actualEditMatrix_norm_le {q : ℝ}
    {s : OriginalSample G} (W : Finset (Vertex G)) (hW : Balanced W)
    (hdist : (taggedDistance (signedRawTarget s) W : ℝ) ≤ rho q*(Fintype.card G : ℝ)) :
    ‖actualEditMatrix W hW (signedSets (rawTarget s))‖ ≤ q^2*(Fintype.card G : ℝ)/10000 := by
  calc
    _ ≤ rho q*(Fintype.card G : ℝ) :=
      (actualEditMatrix_norm_le_tagged W hW (rawTarget s)).trans hdist
    _ = q^2*(Fintype.card G : ℝ)/10000 := by unfold rho; ring

end
end EndpointFractionalRawEvent
