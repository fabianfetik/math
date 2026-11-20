import CorralFormalization.DiversityCompletion.FixedSeedAssembly

/-! A motion's action on the fixed seed and each local letter determines
its action on the entire unlabelled assembled family. -/

namespace CorralFormalization.PhysicalCorral.FixedSeedSupport

variable {M : ℕ} {J A : Type*} [Fintype J]

theorem assembleFixed_motion (D : FixedSeedSupport (ZMod M) J A)
    (f : Motion M) (τ : J → J) (hτ : Function.Involutive τ) (σ : A → A)
    (hseed : f.onFamily D.fixedRows = D.fixedRows)
    (hlocal : ∀ j a, f.onFamily (D.letters j a) = D.letters (τ j) (σ a))
    (t : J → A) :
    f.onFamily (D.assembleFixed t) = D.assembleFixed (fun j => σ (t (τ j))) := by
  classical
  have hunion (F G : Finset (Finset (ZMod M))) :
      f.onFamily (F ∪ G) = f.onFamily F ∪ f.onFamily G := by
    simp [Motion.onFamily, Finset.image_union]
  have himage : f.onFamily (D.toSupportAlphabet.assemble t) =
      Finset.univ.biUnion (fun j => f.onFamily (D.letters j (t j))) := by
    ext S
    simp only [Motion.onFamily, SupportAlphabet.assemble, Finset.mem_image,
      Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨R, ⟨j, hR⟩, rfl⟩
      exact ⟨j, R, hR, rfl⟩
    · rintro ⟨j, R, hR, rfl⟩
      exact ⟨R, ⟨j, hR⟩, rfl⟩
  rw [assembleFixed, hunion, hseed, himage, assembleFixed]
  congr 1
  rw [SupportAlphabet.assemble]
  ext S
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj⟩
    rw [hlocal] at hj
    exact ⟨τ j, by simpa only [hτ j] using hj⟩
  · rintro ⟨j, hj⟩
    refine ⟨τ j, ?_⟩
    rw [hlocal]
    simpa only [hτ j] using hj

end CorralFormalization.PhysicalCorral.FixedSeedSupport
