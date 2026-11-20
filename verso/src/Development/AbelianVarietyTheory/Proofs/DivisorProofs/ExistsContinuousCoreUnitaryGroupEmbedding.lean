import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfFrameCols
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryAdelicPointPrescribedFrameImagesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemUnitaryRationalPointsOfFrameImagesRationalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUnitaryAdelicOfFrameColumnsStatement
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

/- English proof (translation)
Use extensionality with `i k`. Simplify using `[cT, adMat, sigR, inclR]`.
-/
theorem adelicConjTranspose_adelicMatrixOfTensor {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    {a b : Type} (X : Matrix a b E) :
    cT (sigR (AF F) σ) (adMat F X) = adMat F (cT (σ : E →+* E) X) := by
  ext i k
  simp [cT, adMat, sigR, inclR]

/- English proof (translation)
Rewrite using `[adelicConjTranspose_adelicMatrixOfTensor]`. Simplify using `only [adMat, Matrix.map_mul]`.
-/
theorem adelicMatrixOfTensor_gram_conjTranspose_mul {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    {n a b : ℕ} (J : Matrix (Fin n) (Fin n) E) (X : Matrix (Fin n) (Fin a) E) (Y : Matrix (Fin n) (Fin b) E) :
    cT (sigR (AF F) σ) (adMat F X) * adMat F J * adMat F Y = adMat F (cT (σ : E →+* E) X * J * Y) := by
  rw [adelicConjTranspose_adelicMatrixOfTensor]
  simp only [adMat, Matrix.map_mul]

/- English proof (translation)
Simplify using `[cT, Matrix.map_mul, Matrix.transpose_mul]`.
-/
theorem ringHomConjTranspose_mul_rev {A : Type} [CommRing A] (s : A →+* A) {a b c : ℕ} (X : Matrix (Fin a) (Fin b) A)
    (Y : Matrix (Fin b) (Fin c) A) : cT s (X * Y) = cT s Y * cT s X := by
  simp [cT, Matrix.map_mul, Matrix.transpose_mul]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J j m C D Z J₀ hF`. Establish `hU : ∀ g : GAd σ J₀, cT (sigR (AF F) σ) (matHom _ σ J₀ g).1 * adMat F J₀ * (matHom _ σ J₀ g).1 = adMat F J₀` using `fun g => g.2`. Establish `hZ' : ∀ g : GAd σ J₀, cT (sigR (AF F) σ) (adMat F Z * (matHom _ σ J₀ g).1) * adMat F J * (adMat F Z * (matHom _ σ J₀ g).1) = adMat F J₀`. Introduce `g`. Rewrite using `[ringHomConjTranspose_mul_rev]`.

Establish `h` using `adelicMatrixOfTensor_gram_conjTranspose_mul (F := F) σ J Z Z`. Rewrite `h` using `[hF.zz]`. Combine the equalities or inequalities in the displayed calculation. Establish `img : ∀ g : GAd σ J₀, ∃ h : GAd σ J, (matHom _ σ J h).1 * adMat F C = adMat F C ∧ (matHom _ σ J h).1 * adMat F Z = adMat F Z * (matHom _ σ J₀ g).1 ∧ (matHom _ σ J h).1 * adMat F D = adMat F D` using `fun g => GlobalTheory.T.exists_unitaryAdelicPoint_prescribed_frameImages F E σ n J j m C D Z J₀ hF (adMat F C) (adMat F D) (adMat F Z * (matHom _ σ J₀ g).1) (by rw [adelicMatrixOfTensor_gram_conjTranspose_mul, hF.cc]; simp [adMat]) (by rw [adelicMatrixOfTensor_gram_conjTranspose_ …`. Use `choose f hC hZ hD using img`.

Establish `hmul : ∀ a b, f (a * b) = f a * f b`. Introduce `a b`. Apply `GlobalTheory.SphEis.eq_of_frame_cols F E σ n J j m C D Z J₀ hF` to reduce the goal to its premises. Rewrite using `[hC, map_mul, Units.val_mul, Matrix.mul_assoc, hC, hC]`. Rewrite using `[hZ]`.

Use `symm`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_mul, Units.val_mul, Matrix.mul_assoc]`. Use `_ = ((matHom _ σ J (f a)).1 * adMat F Z) * (matHom _ σ J₀ b).1 := by rw [hZ, Matrix.mul_assoc]`. Use `_ = _ := by rw [hZ, map_mul, Units.val_mul, Matrix.mul_assoc]`.

Rewrite using `[hD, map_mul, Units.val_mul, Matrix.mul_assoc, hD, hD]`. Use `⟨MonoidHom.mk' f hmul, ?_, fun g => ⟨hC g, hD g, hZ g⟩, ?_⟩` and prove the remaining obligations. Use `haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩ haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _`. Apply `GlobalTheory.T.continuous_unitaryAdelic_of_frameColumns F E σ n J j m C D Z J₀ hF (GAd σ J₀) f` to reduce the goal to its premises. Simplify using `only [hC]`.

Conclude with `continuous_const`. Simplify using `only [hZ]`. Conclude with `continuous_const.matrix_mul (Units.continuous_val.comp (isEmbedding_matHom (AF F) σ J₀).continuous)`. Simplify using `only [hD]`. Conclude with `continuous_const`.

Introduce `g hg`. Express the relevant statement in the definitionally equal form `(matHom _ σ J₀ g) ∈ HFin (AF F) σ J₀ at hg`. Rewrite `hg` using `[HFin, Subgroup.mem_map]`. Take `⟨γ, -, hγ⟩` from `hg`. Establish `hg' : (matHom _ σ J₀ g).1 = adMat F γ.1`.

Rewrite using `[← hγ]`. Both sides reduce to the same expression. Apply `GlobalTheory.T.mem_unitaryRationalPoints_of_frameImages_rational F E σ n J j m C D Z J₀ hF (f g) C D (Z * γ.1) (hC g)` to reduce the goal to its premises. Rewrite using `[hZ, hg', adMat, adMat, adMat, Matrix.map_mul]`. Conclude with `hD g`.
-/
theorem core_embeds : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∃ e : GAd σ J₀ →* GAd σ J, Continuous e ∧ (∀ g, e g ∈ fixG σ J C ∧ e g ∈ fixG σ J D ∧ (matHom _ σ J (e g)).1 * adMat F Z = adMat F Z * (matHom _ σ J₀ g).1) ∧ ∀ g ∈ ratPts σ J₀, e g ∈ ratPts σ J := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF
  have hU : ∀ g : GAd σ J₀, cT (sigR (AF F) σ) (matHom _ σ J₀ g).1 * adMat F J₀ * (matHom _ σ J₀ g).1 = adMat F J₀ :=
    fun g => g.2
  have hZ' : ∀ g : GAd σ J₀, cT (sigR (AF F) σ) (adMat F Z * (matHom _ σ J₀ g).1) * adMat F J *
      (adMat F Z * (matHom _ σ J₀ g).1) = adMat F J₀ := by
    intro g
    rw [ringHomConjTranspose_mul_rev]
    have h := adelicMatrixOfTensor_gram_conjTranspose_mul (F := F) σ J Z Z
    rw [hF.zz] at h
    calc _ = cT (sigR (AF F) σ) (matHom _ σ J₀ g).1 * (cT (sigR (AF F) σ) (adMat F Z) * adMat F J * adMat F Z) *
          (matHom _ σ J₀ g).1 := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h, hU]
  have img : ∀ g : GAd σ J₀, ∃ h : GAd σ J, (matHom _ σ J h).1 * adMat F C = adMat F C ∧
      (matHom _ σ J h).1 * adMat F Z = adMat F Z * (matHom _ σ J₀ g).1 ∧ (matHom _ σ J h).1 * adMat F D = adMat F D :=
    fun g => GlobalTheory.T.exists_unitaryAdelicPoint_prescribed_frameImages F E σ n J j m C D Z J₀ hF (adMat F C) (adMat F D) (adMat F Z * (matHom _ σ J₀ g).1)
      (by rw [adelicMatrixOfTensor_gram_conjTranspose_mul, hF.cc]; simp [adMat]) (by rw [adelicMatrixOfTensor_gram_conjTranspose_mul, hF.dd]; simp [adMat])
      (by rw [adelicMatrixOfTensor_gram_conjTranspose_mul, hF.cd]; simp [adMat])
      (by rw [← Matrix.mul_assoc, adelicMatrixOfTensor_gram_conjTranspose_mul, hF.cz]; simp [adMat])
      (by rw [← Matrix.mul_assoc, adelicMatrixOfTensor_gram_conjTranspose_mul, hF.dz]; simp [adMat]) (hZ' g)
  choose f hC hZ hD using img
  have hmul : ∀ a b, f (a * b) = f a * f b := by
    intro a b
    apply GlobalTheory.SphEis.eq_of_frame_cols F E σ n J j m C D Z J₀ hF
    · rw [hC, map_mul, Units.val_mul, Matrix.mul_assoc, hC, hC]
    · rw [hZ]
      symm
      calc (matHom _ σ J (f a * f b)).1 * adMat F Z
          = (matHom _ σ J (f a)).1 * ((matHom _ σ J (f b)).1 * adMat F Z) := by
            rw [map_mul, Units.val_mul, Matrix.mul_assoc]
        _ = ((matHom _ σ J (f a)).1 * adMat F Z) * (matHom _ σ J₀ b).1 := by rw [hZ, Matrix.mul_assoc]
        _ = _ := by rw [hZ, map_mul, Units.val_mul, Matrix.mul_assoc]
    · rw [hD, map_mul, Units.val_mul, Matrix.mul_assoc, hD, hD]
  refine ⟨MonoidHom.mk' f hmul, ?_, fun g => ⟨hC g, hD g, hZ g⟩, ?_⟩
  · haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
    haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
    apply GlobalTheory.T.continuous_unitaryAdelic_of_frameColumns F E σ n J j m C D Z J₀ hF (GAd σ J₀) f
    · simp only [hC]; exact continuous_const
    · simp only [hZ]
      exact continuous_const.matrix_mul (Units.continuous_val.comp (isEmbedding_matHom (AF F) σ J₀).continuous)
    · simp only [hD]; exact continuous_const
  · intro g hg
    change (matHom _ σ J₀ g) ∈ HFin (AF F) σ J₀ at hg
    rw [HFin, Subgroup.mem_map] at hg
    obtain ⟨γ, -, hγ⟩ := hg
    have hg' : (matHom _ σ J₀ g).1 = adMat F γ.1 := by
      rw [← hγ]; rfl
    apply GlobalTheory.T.mem_unitaryRationalPoints_of_frameImages_rational F E σ n J j m C D Z J₀ hF (f g) C D (Z * γ.1) (hC g)
    · rw [hZ, hg', adMat, adMat, adMat, Matrix.map_mul]
    · exact hD g

end GlobalTheory.SphEis
