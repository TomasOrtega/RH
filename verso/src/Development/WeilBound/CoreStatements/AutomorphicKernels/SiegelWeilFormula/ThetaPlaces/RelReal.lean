import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.IsPureTIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterUnramifiedExponent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.ThetaDictR

open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def thW (B : Base F E) (w : InfinitePlace F) : HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ :=
  (starRingEnd ℂ).comp ((infEmb (B.emb w)).comp
    (Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id F E)).toRingHom)

/- English proof (translation)
The claim follows from `GlobalTheory.StdCharFromIsStd.isCharAF hB.std`.
-/
theorem isCharAF_of_good (B : Base F E) (hB : B.IsGood σ) : HeckeCharacterZeroLocus.SiegelWeilU.IsCharAF F B.ψ :=
  GlobalTheory.StdCharFromIsStd.isCharAF hB.std

def cW (B : Base F E) (η : E) (w : InfinitePlace F) : ℂ := ((‖(B.emb w).1 η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)

/- English proof (translation)
Establish `h1 : (B.emb w).1 η ≠ 0` using `(map_ne_zero _).2 hη`. Establish `h2 : 0 < ‖(B.emb w).1 η‖` using `norm_pos_iff.2 h1`. Unfold `cW`. Conclude with `(Real.rpow_pos_of_pos h2 _).ne'` after adjusting the coercions.
-/
theorem cW_ne (B : Base F E) {η : E} (hη : η ≠ 0) (w : InfinitePlace F) : cW B η w ≠ 0 := by
  have h1 : (B.emb w).1 η ≠ 0 := (map_ne_zero _).2 hη
  have h2 : 0 < ‖(B.emb w).1 η‖ := norm_pos_iff.2 h1
  unfold cW
  exact_mod_cast (Real.rpow_pos_of_pos h2 _).ne'

/- English proof (translation)
Rewrite using `[isUnit_iff_ne_zero, Matrix.det_smul]`. Use `mul_ne_zero (pow_ne_zero _ (cW_ne d.B hη w)) ?_` and prove the remaining obligations. Establish `hu : IsUnit (R.fr w).1.det` using `(Matrix.isUnit_iff_isUnit_det _).1 (R.fr w).isUnit`. Establish `e : ((R.fr w).1.map star).det = star (R.fr w).1.det`. Rewrite using `[← Matrix.det_conjTranspose, ← Matrix.det_transpose ((R.fr w).1)ᴴ]`.

Both sides reduce to the same expression. Rewrite using `[e, star_ne_zero]`. Conclude with `hu.ne_zero`.
-/
theorem frW_det {d : SD σ} (R : RD d) {η : E} (hη : η ≠ 0) (w : InfinitePlace F) :
    IsUnit (cW d.B η w • (R.fr w).1.map star).det := by
  rw [isUnit_iff_ne_zero, Matrix.det_smul]
  refine mul_ne_zero (pow_ne_zero _ (cW_ne d.B hη w)) ?_
  have hu : IsUnit (R.fr w).1.det := (Matrix.isUnit_iff_isUnit_det _).1 (R.fr w).isUnit
  have e : ((R.fr w).1.map star).det = star (R.fr w).1.det := by
    rw [← Matrix.det_conjTranspose, ← Matrix.det_transpose ((R.fr w).1)ᴴ]; rfl
  rw [e, star_ne_zero]
  exact hu.ne_zero

def frW {d : SD σ} (R : RD d) (η : E) (hη : η ≠ 0) (w : InfinitePlace F) : GL (Fin d.m) ℂ :=
  Matrix.nonsingInvUnit (cW d.B η w • (R.fr w).1.map star) (frW_det R hη w)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem frW_frc {d : SD σ} (R : RD d) (η : E) (hη : η ≠ 0) (w : InfinitePlace F) :
    (frW R η hη w).1 = cW d.B η w • (R.fr w).1.map star := rfl

/- English proof (translation)
Rewrite using `[isUnit_iff_ne_zero, Matrix.det_smul]`. Use `mul_ne_zero (pow_ne_zero _ (cW_ne d.B hη w)) ?_` and prove the remaining obligations. Establish `hu : IsUnit u.1.det` using `(Matrix.isUnit_iff_isUnit_det _).1 u.isUnit`. Establish `h1 : (d.cw w u.1).det = piInf (d.B.emb w) u.1.det`. Unfold `SD.cw`.

Rewrite using `[RingHom.map_det]`. Both sides reduce to the same expression. Establish `h2 : (((d.cw w u.1)ᵀ).map star).det = star (d.cw w u.1).det`. Rewrite using `[← Matrix.det_conjTranspose]`. Both sides reduce to the same expression.

Rewrite using `[Matrix.det_nonsing_inv, Ring.inverse_eq_inv', h2, h1]`. Conclude with `inv_ne_zero (star_ne_zero.2 (hu.map (piInf (d.B.emb w))).ne_zero)`.
-/
theorem gW_det (d : SD σ) (u : GL (Fin d.n) (AE F E)) {η : E} (hη : η ≠ 0) (w : InfinitePlace F) :
    IsUnit (cW d.B η w • (((d.cw w u.1)ᵀ).map star)⁻¹).det := by
  rw [isUnit_iff_ne_zero, Matrix.det_smul]
  refine mul_ne_zero (pow_ne_zero _ (cW_ne d.B hη w)) ?_
  have hu : IsUnit u.1.det := (Matrix.isUnit_iff_isUnit_det _).1 u.isUnit
  have h1 : (d.cw w u.1).det = piInf (d.B.emb w) u.1.det := by
    unfold SD.cw; rw [RingHom.map_det]; rfl
  have h2 : (((d.cw w u.1)ᵀ).map star).det = star (d.cw w u.1).det := by
    rw [← Matrix.det_conjTranspose]; rfl
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv', h2, h1]
  exact inv_ne_zero (star_ne_zero.2 (hu.map (piInf (d.B.emb w))).ne_zero)

def gW (d : SD σ) (u : GL (Fin d.n) (AE F E)) (η : E) (hη : η ≠ 0) (w : InfinitePlace F) : GL (Fin d.n) ℂ :=
  Matrix.nonsingInvUnit (cW d.B η w • (((d.cw w u.1)ᵀ).map star)⁻¹) (gW_det d u hη w)

/- English proof (translation)
Establish `hu : IsUnit u.1.det` using `(Matrix.isUnit_iff_isUnit_det _).1 u.isUnit`. Establish `hN : IsUnit (((d.cw w u.1)ᵀ).map star).det`. Establish `h1 : (d.cw w u.1).det = piInf (d.B.emb w) u.1.det`. Unfold `SD.cw`. Rewrite using `[RingHom.map_det]`.

Both sides reduce to the same expression. Establish `h2 : (((d.cw w u.1)ᵀ).map star).det = star (d.cw w u.1).det`. Rewrite using `[← Matrix.det_conjTranspose]`. Both sides reduce to the same expression. Rewrite using `[h2, h1, isUnit_iff_ne_zero, star_ne_zero]`.

Conclude with `(hu.map (piInf (d.B.emb w))).ne_zero`. Express the relevant statement in the definitionally equal form `(cW d.B η w • (((d.cw w u.1)ᵀ).map star)⁻¹) * ((d.cw w u.1)ᵀ).map star = cW d.B η w • 1`. Rewrite using `[Matrix.smul_mul, Matrix.nonsing_inv_mul _ hN]`.
-/
theorem gW_gc (d : SD σ) (u : GL (Fin d.n) (AE F E)) (η : E) (hη : η ≠ 0) (w : InfinitePlace F) :
    (gW d u η hη w).1 * ((d.cw w u.1)ᵀ).map star = cW d.B η w • 1 := by
  have hu : IsUnit u.1.det := (Matrix.isUnit_iff_isUnit_det _).1 u.isUnit
  have hN : IsUnit (((d.cw w u.1)ᵀ).map star).det := by
    have h1 : (d.cw w u.1).det = piInf (d.B.emb w) u.1.det := by
      unfold SD.cw; rw [RingHom.map_det]; rfl
    have h2 : (((d.cw w u.1)ᵀ).map star).det = star (d.cw w u.1).det := by
      rw [← Matrix.det_conjTranspose]; rfl
    rw [h2, h1, isUnit_iff_ne_zero, star_ne_zero]
    exact (hu.map (piInf (d.B.emb w))).ne_zero
  change (cW d.B η w • (((d.cw w u.1)ᵀ).map star)⁻¹) * ((d.cw w u.1)ᵀ).map star = cW d.B η w • 1
  rw [Matrix.smul_mul, Matrix.nonsing_inv_mul _ hN]

def εsW {d : SD σ} (R : RD d) (η : E) (w : InfinitePlace F) (_ : Fin d.m) : Bool :=
  decide (0 < (((d.B.emb w).1 η / R.ζ) * ((R.sg w : ℤ) : ℂ)).re)

end PositivityTheory.SiegelWeilFormula.ThetaDictR

end
