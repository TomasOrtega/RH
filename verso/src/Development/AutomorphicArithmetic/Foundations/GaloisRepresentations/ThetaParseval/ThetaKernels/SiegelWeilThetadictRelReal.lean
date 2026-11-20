import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaPlaces.RelReal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.ThetaDictR
open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
/- English proof (translation)
The claim follows from `GlobalTheory.StdCharFromIsStd.isCharAF hB.std`.
-/
theorem isCharAF_of_good_k (B : Base F E) (hB : _root_.UpperTheory.TP.W.GoodK σ B) : HeckeCharacterZeroLocus.SiegelWeilU.IsCharAF F B.ψ :=
  GlobalTheory.StdCharFromIsStd.isCharAF hB.std
/- English proof (translation)
Rewrite using `[isUnit_iff_ne_zero, Matrix.det_smul]`. Use `mul_ne_zero (pow_ne_zero _ (cW_ne d.B hη w)) ?_` and prove the remaining obligations. Establish `hu : IsUnit (R.fr w).1.det` using `(Matrix.isUnit_iff_isUnit_det _).1 (R.fr w).isUnit`. Establish `e : ((R.fr w).1.map star).det = star (R.fr w).1.det`. Rewrite using `[← Matrix.det_conjTranspose, ← Matrix.det_transpose ((R.fr w).1)ᴴ]`.

Both sides reduce to the same expression. Rewrite using `[e, star_ne_zero]`. Conclude with `hu.ne_zero`.
-/
theorem frW_det_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {η : E} (hη : η ≠ 0) (w : InfinitePlace F) :
    IsUnit (cW d.B η w • (R.fr w).1.map star).det := by
  rw [isUnit_iff_ne_zero, Matrix.det_smul]
  refine mul_ne_zero (pow_ne_zero _ (cW_ne d.B hη w)) ?_
  have hu : IsUnit (R.fr w).1.det := (Matrix.isUnit_iff_isUnit_det _).1 (R.fr w).isUnit
  have e : ((R.fr w).1.map star).det = star (R.fr w).1.det := by
    rw [← Matrix.det_conjTranspose, ← Matrix.det_transpose ((R.fr w).1)ᴴ]; rfl
  rw [e, star_ne_zero]
  exact hu.ne_zero
def frW_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (η : E) (hη : η ≠ 0) (w : InfinitePlace F) : GL (Fin d.m) ℂ :=
  Matrix.nonsingInvUnit (cW d.B η w • (R.fr w).1.map star) (_root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.frW_det_k R hη w)
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem frW_frc_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (η : E) (hη : η ≠ 0) (w : InfinitePlace F) :
    (_root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.frW_k R η hη w).1 = cW d.B η w • (R.fr w).1.map star := rfl
/- English proof (translation)
Rewrite using `[isUnit_iff_ne_zero, Matrix.det_smul]`. Use `mul_ne_zero (pow_ne_zero _ (cW_ne d.B hη w)) ?_` and prove the remaining obligations. Establish `hu : IsUnit u.1.det` using `(Matrix.isUnit_iff_isUnit_det _).1 u.isUnit`. Establish `h1 : (d.cw w u.1).det = piInf (d.B.emb w) u.1.det`. Unfold `_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw`.

Rewrite using `[RingHom.map_det]`. Both sides reduce to the same expression. Establish `h2 : (((d.cw w u.1)ᵀ).map star).det = star (d.cw w u.1).det`. Rewrite using `[← Matrix.det_conjTranspose]`. Both sides reduce to the same expression.

Rewrite using `[Matrix.det_nonsing_inv, Ring.inverse_eq_inv', h2, h1]`. Conclude with `inv_ne_zero (star_ne_zero.2 (hu.map (piInf (d.B.emb w))).ne_zero)`.
-/
theorem gW_det_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (u : GL (Fin d.n) (AE F E)) {η : E} (hη : η ≠ 0) (w : InfinitePlace F) :
    IsUnit (cW d.B η w • (((d.cw w u.1)ᵀ).map star)⁻¹).det := by
  rw [isUnit_iff_ne_zero, Matrix.det_smul]
  refine mul_ne_zero (pow_ne_zero _ (cW_ne d.B hη w)) ?_
  have hu : IsUnit u.1.det := (Matrix.isUnit_iff_isUnit_det _).1 u.isUnit
  have h1 : (d.cw w u.1).det = piInf (d.B.emb w) u.1.det := by
    unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw; rw [RingHom.map_det]; rfl
  have h2 : (((d.cw w u.1)ᵀ).map star).det = star (d.cw w u.1).det := by
    rw [← Matrix.det_conjTranspose]; rfl
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv', h2, h1]
  exact inv_ne_zero (star_ne_zero.2 (hu.map (piInf (d.B.emb w))).ne_zero)
def gW_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (u : GL (Fin d.n) (AE F E)) (η : E) (hη : η ≠ 0) (w : InfinitePlace F) : GL (Fin d.n) ℂ :=
  Matrix.nonsingInvUnit (cW d.B η w • (((d.cw w u.1)ᵀ).map star)⁻¹) (_root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.gW_det_k d u hη w)
/- English proof (translation)
Establish `hu : IsUnit u.1.det` using `(Matrix.isUnit_iff_isUnit_det _).1 u.isUnit`. Establish `hN : IsUnit (((d.cw w u.1)ᵀ).map star).det`. Establish `h1 : (d.cw w u.1).det = piInf (d.B.emb w) u.1.det`. Unfold `_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw`. Rewrite using `[RingHom.map_det]`.

Both sides reduce to the same expression. Establish `h2 : (((d.cw w u.1)ᵀ).map star).det = star (d.cw w u.1).det`. Rewrite using `[← Matrix.det_conjTranspose]`. Both sides reduce to the same expression. Rewrite using `[h2, h1, isUnit_iff_ne_zero, star_ne_zero]`.

Conclude with `(hu.map (piInf (d.B.emb w))).ne_zero`. Express the relevant statement in the definitionally equal form `(cW d.B η w • (((d.cw w u.1)ᵀ).map star)⁻¹) * ((d.cw w u.1)ᵀ).map star = cW d.B η w • 1`. Rewrite using `[Matrix.smul_mul, Matrix.nonsing_inv_mul _ hN]`.
-/
theorem gW_gc_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (u : GL (Fin d.n) (AE F E)) (η : E) (hη : η ≠ 0) (w : InfinitePlace F) :
    (_root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.gW_k d u η hη w).1 * ((d.cw w u.1)ᵀ).map star = cW d.B η w • 1 := by
  have hu : IsUnit u.1.det := (Matrix.isUnit_iff_isUnit_det _).1 u.isUnit
  have hN : IsUnit (((d.cw w u.1)ᵀ).map star).det := by
    have h1 : (d.cw w u.1).det = piInf (d.B.emb w) u.1.det := by
      unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw; rw [RingHom.map_det]; rfl
    have h2 : (((d.cw w u.1)ᵀ).map star).det = star (d.cw w u.1).det := by
      rw [← Matrix.det_conjTranspose]; rfl
    rw [h2, h1, isUnit_iff_ne_zero, star_ne_zero]
    exact (hu.map (piInf (d.B.emb w))).ne_zero
  change (cW d.B η w • (((d.cw w u.1)ᵀ).map star)⁻¹) * ((d.cw w u.1)ᵀ).map star = cW d.B η w • 1
  rw [Matrix.smul_mul, Matrix.nonsing_inv_mul _ hN]
def εsW_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (η : E) (w : InfinitePlace F) (_ : Fin d.m) : Bool :=
  decide (0 < (((d.B.emb w).1 η / R.ζ) * ((R.sg w : ℤ) : ℂ)).re)
end PositivityTheory.SiegelWeilFormula.ThetaDictR
end
end
