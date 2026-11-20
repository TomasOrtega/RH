import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DOpMemDStep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.ConeEuler
open GlobalTheory.ThK.EvAt0.PolD GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)
open Classical

noncomputable section

namespace GlobalTheory.ThK.EvAt0.PolD.Comm

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

/- English proof (translation)
Establish `e : lin b = ⇑(Complex.ofRealCLM.comp (linL b))`. Use function extensionality and compare the values at `x`. Simplify using `[lin, linL_apply]`. Rewrite using `[e]`. Conclude with `(Complex.ofRealCLM.comp (linL b)).hasFDerivAt`.
-/
theorem hasFDerivAt_lin (b x : κ → mixedEmbedding.mixedSpace F) :
    HasFDerivAt (lin b) (Complex.ofRealCLM.comp (linL b)) x := by
  have e : lin b = ⇑(Complex.ofRealCLM.comp (linL b)) := by
    funext x; simp [lin, linL_apply]
  rw [e]
  exact (Complex.ofRealCLM.comp (linL b)).hasFDerivAt

/- English proof (translation)
Establish `e : (⇑(dOp a' b' f)) = fun y => fderiv ℝ f y a' - 2 * Real.pi * Complex.I * (lin b' y * f y)`. Use function extensionality and compare the values at `y`. Rewrite using `[dOp_apply]`. Expand and normalize the polynomial expressions, which then agree. Establish `hs : ContDiff ℝ 2 (⇑f)` using `f.smooth 2`.

Establish `h1 : DifferentiableAt ℝ (fderiv ℝ (⇑f)) x` using `((hs.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x`. Establish `h2 : HasFDerivAt (fun y => fderiv ℝ (⇑f) y a') _ x` using `h1.hasFDerivAt.clm_apply (hasFDerivAt_const a' x)`. Establish `h3 : HasFDerivAt (⇑f) (fderiv ℝ (⇑f) x) x` using `f.differentiableAt.hasFDerivAt`. Establish `h4` using `h2.sub (((hasFDerivAt_lin b' x).mul h3).const_mul (2 * Real.pi * Complex.I : ℂ))`. Rewrite using `[e]`.

Establish `h5` using `h4.fderiv`. Establish `h6 : fderiv ℝ (fun y => fderiv ℝ (⇑f) y a' - 2 * Real.pi * Complex.I * (lin b' y * f y)) x = _` using `h5`. Rewrite using `[h6]`. Simplify using `[lin, linL_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fderiv_dOp (a a' b' : κ → mixedEmbedding.mixedSpace F) (f : SInf F κ)
    (x : κ → mixedEmbedding.mixedSpace F) :
    fderiv ℝ (dOp a' b' f) x a = fderiv ℝ (fderiv ℝ f) x a a' -
      2 * Real.pi * Complex.I * (lin b' a * f x + lin b' x * fderiv ℝ f x a) := by
  have e : (⇑(dOp a' b' f)) = fun y => fderiv ℝ f y a' - 2 * Real.pi * Complex.I * (lin b' y * f y) := by
    funext y; rw [dOp_apply]; ring
  have hs : ContDiff ℝ 2 (⇑f) := f.smooth 2
  have h1 : DifferentiableAt ℝ (fderiv ℝ (⇑f)) x :=
    ((hs.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x
  have h2 : HasFDerivAt (fun y => fderiv ℝ (⇑f) y a') _ x :=
    h1.hasFDerivAt.clm_apply (hasFDerivAt_const a' x)
  have h3 : HasFDerivAt (⇑f) (fderiv ℝ (⇑f) x) x := f.differentiableAt.hasFDerivAt
  have h4 := h2.sub (((hasFDerivAt_lin b' x).mul h3).const_mul (2 * Real.pi * Complex.I : ℂ))
  rw [e]
  have h5 := h4.fderiv
  have h6 : fderiv ℝ (fun y => fderiv ℝ (⇑f) y a' - 2 * Real.pi * Complex.I * (lin b' y * f y)) x = _ := h5
  rw [h6]
  simp [lin, linL_apply]
  ring

/- English proof (translation)
Use extensionality with `x`. Establish `hs : ContDiff ℝ 2 (⇑f)` using `f.smooth 2`. Establish `hsym : IsSymmSndFDerivAt ℝ (⇑f) x` using `hs.contDiffAt.isSymmSndFDerivAt (by simp)`. Establish `h` using `hsym.eq a a'`. Rewrite using `[SchwartzMap.sub_apply, SchwartzMap.smul_apply, dOp_apply a b, dOp_apply a' b' (dOp a b f), fderiv_dOp, fderiv_dOp, dOp_apply, dOp_apply, h, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem dOp_comm (a b a' b' : κ → mixedEmbedding.mixedSpace F) (f : SInf F κ) :
    dOp a b (dOp a' b' f) - dOp a' b' (dOp a b f) =
      (-(2 * Real.pi * Complex.I * (lin b' a - lin b a')) : ℂ) • f := by
  ext x
  have hs : ContDiff ℝ 2 (⇑f) := f.smooth 2
  have hsym : IsSymmSndFDerivAt ℝ (⇑f) x := hs.contDiffAt.isSymmSndFDerivAt (by simp)
  have h := hsym.eq a a'
  rw [SchwartzMap.sub_apply, SchwartzMap.smul_apply, dOp_apply a b, dOp_apply a' b' (dOp a b f),
    fderiv_dOp, fderiv_dOp, dOp_apply, dOp_apply, h, smul_eq_mul]
  ring

/- English proof (translation)
Introduce `_ _ _ _ _ a b a' b'` and use `⟨_, dOp_comm a b a' b'⟩`.
-/
theorem dOp_comm_scalar : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (a b a' b' : κ → mixedEmbedding.mixedSpace F),
    ∃ s : ℂ, ∀ f : SInf F κ, dOp a b (dOp a' b' f) - dOp a' b' (dOp a b f) = s • f :=
  fun _ _ _ _ _ a b a' b' => ⟨_, dOp_comm a b a' b'⟩

end GlobalTheory.ThK.EvAt0.PolD.Comm
