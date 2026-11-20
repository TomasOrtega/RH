import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormAtStandardFrameEqNormComplexForm
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrmOfPosDef
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
open NumberField Formalism.L2.DIV Formalism.L2.Rows GlobalTheory.AmbCrd
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FNormAtStandardFrameEqNormComplexForm.lean&line=83#L83)
-/
theorem _root_.GlobalTheory.T.normAt_standardFrame_eq_norm_complexForm : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (σ : K →+* ℂ), (∀ a, σ (star a) = starRingEnd ℂ (σ a)) → ∀ {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {n : ℕ} (j : (Fin n → K) →ₛₗ[σ] W) (H E : Matrix (Fin n) (Fin n) K) (op : W →ₗ[ℂ] W), Formalism.L2.DIV.FormsTie σ j H E op → ∀ x : Fin n → K, Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) (GlobalTheory.AmbCrd.frm H) (InfinitePlace.mk σ) x = ‖j x‖ := by
  first | exact @GlobalTheory.AmbNormTie.normAt_frm_mk | exact GlobalTheory.AmbNormTie.normAt_frm_mk | (intros; apply GlobalTheory.AmbNormTie.normAt_frm_mk <;> assumption)
