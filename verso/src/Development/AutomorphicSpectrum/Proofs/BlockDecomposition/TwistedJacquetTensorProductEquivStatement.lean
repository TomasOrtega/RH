import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetTensorProductEquiv
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenFns
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Rodier.PiCoinv.twJacquet_piTensor_equiv` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FTwistedJacquetTensorProductEquiv.lean&line=227#L227)
-/
theorem _root_.GlobalTheory.T.twisted_jacquet_tensor_product_equiv : ∀ {α : Type} [Fintype α] {Γ X : α → Type} [∀ a, Group (Γ a)] [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (π : ∀ a, Representation ℂ (Γ a) (X a)) (H : ∀ a, Subgroup (Γ a)) (χ : ∀ a, H a →* ℂˣ), Nonempty (TwJacquet (piTensor π) (piSub H) (piChar χ) ≃ₗ[ℂ] ⨂[ℂ] a, TwJacquet (π a) (H a) (χ a)) := by
  first | exact @GlobalTheory.CompanionTheory.Rodier.PiCoinv.twJacquet_piTensor_equiv | exact GlobalTheory.CompanionTheory.Rodier.PiCoinv.twJacquet_piTensor_equiv | (intros; apply GlobalTheory.CompanionTheory.Rodier.PiCoinv.twJacquet_piTensor_equiv <;> assumption)
