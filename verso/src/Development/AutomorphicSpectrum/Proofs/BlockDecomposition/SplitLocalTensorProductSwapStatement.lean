import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitLocalTensorProductSwap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat
import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.KFin.SplitBase.exists_split_ringEquiv` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSplitLocalTensorProductSwap.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.split_local_tensor_product_swap : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}, IsCMExt F E σ → ∀ (v : HeightOneSpectrum (𝓞 F)), ¬ IsField (Fv F v ⊗[F] E) → ∃ φ : (Fv F v ⊗[F] E) ≃+* Fv F v × Fv F v, (∀ r, φ (sigR (Fv F v) σ r) = (φ r).swap) ∧ ∀ r, r ∈ intLoc F E v ↔ (φ r).1 ∈ v.adicCompletionIntegers F ∧ (φ r).2 ∈ v.adicCompletionIntegers F := by
  first | exact @GlobalTheory.CompanionTheory.KFin.SplitBase.exists_split_ringEquiv | exact GlobalTheory.CompanionTheory.KFin.SplitBase.exists_split_ringEquiv | (intros; apply GlobalTheory.CompanionTheory.KFin.SplitBase.exists_split_ringEquiv <;> assumption)
