import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplittingFstMemIntegers
import Mathlib
import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
import Formalism.LocalRingCardinality.DataLevel
open NumberField IsDedekindDomain
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FSplittingFstMemIntegers.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.splitting_fst_mem_integers' : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (spl : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F),
    (∀ a : v.adicCompletion F, spl ((1 : E) ⊗ₜ[F] a) = (a, a)) →
    ∀ z ∈ Formalism.BasicNotions.intV E v, (spl z).1 ∈ v.adicCompletionIntegers F := by
  first | exact @GlobalTheory.splitting_fst_mem_integers | exact GlobalTheory.splitting_fst_mem_integers | (intros; apply GlobalTheory.splitting_fst_mem_integers <;> assumption)
