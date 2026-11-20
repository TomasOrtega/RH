import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentCutoffTendstoAdelicUnitary
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialOfLocal
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
open Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UnitaryCutoff.exists_approx` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsIdempotentCutoffTendstoAdelicUnitary.lean&line=60#L60)
-/
theorem _root_.GlobalTheory.T.exists_idempotentCutoff_tendsto_adelicUnitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {ι : Type} [Fintype ι] [DecidableEq ι] (J₀ : Matrix ι ι (AE F E)) (g : UG (cA σ) J₀), ∃ q : Finset (HeightOneSpectrum (𝓞 F)) → UG (cA σ) J₀, (∀ S, ((q S).1.1 : Matrix ι ι (AE F E)) = algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S) • (g.1.1 : Matrix ι ι (AE F E)) + (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S)) • (1 : Matrix ι ι (AE F E))) ∧ Tendsto q atTop (𝓝 g) := by
  first | exact @GlobalTheory.UnitaryCutoff.exists_approx | exact GlobalTheory.UnitaryCutoff.exists_approx | (intros; apply GlobalTheory.UnitaryCutoff.exists_approx <;> assumption)
