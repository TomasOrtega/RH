import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAlgWeightFWeightTensorDualRepOfEmbeddings
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FIsAlgWeightFWeightTensorDualRepOfEmbeddings.lean&line=212#L212)
-/
theorem _root_.GlobalTheory.T.isAlgWeightF_weightTensorDualRepOfEmbeddings : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K]
    (emb : ι → L →+* K) (lam : ι → DomWeight n), NX.IsAlgWeightF L n K (GlobalTheory.AlgWtF.wtRepF emb lam) := by
  first | exact @GlobalTheory.AlgWtF.wtRepF_alg | exact GlobalTheory.AlgWtF.wtRepF_alg | (intros; apply GlobalTheory.AlgWtF.wtRepF_alg <;> assumption)
