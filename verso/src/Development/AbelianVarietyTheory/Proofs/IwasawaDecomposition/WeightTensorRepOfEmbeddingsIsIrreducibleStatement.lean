import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightTensorRepOfEmbeddingsIsIrreducible
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AlgWtF.tenRepF_isIrreducible` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FWeightTensorRepOfEmbeddingsIsIrreducible.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.weightTensorRepOfEmbeddings_isIrreducible : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K] [CharZero K]
    (emb : ι → L →+* K) (lam : ι → DomWeight n), GlobalTheory.AlgWtF.CMDist emb → (GlobalTheory.AlgWtF.tenRepF emb lam).IsIrreducible := by
  first | exact @GlobalTheory.AlgWtF.tenRepF_isIrreducible | exact GlobalTheory.AlgWtF.tenRepF_isIrreducible | (intros; apply GlobalTheory.AlgWtF.tenRepF_isIrreducible <;> assumption)
