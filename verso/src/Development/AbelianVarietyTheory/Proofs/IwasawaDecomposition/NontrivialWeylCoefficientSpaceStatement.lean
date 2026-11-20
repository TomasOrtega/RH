import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NontrivialWeylCoefficientSpace
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FNontrivialWeylCoefficientSpace.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.nontrivial_weylCoefficientSpace : ∀ (K : Type) [Field K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n), Nontrivial (Formalism.L2.DIV.VV K lam) := by
  first | exact @GlobalTheory.CoeffSpace.nontrivial_VV | exact GlobalTheory.CoeffSpace.nontrivial_VV | (intros; apply GlobalTheory.CoeffSpace.nontrivial_VV <;> assumption)
