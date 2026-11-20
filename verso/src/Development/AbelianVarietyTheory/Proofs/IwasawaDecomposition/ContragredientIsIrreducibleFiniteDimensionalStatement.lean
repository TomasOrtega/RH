import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContragredientIsIrreducibleFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FContragredientIsIrreducibleFiniteDimensional.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.contragredient_isIrreducible_finiteDimensional : ∀ (k : Type) [Field k] (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V), ρ.IsIrreducible → ρ.dual.IsIrreducible := by
  first | exact @GlobalTheory.contragredient_isIrreducible | exact GlobalTheory.contragredient_isIrreducible | (intros; apply GlobalTheory.contragredient_isIrreducible <;> assumption)
