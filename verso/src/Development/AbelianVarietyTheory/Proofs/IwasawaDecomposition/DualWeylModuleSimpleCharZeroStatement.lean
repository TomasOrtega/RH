import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DualWeylModuleSimpleCharZero
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FDualWeylModuleSimpleCharZero.lean&line=169#L169)
-/
theorem _root_.GlobalTheory.T.dualWeylModule_simple_charZero : ∀ (k : Type) [Field k] [CharZero k] (N : ℕ) (lam : DomWeight N) (M : Submodule k (MvPolynomial (Fin N × Fin N) k)),
    M ≤ nablaSq k N lam → (∀ g : GL (Fin N) k, ∀ f ∈ M, sqAct k N lam g f ∈ M) → M = ⊥ ∨ M = nablaSq k N lam := by
  first | exact @GlobalTheory.AlcZero.nablaSq_simple_charZero | exact GlobalTheory.AlcZero.nablaSq_simple_charZero | (intros; apply GlobalTheory.AlcZero.nablaSq_simple_charZero <;> assumption)
