import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOrderPreservingPowerHomAlgClosurePrimeFiel
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PowAut.exists_powHom_fbar` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsOrderPreservingPowerHomAlgClosurePrimeFiel.lean&line=119#L119)
-/
theorem _root_.GlobalTheory.T.exists_order_preserving_power_hom_algClosure_primeField : ∀ (g : ℕ) [Fact g.Prime] (M n : ℕ), 0 < M → n.Coprime M → ∃ θ : Formalism.CyclotomicNorms.Fbar g →* Formalism.CyclotomicNorms.Fbar g, Function.Injective θ ∧ (∀ x, orderOf (θ x) = orderOf x) ∧ ∀ x, x ^ M = 1 → θ x = x ^ n := by
  first | exact @GlobalTheory.PowAut.exists_powHom_fbar | exact GlobalTheory.PowAut.exists_powHom_fbar | (intros; apply GlobalTheory.PowAut.exists_powHom_fbar <;> assumption)
