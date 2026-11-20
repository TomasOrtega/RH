import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinCuspOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TeichmullerInertiaLabelCondition
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial MeasureTheory Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.DZero
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.DZero.PsiM

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem valueGroupIso_uniformizer :
    IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k (uniformizer k) = WithZero.exp (-1) := by
  set φ := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k
  have h0 : φ (uniformizer k) ≠ 0 := by simp
  apply le_antisymm
  · have : φ (uniformizer k) < φ 1 := φ.strictMono uniformizer_lt_one
    rw [map_one, ← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at this
    rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
    omega
  · have : φ.symm (WithZero.exp (-1)) ≤ uniformizer k := by
      rw [le_uniformizer_iff, ← map_one φ.symm]
      exact φ.symm.strictMono (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
    simpa using φ.strictMono.monotone this

variable {k}

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem ord_eq_one {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) : ord k ϖ = 1 := by
  rw [ord, hϖ, valueGroupIso_uniformizer, WithZero.log_exp]; rfl

end PsiM

end GlobalTheory.DZero
