import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing

set_option autoImplicit false
noncomputable section
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.LaurentD

variable {K : Type} [Field K] {n d : ℕ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem monL_zero' : monL K (0 : Gam n d) = 1 := rfl

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem monL_add' (g g' : Gam n d) : monL K (g + g') = monL K g * monL K g' := by
  unfold monL
  rw [mon_mul]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem monL_neg_mul (g : Gam n d) : monL K (-g) * monL K g = 1 := by
  rw [← monL_add', neg_add_cancel, monL_zero']

def lam (K : Type) [Field K] {n d : ℕ} (g : Gam n d) : Ω[Lr K n d⁄K] :=
  monL K (-g) • KaehlerDifferential.D K (Lr K n d) (monL K g)

/- English proof (translation)
Replace the relevant objects with their definitions. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem lam_add (g g' : Gam n d) : lam K (g + g') = lam K g + lam K g' := by
  unfold lam
  have h1 : monL K (-(g + g')) = monL K (-g) * monL K (-g') := by
    rw [neg_add, monL_add']
  have e1 : monL K (-g) * monL K (-g') * monL K g = monL K (-g') := by
    rw [mul_comm (monL K (-g)), mul_assoc, monL_neg_mul, mul_one]
  have e2 : monL K (-g) * monL K (-g') * monL K g' = monL K (-g) := by
    rw [mul_assoc, monL_neg_mul, mul_one]
  rw [monL_add', Derivation.leibniz, smul_add, smul_smul, smul_smul, h1, e1, e2]
  exact add_comm _ _

def lamHom (K : Type) [Field K] (n d : ℕ) : Gam n d →+ Ω[Lr K n d⁄K] :=
  AddMonoidHom.mk' (lam K) lam_add

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem exp_eq_sum (g : Gam n d) : g = ∑ e, g e • (oneE e : Gam n d) := by
  funext x
  simp [oneE, Finset.sum_apply, Pi.single_apply]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem lam_eq_sum (g : Gam n d) : lam K g = ∑ e, (g e) • (dl e : Ω[Lr K n d⁄K]) := by
  have h : lam K g = lamHom K n d g := rfl
  rw [h]
  conv_lhs => rw [exp_eq_sum g]
  rw [map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [map_zsmul]
  rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem D_monL (g : Gam n d) :
    KaehlerDifferential.D K (Lr K n d) (monL K g) = monL K g • ∑ e, (g e) • (dl e : Ω[Lr K n d⁄K]) := by
  rw [← lam_eq_sum]
  unfold lam
  rw [smul_smul, mul_comm, monL_neg_mul, one_smul]

end GlobalTheory.CompanionTheory.SurjectionOntoH4.LaurentD
