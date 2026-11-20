import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.PsiApply

open TensorProduct CrystallineSemistableComparison.Pb.Psi

namespace GlobalTheory.CompanionTheory.FrobPairing

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.
-/
theorem T_gal {W A C₀ : Type} [CommRing W] [CommRing A] [CommRing C₀] [Algebra W A] {K₀ : Type} [Field K₀]
    [Algebra W K₀] {L : Type 1} [AddCommGroup L] [Module W L] (c : A →+* C₀) (k : K₀ →+* C₀)
    (hk : ∀ w : W, k (algebraMap W K₀ w) = c (algebraMap W A w)) (σA : A →+* A) (σC : C₀ →+* C₀)
    (gT : A ⊗[W] L →+ A ⊗[W] L) (hg : ∀ a y, gT (a ⊗ₜ y) = σA a ⊗ₜ y)
    (hσ : ∀ a, σC (c a) = c (σA a)) (hσk : ∀ x, σC (k x) = k x)
    (f : Module.Dual K₀ (K₀ ⊗[W] L)) (z : A ⊗[W] L) :
    T c k hk f (gT z) = σC (T c k hk f z) := by
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp only [map_zero]
  · intro a y
    rw [hg]
    simp only [T, TensorProduct.liftAddHom_tmul, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_mul, hσ, hσk]
  · intro x y hx hy
    simp only [map_add, hx, hy]

end GlobalTheory.CompanionTheory.FrobPairing
