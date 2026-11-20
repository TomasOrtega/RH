import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsAnalyticOfTendsto

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.EllipticModel

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Introduce a local definition for the expression. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion. A detailed English derivation is pending.
-/
theorem exists_mul_prod_eq_xy (q : ℕ) [Fact q.Prime] (M : Mdl q) (φ : ℂ → ℂ) (hM : M.Ok) (hφ : Ell M.L φ) :
    ∃ (m : ℕ) (P : Fin m → ℂ) (A B : Polynomial ℂ),
      (∀ i, P i ∉ M.L.lattice ∧ meromorphicOrderAt φ (P i) < 0) ∧
      ∀ z₀ : ℂ, ∀ᶠ z in 𝓝[≠] z₀,
        φ z * (∏ i, (Polynomial.X - Polynomial.C (M.x (P i)))).eval (M.x z) =
          A.eval (M.x z) + B.eval (M.x z) * M.y z := by
  obtain ⟨m, P, A, B, hP, h⟩ := GlobalTheory.EllipticPoles.exists_mul_prod_eq M.L φ hφ
  have hc : M.c ≠ 0 := hM.1
  set r : ℂ := M.ι.symm (M.W.b₂ / 12) with hr
  set a₁ : ℂ := M.ι.symm M.W.a₁ with ha₁
  set a₃ : ℂ := M.ι.symm M.W.a₃ with ha₃
  have hx : ∀ z, M.L.weierstrassP z = M.c ^ 2 * (M.x z + r) := by
    intro z
    simp only [Mdl.x, ← hr]
    field_simp
    ring
  have hy : ∀ z, M.L.derivWeierstrassP z = M.c ^ 3 * (2 * M.y z + a₁ * M.x z + a₃) := by
    intro z
    simp only [Mdl.y, ← ha₁, ← ha₃]
    field_simp
    ring
  let g : Polynomial ℂ := Polynomial.C (M.c ^ 2) * (Polynomial.X + Polynomial.C r)
  let k : ℂ := ((M.c ^ 2) ^ m)⁻¹
  refine ⟨m, P,
    Polynomial.C k * (A.comp g + B.comp g * Polynomial.C (M.c ^ 3) *
      (Polynomial.C a₁ * Polynomial.X + Polynomial.C a₃)),
    Polynomial.C k * (B.comp g * Polynomial.C (2 * M.c ^ 3)), hP, fun z₀ => ?_⟩
  filter_upwards [h z₀] with z hz
  have hg : g.eval (M.x z) = M.L.weierstrassP z := by
    rw [hx z]; simp [g]
  have hprod : ∏ i, (M.L.weierstrassP z - M.L.weierstrassP (P i)) =
      (M.c ^ 2) ^ m * ∏ i, (M.x z - M.x (P i)) := by
    have : ∀ i, M.L.weierstrassP z - M.L.weierstrassP (P i) = M.c ^ 2 * (M.x z - M.x (P i)) := by
      intro i; rw [hx z, hx (P i)]; ring
    simp only [this, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hk : k * (M.c ^ 2) ^ m = 1 := inv_mul_cancel₀ (pow_ne_zero _ (pow_ne_zero _ hc))
  rw [hprod, hy z] at hz
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_comp, hg]
  linear_combination k * hz - (φ z * ∏ i, (M.x z - M.x (P i))) * hk

end GlobalTheory.EllipticModel
