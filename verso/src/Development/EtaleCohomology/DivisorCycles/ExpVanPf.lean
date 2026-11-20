import Development.EtaleCohomology.DivisorCycles.CycleCount

open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb.ExpVanPf
open LateralTheory.DivDb

variable {C : Type} [Field C] [CharZero C] {N : ℕ}

noncomputable def E (Y : Mat C N) : Fin N × Fin N → PowerSeries C :=
  fun p => PowerSeries.mk fun k => ((k.factorial : C)⁻¹ • Y ^ k) p.1 p.2

noncomputable def F (Y : Mat C N) (f : MP C N) : PowerSeries C := MvPolynomial.aeval (E Y) f

/- English proof (translation)
Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations.

Clear the denominators using the available nonvanishing facts. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem deriv_E (Y : Mat C N) (p : Fin N × Fin N) :
    PowerSeries.derivative C (E Y p) = MvPolynomial.aeval (E Y) (DX Y (MvPolynomial.X p)) := by
  rw [DX, MvPolynomial.mkDerivation_X]
  ext n
  rw [PowerSeries.coeff_derivative, map_sum, map_sum]
  simp only [E, PowerSeries.coeff_mk, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [pow_succ', Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  have hn : ((n + 1).factorial : C)⁻¹ * (n + 1) = (n.factorial : C)⁻¹ := by
    have : ((n:C) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    rw [Nat.factorial_succ]; push_cast; field_simp
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Algebra.smul_def, map_smul, PowerSeries.coeff_mk, smul_eq_mul, ← hn]; ring

omit [CharZero C] in
/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Treat this case separately.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Simplify using the standard rewrite rules.
-/
theorem cc_F (Y : Mat C N) (f : MP C N) : PowerSeries.constantCoeff (F Y f) = ev 1 f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [F, ev]
  | add p q hp hq => simp only [F, ev, map_add] at *; rw [hp, hq]
  | mul_X p i hp =>
    simp only [F, ev, map_mul, MvPolynomial.aeval_X, MvPolynomial.eval_X] at *
    rw [hp]; congr 1
    simp [E]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities.
-/
theorem deriv_F (Y : Mat C N) (f : MP C N) :
    PowerSeries.derivative C (F Y f) = F Y (DX Y f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [F]
  | add p q hp hq => simp only [F, map_add] at * <;> rw [hp, hq]
  | mul_X p i hp =>
    simp only [F, map_mul, Derivation.leibniz, MvPolynomial.aeval_X, smul_eq_mul, map_add] at *
    rw [hp, ← deriv_E]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

A detailed English derivation is pending.
-/
theorem coeff_F (hT : TanField) (S : Submonoid (Mat C N)) (Y : Mat C N) (hY : Y ∈ Tan (S : Set (Mat C N))) :
    ∀ k, ∀ f ∈ Van (S : Set (Mat C N)), PowerSeries.coeff k (F Y f) = 0 := by
  intro k
  induction k with
  | zero =>
    intro f hf
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, cc_F]
    exact hf 1 S.one_mem
  | succ k ih =>
    intro f hf
    have h := ih _ ((hT C N S Y).1 hY f hf)
    rw [← deriv_F, PowerSeries.coeff_derivative] at h
    have : ((k:C) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    exact (mul_eq_zero.mp h).resolve_right this

end LateralTheory.DivDb.ExpVanPf

namespace LateralTheory.DivDb
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem ExpVan_of (hT : TanField) : ExpVan := by
  intro C _ _ N S Y hY f hf
  ext k
  have h := ExpVanPf.coeff_F hT S Y hY k f hf
  rw [map_zero]; exact h
end LateralTheory.DivDb
