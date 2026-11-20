import Development.EtaleCohomology.DivisorCycles.CycleCount

open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb.ExpVanPf
open LateralTheory.DivDb

variable {C : Type} [Field C] [CharZero C] {N : ℕ}

noncomputable def E (Y : Mat C N) : Fin N × Fin N → PowerSeries C :=
  fun p => PowerSeries.mk fun k => ((k.factorial : C)⁻¹ • Y ^ k) p.1 p.2

noncomputable def F (Y : Mat C N) (f : MP C N) : PowerSeries C := MvPolynomial.aeval (E Y) f

/- English proof (translation)
Rewrite using `[DX, MvPolynomial.mkDerivation_X]`. Use extensionality with `n`. Rewrite using `[PowerSeries.coeff_derivative, map_sum, map_sum]`. Simplify using `only [E, PowerSeries.coeff_mk, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X]`. Simplify using `only [Matrix.smul_apply, smul_eq_mul]`.

Rewrite using `[pow_succ', Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]`. Establish `hn : ((n + 1).factorial : C)⁻¹ * (n + 1) = (n.factorial : C)⁻¹`. Establish `: ((n:C) + 1) ≠ 0` using `by exact_mod_cast Nat.succ_ne_zero n`. Rewrite using `[Nat.factorial_succ]`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← Algebra.smul_def, map_smul, PowerSeries.coeff_mk, smul_eq_mul, ← hn]`. Expand and normalize the polynomial expressions, which then agree.
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
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a => simp [F, ev]`. Consider the case `add p q hp hq => simp only [F, ev, map_add] at *`. Rewrite using `[hp, hq]`. Consider the case `mul_X p i hp`.

Simplify using `only [F, ev, map_mul, MvPolynomial.aeval_X, MvPolynomial.eval_X] at *`. Rewrite using `[hp]`. Use `congr 1`. Simplify using `[E]`.
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
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a => simp [F]`. Consider the case `add p q hp hq => simp only [F, map_add] at * <;> rw [hp, hq]`. Consider the case `mul_X p i hp`. Simplify using `only [F, map_mul, Derivation.leibniz, MvPolynomial.aeval_X, smul_eq_mul, map_add] at *`.

Rewrite using `[hp, ← deriv_E]`.
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
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `f hf`. Rewrite using `[PowerSeries.coeff_zero_eq_constantCoeff_apply, cc_F]`.

Conclude with `hf 1 S.one_mem`. Consider the case `succ k ih`. Introduce `f hf`. Establish `h` using `ih _ ((hT C N S Y).1 hY f hf)`. Rewrite `h` using `[← deriv_F, PowerSeries.coeff_derivative]`.

Establish `: ((k:C) + 1) ≠ 0` using `by exact_mod_cast Nat.succ_ne_zero k`. Conclude with `(mul_eq_zero.mp h).resolve_right this`.
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
Introduce `C _ _ N S Y hY f hf`. Use extensionality with `k`. Establish `h` using `ExpVanPf.coeff_F hT S Y hY k f hf`. Rewrite using `[map_zero]`. Conclude with `h`.
-/
theorem ExpVan_of (hT : TanField) : ExpVan := by
  intro C _ _ N S Y hY f hf
  ext k
  have h := ExpVanPf.coeff_F hT S Y hY k f hf
  rw [map_zero]; exact h
end LateralTheory.DivDb
