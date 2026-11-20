import Formalism.MahlerMeasure.StatementD
import Formalism.MahlerMeasure.MahlerMeasureProofs.Mahler

namespace Formalism.GM

open Polynomial

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mahler_binomial_unit_ball : MahlerK := by
  intro p hp K _ _ h k t₀ hk m
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective
  set P : ℚ[X] := Polynomial.C ((k.factorial : ℚ)⁻¹) *
    (descPochhammer ℚ k).comp (Polynomial.C ((p : ℚ) ^ h) * X + Polynomial.C (t₀ : ℚ)) with hP
  have hmap : P.map (Rat.castHom K) =
      (binK K k).comp (Polynomial.C ((p : K) ^ h) * X + Polynomial.C (t₀ : K)) := by
    rw [hP, binK, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_comp, descPochhammer_map,
      mul_comp, C_comp]
    simp
  rw [← hmap, Polynomial.coeff_map]
  have h1 := mahler_disc_bound p h k t₀ hp.out hk m
  rw [← hP] at h1
  have h2 : ((Rat.castHom K) (P.coeff m)) = algebraMap ℚ_[p] K ((P.coeff m : ℚ) : ℚ_[p]) := by
    rw [map_ratCast]; rfl
  rw [h2, norm_algebraMap', Padic.eq_padicNorm]
  exact_mod_cast h1

end Formalism.GM
