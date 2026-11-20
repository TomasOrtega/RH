import Formalism.HermitianCurvature.StatementX

namespace Formalism.FourierDecayAlt.P

open Matrix

namespace X

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem scaled_eq {K : Type} [Field K] (n : ℕ) (Z : Matrix (Fin n) (Fin n) K) (κ : K) (l : ℕ)
    (hl : l ≤ n) :
    (Matrix.of (fun a b : Fin n => κ ^ ((a : ℕ) + (b : ℕ)) * Z a b)).submatrix
        (Fin.castLE hl) (Fin.castLE hl) =
      Matrix.diagonal (fun a : Fin l => κ ^ (a : ℕ)) * Z.submatrix (Fin.castLE hl) (Fin.castLE hl) *
        Matrix.diagonal (fun a : Fin l => κ ^ (a : ℕ)) := by
  ext a b
  simp [Matrix.diagonal_mul, Matrix.mul_diagonal, pow_add]
  ring

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem prod_pow_fin {K : Type} [Field K] (κ : K) (l : ℕ) :
    (∏ a : Fin l, κ ^ (a : ℕ)) = κ ^ (∑ a ∈ Finset.range l, a) := by
  rw [Finset.prod_pow_eq_pow_sum, Fin.sum_univ_eq_sum_range (fun a => a) l]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem two_sum (l : ℕ) : 2 * (∑ a ∈ Finset.range l, a) = l * (l - 1) := by
  rw [mul_comm, Finset.sum_range_id_mul_two]

end X

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem minor_scaling_law : Formalism.FourierDecayAlt.X.MinorScale := by
  intro K _ n Z κ l hl
  rw [X.scaled_eq n Z κ l hl, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal,
    X.prod_pow_fin, ← X.two_sum, pow_mul]
  ring

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem scaling_exponent_identities : Formalism.FourierDecayAlt.X.ScaleExponents :=
  ⟨fun l => by ring, fun i s => by ring⟩

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. Supply the required witnesses or components.
-/
theorem germ_power_identity : Formalism.FourierDecayAlt.X.GermPowers :=
  fun s => ⟨by ring, by ring⟩

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem slice_power_identity : Formalism.FourierDecayAlt.X.SlicePowers :=
  fun s M => by ring

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. Supply the required witnesses or components.
-/
theorem weight_exponent_identity : Formalism.FourierDecayAlt.X.WeightExponent :=
  fun k r j s => ⟨by ring, by ring, by ring⟩

end Formalism.FourierDecayAlt.P
