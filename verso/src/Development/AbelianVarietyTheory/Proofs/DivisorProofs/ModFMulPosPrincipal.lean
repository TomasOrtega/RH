import Mathlib
import Formalism.PairingDivisors.StatementA
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor

open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMVal.IdeleModule
variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Use `(FiniteAdeleRing.isUnit_iff.1 y.isUnit).1 v` as an intermediate fact. Simplify using `using this`.
-/
theorem coord_ne (y : (Af E)ˣ) (v : HeightOneSpectrum (𝓞 E)) : Valued.v ((y : Af E) v) ≠ 0 := by
  have := (FiniteAdeleRing.isUnit_iff.1 y.isUnit).1 v
  simpa using this

/- English proof (translation)
Use `(FiniteAdeleRing.isUnit_iff.1 y.isUnit).2` as an intermediate fact. Rewrite `this` using `[Filter.eventually_cofinite]`. Use `this.subset fun v hv h1 => hv ?_` and prove the remaining obligations. Simplify using `[h1]`.
-/
theorem modF_finite (y : (Af E)ˣ) : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 E) =>
    ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (WithZero.log (Valued.v ((y : Af E) v)))).Finite := by
  have := (FiniteAdeleRing.isUnit_iff.1 y.isUnit).2
  rw [Filter.eventually_cofinite] at this
  refine this.subset fun v hv h1 => hv ?_
  simp [h1]

/- English proof (translation)
Establish `: Ideal.absNorm v.asIdeal ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `v.ne_bot`. Check the signs of the components of the expression.
-/
theorem absNorm_pos (v : HeightOneSpectrum (𝓞 E)) : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
  have : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  positivity

/- English proof (translation)
Unfold `modF`. Rewrite using `[← finprod_mul_distrib (modF_finite y) (modF_finite y')]`. Use `finprod_congr fun v => ?_` and prove the remaining obligations. Establish `: ((y * y' : (Af E)ˣ) : Af E) v = (y : Af E) v * (y' : Af E) v` using `rfl`. Rewrite using `[this, map_mul, WithZero.log_mul (coord_ne y v) (coord_ne y' v), zpow_add₀ (absNorm_pos v).ne']`.
-/
theorem modF_mul (y y' : (Af E)ˣ) : modF (y * y') = modF y * modF y' := by
  unfold modF
  rw [← finprod_mul_distrib (modF_finite y) (modF_finite y')]
  refine finprod_congr fun v => ?_
  have : ((y * y' : (Af E)ˣ) : Af E) v = (y : Af E) v * (y' : Af E) v := rfl
  rw [this, map_mul, WithZero.log_mul (coord_ne y v) (coord_ne y' v), zpow_add₀ (absNorm_pos v).ne']

/- English proof (translation)
The claim follows from `finprod_induction (fun x : ℝ => 0 < x) one_pos (fun _ _ => mul_pos) fun v => zpow_pos (absNorm_pos v) _`.
-/
theorem modF_pos (y : (Af E)ˣ) : 0 < modF y :=
  finprod_induction (fun x : ℝ => 0 < x) one_pos (fun _ _ => mul_pos) fun v => zpow_pos (absNorm_pos v) _

/- English proof (translation)
Establish `h` using `FinitePlace.prod_eq_inv_abs_norm (K := E) k.ne_zero`. Move the coercions through the operations in `at h`. Rewrite using `[← h, ← finprod_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := E)).symm]`. Unfold `modF`. Use `finprod_congr fun v => ?_` and prove the remaining obligations.

Rewrite using `[FinitePlace.equivHeightOneSpectrum_symm_apply, FinitePlace.norm_embedding']`. Establish `h0 : v.valuation E (k : E) ≠ 0` using `by simp`. Establish `h1 : Valued.v (((Units.map (algebraMap E (Af E)).toMonoidHom k : (Af E)ˣ) : Af E) v) = v.valuation E (k : E)` using `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (k : E)`. Rewrite using `[h1, WithZeroMulInt.toNNReal_neg_apply _ h0]`. Use `push_cast`.

Use `congr 1`. Use `conv_lhs => rw [← WithZero.coe_unzero h0]`. Both sides reduce to the same expression.
-/
theorem modF_princ (k : Eˣ) :
    modF (Units.map (algebraMap E (Af E)).toMonoidHom k) = (|((Algebra.norm ℚ (k : E) : ℚ) : ℝ)|)⁻¹ := by
  have h := FinitePlace.prod_eq_inv_abs_norm (K := E) k.ne_zero
  push_cast at h
  rw [← h, ← finprod_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := E)).symm]
  unfold modF
  refine finprod_congr fun v => ?_
  rw [FinitePlace.equivHeightOneSpectrum_symm_apply, FinitePlace.norm_embedding']
  have h0 : v.valuation E (k : E) ≠ 0 := by simp
  have h1 : Valued.v (((Units.map (algebraMap E (Af E)).toMonoidHom k : (Af E)ˣ) : Af E) v) = v.valuation E (k : E) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (k : E)
  rw [h1, WithZeroMulInt.toNNReal_neg_apply _ h0]
  push_cast
  congr 1
  conv_lhs => rw [← WithZero.coe_unzero h0]
  rfl

end GlobalTheory.CMVal.IdeleModule

/- English proof (translation)
Introduce `_ _ _` and use `⟨IdeleModule.modF_mul, IdeleModule.modF_pos, IdeleModule.modF_princ⟩`.
-/
theorem GlobalTheory.CMVal.modF_mul_pos_principal : ∀ (E : Type) [Field E] [NumberField E], (∀ y y' : (Af E)ˣ, modF (y * y') = modF y * modF y') ∧ (∀ y : (Af E)ˣ, 0 < modF y) ∧ ∀ k : Eˣ, modF (Units.map (algebraMap E (Af E)).toMonoidHom k) = (|(Algebra.norm ℚ (k : E) : ℝ)|)⁻¹ :=
  fun _ _ _ => ⟨IdeleModule.modF_mul, IdeleModule.modF_pos, IdeleModule.modF_princ⟩
