import Mathlib
import Formalism.PeriodIntegrals.LocJacTyp

noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain PI.LocJacTyp

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

/- English proof (translation)
Establish `h : Ideal.absNorm v.asIdeal ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `v.ne_bot`. Conclude with `Nat.pos_of_ne_zero h` after adjusting the coercions.
-/
theorem q_pos : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
  have h : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  exact_mod_cast Nat.pos_of_ne_zero h

/- English proof (translation)
Unfold `absV`. Simplify using the standard rewrite rules.
-/
theorem absV_zero : absV v (0 : Fv F v) = 0 := by
  unfold absV
  simp

/- English proof (translation)
Establish `h : Valued.v x ≠ 0` using `by simpa using hx`. Unfold `absV`. Rewrite using `[dif_neg h]`. Conclude with `zpow_pos (q_pos v) _`.
-/
theorem absV_pos {x : Fv F v} (hx : x ≠ 0) : 0 < absV v x := by
  have h : Valued.v x ≠ 0 := by simpa using hx
  unfold absV
  rw [dif_neg h]
  exact zpow_pos (q_pos v) _

/- English proof (translation)
The claim follows from `(absV_pos v hx).ne'`.
-/
theorem absV_ne_zero {x : Fv F v} (hx : x ≠ 0) : absV v x ≠ 0 := (absV_pos v hx).ne'

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Simplify using `[hx, absV_zero]`. Distinguish the cases in `hy : y = 0`. Simplify using `[hy, absV_zero]`. Establish `h1 : Valued.v x ≠ 0` using `by simpa using hx`.

Establish `h2 : Valued.v y ≠ 0` using `by simpa using hy`. Establish `h3 : Valued.v (x * y) ≠ 0` using `by simpa using mul_ne_zero hx hy`. Unfold `absV`. Rewrite using `[dif_neg h1, dif_neg h2, dif_neg h3, ← zpow_add₀ (q_pos v).ne', ← toAdd_mul]`. Use `congr 2`.

Apply `WithZero.coe_injective` to reduce the goal to its premises. Rewrite using `[WithZero.coe_mul, WithZero.coe_unzero, WithZero.coe_unzero, WithZero.coe_unzero, map_mul]`.
-/
theorem absV_mul (x y : Fv F v) : absV v (x * y) = absV v x * absV v y := by
  by_cases hx : x = 0
  · simp [hx, absV_zero]
  by_cases hy : y = 0
  · simp [hy, absV_zero]
  have h1 : Valued.v x ≠ 0 := by simpa using hx
  have h2 : Valued.v y ≠ 0 := by simpa using hy
  have h3 : Valued.v (x * y) ≠ 0 := by simpa using mul_ne_zero hx hy
  unfold absV
  rw [dif_neg h1, dif_neg h2, dif_neg h3, ← zpow_add₀ (q_pos v).ne', ← toAdd_mul]
  congr 2
  apply WithZero.coe_injective
  rw [WithZero.coe_mul, WithZero.coe_unzero, WithZero.coe_unzero, WithZero.coe_unzero, map_mul]

/- English proof (translation)
Establish `h : Valued.v (1 : Fv F v) ≠ 0` using `by simp`. Unfold `absV`. Rewrite using `[dif_neg h]`. Establish `h1 : WithZero.unzero h = 1`. Apply `WithZero.coe_injective` to reduce the goal to its premises.

Rewrite using `[WithZero.coe_unzero, map_one, WithZero.coe_one]`. Rewrite using `[h1, toAdd_one, zpow_zero]`.
-/
theorem absV_one : absV v (1 : Fv F v) = 1 := by
  have h : Valued.v (1 : Fv F v) ≠ 0 := by simp
  unfold absV
  rw [dif_neg h]
  have h1 : WithZero.unzero h = 1 := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, map_one, WithZero.coe_one]
  rw [h1, toAdd_one, zpow_zero]

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Simplify using `[hx, absV_zero]`. Establish `h` using `absV_mul v x x⁻¹`. Rewrite `h` using `[mul_inv_cancel₀ hx, absV_one]`. Conclude with `eq_inv_of_mul_eq_one_right h.symm`.
-/
theorem absV_inv (x : Fv F v) : absV v x⁻¹ = (absV v x)⁻¹ := by
  by_cases hx : x = 0
  · simp [hx, absV_zero]
  have h := absV_mul v x x⁻¹
  rw [mul_inv_cancel₀ hx, absV_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp [absV_one]`. Consider the case `succ n ih => rw [pow_succ, absV_mul, ih, pow_succ]`.
-/
theorem absV_pow (x : Fv F v) (n : ℕ) : absV v (x ^ n) = absV v x ^ n := by
  induction n with
  | zero => simp [absV_one]
  | succ n ih => rw [pow_succ, absV_mul, ih, pow_succ]

/- English proof (translation)
Rewrite using `[div_eq_mul_inv, absV_mul, absV_inv, div_eq_mul_inv]`.
-/
theorem absV_div (x y : Fv F v) : absV v (x / y) = absV v x / absV v y := by
  rw [div_eq_mul_inv, absV_mul, absV_inv, div_eq_mul_inv]

/- English proof (translation)
Unfold `dV`. Use `split_ifs with h`. Conclude with `h.choose_spec.1`. Conclude with `one_ne_zero`.
-/
theorem dV_ne_zero : dV v ≠ 0 := by
  unfold dV
  split_ifs with h
  · exact h.choose_spec.1
  · exact one_ne_zero

/- English proof (translation)
Unfold `alp`. Use `split_ifs`. Conclude with `pow_ne_zero _ (inv_ne_zero (dV_ne_zero v))`. Conclude with `one_ne_zero`.
-/
theorem alp_ne_zero (r : ℕ) (a : Fin (r + 1)) : alp v r a ≠ 0 := by
  unfold alp
  split_ifs
  · exact pow_ne_zero _ (inv_ne_zero (dV_ne_zero v))
  · exact one_ne_zero

/- English proof (translation)
Unfold `alp`. Simplify using the standard rewrite rules.
-/
theorem alp_last (r : ℕ) : alp v r (Fin.last r) = 1 := by
  unfold alp
  simp

/- English proof (translation)
Introduce `h0`. Establish `h1 : algebraMap F (Fv F v) (g : F) = algebraMap F (Fv F v) 0`. Rewrite using `[map_natCast, map_zero]`. Conclude with `h0`. Conclude with `(Nat.cast_ne_zero.2 hg.ne') ((algebraMap F (Fv F v)).injective h1)`.
-/
theorem natCast_ne_zero {g : ℕ} (hg : 0 < g) : (g : Fv F v) ≠ 0 := by
  intro h0
  have h1 : algebraMap F (Fv F v) (g : F) = algebraMap F (Fv F v) 0 := by
    rw [map_natCast, map_zero]
    exact h0
  exact (Nat.cast_ne_zero.2 hg.ne') ((algebraMap F (Fv F v)).injective h1)

end PI.UnitaryGroupMassFormula.LocJacTyp
