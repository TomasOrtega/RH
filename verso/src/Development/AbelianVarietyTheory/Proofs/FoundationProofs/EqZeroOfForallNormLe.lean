import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowMulMemAdd
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormLeOneOfMemCoef

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Rf3.norm_le_one_of_mem_coef c hx`.
-/
theorem norm_le_one_of_mem_coef (c : Coef l) {x : Qbar l} (hx : x ∈ c.O) : ‖x‖ ≤ 1 :=
  _root_.UpperTheory.Reformulated.B.Rf3.norm_le_one_of_mem_coef c hx

/- English proof (translation)
Establish `: ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l])` using `by simp`. Rewrite using `[this, norm_algebraMap', Padic.norm_p]`.
-/
theorem norm_natCast_l : ‖((l : ℕ) : Qbar l)‖ = (l : ℝ)⁻¹ := by
  have : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
  rw [this, norm_algebraMap', Padic.norm_p]

/- English proof (translation)
Rewrite using `[norm_natCast_l]`. Conclude with `inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)`.
-/
theorem norm_natCast_l_lt_one : ‖((l : ℕ) : Qbar l)‖ < 1 := by
  rw [norm_natCast_l]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)

/- English proof (translation)
Simplify using `only [norm_pow]`. Conclude with `tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) norm_natCast_l_lt_one`.
-/
theorem tendsto_norm_l_pow :
    Filter.Tendsto (fun n : ℕ => ‖((l : ℕ) : Qbar l) ^ n‖) Filter.atTop (nhds 0) := by
  simp only [norm_pow]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) norm_natCast_l_lt_one

/- English proof (translation)
Establish `h0 : ‖x‖ ≤ 0` using `ge_of_tendsto' tendsto_norm_l_pow h`. Conclude with `norm_le_zero_iff.1 h0`.
-/
theorem eq_zero_of_forall_norm_le (x : Qbar l) (h : ∀ n : ℕ, ‖x‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖) : x = 0 := by
  have h0 : ‖x‖ ≤ 0 := ge_of_tendsto' tendsto_norm_l_pow h
  exact norm_le_zero_iff.1 h0

/- English proof (translation)
Unfold `Cg at *`. Rewrite using `[norm_sub_rev]` and apply the resulting hypothesis.
-/
theorem cg_symm {n : ℕ} {a b : Qbar l} (h : Cg n a b) : Cg n b a := by
  unfold Cg at *; rwa [norm_sub_rev]

/- English proof (translation)
Unfold `Cg at *`. Establish `e : a - d = (a - b) + (b - d)` using `by ring`. Rewrite using `[e]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le h h')`.
-/
theorem cg_trans {n : ℕ} {a b d : Qbar l} (h : Cg n a b) (h' : Cg n b d) : Cg n a d := by
  unfold Cg at *
  have e : a - d = (a - b) + (b - d) := by ring
  rw [e]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h h')

/- English proof (translation)
Introduce `i` and use `cg_symm (h i)`.
-/
theorem cv_symm {n : ℕ} {a b : Fin 2 → Qbar l} (h : Cv n a b) : Cv n b a := fun i => cg_symm (h i)

/- English proof (translation)
Introduce `i` and use `cg_trans (h i) (h' i)`.
-/
theorem cv_trans {n : ℕ} {a b d : Fin 2 → Qbar l} (h : Cv n a b) (h' : Cv n b d) : Cv n a d :=
  fun i => cg_trans (h i) (h' i)

/- English proof (translation)
The claim follows from `sub_eq_zero.1 (eq_zero_of_forall_norm_le _ h)`.
-/
theorem eq_of_forall_cg {a b : Qbar l} (h : ∀ n, Cg n a b) : a = b :=
  sub_eq_zero.1 (eq_zero_of_forall_norm_le _ h)

end GlobalTheory.Ord2

end
