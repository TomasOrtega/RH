import Mathlib
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.CoePolarExpHomeomorphComplexApply
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.MaximalCompactIsCompact

namespace CompanionTheory.D.Upq

open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

set_option linter.unusedSectionVars false

variable {m : Type*} [Fintype m] [DecidableEq m] {J : Matrix m m ℂ}

/- English proof (translation)
Establish `h1 : (J * gᴴ * J) * g = 1`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : g * (J * gᴴ * J) = 1` using `mul_eq_one_comm.1 h1`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem mul_J_mul_conjTranspose (hJJ : J * J = 1) {g : Matrix m m ℂ} (hg : gᴴ * J * g = J) :
    g * J * gᴴ = J := by
  have h1 : (J * gᴴ * J) * g = 1 := by
    calc (J * gᴴ * J) * g = J * (gᴴ * J * g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg, hJJ]
  have h2 : g * (J * gᴴ * J) = 1 := mul_eq_one_comm.1 h1
  calc g * J * gᴴ = g * (J * gᴴ * J) * J := by simp only [Matrix.mul_assoc, hJJ, Matrix.mul_one]
    _ = J := by rw [h2, Matrix.one_mul]

/- English proof (translation)
Use `set S := CFC.sqrt P with hSdef`. Establish `hSpd : S.PosDef`. Rewrite `hP`, the goal using `[← isStrictlyPositive_iff_posDef]`. Conclude with `IsStrictlyPositive.sqrt _ hP`. Establish `hSh : Sᴴ = S` using `hSpd.isHermitian`.

Establish `hPh : Pᴴ = P` using `hP.isHermitian`. Establish `hSS : S * S = P` using `CFC.sqrt_mul_sqrt_self _ hP.posSemidef.nonneg`. Establish `hPJ' : P * J * P = J` using `by rwa [hPh] at hPJ`. Establish `hJPJ : J * P * J = P⁻¹`. Use `(Matrix.inv_eq_left_inv ?_).symm` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Establish `h1 : CFC.sqrt (J * P * J) = J * S * J`. Use `CFC.sqrt_unique ?_ ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `hSpd.posSemidef.conjTranspose_mul_mul_same J` as an intermediate fact.

Rewrite `this` using `[hJh]`. Conclude with `this.nonneg`. Establish `h2 : CFC.sqrt P⁻¹ = S⁻¹`. Use `CFC.sqrt_unique ?_ hSpd.inv.posSemidef.nonneg` and prove the remaining obligations. Rewrite using `[← Matrix.mul_inv_rev, hSS]`.

Establish `h3 : J * S * J = S⁻¹` using `by rw [← h1, hJPJ, h2]`. Establish `hSu : IsUnit S.det` using `(Matrix.isUnit_iff_isUnit_det S).1 hSpd.isUnit`. Rewrite using `[hSh]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc, hJJ, Matrix.mul_one]`.

Use `_ = J := by rw [h3, Matrix.mul_nonsing_inv _ hSu, Matrix.one_mul]`.
-/
theorem sqrt_mem_UJ (hJJ : J * J = 1) (hJh : Jᴴ = J) {P : Matrix m m ℂ} (hP : P.PosDef)
    (hPJ : Pᴴ * J * P = J) : (CFC.sqrt P)ᴴ * J * CFC.sqrt P = J := by
  set S := CFC.sqrt P with hSdef
  have hSpd : S.PosDef := by
    rw [← isStrictlyPositive_iff_posDef] at hP ⊢
    exact IsStrictlyPositive.sqrt _ hP
  have hSh : Sᴴ = S := hSpd.isHermitian
  have hPh : Pᴴ = P := hP.isHermitian
  have hSS : S * S = P := CFC.sqrt_mul_sqrt_self _ hP.posSemidef.nonneg
  have hPJ' : P * J * P = J := by rwa [hPh] at hPJ
  have hJPJ : J * P * J = P⁻¹ := by
    refine (Matrix.inv_eq_left_inv ?_).symm
    calc J * P * J * P = J * (P * J * P) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hPJ', hJJ]
  have h1 : CFC.sqrt (J * P * J) = J * S * J := by
    refine CFC.sqrt_unique ?_ ?_
    · calc J * S * J * (J * S * J) = J * S * (J * J) * S * J := by simp only [Matrix.mul_assoc]
        _ = J * P * J := by rw [hJJ, Matrix.mul_one, Matrix.mul_assoc J S S, hSS]
    · have := hSpd.posSemidef.conjTranspose_mul_mul_same J
      rw [hJh] at this
      exact this.nonneg
  have h2 : CFC.sqrt P⁻¹ = S⁻¹ := by
    refine CFC.sqrt_unique ?_ hSpd.inv.posSemidef.nonneg
    rw [← Matrix.mul_inv_rev, hSS]
  have h3 : J * S * J = S⁻¹ := by rw [← h1, hJPJ, h2]
  have hSu : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).1 hSpd.isUnit
  rw [hSh]
  calc S * J * S = S * (J * S * J) * J := by
        simp only [Matrix.mul_assoc, hJJ, Matrix.mul_one]
    _ = J := by rw [h3, Matrix.mul_nonsing_inv _ hSu, Matrix.one_mul]

/- English proof (translation)
Rewrite using `[conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem mul_mem_UJ {a b : Matrix m m ℂ} (ha : aᴴ * J * a = J) (hb : bᴴ * J * b = J) :
    (a * b)ᴴ * J * (a * b) = J := by
  rw [conjTranspose_mul]
  calc bᴴ * aᴴ * J * (a * b) = bᴴ * (aᴴ * J * a) * b := by simp only [Matrix.mul_assoc]
    _ = J := by rw [ha, hb]

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem inv_mem_UJ {a : Matrix m m ℂ} (hu : IsUnit a.det) (ha : aᴴ * J * a = J) :
    a⁻¹ᴴ * J * a⁻¹ = J := by
  calc a⁻¹ᴴ * J * a⁻¹ = a⁻¹ᴴ * (aᴴ * J * a) * a⁻¹ := by rw [ha]
    _ = (a * a⁻¹)ᴴ * J * (a * a⁻¹) := by simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = J := by rw [Matrix.mul_nonsing_inv _ hu, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

/- English proof (translation)
Establish `hp : (polarPos g)ᴴ * J * polarPos g = J`. Use `sqrt_mem_UJ hJJ hJh (posDef_conjTranspose_mul_self_GL g) ?_` and prove the remaining obligations. Establish `hg'` using `mul_J_mul_conjTranspose hJJ hg`. Rewrite using `[conjTranspose_mul, conjTranspose_conjTranspose]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = J := by rw [hg', hg]`. Conclude with `⟨hp, mul_mem_UJ hg (inv_mem_UJ (isUnit_det_of_posDef (polarPos_posDef g)) hp)⟩`.
-/
theorem polar_mem_UJ (hJJ : J * J = 1) (hJh : Jᴴ = J) (g : GL m ℂ)
    (hg : (g : Matrix m m ℂ)ᴴ * J * g = J) :
    (polarPos g)ᴴ * J * polarPos g = J ∧ (polarUnitary g)ᴴ * J * polarUnitary g = J := by
  have hp : (polarPos g)ᴴ * J * polarPos g = J := by
    refine sqrt_mem_UJ hJJ hJh (posDef_conjTranspose_mul_self_GL g) ?_
    have hg' := mul_J_mul_conjTranspose hJJ hg
    rw [conjTranspose_mul, conjTranspose_conjTranspose]
    calc (g : Matrix m m ℂ)ᴴ * g * J * ((g : Matrix m m ℂ)ᴴ * g)
        = (g : Matrix m m ℂ)ᴴ * ((g : Matrix m m ℂ) * J * (g : Matrix m m ℂ)ᴴ) * g := by
          simp only [Matrix.mul_assoc]
      _ = J := by rw [hg', hg]
  exact ⟨hp, mul_mem_UJ hg (inv_mem_UJ (isUnit_det_of_posDef (polarPos_posDef g)) hp)⟩

/- English proof (translation)
Introduce `k r g hg`. Establish `hHh` using `PI.QuotSetU.UnitaryGroupMassFormula.hpk_conjTranspose k r`. Establish `hHH` using `PI.QuotSetU.UnitaryGroupMassFormula.hpk_mul_self k r`. Establish `hU : IsUnit g` using `(Matrix.isUnit_iff_isUnit_det g).2 (PI.QuotSetU.UnitaryGroupMassFormula.uh_det hg)`. Use `set G : GL (Fin (2 * r + k + 1)) ℂ := hU.unit with hGdef`.

Establish `hGg : (G : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) = g` using `hU.unit_spec`. Establish `hgG : (G : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ᴴ * PI.QuotSetU.Hpk k r * G = PI.QuotSetU.Hpk k r` using `by rw [hGg]; exact hg`. Take `⟨hp, hu⟩` from `polar_mem_UJ hHH hHh G hgG`. Use `⟨polarUnitary G, polarPos G, hu, ?_, hp, (polarPos_posDef G).isHermitian, ?_⟩` and prove the remaining obligations. Use `mem_unitaryGroup_iff'.1 (polarUnitary_mem G)` as an intermediate fact.

Rewrite `this` using `[star_eq_conjTranspose]`. Then use the resulting hypothesis. Rewrite using `[polarUnitary_mul_polarPos, hGg]`.
-/
theorem unitary_group_polar_decomposition : PI.QuotSetU.UnitaryGroupMassFormula.PolarUH := by
  intro k r g hg
  have hHh := PI.QuotSetU.UnitaryGroupMassFormula.hpk_conjTranspose k r
  have hHH := PI.QuotSetU.UnitaryGroupMassFormula.hpk_mul_self k r
  have hU : IsUnit g := (Matrix.isUnit_iff_isUnit_det g).2 (PI.QuotSetU.UnitaryGroupMassFormula.uh_det hg)
  set G : GL (Fin (2 * r + k + 1)) ℂ := hU.unit with hGdef
  have hGg : (G : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) = g := hU.unit_spec
  have hgG : (G : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ᴴ *
      PI.QuotSetU.Hpk k r * G = PI.QuotSetU.Hpk k r := by rw [hGg]; exact hg
  obtain ⟨hp, hu⟩ := polar_mem_UJ hHH hHh G hgG
  refine ⟨polarUnitary G, polarPos G, hu, ?_, hp, (polarPos_posDef G).isHermitian, ?_⟩
  · have := mem_unitaryGroup_iff'.1 (polarUnitary_mem G)
    rwa [star_eq_conjTranspose] at this
  · rw [polarUnitary_mul_polarPos, hGg]

/- English proof (translation)
The claim follows from `PI.QuotSetU.UnitaryGroupMassFormula.trivG_of unitary_group_polar_decomposition PI.QuotSetU.UnitaryGroupMassFormula.maximal_compact_isCompact`.
-/
theorem unitary_group_modular_function_trivial : PI.QuotSetU.UnitaryGroupMassFormula.TrivG :=
  PI.QuotSetU.UnitaryGroupMassFormula.trivG_of unitary_group_polar_decomposition PI.QuotSetU.UnitaryGroupMassFormula.maximal_compact_isCompact

end CompanionTheory.D.Upq
