import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IrreducibleCharacterSeries.IrrCharIff

noncomputable section
open Matrix ComplexOrder

namespace PI.SerBridgeGLW

/- English proof (translation)
Use `set P : Matrix n n ℂ := ∑ g, (M g)ᴴ * M g with hPdef`. Establish `hinv : ∀ y : G, M y * M y⁻¹ = 1` using `fun y => by rw [← map_mul, mul_inv_cancel, map_one]`. Establish `hP : (M x)ᴴ * P * M x = P`. Rewrite using `[hPdef, Finset.mul_sum, Finset.sum_mul]`. Use `Fintype.sum_equiv (Equiv.mulRight x) _ _ (fun g => ?_)` and prove the remaining obligations.

Simplify using `only [Equiv.coe_mulRight, map_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Establish `hPpd : P.PosDef`. Rewrite using `[hPdef, ← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : G))]`. Simplify using `only [map_one, Matrix.conjTranspose_one, Matrix.mul_one]`. Conclude with `Matrix.PosDef.one.add_posSemidef (Matrix.posSemidef_sum _ fun g _ => Matrix.posSemidef_conjTranspose_mul_self _)`.

Establish `hPu : IsUnit P` using `hPpd.isUnit`. Establish `hPP : P * P⁻¹ = 1` using `Matrix.mul_nonsing_inv P ((Matrix.isUnit_iff_isUnit_det P).1 hPu)`. Establish `hct : (M x)ᴴ = P * M x⁻¹ * P⁻¹`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hinv, Matrix.mul_one, Matrix.mul_assoc, hPP, Matrix.mul_one]`.

Use `_ = ((M x)ᴴ * P * M x) * M x⁻¹ * P⁻¹ := by simp only [Matrix.mul_assoc]`. Use `_ = P * M x⁻¹ * P⁻¹ := by rw [hP]`. Rewrite using `[← Matrix.trace_conjTranspose, hct, Matrix.trace_mul_cycle, Matrix.nonsing_inv_mul P ((Matrix.isUnit_iff_isUnit_det P).1 hPu), Matrix.one_mul]`.
-/
theorem trace_inv_of_monoidHom {G : Type} [Group G] [Fintype G] {n : Type} [Fintype n] [DecidableEq n]
    (M : G →* Matrix n n ℂ) (x : G) : star (trace (M x)) = trace (M x⁻¹) := by
  classical
  set P : Matrix n n ℂ := ∑ g, (M g)ᴴ * M g with hPdef
  have hinv : ∀ y : G, M y * M y⁻¹ = 1 := fun y => by rw [← map_mul, mul_inv_cancel, map_one]
  have hP : (M x)ᴴ * P * M x = P := by
    rw [hPdef, Finset.mul_sum, Finset.sum_mul]
    refine Fintype.sum_equiv (Equiv.mulRight x) _ _ (fun g => ?_)
    simp only [Equiv.coe_mulRight, map_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hPpd : P.PosDef := by
    rw [hPdef, ← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : G))]
    simp only [map_one, Matrix.conjTranspose_one, Matrix.mul_one]
    exact Matrix.PosDef.one.add_posSemidef
      (Matrix.posSemidef_sum _ fun g _ => Matrix.posSemidef_conjTranspose_mul_self _)
  have hPu : IsUnit P := hPpd.isUnit
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P ((Matrix.isUnit_iff_isUnit_det P).1 hPu)
  have hct : (M x)ᴴ = P * M x⁻¹ * P⁻¹ := by
    calc (M x)ᴴ = (M x)ᴴ * P * (M x * M x⁻¹) * P⁻¹ := by
          rw [hinv, Matrix.mul_one, Matrix.mul_assoc, hPP, Matrix.mul_one]
      _ = ((M x)ᴴ * P * M x) * M x⁻¹ * P⁻¹ := by simp only [Matrix.mul_assoc]
      _ = P * M x⁻¹ * P⁻¹ := by rw [hP]
  rw [← Matrix.trace_conjTranspose, hct, Matrix.trace_mul_cycle,
    Matrix.nonsing_inv_mul P ((Matrix.isUnit_iff_isUnit_det P).1 hPu), Matrix.one_mul]

/- English proof (translation)
Introduce `G _ _ V x`. Set `b` to `Module.finBasis ℂ V`. Set `M : G →* Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ` to `(LinearMap.toMatrixAlgEquiv b).toAlgHom.toRingHom.toMonoidHom.comp V.ρ`. Establish `hc : ∀ y, V.character y = Matrix.trace (M y)` using `fun y => by`. Simplify using `only [FDRep.character, M, MonoidHom.comp_apply]`.

Rewrite using `[LinearMap.trace_eq_matrix_trace ℂ b]`. Both sides reduce to the same expression. Rewrite using `[hc, hc]`. Conclude with `trace_inv_of_monoidHom M x`.
-/
theorem conjugate_character_formula : ConjChar := by
  intro G _ _ V x
  let b := Module.finBasis ℂ V
  let M : G →* Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ :=
    (LinearMap.toMatrixAlgEquiv b).toAlgHom.toRingHom.toMonoidHom.comp V.ρ
  have hc : ∀ y, V.character y = Matrix.trace (M y) := fun y => by
    simp only [FDRep.character, M, MonoidHom.comp_apply]
    rw [LinearMap.trace_eq_matrix_trace ℂ b]
    rfl
  rw [hc, hc]
  exact trace_inv_of_monoidHom M x

end PI.SerBridgeGLW
