import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RationalRealBlocks.EvenStep
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RationalRealBlocks.Bridge

open MvPolynomial Matrix

noncomputable section

namespace PI.BlockRatReal.UnitaryGroupMassFormula

/- English proof (translation)
Introduce `a b hab`. Establish `h1` using `h hab`. Conclude with `Int.toNat_le_toNat (by omega)`.
-/
theorem nuOf_antitone {m : ℕ} {lam : Fin (m + 1) → ℤ} (h : Antitone lam) : Antitone (nuOf lam) := by
  intro a b hab
  have h1 := h hab
  exact Int.toNat_le_toNat (by omega)

/- English proof (translation)
Establish `hu : IsUnit M0.1.det` using `(Matrix.isUnit_iff_isUnit_det _).mp M0.isUnit`. Establish `hm` using `RingHom.map_det embLL M0.1`. Rewrite `hm` using `[RingHom.mapMatrix_apply]`. Rewrite using `[← hm]`. Conclude with `(map_ne_zero embLL).mpr hu.ne_zero`.
-/
theorem det_map_ne {LL : Type} [Field LL] (embLL : LL →+* ℂ) {k : ℕ} (M0 : GL (Fin k) LL) :
    (M0.1.map embLL).det ≠ 0 := by
  have hu : IsUnit M0.1.det := (Matrix.isUnit_iff_isUnit_det _).mp M0.isUnit
  have hm := RingHom.map_det embLL M0.1
  rw [RingHom.mapMatrix_apply] at hm
  rw [← hm]
  exact (map_ne_zero embLL).mpr hu.ne_zero

/- English proof (translation)
Introduce `m LL _ embLL lam hl M0 f hf`. Use `⟨C (M0.1.det ^ (-lam (Fin.last m))) * Formalism.GradedWeylDivisibility.rowAct LL (↑M0⁻¹ : Matrix (Fin (m + 1)) (Fin (m + 1)) LL) (MvPolynomial.map (Int.castRingHom LL) f), ?_, fun y _ => ?_⟩` and prove the remaining obligations. Rewrite using `[MvPolynomial.C_mul']`. Conclude with `Submodule.smul_mem _ _ (s2 _ _ _ _ (s1 _ _ _ (nuOf_antitone hl) f hf))`. Establish `hd` using `det_map_ne embLL M0`.

Establish `hmul : (↑M0⁻¹ : Matrix (Fin (m + 1)) (Fin (m + 1)) LL).map embLL * (M0.1.map embLL * y) = y`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.map_mul, M0.inv_mul, Matrix.map_one embLL (map_zero _) (map_one _), Matrix.one_mul]`. Establish `hc : embLL (M0.1.det ^ (-lam (Fin.last m))) = (M0.1.map embLL).det ^ (-lam (Fin.last m))`. Rewrite using `[map_zpow₀, RingHom.map_det, RingHom.mapMatrix_apply]`. Rewrite using `[map_mul, map_C, eval_mul, eval_C, eval_map_rowAct, hmul, map_map_int, hc, Matrix.det_mul, mul_zpow, _root_.zpow_neg]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem evenStep : EvenStep := by
  intro m LL _ embLL lam hl M0 f hf
  refine ⟨C (M0.1.det ^ (-lam (Fin.last m))) * Formalism.GradedWeylDivisibility.rowAct LL (↑M0⁻¹ : Matrix (Fin (m + 1)) (Fin (m + 1)) LL)
    (MvPolynomial.map (Int.castRingHom LL) f), ?_, fun y _ => ?_⟩
  · rw [MvPolynomial.C_mul']
    exact Submodule.smul_mem _ _ (s2 _ _ _ _ (s1 _ _ _ (nuOf_antitone hl) f hf))
  · have hd := det_map_ne embLL M0
    have hmul : (↑M0⁻¹ : Matrix (Fin (m + 1)) (Fin (m + 1)) LL).map embLL * (M0.1.map embLL * y) = y := by
      rw [← Matrix.mul_assoc, ← Matrix.map_mul, M0.inv_mul, Matrix.map_one embLL (map_zero _) (map_one _),
        Matrix.one_mul]
    have hc : embLL (M0.1.det ^ (-lam (Fin.last m))) = (M0.1.map embLL).det ^ (-lam (Fin.last m)) := by
      rw [map_zpow₀, RingHom.map_det, RingHom.mapMatrix_apply]
    rw [map_mul, map_C, eval_mul, eval_C, eval_map_rowAct, hmul, map_map_int, hc, Matrix.det_mul, mul_zpow,
      _root_.zpow_neg]
    field_simp

end PI.BlockRatReal.UnitaryGroupMassFormula
