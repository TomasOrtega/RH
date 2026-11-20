import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.FrMulK
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.HaarGramPositivity.GramStrictPos

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace PositivityTheory.RgBcC.CxeAvg

open PositivityTheory.RgTw (Mat)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lefFr_eq (lam : Fin n → ℤ) (x : Mat n) :
    lefFr n lam x = sqQ lam * (clm lam (fr0 lam x) * Ring.inverse (sqQ lam)) := rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨Ring.mul_inverse_cancel _ (hA n lam).1, Ring.inverse_mul_cancel _ (hA n lam).1⟩`.
-/
theorem sq_inv (hA : Avg) (lam : Fin n → ℤ) :
    sqQ lam * Ring.inverse (sqQ lam) = 1 ∧ Ring.inverse (sqQ lam) * sqQ lam = 1 :=
  ⟨Ring.mul_inverse_cancel _ (hA n lam).1, Ring.inverse_mul_cancel _ (hA n lam).1⟩

/- English proof (translation)
Take `⟨h1, _⟩` from `sq_inv hA lam`. Establish `hs : star (sqQ (n` using `n) lam) = sqQ lam := (hA n lam).2.1.star_eq`. Rewrite using `[← ContinuousLinearMap.star_eq_adjoint]`. Establish `key : star (Ring.inverse (sqQ (n` using `n) lam)) * star (sqQ lam) = 1 := by`. Rewrite using `[← star_mul, h1, star_one]`.

Rewrite `key` using `[hs]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h1, mul_one]`. Use `_ = (star (Ring.inverse (sqQ (n := n) lam)) * sqQ lam) * Ring.inverse (sqQ lam) := by`. Rewrite using `[mul_assoc]`.

Use `_ = Ring.inverse (sqQ lam) := by rw [key, one_mul]`.
-/
theorem adjoint_inv (hA : Avg) (lam : Fin n → ℤ) :
    ContinuousLinearMap.adjoint (Ring.inverse (sqQ (n := n) lam)) = Ring.inverse (sqQ lam) := by
  obtain ⟨h1, _⟩ := sq_inv hA lam
  have hs : star (sqQ (n := n) lam) = sqQ lam := (hA n lam).2.1.star_eq
  rw [← ContinuousLinearMap.star_eq_adjoint]
  have key : star (Ring.inverse (sqQ (n := n) lam)) * star (sqQ lam) = 1 := by
    rw [← star_mul, h1, star_one]
  rw [hs] at key
  calc star (Ring.inverse (sqQ (n := n) lam))
      = star (Ring.inverse (sqQ (n := n) lam)) * (sqQ lam * Ring.inverse (sqQ lam)) := by
        rw [h1, mul_one]
    _ = (star (Ring.inverse (sqQ (n := n) lam)) * sqQ lam) * Ring.inverse (sqQ lam) := by
        rw [mul_assoc]
    _ = Ring.inverse (sqQ lam) := by rw [key, one_mul]

/- English proof (translation)
Simplify using `only [clm, map_mul]`.
-/
theorem clm_mul' (lam : Fin n → ℤ) (A B : Matrix (Ix n lam) (Ix n lam) ℂ) :
    clm lam (A * B) = clm lam A * clm lam B := by simp only [clm, map_mul]

end PositivityTheory.RgBcC.CxeAvg

namespace PositivityTheory.RgBcC

open PositivityTheory.RgBcC.CxeAvg

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Introduce `n lam`. Rewrite using `[lefFr_eq, (hF n lam).1]`. Simplify using `only [clm, map_one, one_mul]`. Conclude with `(sq_inv hA lam).1`.
-/
theorem frOne' (hF : MatrixFrechetDerivativeAtZeroLaws) (hA : Avg) : FrOne := by
  intro n lam
  rw [lefFr_eq, (hF n lam).1]
  simp only [clm, map_one, one_mul]
  exact (sq_inv hA lam).1

/- English proof (translation)
Introduce `n lam k k'`. Establish `h2` using `(sq_inv hA lam).2`. Rewrite using `[CxeAvg.lefFr_eq, CxeAvg.lefFr_eq, CxeAvg.lefFr_eq, Submonoid.coe_mul, (hF n lam).2.1 _ _ (Matrix.UnitaryGroup.det_isUnit k) (Matrix.UnitaryGroup.det_isUnit k'), clm_mul']`. Simplify using `only [mul_assoc]`. Rewrite using `[← mul_assoc (Ring.inverse (sqQ lam)) (sqQ lam), h2, one_mul]`.
-/
theorem frMulK' (hF : MatrixFrechetDerivativeAtZeroLaws) (hA : Avg) : FrMulK := by
  intro n lam k k'
  have h2 := (sq_inv hA lam).2
  rw [CxeAvg.lefFr_eq, CxeAvg.lefFr_eq, CxeAvg.lefFr_eq, Submonoid.coe_mul,
    (hF n lam).2.1 _ _ (Matrix.UnitaryGroup.det_isUnit k) (Matrix.UnitaryGroup.det_isUnit k'),
    clm_mul']
  simp only [mul_assoc]
  rw [← mul_assoc (Ring.inverse (sqQ lam)) (sqQ lam), h2, one_mul]

/- English proof (translation)
Introduce `n lam k v`. Take `⟨h1, h2⟩` from `sq_inv hA lam`. Establish `hs : star (sqQ (n` using `n) lam) = sqQ lam := (hA n lam).2.1.star_eq`. Establish `hr : star (Ring.inverse (sqQ (n` using `n) lam)) = Ring.inverse (sqQ lam) := by`. Rewrite using `[ContinuousLinearMap.star_eq_adjoint]`.

Conclude with `adjoint_inv hA lam`. Use `set C := clm lam (fr0 lam (k : Matrix (Fin n) (Fin n) ℂ)) with hCdef`. Establish `hC : star C * gramQ lam * C = gramQ lam`. Rewrite using `[ContinuousLinearMap.star_eq_adjoint]`. Conclude with `(hA n lam).2.2.2.1 k`.

Establish `hg : sqQ lam * sqQ lam = gramQ lam` using `(hA n lam).2.2.1`. Establish `hTT : star (sqQ lam * (C * Ring.inverse (sqQ lam))) * (sqQ lam * (C * Ring.inverse (sqQ lam))) = 1`. Rewrite using `[star_mul, star_mul, hs, hr]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_assoc]`.

Use `_ = 1 := by`. Rewrite using `[hg, hC, ← hg, ← mul_assoc (Ring.inverse (sqQ lam)) (sqQ lam) (sqQ lam), h2, one_mul, h1]`. Rewrite using `[CxeAvg.lefFr_eq]`. Use `set T := sqQ lam * (C * Ring.inverse (sqQ lam)) with hT`. Establish `hin : inner ℂ (T v) (T v) = inner ℂ v v`.

Rewrite using `[← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.mul_apply, hTT, ContinuousLinearMap.one_apply]`. Establish `h3 : ‖T v‖ ^ 2 = ‖v‖ ^ 2`. Rewrite using `[← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ), hin]`. Conclude with `(sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h3`.
-/
theorem frIso' (_hF : MatrixFrechetDerivativeAtZeroLaws) (hA : Avg) : FrIso := by
  intro n lam k v
  obtain ⟨h1, h2⟩ := sq_inv hA lam
  have hs : star (sqQ (n := n) lam) = sqQ lam := (hA n lam).2.1.star_eq
  have hr : star (Ring.inverse (sqQ (n := n) lam)) = Ring.inverse (sqQ lam) := by
    rw [ContinuousLinearMap.star_eq_adjoint]; exact adjoint_inv hA lam
  set C := clm lam (fr0 lam (k : Matrix (Fin n) (Fin n) ℂ)) with hCdef
  have hC : star C * gramQ lam * C = gramQ lam := by
    rw [ContinuousLinearMap.star_eq_adjoint]; exact (hA n lam).2.2.2.1 k
  have hg : sqQ lam * sqQ lam = gramQ lam := (hA n lam).2.2.1
  have hTT : star (sqQ lam * (C * Ring.inverse (sqQ lam))) * (sqQ lam * (C * Ring.inverse (sqQ lam))) = 1 := by
    rw [star_mul, star_mul, hs, hr]
    calc Ring.inverse (sqQ lam) * star C * sqQ lam * (sqQ lam * (C * Ring.inverse (sqQ lam)))
        = Ring.inverse (sqQ lam) * (star C * (sqQ lam * sqQ lam) * C) * Ring.inverse (sqQ lam) := by
          simp only [mul_assoc]
      _ = 1 := by
          rw [hg, hC, ← hg, ← mul_assoc (Ring.inverse (sqQ lam)) (sqQ lam) (sqQ lam), h2, one_mul, h1]
  rw [CxeAvg.lefFr_eq]
  set T := sqQ lam * (C * Ring.inverse (sqQ lam)) with hT
  have hin : inner ℂ (T v) (T v) = inner ℂ v v := by
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
      ← ContinuousLinearMap.mul_apply, hTT, ContinuousLinearMap.one_apply]
  have h3 : ‖T v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ), hin]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h3

/- English proof (translation)
Introduce `n lam`. Simplify using `only [lefFr_eq]`. Establish `h1 : ContinuousOn (fr0 (n` using `n) lam) (GLs n) := ((hF n lam).2.2).continuousOn`. Establish `h2 : Continuous fun k : UK n => fr0 lam k.1` using `h1.comp_continuous continuous_subtype_val mem_GLs`. Conclude with `continuous_const.mul (((clm_continuous lam).comp h2).mul continuous_const)`.
-/
theorem frCont' (hF : MatrixFrechetDerivativeAtZeroLaws) (hA : Avg) : FrCont := by
  intro n lam
  simp only [lefFr_eq]
  have h1 : ContinuousOn (fr0 (n := n) lam) (GLs n) := ((hF n lam).2.2).continuousOn
  have h2 : Continuous fun k : UK n => fr0 lam k.1 := h1.comp_continuous continuous_subtype_val mem_GLs
  exact continuous_const.mul (((clm_continuous lam).comp h2).mul continuous_const)

end PositivityTheory.RgBcC
