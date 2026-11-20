import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementR
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.FlowDouble
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.DifferenceLinearCoeff

open PowerSeries

universe u

noncomputable section

namespace Formalism.L2.Th1.A

namespace Rr

variable {K : Type u} [Field K] [CharZero K] (W : WeierstrassCurve K)

/- English proof (translation)
Establish `h1` using `(wpODE K W).1`. Establish `h2` using `(wpPrimeShape K W).1`. Establish `hq` using `Two.exp_mul_inv W`. Establish `hz : (toL X : LaurentSeries K) * uPow (-1) = 1` using `Plus.toL_X_mul`. Establish `hy : (yS W).subst (expSer W) = -(xS W).subst (expSer W)`.

Rewrite using `[yS, ← coe_substAlgHom (Two.he W), map_neg]`. Rewrite `h1` using `[h2, xZ, yZ, hy, Plus.uPow_neg_three]`. Apply `toL_injective` to reduce the goal to its premises. Simplify using `only [map_mul, map_add, map_neg, map_pow, map_ofNat, toL_C] at h1 ⊢`. Generalize the expression as in `toL ((xS W).subst (expSer W)) = xs at h1 ⊢`.

Generalize the expression as in `toL (derivative K (wpReg W)) = P at h1 ⊢`. Generalize the expression as in `(toL (expSer W))⁻¹ = q at h1 hq ⊢`. Generalize the expression as in `toL (expSer W) = E at hq ⊢`. Generalize the expression as in `(uPow (-1) : LaurentSeries K) = zi at h1 hz`. Generalize the expression as in `(toL X : LaurentSeries K) = Z at hz ⊢`.

Take the linear combination `E ^ 3 * Z ^ 3 * h1 + 2 * E ^ 3 * ((Z * zi) ^ 2 + Z * zi + 1) * hz - Z ^ 3 * (2 * xs * ((E * q) ^ 2 + E * q + 1) - HahnSeries.C W.a₁ * E * xs * (E * q + 1)) * hq`.
-/
theorem wpPrimeInZ : expSer W ^ 3 * (-2 + X ^ 3 * derivative K (wpReg W))
    = X ^ 3 * (-2 * (xS W).subst (expSer W) + C W.a₁ * expSer W * (xS W).subst (expSer W)
        + C W.a₃ * expSer W ^ 3) := by
  have h1 := (wpODE K W).1
  have h2 := (wpPrimeShape K W).1
  have hq := Two.exp_mul_inv W
  have hz : (toL X : LaurentSeries K) * uPow (-1) = 1 := Plus.toL_X_mul
  have hy : (yS W).subst (expSer W) = -(xS W).subst (expSer W) := by
    rw [yS, ← coe_substAlgHom (Two.he W), map_neg]
  rw [h2, xZ, yZ, hy, Plus.uPow_neg_three] at h1
  apply toL_injective
  simp only [map_mul, map_add, map_neg, map_pow, map_ofNat, toL_C] at h1 ⊢
  generalize toL ((xS W).subst (expSer W)) = xs at h1 ⊢
  generalize toL (derivative K (wpReg W)) = P at h1 ⊢
  generalize (toL (expSer W))⁻¹ = q at h1 hq ⊢
  generalize toL (expSer W) = E at hq ⊢
  generalize (uPow (-1) : LaurentSeries K) = zi at h1 hz
  generalize (toL X : LaurentSeries K) = Z at hz ⊢
  linear_combination E ^ 3 * Z ^ 3 * h1 + 2 * E ^ 3 * ((Z * zi) ^ 2 + Z * zi + 1) * hz
    - Z ^ 3 * (2 * xs * ((E * q) ^ 2 + E * q + 1) - HahnSeries.C W.a₁ * E * xs * (E * q + 1)) * hq

end Rr

/- English proof (translation)
Introduce `K _ _ W`. Take `⟨l0, -, -, -⟩` from `logSpec K W`. Take `⟨-, -, -, hel, -⟩` from `expSpec K W`. Establish `hl : HasSubst (logSer W)` using `HasSubst.of_constantCoeff_zero' l0`. Establish `h` using `congrArg (ISer.subHom (logSer W) l0) (Rr.wpPrimeInZ W)`.

Establish `k` using `subst_comp_subst_apply (Two.he W) hl (xS W)`. Rewrite `k` using `[hel, X_subst]`. Simplify using `only [map_mul, map_add, map_neg, map_pow, map_ofNat, ISer.subHom_C, ISer.subHom_X] at h`. Simplify using `only [ISer.subHom_apply, hel, k] at h`. Conclude with `h`.
-/
theorem weierstrass_p_prime_unit : WpPrimeInU.{u} := by
  intro K _ _ W
  obtain ⟨l0, -, -, -⟩ := logSpec K W
  obtain ⟨-, -, -, hel, -⟩ := expSpec K W
  have hl : HasSubst (logSer W) := HasSubst.of_constantCoeff_zero' l0
  have h := congrArg (ISer.subHom (logSer W) l0) (Rr.wpPrimeInZ W)
  have k := subst_comp_subst_apply (Two.he W) hl (xS W)
  rw [hel, X_subst] at k
  simp only [map_mul, map_add, map_neg, map_pow, map_ofNat, ISer.subHom_C, ISer.subHom_X] at h
  simp only [ISer.subHom_apply, hel, k] at h
  exact h

/- English proof (translation)
Introduce `K _ _ _ W hW`. Use `⟨weierstrass_p_prime_unit K W, ?_⟩` and prove the remaining obligations. Take `⟨-, ⟨e, he, he0, hdet⟩, -⟩` from `cube_mem' K W (Formalism.G.unitBall K) hW.1 hW.2.1 hW.2.2.1 hW.2.2.2.1 hW.2.2.2.2`. Use `⟨e, Bridge.integral_of_mvCoeff he, he0, ?_⟩` and prove the remaining obligations. Establish `hy : ∀ i : Fin 3, (yS W).subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) K) = -(xS W).subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) K)` using `fun i => CubeR.yS_subst W (MvPowerSeries.constantCoeff_X i)`.

Simplify using `only [hy] at hdet`. Unfold `Formalism.L2.Th1.B.F3 Formalism.InvariantFactorPaths.G7.in3 Formalism.InvariantFactorPaths.G7.at1`. Conclude with `hdet`.
-/
theorem three_curves_relation : BridgeCurve3 := by
  intro K _ _ _ W hW
  refine ⟨weierstrass_p_prime_unit K W, ?_⟩
  obtain ⟨-, ⟨e, he, he0, hdet⟩, -⟩ :=
    cube_mem' K W (Formalism.G.unitBall K) hW.1 hW.2.1 hW.2.2.1 hW.2.2.2.1 hW.2.2.2.2
  refine ⟨e, Bridge.integral_of_mvCoeff he, he0, ?_⟩
  have hy : ∀ i : Fin 3, (yS W).subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) K)
      = -(xS W).subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) K) := fun i =>
    CubeR.yS_subst W (MvPowerSeries.constantCoeff_X i)
  simp only [hy] at hdet
  unfold Formalism.L2.Th1.B.F3 Formalism.InvariantFactorPaths.G7.in3 Formalism.InvariantFactorPaths.G7.at1
  exact hdet

end Formalism.L2.Th1.A
