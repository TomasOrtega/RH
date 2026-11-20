import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.XphiLinInd

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B HermitianLiftIdentities

/- English proof (translation)
Introduce `k r s μG Φ hk hμ _ hK x hx`. Take `⟨κ, hκ, hF⟩` from `fsE_left hIW hk hx`. Establish `h1 : ∀ g : Mt k r, κ⁻¹ * Matrix.of (lmulM κ g) = Matrix.of g` using `fun g => by show κ⁻¹ * (κ * Matrix.of g) = Matrix.of g`. Rewrite using `[← Matrix.mul_assoc, uh_inv_mul hκ.1, Matrix.one_mul]`. Combine the equalities or inequalities in the displayed calculation.

Use `lintegral_congr fun g => ?_` and prove the remaining obligations. Rewrite using `[hF s]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = ENNReal.ofReal (fsR k r s x) * ∫⁻ g, Φ g * FsE k r s (κ⁻¹ * Matrix.of g) ∂μG := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top`. Use `_ = _ := by`.

Rewrite using `[← lmul_int hκ.1 hμ (fun g => Φ g * FsE k r s (κ⁻¹ * Matrix.of g))]`. Use `congrArg _ (lintegral_congr fun g => ?_)` and prove the remaining obligations. Simplify using `only [hK κ hκ g, h1]`.
-/
theorem tLeftH (hIW : IW) (hB2 : InductiveHeisenbergInputs) : TLeft := by
  intro k r s μG Φ hk hμ _ hK x hx
  obtain ⟨κ, hκ, hF⟩ := fsE_left hIW hk hx
  have h1 : ∀ g : Mt k r, κ⁻¹ * Matrix.of (lmulM κ g) = Matrix.of g := fun g => by
    show κ⁻¹ * (κ * Matrix.of g) = Matrix.of g
    rw [← Matrix.mul_assoc, uh_inv_mul hκ.1, Matrix.one_mul]
  calc ∫⁻ g, Φ g * FsE k r s (x⁻¹ * Matrix.of g) ∂μG
      = ∫⁻ g, ENNReal.ofReal (fsR k r s x) * (Φ g * FsE k r s (κ⁻¹ * Matrix.of g)) ∂μG := by
        refine lintegral_congr fun g => ?_
        rw [hF s]; ring
    _ = ENNReal.ofReal (fsR k r s x) * ∫⁻ g, Φ g * FsE k r s (κ⁻¹ * Matrix.of g) ∂μG :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = _ := by
        rw [← lmul_int hκ.1 hμ (fun g => Φ g * FsE k r s (κ⁻¹ * Matrix.of g))]
        refine congrArg _ (lintegral_congr fun g => ?_)
        simp only [hK κ hκ g, h1]

/- English proof (translation)
Introduce `k r s μG Φ hk hμ hΦ hK x hx y hy`. Take `⟨κ, hκ, hF⟩` from `fsE_right hIW hk hy`. Establish `hL` using `tLeftH hIW hB2 k r s μG Φ hk hμ hΦ (fun κ hκ g => (hK κ hκ g).1) x hx`. Establish `h1 : ∀ g : Mt k r, x⁻¹ * Matrix.of (rmulF κ g) = x⁻¹ * Matrix.of g * κ` using `fun g => by show x⁻¹ * (Matrix.of g * κ) = x⁻¹ * Matrix.of g * κ`. Rewrite using `[Matrix.mul_assoc]`.

Combine the equalities or inequalities in the displayed calculation. Use `lintegral_congr fun g => ?_` and prove the remaining obligations. Rewrite using `[hF s]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = ENNReal.ofReal (fsR k r s y) * ∫⁻ g, Φ g * FsE k r s (x⁻¹ * Matrix.of g * κ) ∂μG := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top`.

Use `_ = ENNReal.ofReal (fsR k r s y) * ∫⁻ g, Φ g * FsE k r s (x⁻¹ * Matrix.of g) ∂μG := by`. Rewrite using `[← rmul_int hκ.1 hμ (fun g => Φ g * FsE k r s (x⁻¹ * Matrix.of g))]`. Use `congrArg _ (lintegral_congr fun g => ?_)` and prove the remaining obligations. Simplify using `only [(hK κ hκ g).2, h1]`. Use `_ = _ := by`.

Rewrite using `[hL, ENNReal.ofReal_mul (fsR_nonneg hk hx s)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tBothH (hIW : IW) (hB2 : InductiveHeisenbergInputs) : TBoth := by
  intro k r s μG Φ hk hμ hΦ hK x hx y hy
  obtain ⟨κ, hκ, hF⟩ := fsE_right hIW hk hy
  have hL := tLeftH hIW hB2 k r s μG Φ hk hμ hΦ (fun κ hκ g => (hK κ hκ g).1) x hx
  have h1 : ∀ g : Mt k r, x⁻¹ * Matrix.of (rmulF κ g) = x⁻¹ * Matrix.of g * κ := fun g => by
    show x⁻¹ * (Matrix.of g * κ) = x⁻¹ * Matrix.of g * κ
    rw [Matrix.mul_assoc]
  calc ∫⁻ g, Φ g * FsE k r s (x⁻¹ * Matrix.of g * y) ∂μG
      = ∫⁻ g, ENNReal.ofReal (fsR k r s y) * (Φ g * FsE k r s (x⁻¹ * Matrix.of g * κ)) ∂μG := by
        refine lintegral_congr fun g => ?_
        rw [hF s]; ring
    _ = ENNReal.ofReal (fsR k r s y) * ∫⁻ g, Φ g * FsE k r s (x⁻¹ * Matrix.of g * κ) ∂μG :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (fsR k r s y) * ∫⁻ g, Φ g * FsE k r s (x⁻¹ * Matrix.of g) ∂μG := by
        rw [← rmul_int hκ.1 hμ (fun g => Φ g * FsE k r s (x⁻¹ * Matrix.of g))]
        refine congrArg _ (lintegral_congr fun g => ?_)
        simp only [(hK κ hκ g).2, h1]
    _ = _ := by
        rw [hL, ENNReal.ofReal_mul (fsR_nonneg hk hx s)]
        ring

end ReciprocityTheory.ChartRestriction.DS.Xi
