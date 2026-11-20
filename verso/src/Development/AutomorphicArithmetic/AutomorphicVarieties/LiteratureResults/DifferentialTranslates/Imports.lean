import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.SecondFromFirstStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.NormFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.NormInf

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped TensorProduct ContDiff

namespace UpperTheory.V.Lit.Dr

/- English proof (translation)
Introduce `E _ _ _ a ha ho U Ξ hU`. Take `⟨f, hf, hfe⟩` from `normFin E a U hU`. Take `⟨δ, hδs, hδp, hδh, hδe⟩` from `normInf E a`. Establish `hN : a * Fintype.card (InfinitePlace E) ≠ 0` using `Nat.mul_ne_zero (by omega) Fintype.card_ne_zero`. Generalize the expression as in `a * Fintype.card (InfinitePlace E) = N at hδh hN`.

Use `⟨fun s p => (δ p * f s) ^ (-(N : ℝ)⁻¹), fun s => ⟨?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `p hp`. Conclude with `(((hδs.mul contDiff_const).contDiffAt (x := p)).rpow_const_of_ne (mul_pos (hδp p hp) (hf s)).ne').contDiffWithinAt`. Introduce `p hp`. Conclude with `Real.rpow_pos_of_pos (mul_pos (hδp p hp) (hf s)) _`.

Introduce `t ht p hp beta_reduce`. Rewrite using `[hδh, mul_assoc, Real.mul_rpow (pow_pos ht N).le (mul_pos (hδp p hp) (hf s)).le, Real.rpow_neg (pow_pos ht N).le, Real.pow_rpow_inv_natCast ht.le hN]`. Introduce `γ s p _ beta_reduce`. Establish `h0 : |((Algebra.norm ℚ γ.1.val.det : ℚ) : ℝ)| ≠ 0`. Rewrite using `[abs_ne_zero, Rat.cast_ne_zero, Algebra.norm_ne_zero_iff]`.

Conclude with `γ.1.det_ne_zero`. Rewrite using `[geo_ρ, geo_σ, hfe, hδe]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts.
-/
theorem gauge : Gauge := by
  intro E _ _ _ a ha ho U Ξ hU
  obtain ⟨f, hf, hfe⟩ := normFin E a U hU
  obtain ⟨δ, hδs, hδp, hδh, hδe⟩ := normInf E a
  have hN : a * Fintype.card (InfinitePlace E) ≠ 0 :=
    Nat.mul_ne_zero (by omega) Fintype.card_ne_zero
  generalize a * Fintype.card (InfinitePlace E) = N at hδh hN
  refine ⟨fun s p => (δ p * f s) ^ (-(N : ℝ)⁻¹), fun s => ⟨?_, ?_, ?_⟩, ?_⟩
  · intro p hp
    exact (((hδs.mul contDiff_const).contDiffAt (x := p)).rpow_const_of_ne
      (mul_pos (hδp p hp) (hf s)).ne').contDiffWithinAt
  · intro p hp
    exact Real.rpow_pos_of_pos (mul_pos (hδp p hp) (hf s)) _
  · intro t ht p hp
    beta_reduce
    rw [hδh, mul_assoc, Real.mul_rpow (pow_pos ht N).le (mul_pos (hδp p hp) (hf s)).le,
      Real.rpow_neg (pow_pos ht N).le, Real.pow_rpow_inv_natCast ht.le hN]
  · intro γ s p _
    beta_reduce
    have h0 : |((Algebra.norm ℚ γ.1.val.det : ℚ) : ℝ)| ≠ 0 := by
      rw [abs_ne_zero, Rat.cast_ne_zero, Algebra.norm_ne_zero_iff]
      exact γ.1.det_ne_zero
    rw [geo_ρ, geo_σ, hfe, hδe]
    congr 1
    field_simp

end UpperTheory.V.Lit.Dr
