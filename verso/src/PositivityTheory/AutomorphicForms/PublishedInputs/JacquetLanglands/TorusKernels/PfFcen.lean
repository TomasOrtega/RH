import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormula

open Matrix

namespace UpperTheory.Esk.CentralTermsContribution

/- English proof (translation)
Simplify using `only [Units.val_mul]`. Rewrite using `[Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]`.
-/
theorem trace_conj {F : Type} [Field F] (γ δ : GL (Fin 2) F) :
    ((δ * γ * δ⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace = (γ : Matrix (Fin 2) (Fin 2) F).trace := by
  simp only [Units.val_mul]
  rw [Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]

end UpperTheory.Esk.CentralTermsContribution

/- English proof (translation)
Introduce `F _ γ δ htr h`. Establish `h' : ((δ * γ * δ⁻¹ : GL (Fin 2) F) : UpperTheory.Esk.PG F) = (γ : UpperTheory.Esk.PG F)`. Rewrite using `[QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]`. Conclude with `h`. Rewrite `h'` using `[QuotientGroup.eq]`.

Use `set c := (δ * γ * δ⁻¹)⁻¹ * γ with hc`. Take `⟨h1, h2, h3⟩` from `UpperTheory.Esk.center_entries h'`. Establish `hcv : (c : Matrix (Fin 2) (Fin 2) F) = c 0 0 • (1 : Matrix (Fin 2) (Fin 2) F)`. Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;> simp [h1, h2, h3]`. Establish `hγ : γ = (δ * γ * δ⁻¹) * c` using `by rw [hc]; group`.

Establish `hv : (γ : Matrix (Fin 2) (Fin 2) F) = ((δ * γ * δ⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (c : Matrix (Fin 2) (Fin 2) F)` using `by conv_lhs => rw [hγ]`. Rewrite using `[Units.val_mul]`. Establish `htr2 : c 0 0 * (γ : Matrix (Fin 2) (Fin 2) F).trace = 1 * (γ : Matrix (Fin 2) (Fin 2) F).trace` using `by conv_rhs => rw [hv, hcv, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul, UpperTheory.Esk.CentralTermsContribution.trace_conj]`. Expand and normalize the polynomial expressions, which then agree. Establish `ht : c 0 0 = 1` using `mul_right_cancel₀ htr htr2`.

Establish `hc1 : c = 1`. Use extensionality with `: 1`. Rewrite using `[hcv, ht, one_smul, Units.val_one]`. Rewrite `hγ` using `[hc1, mul_one]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem UpperTheory.Esk.pf_Fcen : UpperTheory.Esk.Fcen := by
  intro F _ γ δ htr h
  have h' : ((δ * γ * δ⁻¹ : GL (Fin 2) F) : UpperTheory.Esk.PG F) = (γ : UpperTheory.Esk.PG F) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]; exact h
  rw [QuotientGroup.eq] at h'
  set c := (δ * γ * δ⁻¹)⁻¹ * γ with hc
  obtain ⟨h1, h2, h3⟩ := UpperTheory.Esk.center_entries h'
  have hcv : (c : Matrix (Fin 2) (Fin 2) F) = c 0 0 • (1 : Matrix (Fin 2) (Fin 2) F) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [h1, h2, h3]
  have hγ : γ = (δ * γ * δ⁻¹) * c := by rw [hc]; group
  have hv : (γ : Matrix (Fin 2) (Fin 2) F) = ((δ * γ * δ⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (c : Matrix (Fin 2) (Fin 2) F) := by
    conv_lhs => rw [hγ]
    rw [Units.val_mul]
  have htr2 : c 0 0 * (γ : Matrix (Fin 2) (Fin 2) F).trace = 1 * (γ : Matrix (Fin 2) (Fin 2) F).trace := by
    conv_rhs => rw [hv, hcv, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul, UpperTheory.Esk.CentralTermsContribution.trace_conj]
    ring
  have ht : c 0 0 = 1 := mul_right_cancel₀ htr htr2
  have hc1 : c = 1 := by
    ext : 1
    rw [hcv, ht, one_smul, Units.val_one]
  rw [hc1, mul_one] at hγ
  calc δ * γ = δ * γ * δ⁻¹ * δ := by group
    _ = γ * δ := by rw [← hγ]
