import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.PerronHorizontalSegmentBound
import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.IntegralEqIntervalIntegralAddCompl
import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.NormIntegralComplLe

open Complex MeasureTheory

noncomputable section

namespace Formalism.ZeroFreeDirichlet

/- English proof (translation)
Establish `hab : (1 - c₁ / (3 * L)) - (1 - c₁ / (4 * L)) = -(2 * (c₁ / (24 * L)))`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `he : 0 < c₁ / (24 * L)` using `by positivity`. Break down `Finset.eq_empty_or_nonempty B with hB0 | ⟨β, hβ⟩` into its components or cases.

Conclude with `⟨_, Or.inl rfl, fun β hβ => by simp [hB0] at hβ⟩`. Establish `hBs : ∀ β' ∈ B, β' = β` using `fun β' hβ' => Finset.card_le_one.mp hB β' hβ' β hβ`. Distinguish the cases in `h : c₁ / (24 * L) ≤ |(1 - c₁ / (3 * L)) - β|`. Conclude with `⟨_, Or.inl rfl, fun β' hβ' => by rw [hBs β' hβ']; exact h⟩`. Use `⟨_, Or.inr rfl, fun β' hβ' => ?_⟩` and prove the remaining obligations.

Rewrite using `[hBs β' hβ']`. Use `push_neg at h`. Establish `tri` using `abs_sub_le (1 - c₁ / (3 * L)) β (1 - c₁ / (4 * L))`. Rewrite `tri` using `[hab, abs_neg, abs_of_pos (by positivity), abs_sub_comm β]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_contour_avoiding_real_zero (B : Finset ℝ) (hB : B.card ≤ 1) (L c₁ : ℝ) (hL : 0 < L) (hc₁ : 0 < c₁) :
    ∃ σ₁ : ℝ, (σ₁ = 1 - c₁ / (3 * L) ∨ σ₁ = 1 - c₁ / (4 * L)) ∧
      ∀ β ∈ B, c₁ / (24 * L) ≤ |σ₁ - β| := by
  have hab : (1 - c₁ / (3 * L)) - (1 - c₁ / (4 * L)) = -(2 * (c₁ / (24 * L))) := by
    field_simp
    ring
  have he : 0 < c₁ / (24 * L) := by positivity
  rcases Finset.eq_empty_or_nonempty B with hB0 | ⟨β, hβ⟩
  · exact ⟨_, Or.inl rfl, fun β hβ => by simp [hB0] at hβ⟩
  have hBs : ∀ β' ∈ B, β' = β := fun β' hβ' => Finset.card_le_one.mp hB β' hβ' β hβ
  by_cases h : c₁ / (24 * L) ≤ |(1 - c₁ / (3 * L)) - β|
  · exact ⟨_, Or.inl rfl, fun β' hβ' => by rw [hBs β' hβ']; exact h⟩
  · refine ⟨_, Or.inr rfl, fun β' hβ' => ?_⟩
    rw [hBs β' hβ']
    push_neg at h
    have tri := abs_sub_le (1 - c₁ / (3 * L)) β (1 - c₁ / (4 * L))
    rw [hab, abs_neg, abs_of_pos (by positivity), abs_sub_comm β] at tri
    linarith

/- English proof (translation)
Take `⟨hint, hS⟩` from `hP q χ y hy σ₀ hσ₀`. Establish `hsplit` using `integral_add_compl (s := Set.Ioc (-T) T) measurableSet_Ioc hint`. Establish `hIoc : ∫ t in Set.Ioc (-T) T, Fchi χ y ((σ₀ : ℂ) + t * I) = ∫ t in (-T)..T, Fchi χ y ((σ₀ : ℂ) + t * I)` using `(intervalIntegral.integral_of_le (by linarith)).symm`. Unfold `Formalism.ZF.rectInt at hrect`. Use `set Cp := ∫ t in (Set.Ioc (-T) T)ᶜ, Fchi χ y ((σ₀ : ℂ) + t * I) with hCp`.

Use `set Bt := ∫ x in σ₁..σ₀, Fchi χ y ((x : ℂ) + ((-T : ℝ) : ℂ) * I) with hBt`. Use `set Tp := ∫ x in σ₁..σ₀, Fchi χ y ((x : ℂ) + (T : ℂ) * I) with hTp`. Use `set Lf := ∫ u in (-T)..T, Fchi χ y ((σ₁ : ℂ) + u * I) with hLf`. Use `set Rt := ∫ t in (-T)..T, Fchi χ y ((σ₀ : ℂ) + t * I) with hRt`. Establish `hpi : (2 * (Real.pi : ℂ)) ≠ 0` using `mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')`.

Establish `hinv : (2 * (Real.pi : ℂ)) * (1 / (2 * Real.pi)) = 1` using `by field_simp`. Establish `hI : I * I = -1` using `Complex.I_mul_I`. Establish `key : (2 * (Real.pi : ℂ)) * (Schi χ y - R) = Cp + I * (Bt - Tp) + Lf`. Rewrite using `[hS, ← hsplit, hIoc]`. Take the linear combination `(-I) * hrect + (Rt + Cp) * hinv + (Rt - Lf - 2 * Real.pi * R) * hI`.

Establish `hn : ‖(2 * (Real.pi : ℂ))‖ = 2 * Real.pi`. Rewrite using `[show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring, Complex.norm_of_nonneg (by positivity)]`. Establish `hsub` using `norm_sub_le Bt Tp`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_mul, hn]`.

Use `_ = ‖Cp + I * (Bt - Tp) + Lf‖ := by rw [key]`. Use `_ ≤ ‖Cp‖ + ‖I * (Bt - Tp)‖ + ‖Lf‖ := norm_add₃_le`. Use `_ ≤ ‖Cp‖ + ‖Bt‖ + ‖Tp‖ + ‖Lf‖ := by`. Rewrite using `[norm_mul, Complex.norm_I, one_mul]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem perron_contour_decomposition (hP : PerronChi) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (y σ₁ σ₀ T : ℝ) (R : ℂ) (hy : 1 ≤ y) (hσ₀ : 1 < σ₀) (hT : 0 ≤ T)
    (hrect : Formalism.ZF.rectInt (Fchi χ y) σ₁ σ₀ (-T) T = 2 * Real.pi * I * R) :
    2 * Real.pi * ‖Schi χ y - R‖ ≤
      ‖∫ t in (Set.Ioc (-T) T)ᶜ, Fchi χ y ((σ₀ : ℂ) + t * I)‖
      + ‖∫ x in σ₁..σ₀, Fchi χ y ((x : ℂ) + ((-T : ℝ) : ℂ) * I)‖
      + ‖∫ x in σ₁..σ₀, Fchi χ y ((x : ℂ) + (T : ℂ) * I)‖
      + ‖∫ u in (-T)..T, Fchi χ y ((σ₁ : ℂ) + u * I)‖ := by
  obtain ⟨hint, hS⟩ := hP q χ y hy σ₀ hσ₀
  have hsplit := integral_add_compl (s := Set.Ioc (-T) T) measurableSet_Ioc hint
  have hIoc : ∫ t in Set.Ioc (-T) T, Fchi χ y ((σ₀ : ℂ) + t * I) =
      ∫ t in (-T)..T, Fchi χ y ((σ₀ : ℂ) + t * I) :=
    (intervalIntegral.integral_of_le (by linarith)).symm
  unfold Formalism.ZF.rectInt at hrect
  set Cp := ∫ t in (Set.Ioc (-T) T)ᶜ, Fchi χ y ((σ₀ : ℂ) + t * I) with hCp
  set Bt := ∫ x in σ₁..σ₀, Fchi χ y ((x : ℂ) + ((-T : ℝ) : ℂ) * I) with hBt
  set Tp := ∫ x in σ₁..σ₀, Fchi χ y ((x : ℂ) + (T : ℂ) * I) with hTp
  set Lf := ∫ u in (-T)..T, Fchi χ y ((σ₁ : ℂ) + u * I) with hLf
  set Rt := ∫ t in (-T)..T, Fchi χ y ((σ₀ : ℂ) + t * I) with hRt
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')
  have hinv : (2 * (Real.pi : ℂ)) * (1 / (2 * Real.pi)) = 1 := by field_simp
  have hI : I * I = -1 := Complex.I_mul_I
  have key : (2 * (Real.pi : ℂ)) * (Schi χ y - R) = Cp + I * (Bt - Tp) + Lf := by
    rw [hS, ← hsplit, hIoc]
    linear_combination (-I) * hrect + (Rt + Cp) * hinv + (Rt - Lf - 2 * Real.pi * R) * hI
  have hn : ‖(2 * (Real.pi : ℂ))‖ = 2 * Real.pi := by
    rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_of_nonneg (by positivity)]
  have hsub := norm_sub_le Bt Tp
  calc 2 * Real.pi * ‖Schi χ y - R‖ = ‖(2 * (Real.pi : ℂ)) * (Schi χ y - R)‖ := by
        rw [norm_mul, hn]
    _ = ‖Cp + I * (Bt - Tp) + Lf‖ := by rw [key]
    _ ≤ ‖Cp‖ + ‖I * (Bt - Tp)‖ + ‖Lf‖ := norm_add₃_le
    _ ≤ ‖Cp‖ + ‖Bt‖ + ‖Tp‖ + ‖Lf‖ := by
        rw [norm_mul, Complex.norm_I, one_mul]
        linarith

end Formalism.ZeroFreeDirichlet
