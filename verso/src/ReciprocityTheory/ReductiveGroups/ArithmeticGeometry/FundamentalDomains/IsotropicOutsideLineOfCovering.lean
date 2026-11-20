import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicOutsideLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.UnipotentCoefficientShift
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IntegerApproximationCountHolds

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

/- English proof (translation)
Introduce `r X ξ hξ z0 hz0 x hxL hxξ _hxne hsmall`. Take `⟨hξΛ, hξξ, -⟩` from `hξ`. Take `⟨hzdom, hzD⟩` from `hz0`. Establish `hmaj_ne : ∀ τ : X.Ψ, X.maj z0 τ (Data.emb τ.1 ξ) ≠ 0` using `fun τ h => by`. Establish `h1` using `hzD τ`.

Rewrite `h1` using `[h, mul_zero]`. Conclude with `zero_ne_one h1`. Establish `hHne : ∀ τ : X.Ψ, X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) ≠ 0` using `fun τ => by`. Rewrite using `[X.Hf_self hzdom τ]`. Conclude with `hmaj_ne τ` after adjusting the coercions.

Establish `hu : ∀ (v : Fin r → E) (τ : X.Ψ), X.ucomp z0 ξ (X.embV v) τ = Data.emb τ.1 v - (X.Hf z0 τ (Data.emb τ.1 v) (Data.emb τ.1 ξ) / X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)) • Data.emb τ.1 ξ` using `fun v τ => rfl`. Establish `hxx : herm X.Gm x x = 0`. Apply `UnipotentCoefficientShift.eq_zero_of_conj_lt_one (X.L'_int x hxL x hxL)` to reduce the goal to its premises. Establish `hΨ : ∀ τ : X.Ψ, ‖τ.1 (herm X.Gm x x)‖ < 1`. Introduce `τ`.

Establish `h1 : hermC τ.1 X.Gm (Data.emb τ.1 x) (Data.emb τ.1 ξ) = 0`. Rewrite using `[hermC_emb, hxξ, map_zero]`. Establish `h2 : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 x) = 0`. Rewrite using `[← hermC_conj τ.1 X.Gm_herm, h1, map_zero]`. Establish `h3 : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0`.

Rewrite using `[hermC_emb, hξξ, map_zero]`. Establish `hww : hermC τ.1 X.Gm (X.ucomp z0 ξ (X.embV x) τ) (X.ucomp z0 ξ (X.embV x) τ) = τ.1 (herm X.Gm x x)`. Rewrite using `[hu x τ]`. Simplify using `only [hermC_sub_left, hermC_sub_right, hermC_smul_left, hermC_smul_right]`. Rewrite using `[h1, h2, h3, hermC_emb]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← hww]`. Conclude with `lt_of_le_of_lt (UnipotentCoefficientShift.norm_hermC_le_maj hzdom τ _) (hsmall τ)`. Introduce `σ`. Distinguish the cases in `hσ : σ ∈ X.Ψ`.

Conclude with `hΨ ⟨σ, hσ⟩`. Establish `hc : ComplexEmbedding.conjugate σ ∈ X.Ψ`. Establish `hcc : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ` using `RingHom.ext fun a => by simp`. Rewrite using `[X.cmType, hcc]`. Conclude with `hσ`.

Establish `h` using `hΨ ⟨_, hc⟩`. Simplify `h` using `[ComplexEmbedding.conjugate_coe_eq]`. Use `⟨hxx, ?_⟩` and prove the remaining obligations. Take `⟨α, hα⟩` from `(hD3 r X.toData).1 (fun τ => -(X.Hf z0 τ (Data.emb τ.1 x) (Data.emb τ.1 ξ) / X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)) / (X.NA : ℂ))`. Use `⟨α, ?_⟩` and prove the remaining obligations.

Introduce `x'`. Establish `hemb : ∀ τ : X.Ψ, Data.emb τ.1 x' = Data.emb τ.1 x + τ.1 ((X.NA : E) * α) • Data.emb τ.1 ξ`. Introduce `τ`. Use function extensionality and compare the values at `a`. Simplify using `[x', Data.emb]`.

Establish `hx'L : x' ∈ X.L'`. Apply `X.L'.add_mem hxL` to reduce the goal to its premises. Establish `h1 : (X.NA : E) • ξ ∈ X.L'` using `X.NA_sub ξ hξΛ`. Establish `h2` using `X.L'.smul_mem α h1`. Establish `h3 : α • ((X.NA : E) • ξ) = ((X.NA : E) * (α : E)) • ξ`.

Rewrite using `[← algebraMap_smul E α ((X.NA : E) • ξ), smul_smul]`. Use `congr 1`. Conclude with `mul_comm _ _`. Rewrite `h2` using `[h3]`. Then use the resulting hypothesis. Establish `hx'ξ : herm X.Gm x' ξ = 0`.

Simplify using `only [x']`. Rewrite using `[HermitianTraceFormVanishing.herm_add_left, HermitianTraceFormVanishing.herm_smul_left, hxξ, hξξ, mul_zero, add_zero]`. Establish `hucomp : X.ucomp z0 ξ (X.embV x') = X.ucomp z0 ξ (X.embV x)`. Use function extensionality and compare the values at `τ`. Rewrite using `[hu x' τ, hu x τ, hemb τ, UnipotentCoefficientShift.ucomp_shift _ _ _ _ _ (hHne τ)]`.

Establish `hcoef : ∀ τ : X.Ψ, ‖X.Hf z0 τ (Data.emb τ.1 x') (Data.emb τ.1 ξ) / X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)‖ ≤ 2 * (fdeg E : ℝ) ^ 2 * rdE E * X.NA`. Introduce `τ`. Rewrite using `[hemb τ, UnipotentCoefficientShift.coef_shift _ _ _ _ _ (hHne τ)]`. Establish `hNA : (X.NA : ℂ) ≠ 0` using `by exact_mod_cast X.NA_pos.ne'`. Use `set k := X.Hf z0 τ (Data.emb τ.1 x) (Data.emb τ.1 ξ) / X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) with hkdef`.

Establish `hk : (X.NA : ℂ) * (k / X.NA) = k` using `by field_simp`. Establish `e : k + τ.1 ((X.NA : E) * α) = (X.NA : ℂ) * (τ.1 (α : E) - -k / X.NA)`. Rewrite using `[map_mul, map_natCast]`. Take the linear combination `(-1 : ℂ) * hk`. Rewrite using `[e, norm_mul, Complex.norm_natCast]`.

Establish `hb : ‖τ.1 (α : E) - -k / X.NA‖ ≤ 2 * (fdeg E : ℝ) ^ 2 * rdE E` using `hα τ`. Combine the equalities or inequalities in the displayed calculation. Use `⟨hx'L, hx'ξ, hucomp, hcoef, ?_⟩` and prove the remaining obligations. Introduce `τ`. Establish `hembNC : Data.emb τ.1 ((X.NC : E) • x') = ((X.NC : ℝ) : ℂ) • Data.emb τ.1 x'`.

Use function extensionality and compare the values at `a`. Simplify using `[Data.emb]`. Rewrite using `[hembNC, UnipotentCoefficientShift.maj_smul hzdom, UnipotentCoefficientShift.maj_decomp hzdom τ _ _ (hHne τ)]`. Establish `hw : Data.emb τ.1 x' - (X.Hf z0 τ (Data.emb τ.1 x') (Data.emb τ.1 ξ) / X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)) • Data.emb τ.1 ξ = X.ucomp z0 ξ (X.embV x) τ`. Rewrite using `[← hucomp, hu x' τ]`.

Rewrite using `[hw]`. Establish `hK` using `hcoef τ`. Use `set K := ‖X.Hf z0 τ (Data.emb τ.1 x') (Data.emb τ.1 ξ) / X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)‖ with hKdef`. Use `set m := X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ) with hmdef`. Establish `hc2 : X.c τ ≤ 2`.

Unfold `Data.c`. Rewrite using `[X.ξ0_abs τ]`. Combine the linear relations using `[X.k0_le]`. Establish `hc0 : 0 ≤ X.c τ`. Unfold `Data.c`.

Check the signs of the components of the expression. Establish `hD` using `hzD τ`. Establish `hm : m < 1` using `hsmall τ`. Establish `hK0 : 0 ≤ K` using `norm_nonneg _`. Establish `h1 : X.c τ * m ≤ 2` using `by nlinarith`.

Establish `h2 : K ^ 2 ≤ 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 * (X.NA : ℝ) ^ 2`. Use polynomial arithmetic with `[mul_le_mul hK hK hK0 (le_trans hK0 hK)]`. Establish `h3 : X.c τ * (m + K ^ 2 * X.maj z0 τ (Data.emb τ.1 ξ)) = X.c τ * m + K ^ 2`. Take the linear combination `K ^ 2 * hD`. Establish `h4 : X.c τ * (m + K ^ 2 * X.maj z0 τ (Data.emb τ.1 ξ)) ≤ 2 + 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 * (X.NA : ℝ) ^ 2`.

Rewrite using `[h3]`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation.
-/
theorem isotropic_outside_line_of_covering (hD3 : IntegerApproximationCount (E := E)) : IsotropicOutsideLine (E := E) := by
  intro r X ξ hξ z0 hz0 x hxL hxξ _hxne hsmall
  obtain ⟨hξΛ, hξξ, -⟩ := hξ
  obtain ⟨hzdom, hzD⟩ := hz0
  have hmaj_ne : ∀ τ : X.Ψ, X.maj z0 τ (Data.emb τ.1 ξ) ≠ 0 := fun τ h => by
    have h1 := hzD τ
    rw [h, mul_zero] at h1
    exact zero_ne_one h1
  have hHne : ∀ τ : X.Ψ, X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) ≠ 0 := fun τ => by
    rw [X.Hf_self hzdom τ]
    exact_mod_cast hmaj_ne τ
  have hu : ∀ (v : Fin r → E) (τ : X.Ψ), X.ucomp z0 ξ (X.embV v) τ = Data.emb τ.1 v -
      (X.Hf z0 τ (Data.emb τ.1 v) (Data.emb τ.1 ξ) / X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)) •
        Data.emb τ.1 ξ := fun v τ => rfl
  have hxx : herm X.Gm x x = 0 := by
    apply UnipotentCoefficientShift.eq_zero_of_conj_lt_one (X.L'_int x hxL x hxL)
    have hΨ : ∀ τ : X.Ψ, ‖τ.1 (herm X.Gm x x)‖ < 1 := by
      intro τ
      have h1 : hermC τ.1 X.Gm (Data.emb τ.1 x) (Data.emb τ.1 ξ) = 0 := by
        rw [hermC_emb, hxξ, map_zero]
      have h2 : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 x) = 0 := by
        rw [← hermC_conj τ.1 X.Gm_herm, h1, map_zero]
      have h3 : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0 := by
        rw [hermC_emb, hξξ, map_zero]
      have hww : hermC τ.1 X.Gm (X.ucomp z0 ξ (X.embV x) τ) (X.ucomp z0 ξ (X.embV x) τ) =
          τ.1 (herm X.Gm x x) := by
        rw [hu x τ]
        simp only [hermC_sub_left, hermC_sub_right, hermC_smul_left, hermC_smul_right]
        rw [h1, h2, h3, hermC_emb]
        ring
      rw [← hww]
      exact lt_of_le_of_lt (UnipotentCoefficientShift.norm_hermC_le_maj hzdom τ _) (hsmall τ)
    intro σ
    by_cases hσ : σ ∈ X.Ψ
    · exact hΨ ⟨σ, hσ⟩
    · have hc : ComplexEmbedding.conjugate σ ∈ X.Ψ := by
        have hcc : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ :=
          RingHom.ext fun a => by simp
        rw [X.cmType, hcc]
        exact hσ
      have h := hΨ ⟨_, hc⟩
      simpa [ComplexEmbedding.conjugate_coe_eq] using h
  refine ⟨hxx, ?_⟩
  obtain ⟨α, hα⟩ := (hD3 r X.toData).1 (fun τ => -(X.Hf z0 τ (Data.emb τ.1 x) (Data.emb τ.1 ξ) /
    X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)) / (X.NA : ℂ))
  refine ⟨α, ?_⟩
  intro x'
  have hemb : ∀ τ : X.Ψ, Data.emb τ.1 x' =
      Data.emb τ.1 x + τ.1 ((X.NA : E) * α) • Data.emb τ.1 ξ := by
    intro τ
    funext a
    simp [x', Data.emb]
  have hx'L : x' ∈ X.L' := by
    apply X.L'.add_mem hxL
    have h1 : (X.NA : E) • ξ ∈ X.L' := X.NA_sub ξ hξΛ
    have h2 := X.L'.smul_mem α h1
    have h3 : α • ((X.NA : E) • ξ) = ((X.NA : E) * (α : E)) • ξ := by
      rw [← algebraMap_smul E α ((X.NA : E) • ξ), smul_smul]
      congr 1
      exact mul_comm _ _
    rwa [h3] at h2
  have hx'ξ : herm X.Gm x' ξ = 0 := by
    simp only [x']
    rw [HermitianTraceFormVanishing.herm_add_left, HermitianTraceFormVanishing.herm_smul_left, hxξ, hξξ, mul_zero, add_zero]
  have hucomp : X.ucomp z0 ξ (X.embV x') = X.ucomp z0 ξ (X.embV x) := by
    funext τ
    rw [hu x' τ, hu x τ, hemb τ, UnipotentCoefficientShift.ucomp_shift _ _ _ _ _ (hHne τ)]
  have hcoef : ∀ τ : X.Ψ, ‖X.Hf z0 τ (Data.emb τ.1 x') (Data.emb τ.1 ξ) /
      X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)‖ ≤ 2 * (fdeg E : ℝ) ^ 2 * rdE E * X.NA := by
    intro τ
    rw [hemb τ, UnipotentCoefficientShift.coef_shift _ _ _ _ _ (hHne τ)]
    have hNA : (X.NA : ℂ) ≠ 0 := by exact_mod_cast X.NA_pos.ne'
    set k := X.Hf z0 τ (Data.emb τ.1 x) (Data.emb τ.1 ξ) /
      X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) with hkdef
    have hk : (X.NA : ℂ) * (k / X.NA) = k := by field_simp
    have e : k + τ.1 ((X.NA : E) * α) = (X.NA : ℂ) * (τ.1 (α : E) - -k / X.NA) := by
      rw [map_mul, map_natCast]
      linear_combination (-1 : ℂ) * hk
    rw [e, norm_mul, Complex.norm_natCast]
    have hb : ‖τ.1 (α : E) - -k / X.NA‖ ≤ 2 * (fdeg E : ℝ) ^ 2 * rdE E := hα τ
    calc (X.NA : ℝ) * ‖τ.1 (α : E) - -k / X.NA‖ ≤ X.NA * (2 * (fdeg E : ℝ) ^ 2 * rdE E) :=
          mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
      _ = 2 * (fdeg E : ℝ) ^ 2 * rdE E * X.NA := by ring
  refine ⟨hx'L, hx'ξ, hucomp, hcoef, ?_⟩
  intro τ
  have hembNC : Data.emb τ.1 ((X.NC : E) • x') = ((X.NC : ℝ) : ℂ) • Data.emb τ.1 x' := by
    funext a
    simp [Data.emb]
  rw [hembNC, UnipotentCoefficientShift.maj_smul hzdom, UnipotentCoefficientShift.maj_decomp hzdom τ _ _ (hHne τ)]
  have hw : Data.emb τ.1 x' - (X.Hf z0 τ (Data.emb τ.1 x') (Data.emb τ.1 ξ) /
      X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)) • Data.emb τ.1 ξ =
        X.ucomp z0 ξ (X.embV x) τ := by
    rw [← hucomp, hu x' τ]
  rw [hw]
  have hK := hcoef τ
  set K := ‖X.Hf z0 τ (Data.emb τ.1 x') (Data.emb τ.1 ξ) /
    X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)‖ with hKdef
  set m := X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ) with hmdef
  have hc2 : X.c τ ≤ 2 := by
    unfold Data.c
    rw [X.ξ0_abs τ]
    linarith [X.k0_le]
  have hc0 : 0 ≤ X.c τ := by
    unfold Data.c
    positivity
  have hD := hzD τ
  have hm : m < 1 := hsmall τ
  have hK0 : 0 ≤ K := norm_nonneg _
  have h1 : X.c τ * m ≤ 2 := by nlinarith
  have h2 : K ^ 2 ≤ 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 * (X.NA : ℝ) ^ 2 := by
    nlinarith [mul_le_mul hK hK hK0 (le_trans hK0 hK)]
  have h3 : X.c τ * (m + K ^ 2 * X.maj z0 τ (Data.emb τ.1 ξ)) = X.c τ * m + K ^ 2 := by
    linear_combination K ^ 2 * hD
  have h4 : X.c τ * (m + K ^ 2 * X.maj z0 τ (Data.emb τ.1 ξ)) ≤
      2 + 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 * (X.NA : ℝ) ^ 2 := by
    rw [h3]
    linarith
  calc X.c τ * ((X.NC : ℝ) ^ 2 * (m + K ^ 2 * X.maj z0 τ (Data.emb τ.1 ξ)))
      = (X.NC : ℝ) ^ 2 * (X.c τ * (m + K ^ 2 * X.maj z0 τ (Data.emb τ.1 ξ))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h4 (by positivity)

/- English proof (translation)
The claim follows from `isotropic_outside_line_of_covering integerApproximationCount_holds`.
-/
theorem isotropic_outside_line : IsotropicOutsideLine (E := E) := isotropic_outside_line_of_covering integerApproximationCount_holds

end ReciprocityTheory.ChartRestriction.G.FD
