import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicOutsideLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.QuadraticOffDiagonalBounds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IntegerApproximationCountHolds

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate ComplexOrder

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

/- English proof (translation)
Introduce `r X la P ξ ν c1 w z0 x a hS hHmax t ht K2 S`. Take `⟨hHyp, hxL, hxξ, hxx, hxne, hw0, hua⟩` from `hS`. Take `⟨-, hPSS, hξ, hc1, hνsum, -, -, -, hchar, hz0, -⟩` from `hHyp`. Take `⟨hξΛ, hξξ, hξ0⟩` from `hξ`. Take `⟨hzdom, hzD⟩` from `hz0`.

Establish `hNC : (X.NC : E) ≠ 0` using `by exact_mod_cast X.NC_pos.ne'`. Establish `hξx : herm X.Gm ξ x = 0`. Rewrite using `[← HermitianTraceFormVanishing.herm_conj X.Gm X.Gm_herm x ξ, hxξ]`. Simplify using the standard rewrite rules. Establish `hIso : IsIsoPair X.Gm ![ξ, (X.NC : E) • x]`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `intro i k fin_cases i <;> fin_cases k <;>`. Simplify using `[HermitianTraceFormVanishing.herm_smul_left, HermitianTraceFormVanishing.herm_smul_right, hξξ, hxξ, hξx, hxx]`. Rewrite using `[LinearIndependent.pair_iff]`. Introduce `s s' hst`.

Distinguish the cases in `hs0 : s' = 0`. Substitute `hs0` using the available equality. Use `⟨?_, rfl⟩` and prove the remaining obligations. Simplify `hst` using `[hξ0]`. It suffices to derive a contradiction.

Establish `hsn : s' * (X.NC : E) ≠ 0` using `mul_ne_zero hs0 hNC`. Apply `hxne (-(s / (s' * (X.NC : E))))` to reduce the goal to its premises. Establish `h' : (s' * (X.NC : E)) • x = -(s • ξ)`. Rewrite using `[mul_smul]`. Conclude with `eq_neg_of_add_eq_zero_right hst`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[smul_smul, inv_mul_cancel₀ hsn, one_smul]`. Use `_ = -(s / (s' * (X.NC : E))) • ξ := by`. Rewrite using `[h', smul_neg, smul_smul, neg_smul, div_eq_inv_mul]`. Establish `hΛ : ∀ i, (![ξ, (X.NC : E) • x] : Fin 2 → Fin r → E) i ∈ X.Λ`.

Introduce `i`. Use `fin_cases i`. Simplify using `using hξΛ`. Simplify using `using X.NC_sub x hxL`. Establish `hmem : ∀ χ ∈ S, IsHermFam χ ∧ X.IsFreqZ X.g χ ∧ (∀ τ, χ τ 0 0 = (ν τ : ℂ)) ∧ (∀ τ, (Matrix.of (χ τ)).PosSemidef)`.

Introduce `χ hχ`. Take `⟨⟨y, hy, hfz⟩, -⟩` from `hχ`. Establish `hHF : IsHermFam χ ∧ X.IsFreqZ X.g χ`. Assume the negation of the conclusion as `hn`. Apply `hfz` to reduce the goal to its premises.

Unfold `Data.fz`. Rewrite using `[if_neg hn]`. Establish `e` using `h3d r X ![ξ, (X.NC : E) • x] hIso hΛ la P hPSS.1.1 hchar ν χ y hy`. Distinguish the cases in `hν : ∀ τ, χ τ 0 0 = (ν τ : ℂ)`. Rewrite `e` using `[if_pos hν]`.

Establish `hP : X.fz ![ξ, (X.NC : E) • x] X.g χ P y ≠ 0` using `fun h0 => hfz (e.trans h0)`. Conclude with `⟨hHF.1, hHF.2, hν, fun τ => (h5 r X _ hIso hΛ la P hPSS hchar χ ⟨y, hy, hP⟩ τ).posSemidef⟩`. It suffices to derive a contradiction. Rewrite `e` using `[if_neg hν]`. Conclude with `hfz e`.

Establish `hHne : ∀ τ : X.Ψ, X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) ≠ 0` using `fun τ h => by`. Establish `h1` using `hzD τ`. Rewrite `h` using `[X.Hf_self hzdom τ]`. Rewrite `h1` using `[Complex.ofReal_eq_zero.mp h, mul_zero]`. Conclude with `zero_ne_one h1`.

Establish `hcoord : ∀ τ : X.Ψ, ∃ p q : ℂ, q * a τ 0 + p = 0 ∧ q * a τ 1 = 1 ∧ ‖p‖ ^ 2 + ‖q‖ ^ 2 ≤ (X.NC : ℝ) ^ 2 * (2 + 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 * (X.NA : ℝ) ^ 2)`. Introduce `τ`. Establish `hcpos : 0 < X.c τ`. Unfold `Data.c`. Rewrite using `[X.ξ0_abs τ]`.

Combine the linear relations using `[X.minWeight_pos]`. Establish `hmw : 0 < X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ)` using `X.maj_pos hzdom τ (hw0 τ)`. Establish `hc0 : X.c τ ≠ 0` using `hcpos.ne'`. Establish `hm0 : X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ) ≠ 0` using `hmw.ne'`. Establish `hs : Real.sqrt (X.c τ * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ)) ^ 2 = X.c τ * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ)` using `Real.sq_sqrt (mul_pos hcpos hmw).le`.

Establish `hcast : ((Real.sqrt (X.c τ * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ)))⁻¹ : ℂ) = (((Real.sqrt (X.c τ * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ)))⁻¹ : ℝ) : ℂ)`. Simplify using the standard rewrite rules. Establish `hua' : X.uvec ![ξ, (X.NC : E) • x] a τ = (((Real.sqrt (X.c τ * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ)))⁻¹ : ℝ) : ℂ) • X.ucomp z0 ξ (X.embV x) τ`. Rewrite using `[hua τ, hcast]`. Establish `he : X.uvec ![ξ, (X.NC : E) • x] a τ = a τ 0 • Data.emb τ.1 ξ + a τ 1 • Data.emb τ.1 ((X.NC : E) • x)`.

Simplify using `[Data.uvec, Fin.sum_univ_two]`. Establish `h1 : X.c τ * (X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)).re = 1`. Rewrite using `[X.Hf_self hzdom, Complex.ofReal_re]`. Conclude with `hzD τ`. Establish `hwf : X.Hf z0 τ (X.ucomp z0 ξ (X.embV x) τ) (Data.emb τ.1 ξ) = 0` using `by show X.Hf z0 τ (Data.emb τ.1 x - (X.Hf z0 τ (Data.emb τ.1 x) (Data.emb τ.1 ξ) / X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)) • Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0`.

Rewrite using `[UnipotentCoefficientShift.Hf_sub_left, UnipotentCoefficientShift.Hf_smul_left, div_mul_cancel₀ _ (hHne τ), sub_self]`. Establish `h2e : X.Hf z0 τ (X.uvec ![ξ, (X.NC : E) • x] a τ) (Data.emb τ.1 ξ) = 0`. Rewrite using `[hua', UnipotentCoefficientShift.Hf_smul_left, hwf, mul_zero]`. Establish `h3 : X.c τ * (X.Hf z0 τ (X.uvec ![ξ, (X.NC : E) • x] a τ) (X.uvec ![ξ, (X.NC : E) • x] a τ)).re = 1`. Rewrite using `[hua', X.Hf_self hzdom, Complex.ofReal_re, UnipotentCoefficientShift.maj_smul hzdom, inv_pow, hs]`.

Clear the denominators using the available nonvanishing facts. Take `⟨p, q, hp1, hp2, hpq⟩` from `QuadraticOffDiagonalBounds.coord hzdom τ _ _ _ (a τ 0) (a τ 1) (X.c τ) he h1 h2e h3`. Use `⟨p, q, hp1, hp2, ?_⟩` and prove the remaining obligations. Rewrite using `[hpq, X.Hf_self hzdom, Complex.ofReal_re]`. Conclude with `hHmax τ`.

Use `set Hm : ℝ := (X.NC : ℝ) ^ 2 * (2 + 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 * (X.NA : ℝ) ^ 2) with hHm`. Establish `hHm1 : 1 ≤ Hm`. Establish `h1 : (1 : ℝ) ≤ X.NC` using `by exact_mod_cast X.NC_pos`. Establish `h2 : 0 ≤ 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 * (X.NA : ℝ) ^ 2` using `by positivity`. Rewrite using `[hHm]`.

Use the polynomial consequences of the given equalities and inequalities. Use `set B : ℝ := Hm * (c1 + t / 2) with hB`. Establish `hB0 : 0 ≤ B` using `mul_nonneg (by linarith) (by linarith)`. Establish `hent : ∀ χ ∈ S, ∀ τ : X.Ψ, ‖χ τ 0 1‖ ≤ B ∧ ‖χ τ 1 1‖ ≤ B`. Introduce `χ hχ τ`.

Take `⟨hH, -, hν, hpsd⟩` from `hmem χ hχ`. Establish `hχt : 2 * ∑ τ, (X.chiAt χ a τ).re ≤ t` using `hχ.2`. Establish `q00 : ∀ τ', (∑ i, ∑ k, χ τ' i k * (![1, 0] : Fin 2 → ℂ) i * conj ((![1, 0] : Fin 2 → ℂ) k)) = χ τ' 0 0`. Introduce `τ'`. Simplify using `[Fin.sum_univ_two]`.

Establish `q11 : (∑ i, ∑ k, χ τ i k * (![0, 1] : Fin 2 → ℂ) i * conj ((![0, 1] : Fin 2 → ℂ) k)) = χ τ 1 1`. Simplify using `[Fin.sum_univ_two]`. Establish `hνnn : ∀ τ', 0 ≤ ν τ'`. Introduce `τ'`. Establish `h` using `QuadraticOffDiagonalBounds.quad_nonneg (hpsd τ') ![1, 0]`.

Rewrite `h` using `[q00, hν τ', Complex.ofReal_re]`. Conclude with `h`. Establish `hchinn : ∀ τ', 0 ≤ (X.chiAt χ a τ').re` using `fun τ' => QuadraticOffDiagonalBounds.quad_nonneg (hpsd τ') (a τ')`. Establish `hντ : ν τ ≤ c1` using `le_trans (Finset.single_le_sum (fun τ' _ => hνnn τ') (Finset.mem_univ τ)) hνsum`. Establish `hchτ : (X.chiAt χ a τ).re ≤ t / 2`.

Use `Finset.single_le_sum (fun τ' _ => hchinn τ') (Finset.mem_univ τ)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨p, q, hp1, hp2, hpq⟩` from `hcoord τ`. Establish `hvec : q • a τ + p • (![1, 0] : Fin 2 → ℂ) = ![0, 1]`. Use function extensionality and compare the values at `i`.

Use `fin_cases i`. Simplify using the standard rewrite rules. Take the linear combination `hp1`. Simplify using the standard rewrite rules. Take the linear combination `hp2`.

Establish `hc` using `QuadraticOffDiagonalBounds.quad_comb (hpsd τ) q p (a τ) ![1, 0]`. Rewrite `hc` using `[hvec, q11, q00 τ, hν τ, Complex.ofReal_re]`. Establish `hchi : (∑ i, ∑ k, χ τ i k * a τ i * conj (a τ k)).re = (X.chiAt χ a τ).re` using `rfl`. Rewrite `hc` using `[hchi]`. Establish `hre11 : (χ τ 1 1).re ≤ B`.

Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul (by linarith) (by linarith) (by linarith [hchinn τ, hνnn τ]) (by linarith)` to reduce the goal to its premises. Establish `hnn11 : 0 ≤ (χ τ 1 1).re`. Establish `h` using `QuadraticOffDiagonalBounds.quad_nonneg (hpsd τ) ![0, 1]`. Rewrite `h` using `[q11]`. Then use the resulting hypothesis.

Establish `hreal11 : χ τ 1 1 = ((χ τ 1 1).re : ℂ)` using `(Complex.conj_eq_iff_re.mp (hH τ 1 1).symm).symm`. Establish `hn11 : ‖χ τ 1 1‖ ≤ B`. Rewrite using `[hreal11, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn11]`. Conclude with `hre11`. Establish `hoff` using `QuadraticOffDiagonalBounds.offdiag_le (hpsd τ) (hH τ 0 1)`.

Rewrite `hoff` using `[hν τ, Complex.ofReal_re]`. Establish `hcB : c1 ≤ B`. Establish `: c1 + t / 2 ≤ Hm * (c1 + t / 2)` using `by nlinarith`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `⟨by linarith, hn11⟩`.

Establish `hdisc : 0 < dEnat E` using `Int.natAbs_pos.mpr (NumberField.discr_ne_zero E)`. Take `⟨N0, hN0⟩ : ∃ n : ℕ, n = X.g * dEnat E ^ 2` from `⟨_, rfl⟩`. Establish `hN0E : (N0 : E) ≠ 0`. Rewrite using `[hN0]`. Conclude with `(Nat.mul_pos X.g_pos (pow_pos hdisc 2)).ne'` after adjusting the coercions.

Establish `hN0r : (N0 : ℝ) = X.g * dE E ^ 2`. Simplify using `only [hN0, dEnat, dE, Nat.cast_mul, Nat.cast_pow, Nat.cast_natAbs, Int.cast_abs]`. Establish `hβ : ∀ χ ∈ S, ∃ β : Matrix (Fin 2) (Fin 2) E, (∀ i k, cc (β i k) = β k i) ∧ χ = X.embH β ∧ ∀ i k, IsIntegral ℤ ((N0 : E) * β i k)`. Introduce `χ hχ`. Take `⟨hH, hF, -, -⟩` from `hmem χ hχ`.

Take `⟨β, hβ1, hβ2, hβ3⟩` from `(h2 r X _ hIso hΛ).2.2 χ hH hF`. Conclude with `⟨β, hβ1, hβ2, fun i k => by rw [hN0]; exact hβ3 i k⟩`. Use `choose! β hβh hβe hβi using hβ`. Establish `hent' : ∀ χ ∈ S, ∀ (τ : X.Ψ) (i k : Fin 2), χ τ i k = τ.1 (β χ i k)` using `fun χ hχ τ i k => congrFun (congrFun (congrFun (hβe χ hχ) τ) i) k`. Establish `hσ : ∀ χ ∈ S, ∀ i k : Fin 2, (∀ τ : X.Ψ, ‖χ τ i k‖ ≤ B) → ∀ σ : E →+* ℂ, ‖σ ((N0 : E) * β χ i k)‖ ≤ (N0 : ℝ) * B`.

Introduce `χ hχ i k hb σ`. Rewrite using `[map_mul, map_natCast, norm_mul, Complex.norm_natCast]`. Apply `mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)` to reduce the goal to its premises. Distinguish the cases in `hs : σ ∈ X.Ψ`. Establish `h` using `hb ⟨σ, hs⟩`.

Rewrite `h` using `[hent' χ hχ]`. Conclude with `h`. Establish `hcc : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ` using `RingHom.ext fun a => by simp`. Establish `hc : ComplexEmbedding.conjugate σ ∈ X.Ψ`. Rewrite using `[X.cmType, hcc]`.

Conclude with `hs`. Establish `h` using `hb ⟨_, hc⟩`. Rewrite `h` using `[hent' χ hχ]`. Simplify `h` using `[ComplexEmbedding.conjugate_coe_eq]`. Take `⟨hAfin, hAcard⟩` from `(hD3 r X.toData).2 ((N0 : ℝ) * B) (mul_nonneg (Nat.cast_nonneg _) hB0)`.

Use `set A := {α : 𝓞 E | ∀ σ : E →+* ℂ, ‖σ (α : E)‖ ≤ (N0 : ℝ) * B} with hA`. Set `φ : (X.Ψ → Fin 2 → Fin 2 → ℂ) → E × E` to `fun χ => ((N0 : E) * β χ 0 1, (N0 : E) * β χ 1 1)`. Establish `hmaps : ∀ χ ∈ S, φ χ ∈ (Subtype.val '' A) ×ˢ (Subtype.val '' A)`. Introduce `χ hχ`. Conclude with `⟨⟨⟨(N0 : E) * β χ 0 1, hβi χ hχ 0 1⟩, hσ χ hχ 0 1 (fun τ => (hent χ hχ τ).1), rfl⟩, ⟨⟨(N0 : E) * β χ 1 1, hβi χ hχ 1 1⟩, hσ χ hχ 1 1 (fun τ => (hent χ hχ τ).2), rfl⟩⟩`.

Establish `hinj : Set.InjOn φ S`. Introduce `χ hχ χ' hχ' hφ`. Take `⟨h01', h11'⟩` from `Prod.mk.inj (hφ : ((N0 : E) * β χ 0 1, (N0 : E) * β χ 1 1) = ((N0 : E) * β χ' 0 1, (N0 : E) * β χ' 1 1))`. Establish `h01 : β χ 0 1 = β χ' 0 1` using `mul_left_cancel₀ hN0E h01'`. Establish `h11 : β χ 1 1 = β χ' 1 1` using `mul_left_cancel₀ hN0E h11'`.

Take `⟨hH, -, hν, -⟩` from `hmem χ hχ`. Take `⟨hH', -, hν', -⟩` from `hmem χ' hχ'`. Establish `e01 : ∀ τ, χ τ 0 1 = χ' τ 0 1` using `fun τ => by`. Rewrite using `[hent' χ hχ, hent' χ' hχ', h01]`. Establish `e11 : ∀ τ, χ τ 1 1 = χ' τ 1 1` using `fun τ => by`.

Rewrite using `[hent' χ hχ, hent' χ' hχ', h11]`. Use function extensionality and compare the values at `τ i k`. Apply the tactic sequence `fin_cases i <;> fin_cases k`. Conclude with `(hν τ).trans (hν' τ).symm`. Conclude with `e01 τ`.

Conclude with `(hH τ 0 1).trans ((congrArg conj (e01 τ)).trans (hH' τ 0 1).symm)`. Conclude with `e11 τ`. Establish `hTfin : ((Subtype.val '' A) ×ˢ (Subtype.val '' A)).Finite` using `(hAfin.image _).prod (hAfin.image _)`. Establish `hSfin : S.Finite` using `Set.Finite.of_finite_image (hTfin.subset (by rintro _ ⟨χ, hχ, rfl⟩; exact hmaps χ hχ)) hinj`. Establish `hcard` using `Set.ncard_le_ncard_of_injOn φ hmaps hinj hTfin`.

Rewrite `hcard` using `[Set.ncard_prod]`. Establish `himA : (Subtype.val '' A).ncard ≤ A.ncard` using `Set.ncard_image_le hAfin`. Establish `hcard' : S.ncard ≤ A.ncard * A.ncard` using `hcard.trans (Nat.mul_le_mul himA himA)`. Use `⟨hSfin, ?_⟩` and prove the remaining obligations. Establish `hR0 : 0 ≤ (N0 : ℝ) * B` using `mul_nonneg (Nat.cast_nonneg _) hB0`.

Establish `hNH : 0 ≤ (N0 : ℝ) * Hm` using `mul_nonneg (Nat.cast_nonneg _) (by linarith)`. Establish `hR1 : 1 + 2 * ((N0 : ℝ) * B) ≤ K2 * t`. Simplify using `only [K2, ← hHm]`. Rewrite using `[← hN0r, hB]`. Use polynomial arithmetic with `[mul_nonneg (mul_nonneg hNH hc1.le) (sub_nonneg.mpr ht)]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← pow_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ (K2 * t) ^ (4 * fdeg E) := pow_le_pow_left₀ (by linarith) hR1 _`.
-/
theorem coefficient_height_bound_of (h2 : UnipotentLatticeLift (E := E)) (h3d : FourierCoefficientSupport (E := E))
    (h5 : NonvanishingCoefficientPositivity (E := E)) (hD3 : IntegerApproximationCount (E := E)) : CoefficientHeightBound (E := E) := by
  intro r X la P ξ ν c1 w z0 x a hS hHmax t ht K2 S
  classical
  obtain ⟨hHyp, hxL, hxξ, hxx, hxne, hw0, hua⟩ := hS
  obtain ⟨-, hPSS, hξ, hc1, hνsum, -, -, -, hchar, hz0, -⟩ := hHyp
  obtain ⟨hξΛ, hξξ, hξ0⟩ := hξ
  obtain ⟨hzdom, hzD⟩ := hz0
  have hNC : (X.NC : E) ≠ 0 := by exact_mod_cast X.NC_pos.ne'
  have hξx : herm X.Gm ξ x = 0 := by
    rw [← HermitianTraceFormVanishing.herm_conj X.Gm X.Gm_herm x ξ, hxξ]
    simp
  have hIso : IsIsoPair X.Gm ![ξ, (X.NC : E) • x] := by
    refine ⟨?_, ?_⟩
    · intro i k
      fin_cases i <;> fin_cases k <;>
        simp [HermitianTraceFormVanishing.herm_smul_left, HermitianTraceFormVanishing.herm_smul_right, hξξ, hxξ, hξx, hxx]
    · rw [LinearIndependent.pair_iff]
      intro s s' hst
      by_cases hs0 : s' = 0
      · subst hs0
        refine ⟨?_, rfl⟩
        simpa [hξ0] using hst
      · exfalso
        have hsn : s' * (X.NC : E) ≠ 0 := mul_ne_zero hs0 hNC
        apply hxne (-(s / (s' * (X.NC : E))))
        have h' : (s' * (X.NC : E)) • x = -(s • ξ) := by
          rw [mul_smul]
          exact eq_neg_of_add_eq_zero_right hst
        calc x = (s' * (X.NC : E))⁻¹ • ((s' * (X.NC : E)) • x) := by
              rw [smul_smul, inv_mul_cancel₀ hsn, one_smul]
          _ = -(s / (s' * (X.NC : E))) • ξ := by
              rw [h', smul_neg, smul_smul, neg_smul, div_eq_inv_mul]
  have hΛ : ∀ i, (![ξ, (X.NC : E) • x] : Fin 2 → Fin r → E) i ∈ X.Λ := by
    intro i
    fin_cases i
    · simpa using hξΛ
    · simpa using X.NC_sub x hxL

  have hmem : ∀ χ ∈ S, IsHermFam χ ∧ X.IsFreqZ X.g χ ∧ (∀ τ, χ τ 0 0 = (ν τ : ℂ)) ∧
      (∀ τ, (Matrix.of (χ τ)).PosSemidef) := by
    intro χ hχ
    obtain ⟨⟨y, hy, hfz⟩, -⟩ := hχ
    have hHF : IsHermFam χ ∧ X.IsFreqZ X.g χ := by
      by_contra hn
      apply hfz
      unfold Data.fz
      rw [if_neg hn]
    have e := h3d r X ![ξ, (X.NC : E) • x] hIso hΛ la P hPSS.1.1 hchar ν χ y hy
    by_cases hν : ∀ τ, χ τ 0 0 = (ν τ : ℂ)
    · rw [if_pos hν] at e
      have hP : X.fz ![ξ, (X.NC : E) • x] X.g χ P y ≠ 0 := fun h0 => hfz (e.trans h0)
      exact ⟨hHF.1, hHF.2, hν,
        fun τ => (h5 r X _ hIso hΛ la P hPSS hchar χ ⟨y, hy, hP⟩ τ).posSemidef⟩
    · exfalso
      rw [if_neg hν] at e
      exact hfz e

  have hHne : ∀ τ : X.Ψ, X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) ≠ 0 := fun τ h => by
    have h1 := hzD τ
    rw [X.Hf_self hzdom τ] at h
    rw [Complex.ofReal_eq_zero.mp h, mul_zero] at h1
    exact zero_ne_one h1
  have hcoord : ∀ τ : X.Ψ, ∃ p q : ℂ, q * a τ 0 + p = 0 ∧ q * a τ 1 = 1 ∧
      ‖p‖ ^ 2 + ‖q‖ ^ 2 ≤ (X.NC : ℝ) ^ 2 * (2 + 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 * (X.NA : ℝ) ^ 2) := by
    intro τ
    have hcpos : 0 < X.c τ := by
      unfold Data.c
      rw [X.ξ0_abs τ]
      linarith [X.minWeight_pos]
    have hmw : 0 < X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ) := X.maj_pos hzdom τ (hw0 τ)
    have hc0 : X.c τ ≠ 0 := hcpos.ne'
    have hm0 : X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ) ≠ 0 := hmw.ne'
    have hs : Real.sqrt (X.c τ * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ)) ^ 2 =
        X.c τ * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ) := Real.sq_sqrt (mul_pos hcpos hmw).le
    have hcast : ((Real.sqrt (X.c τ * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ)))⁻¹ : ℂ) =
        (((Real.sqrt (X.c τ * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ)))⁻¹ : ℝ) : ℂ) := by
      simp
    have hua' : X.uvec ![ξ, (X.NC : E) • x] a τ =
        (((Real.sqrt (X.c τ * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ)))⁻¹ : ℝ) : ℂ) •
          X.ucomp z0 ξ (X.embV x) τ := by
      rw [hua τ, hcast]
    have he : X.uvec ![ξ, (X.NC : E) • x] a τ =
        a τ 0 • Data.emb τ.1 ξ + a τ 1 • Data.emb τ.1 ((X.NC : E) • x) := by
      simp [Data.uvec, Fin.sum_univ_two]
    have h1 : X.c τ * (X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)).re = 1 := by
      rw [X.Hf_self hzdom, Complex.ofReal_re]
      exact hzD τ
    have hwf : X.Hf z0 τ (X.ucomp z0 ξ (X.embV x) τ) (Data.emb τ.1 ξ) = 0 := by
      show X.Hf z0 τ (Data.emb τ.1 x - (X.Hf z0 τ (Data.emb τ.1 x) (Data.emb τ.1 ξ) /
        X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)) • Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0
      rw [UnipotentCoefficientShift.Hf_sub_left, UnipotentCoefficientShift.Hf_smul_left, div_mul_cancel₀ _ (hHne τ), sub_self]
    have h2e : X.Hf z0 τ (X.uvec ![ξ, (X.NC : E) • x] a τ) (Data.emb τ.1 ξ) = 0 := by
      rw [hua', UnipotentCoefficientShift.Hf_smul_left, hwf, mul_zero]
    have h3 : X.c τ * (X.Hf z0 τ (X.uvec ![ξ, (X.NC : E) • x] a τ)
        (X.uvec ![ξ, (X.NC : E) • x] a τ)).re = 1 := by
      rw [hua', X.Hf_self hzdom, Complex.ofReal_re, UnipotentCoefficientShift.maj_smul hzdom, inv_pow, hs]
      field_simp
    obtain ⟨p, q, hp1, hp2, hpq⟩ :=
      QuadraticOffDiagonalBounds.coord hzdom τ _ _ _ (a τ 0) (a τ 1) (X.c τ) he h1 h2e h3
    refine ⟨p, q, hp1, hp2, ?_⟩
    rw [hpq, X.Hf_self hzdom, Complex.ofReal_re]
    exact hHmax τ

  set Hm : ℝ := (X.NC : ℝ) ^ 2 * (2 + 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 * (X.NA : ℝ) ^ 2) with hHm
  have hHm1 : 1 ≤ Hm := by
    have h1 : (1 : ℝ) ≤ X.NC := by exact_mod_cast X.NC_pos
    have h2 : 0 ≤ 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 * (X.NA : ℝ) ^ 2 := by positivity
    rw [hHm]
    nlinarith
  set B : ℝ := Hm * (c1 + t / 2) with hB
  have hB0 : 0 ≤ B := mul_nonneg (by linarith) (by linarith)
  have hent : ∀ χ ∈ S, ∀ τ : X.Ψ, ‖χ τ 0 1‖ ≤ B ∧ ‖χ τ 1 1‖ ≤ B := by
    intro χ hχ τ
    obtain ⟨hH, -, hν, hpsd⟩ := hmem χ hχ
    have hχt : 2 * ∑ τ, (X.chiAt χ a τ).re ≤ t := hχ.2
    have q00 : ∀ τ', (∑ i, ∑ k, χ τ' i k * (![1, 0] : Fin 2 → ℂ) i *
        conj ((![1, 0] : Fin 2 → ℂ) k)) = χ τ' 0 0 := by
      intro τ'
      simp [Fin.sum_univ_two]
    have q11 : (∑ i, ∑ k, χ τ i k * (![0, 1] : Fin 2 → ℂ) i * conj ((![0, 1] : Fin 2 → ℂ) k)) =
        χ τ 1 1 := by
      simp [Fin.sum_univ_two]
    have hνnn : ∀ τ', 0 ≤ ν τ' := by
      intro τ'
      have h := QuadraticOffDiagonalBounds.quad_nonneg (hpsd τ') ![1, 0]
      rw [q00, hν τ', Complex.ofReal_re] at h
      exact h
    have hchinn : ∀ τ', 0 ≤ (X.chiAt χ a τ').re := fun τ' => QuadraticOffDiagonalBounds.quad_nonneg (hpsd τ') (a τ')
    have hντ : ν τ ≤ c1 :=
      le_trans (Finset.single_le_sum (fun τ' _ => hνnn τ') (Finset.mem_univ τ)) hνsum
    have hchτ : (X.chiAt χ a τ).re ≤ t / 2 := by
      have := Finset.single_le_sum (fun τ' _ => hchinn τ') (Finset.mem_univ τ)
      linarith
    obtain ⟨p, q, hp1, hp2, hpq⟩ := hcoord τ
    have hvec : q • a τ + p • (![1, 0] : Fin 2 → ℂ) = ![0, 1] := by
      funext i
      fin_cases i
      · simp
        linear_combination hp1
      · simp
        linear_combination hp2
    have hc := QuadraticOffDiagonalBounds.quad_comb (hpsd τ) q p (a τ) ![1, 0]
    rw [hvec, q11, q00 τ, hν τ, Complex.ofReal_re] at hc
    have hchi : (∑ i, ∑ k, χ τ i k * a τ i * conj (a τ k)).re = (X.chiAt χ a τ).re := rfl
    rw [hchi] at hc
    have hre11 : (χ τ 1 1).re ≤ B := by
      calc (χ τ 1 1).re ≤ (‖q‖ ^ 2 + ‖p‖ ^ 2) * ((X.chiAt χ a τ).re + ν τ) := hc
        _ ≤ Hm * (c1 + t / 2) := by
            apply mul_le_mul (by linarith) (by linarith) (by linarith [hchinn τ, hνnn τ])
              (by linarith)
    have hnn11 : 0 ≤ (χ τ 1 1).re := by
      have h := QuadraticOffDiagonalBounds.quad_nonneg (hpsd τ) ![0, 1]
      rwa [q11] at h
    have hreal11 : χ τ 1 1 = ((χ τ 1 1).re : ℂ) :=
      (Complex.conj_eq_iff_re.mp (hH τ 1 1).symm).symm
    have hn11 : ‖χ τ 1 1‖ ≤ B := by
      rw [hreal11, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn11]
      exact hre11
    have hoff := QuadraticOffDiagonalBounds.offdiag_le (hpsd τ) (hH τ 0 1)
    rw [hν τ, Complex.ofReal_re] at hoff
    have hcB : c1 ≤ B := by
      have : c1 + t / 2 ≤ Hm * (c1 + t / 2) := by nlinarith
      linarith
    exact ⟨by linarith, hn11⟩

  have hdisc : 0 < dEnat E := Int.natAbs_pos.mpr (NumberField.discr_ne_zero E)
  obtain ⟨N0, hN0⟩ : ∃ n : ℕ, n = X.g * dEnat E ^ 2 := ⟨_, rfl⟩
  have hN0E : (N0 : E) ≠ 0 := by
    rw [hN0]
    exact_mod_cast (Nat.mul_pos X.g_pos (pow_pos hdisc 2)).ne'
  have hN0r : (N0 : ℝ) = X.g * dE E ^ 2 := by
    simp only [hN0, dEnat, dE, Nat.cast_mul, Nat.cast_pow, Nat.cast_natAbs, Int.cast_abs]
  have hβ : ∀ χ ∈ S, ∃ β : Matrix (Fin 2) (Fin 2) E, (∀ i k, cc (β i k) = β k i) ∧
      χ = X.embH β ∧ ∀ i k, IsIntegral ℤ ((N0 : E) * β i k) := by
    intro χ hχ
    obtain ⟨hH, hF, -, -⟩ := hmem χ hχ
    obtain ⟨β, hβ1, hβ2, hβ3⟩ := (h2 r X _ hIso hΛ).2.2 χ hH hF
    exact ⟨β, hβ1, hβ2, fun i k => by rw [hN0]; exact hβ3 i k⟩
  choose! β hβh hβe hβi using hβ
  have hent' : ∀ χ ∈ S, ∀ (τ : X.Ψ) (i k : Fin 2), χ τ i k = τ.1 (β χ i k) := fun χ hχ τ i k =>
    congrFun (congrFun (congrFun (hβe χ hχ) τ) i) k
  have hσ : ∀ χ ∈ S, ∀ i k : Fin 2, (∀ τ : X.Ψ, ‖χ τ i k‖ ≤ B) →
      ∀ σ : E →+* ℂ, ‖σ ((N0 : E) * β χ i k)‖ ≤ (N0 : ℝ) * B := by
    intro χ hχ i k hb σ
    rw [map_mul, map_natCast, norm_mul, Complex.norm_natCast]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    by_cases hs : σ ∈ X.Ψ
    · have h := hb ⟨σ, hs⟩
      rw [hent' χ hχ] at h
      exact h
    · have hcc : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ :=
        RingHom.ext fun a => by simp
      have hc : ComplexEmbedding.conjugate σ ∈ X.Ψ := by
        rw [X.cmType, hcc]
        exact hs
      have h := hb ⟨_, hc⟩
      rw [hent' χ hχ] at h
      simpa [ComplexEmbedding.conjugate_coe_eq] using h
  obtain ⟨hAfin, hAcard⟩ := (hD3 r X.toData).2 ((N0 : ℝ) * B) (mul_nonneg (Nat.cast_nonneg _) hB0)
  set A := {α : 𝓞 E | ∀ σ : E →+* ℂ, ‖σ (α : E)‖ ≤ (N0 : ℝ) * B} with hA
  let φ : (X.Ψ → Fin 2 → Fin 2 → ℂ) → E × E := fun χ => ((N0 : E) * β χ 0 1, (N0 : E) * β χ 1 1)
  have hmaps : ∀ χ ∈ S, φ χ ∈ (Subtype.val '' A) ×ˢ (Subtype.val '' A) := by
    intro χ hχ
    exact ⟨⟨⟨(N0 : E) * β χ 0 1, hβi χ hχ 0 1⟩, hσ χ hχ 0 1 (fun τ => (hent χ hχ τ).1), rfl⟩,
      ⟨⟨(N0 : E) * β χ 1 1, hβi χ hχ 1 1⟩, hσ χ hχ 1 1 (fun τ => (hent χ hχ τ).2), rfl⟩⟩
  have hinj : Set.InjOn φ S := by
    intro χ hχ χ' hχ' hφ
    obtain ⟨h01', h11'⟩ := Prod.mk.inj (hφ : ((N0 : E) * β χ 0 1, (N0 : E) * β χ 1 1) =
      ((N0 : E) * β χ' 0 1, (N0 : E) * β χ' 1 1))
    have h01 : β χ 0 1 = β χ' 0 1 := mul_left_cancel₀ hN0E h01'
    have h11 : β χ 1 1 = β χ' 1 1 := mul_left_cancel₀ hN0E h11'
    obtain ⟨hH, -, hν, -⟩ := hmem χ hχ
    obtain ⟨hH', -, hν', -⟩ := hmem χ' hχ'
    have e01 : ∀ τ, χ τ 0 1 = χ' τ 0 1 := fun τ => by
      rw [hent' χ hχ, hent' χ' hχ', h01]
    have e11 : ∀ τ, χ τ 1 1 = χ' τ 1 1 := fun τ => by
      rw [hent' χ hχ, hent' χ' hχ', h11]
    funext τ i k
    fin_cases i <;> fin_cases k
    · exact (hν τ).trans (hν' τ).symm
    · exact e01 τ
    · exact (hH τ 0 1).trans ((congrArg conj (e01 τ)).trans (hH' τ 0 1).symm)
    · exact e11 τ
  have hTfin : ((Subtype.val '' A) ×ˢ (Subtype.val '' A)).Finite :=
    (hAfin.image _).prod (hAfin.image _)
  have hSfin : S.Finite := Set.Finite.of_finite_image
    (hTfin.subset (by rintro _ ⟨χ, hχ, rfl⟩; exact hmaps χ hχ)) hinj
  have hcard := Set.ncard_le_ncard_of_injOn φ hmaps hinj hTfin
  rw [Set.ncard_prod] at hcard
  have himA : (Subtype.val '' A).ncard ≤ A.ncard := Set.ncard_image_le hAfin
  have hcard' : S.ncard ≤ A.ncard * A.ncard := hcard.trans (Nat.mul_le_mul himA himA)
  refine ⟨hSfin, ?_⟩
  have hR0 : 0 ≤ (N0 : ℝ) * B := mul_nonneg (Nat.cast_nonneg _) hB0
  have hNH : 0 ≤ (N0 : ℝ) * Hm := mul_nonneg (Nat.cast_nonneg _) (by linarith)
  have hR1 : 1 + 2 * ((N0 : ℝ) * B) ≤ K2 * t := by
    simp only [K2, ← hHm]
    rw [← hN0r, hB]
    nlinarith [mul_nonneg (mul_nonneg hNH hc1.le) (sub_nonneg.mpr ht)]
  calc (S.ncard : ℝ) ≤ (A.ncard : ℝ) * A.ncard := by exact_mod_cast hcard'
    _ ≤ (1 + 2 * ((N0 : ℝ) * B)) ^ (2 * fdeg E) * (1 + 2 * ((N0 : ℝ) * B)) ^ (2 * fdeg E) :=
        mul_le_mul hAcard hAcard (Nat.cast_nonneg _) (pow_nonneg (by linarith) _)
    _ = (1 + 2 * ((N0 : ℝ) * B)) ^ (4 * fdeg E) := by
        rw [← pow_add]
        congr 1
        ring
    _ ≤ (K2 * t) ^ (4 * fdeg E) := pow_le_pow_left₀ (by linarith) hR1 _

/- English proof (translation)
The claim follows from `coefficient_height_bound_of h2 h3d h5 integerApproximationCount_holds`.
-/
theorem coefficient_height_bound_of_lift_support_positivity (h2 : UnipotentLatticeLift (E := E)) (h3d : FourierCoefficientSupport (E := E))
    (h5 : NonvanishingCoefficientPositivity (E := E)) : CoefficientHeightBound (E := E) :=
  coefficient_height_bound_of h2 h3d h5 integerApproximationCount_holds

end ReciprocityTheory.ChartRestriction.G.FD
