import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.QCoreLocalPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.QCoreGlobPf

namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open NumberField IsDedekindDomain

/- English proof (translation)
Introduce `hLD K K₁ V _ _ _ _ _ _ _ _ _ _ M hfg hspan W θ hθ c hker be s hbe _ hs hint supN a Bθ Carch Bdeg hconj hshort harch hdeg`. Take `⟨hdet, hloc⟩` from `qcoreLocal hLD hL K K₁ V M hfg hspan W θ hθ c hker be s hbe hs hint`. Take `⟨hsupp, hglob⟩` from `qcoreGlobal_holds K K₁ V M _ θ c hdet s hs supN a Bθ Carch Bdeg hconj hshort harch hdeg`. Use `⟨Finsupp.ofSupportFinite _ hsupp, ?_, ?_⟩` and prove the remaining obligations. Introduce `la`.

Take `⟨ℓ, hℓ, hle⟩` from `hloc la`. Conclude with `⟨ℓ, hℓ, hle⟩`. Establish `hsum : ((Finsupp.ofSupportFinite _ hsupp).sum fun la v => v * logN la) = ∑ᶠ la : HeightOneSpectrum (𝓞 K), nnFun (K` using `K) (detCT c θ) s la * logN la := by`. Rewrite using `[finsum_eq_sum_of_support_subset (s := hsupp.toFinset)]`. Both sides reduce to the same expression.

Introduce `la hla`. Rewrite using `[Set.Finite.coe_toFinset]`. Conclude with `Function.support_mul_subset_left _ _ hla`. Rewrite using `[hsum]`. Conclude with `hglob`.
-/
theorem quotCore_of_local (hL : QuotLocalStatement) : QuotCoreStatement := by
  intro hLD K K₁ V _ _ _ _ _ _ _ _ _ _ M hfg hspan W θ hθ c hker be s hbe _ hs hint supN a Bθ Carch
    Bdeg hconj hshort harch hdeg
  obtain ⟨hdet, hloc⟩ :=
    qcoreLocal hLD hL K K₁ V M hfg hspan W θ hθ c hker be s hbe hs hint
  obtain ⟨hsupp, hglob⟩ :=
    qcoreGlobal_holds K K₁ V M _ θ c hdet s hs supN a Bθ Carch Bdeg hconj hshort harch hdeg
  refine ⟨Finsupp.ofSupportFinite _ hsupp, ?_, ?_⟩
  · intro la
    obtain ⟨ℓ, hℓ, hle⟩ := hloc la
    exact ⟨ℓ, hℓ, hle⟩
  · have hsum : ((Finsupp.ofSupportFinite _ hsupp).sum fun la v => v * logN la) =
        ∑ᶠ la : HeightOneSpectrum (𝓞 K), nnFun (K := K) (detCT c θ) s la * logN la := by
      rw [finsum_eq_sum_of_support_subset (s := hsupp.toFinset)]
      · rfl
      · intro la hla
        rw [Set.Finite.coe_toFinset]
        exact Function.support_mul_subset_left _ _ hla
    rw [hsum]
    exact hglob

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
