import Mathlib

open NumberField IsDedekindDomain

namespace GlobalTheory

/- English proof (translation)
Establish `hfun : (fun v : HeightOneSpectrum (𝓞 F) => NumberField.HeightOneSpectrum.adicAbv F v N) = (fun w : FinitePlace F => w N) ∘ (FinitePlace.equivHeightOneSpectrum (K` using `F)).symm := by`. Use function extensionality and compare the values at `v`. Simplify using `only [Function.comp, FinitePlace.equivHeightOneSpectrum_symm_apply, FinitePlace.norm_embedding]`. Establish `hfin : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => NumberField.HeightOneSpectrum.adicAbv F v N).Finite`. Rewrite using `[hfun, Function.mulSupport_comp_eq_preimage]`.

Conclude with `Set.Finite.preimage (FinitePlace.equivHeightOneSpectrum (K := F)).symm.injective.injOn (FinitePlace.hasFiniteMulSupport hN)`. Establish `hpos : ∀ v : HeightOneSpectrum (𝓞 F), 0 < NumberField.HeightOneSpectrum.adicAbv F v N` using `fun v => (NumberField.HeightOneSpectrum.adicAbv F v).pos hN`. Establish `hprod : ∏ᶠ v : HeightOneSpectrum (𝓞 F), NumberField.HeightOneSpectrum.adicAbv F v N = ((|Algebra.norm ℚ N|⁻¹ : ℚ) : ℝ)`. Rewrite using `[← FinitePlace.prod_eq_inv_abs_norm hN, ← finprod_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := F)).symm]`. Conclude with `congrArg finprod hfun`.

Establish `hsub : (Function.support fun v : HeightOneSpectrum (𝓞 F) => Real.log (NumberField.HeightOneSpectrum.adicAbv F v N)) ⊆ hfin.toFinset`. Introduce `v hv`. Simplify using `only [Set.Finite.coe_toFinset, Function.mem_mulSupport]`. Introduce `h`. Conclude with `hv (by simp only [h, Real.log_one])`.

Use `⟨hfin.toFinset.finite_toSet.subset hsub, ?_⟩` and prove the remaining obligations. Establish `h1 : ∑ᶠ v : HeightOneSpectrum (𝓞 F), Real.log (NumberField.HeightOneSpectrum.adicAbv F v N) = - Real.log ((|Algebra.norm ℚ N| : ℚ) : ℝ)`. Rewrite using `[finsum_eq_sum_of_support_subset _ hsub, ← Real.log_prod (fun v _ => (hpos v).ne'), ← finprod_eq_prod_of_mulSupport_subset _ (by simp), hprod, Rat.cast_inv, Real.log_inv]`. Establish `h2 : ∑ σ : F →+* ℂ, Real.log ‖σ N‖ = Real.log ((|Algebra.norm ℚ N| : ℚ) : ℝ)`. Establish `h` using `congr_arg (‖·‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ N)`.

Simplify using `only [norm_prod] at h`. Rewrite using `[← Real.log_prod (fun σ _ => by simpa using hN)]`. Use `congr 1`. Rewrite using `[Fintype.prod_equiv (RingHom.equivRatAlgHom F ℂ) (fun σ : F →+* ℂ => ‖σ N‖) (fun σ : F →ₐ[ℚ] ℂ => ‖σ N‖) (fun _ => by simp [RingHom.equivRatAlgHom_apply]), ← h]`. Simplify using `[← Complex.norm_ratCast]`.

Rewrite using `[h1, h2, add_neg_cancel]`.
-/
theorem sum_log_embedding_add_finsum_log_adicAbv_eq_zero
    (F : Type) [Field F] [NumberField F] (N : F) (hN : N ≠ 0) :
    (Function.support fun v : HeightOneSpectrum (𝓞 F) =>
        Real.log (NumberField.HeightOneSpectrum.adicAbv F v N)).Finite ∧
      (∑ σ : F →+* ℂ, Real.log ‖σ N‖) +
        ∑ᶠ v : HeightOneSpectrum (𝓞 F),
          Real.log (NumberField.HeightOneSpectrum.adicAbv F v N) = 0 := by
  have hfun : (fun v : HeightOneSpectrum (𝓞 F) => NumberField.HeightOneSpectrum.adicAbv F v N) =
      (fun w : FinitePlace F => w N) ∘ (FinitePlace.equivHeightOneSpectrum (K := F)).symm := by
    funext v
    simp only [Function.comp, FinitePlace.equivHeightOneSpectrum_symm_apply,
      FinitePlace.norm_embedding]
  have hfin : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      NumberField.HeightOneSpectrum.adicAbv F v N).Finite := by
    rw [hfun, Function.mulSupport_comp_eq_preimage]
    exact Set.Finite.preimage (FinitePlace.equivHeightOneSpectrum (K := F)).symm.injective.injOn
      (FinitePlace.hasFiniteMulSupport hN)
  have hpos : ∀ v : HeightOneSpectrum (𝓞 F), 0 < NumberField.HeightOneSpectrum.adicAbv F v N :=
    fun v => (NumberField.HeightOneSpectrum.adicAbv F v).pos hN
  have hprod : ∏ᶠ v : HeightOneSpectrum (𝓞 F), NumberField.HeightOneSpectrum.adicAbv F v N =
      ((|Algebra.norm ℚ N|⁻¹ : ℚ) : ℝ) := by
    rw [← FinitePlace.prod_eq_inv_abs_norm hN,
      ← finprod_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := F)).symm]
    exact congrArg finprod hfun
  have hsub : (Function.support fun v : HeightOneSpectrum (𝓞 F) =>
      Real.log (NumberField.HeightOneSpectrum.adicAbv F v N)) ⊆ hfin.toFinset := by
    intro v hv
    simp only [Set.Finite.coe_toFinset, Function.mem_mulSupport]
    intro h
    exact hv (by simp only [h, Real.log_one])
  refine ⟨hfin.toFinset.finite_toSet.subset hsub, ?_⟩
  have h1 : ∑ᶠ v : HeightOneSpectrum (𝓞 F),
      Real.log (NumberField.HeightOneSpectrum.adicAbv F v N) =
      - Real.log ((|Algebra.norm ℚ N| : ℚ) : ℝ) := by
    rw [finsum_eq_sum_of_support_subset _ hsub, ← Real.log_prod (fun v _ => (hpos v).ne'),
      ← finprod_eq_prod_of_mulSupport_subset _ (by simp), hprod, Rat.cast_inv, Real.log_inv]
  have h2 : ∑ σ : F →+* ℂ, Real.log ‖σ N‖ = Real.log ((|Algebra.norm ℚ N| : ℚ) : ℝ) := by
    have h := congr_arg (‖·‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ N)
    simp only [norm_prod] at h
    rw [← Real.log_prod (fun σ _ => by simpa using hN)]
    congr 1
    rw [Fintype.prod_equiv (RingHom.equivRatAlgHom F ℂ) (fun σ : F →+* ℂ => ‖σ N‖)
      (fun σ : F →ₐ[ℚ] ℂ => ‖σ N‖) (fun _ => by simp [RingHom.equivRatAlgHom_apply]), ← h]
    simp [← Complex.norm_ratCast]
  rw [h1, h2, add_neg_cancel]

end GlobalTheory
