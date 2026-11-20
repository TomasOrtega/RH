import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.RootSumWOff

noncomputable section

open NumberField Polynomial
open scoped Matrix Classical

namespace UpperTheory.Gal.W2

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
private theorem emb_eq_of_coeffs {F : Type} [Field F] [NumberField F] (N m : (F →+* ℂ) → ℕ)
    (h : ∀ c : 𝓞 F, ∑ τ : F →+* ℂ, (N τ : ℂ) * τ (c : F) = ∑ τ : F →+* ℂ, (m τ : ℂ) * τ (c : F)) :
    ∀ τ, N τ = m τ := by
  let f : (F →+* ℂ) → (𝓞 F →* ℂ) := fun τ => (τ.comp (algebraMap (𝓞 F) F)).toMonoidHom
  have hf : Function.Injective f := by
    intro σ τ hστ
    apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 F))
    ext c
    exact DFunLike.congr_fun hστ c
  have hli := (linearIndependent_monoidHom (𝓞 F) ℂ).comp f hf
  rw [Fintype.linearIndependent_iff] at hli
  have key := hli (fun τ => (N τ : ℂ) - m τ) (by
    funext c
    have hc := h c
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, Pi.zero_apply]
    simp only [f, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, RingHom.coe_comp, Function.comp_apply, sub_mul, Finset.sum_sub_distrib]
    rw [sub_eq_zero]
    exact hc)
  intro τ
  have := key τ
  rw [sub_eq_zero] at this
  exact_mod_cast this

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Consider separately whether the proposition holds or fails.

Substitute using the available equality. Establish an intermediate fact. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Consider separately whether the proposition holds or fails.

Substitute using the available equality. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem typeCount_of : TypeCount := by
  intro F _ _ O _ bar g ρ a n t₀ ε hS H Sb ty ev hD
  obtain ⟨hdet, hρ, -⟩ := hD
  have hU : IsUnit Sb.det := isUnit_iff_ne_zero.mpr hdet
  have htr : ∀ c : 𝓞 F, (ρ (a c)).trace
      = ∑ τ : F →+* ℂ, ((Finset.univ.filter (fun i => ty i = τ)).card : ℂ) * τ (c : F) := by
    intro c
    have e1 : ρ (a c) = Sb * Matrix.diagonal (fun i => (ty i) (c : F)) * Sb⁻¹ := by
      rw [← hρ c, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hU, Matrix.mul_one]
    rw [e1, Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hU,
      Matrix.one_mul, Matrix.trace_diagonal]
    rw [← Finset.sum_fiberwise Finset.univ ty (fun i => (ty i) (c : F))]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    rw [Finset.sum_congr rfl (g := fun _ => τ (c : F)) (fun i hi => by
      rw [(Finset.mem_filter.mp hi).2]), Finset.sum_const, nsmul_eq_mul]
  have hcount : ∀ τ, (Finset.univ.filter (fun i => ty i = τ)).card = typeMult n t₀ ε τ := by
    refine emb_eq_of_coeffs _ _ (fun c => ?_)
    rw [← htr c, hS.tr c]
  have hcard : ∀ τ, (evAt ty ev τ).card = typeMult n t₀ ε τ := by
    intro τ
    rw [← hcount τ, evAt, Multiset.card_map]
    rfl
  have hconj : ∀ τ : F →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ :=
    fun τ => star_star τ
  intro τ
  refine ⟨hcard τ, ?_⟩
  rw [evFull, Multiset.card_add, Multiset.card_map, hcard, hcard]
  have hpos := hS.pos
  by_cases h0 : τ = t₀
  · subst h0
    have hne : ComplexEmbedding.conjugate τ ≠ τ := hS.cx τ
    simp only [typeMult, if_true, if_neg hne]
    omega
  · by_cases h1 : τ = ComplexEmbedding.conjugate t₀
    · subst h1
      rw [hconj]
      simp only [typeMult, if_neg h0, if_true]
      omega
    · have h2 : ComplexEmbedding.conjugate τ ≠ t₀ := by
        intro e; apply h1; rw [← e, hconj]
      have h3 : ComplexEmbedding.conjugate τ ≠ ComplexEmbedding.conjugate t₀ := by
        intro e; apply h0; rw [← hconj τ, e, hconj]
      simp only [typeMult, if_neg h0, if_neg h1, if_neg h2, if_neg h3]
      rw [← Nat.mul_add, hS.eps τ h0 h1, Nat.mul_one]

end UpperTheory.Gal.W2
