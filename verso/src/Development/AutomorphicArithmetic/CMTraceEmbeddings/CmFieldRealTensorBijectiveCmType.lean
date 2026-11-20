import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.OrientEv
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed UpperTheory.Gal.W2.Seed.Ori
open scoped TensorProduct

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. By extensionality, compare the relevant components. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
private theorem func_repr {ι : Type} [Fintype ι] [DecidableEq ι] (f : (ι → ℂ) →ₗ[ℝ] ℝ) :
    ∃ a : ι → ℂ, ∀ z, f z = ∑ τ, (a τ * z τ).re := by
  refine ⟨fun τ => (f (Pi.single τ 1) : ℂ) - Complex.I * (f (Pi.single τ Complex.I) : ℂ), fun z => ?_⟩
  have h1 : z = ∑ τ, ((z τ).re • (Pi.single τ 1 : ι → ℂ) + (z τ).im • (Pi.single τ Complex.I : ι → ℂ)) := by
    ext k
    have hk : ∀ τ, ((z τ).re • (Pi.single τ 1 : ι → ℂ) + (z τ).im • (Pi.single τ Complex.I : ι → ℂ)) k =
        if k = τ then z k else 0 := by
      intro τ
      by_cases h : k = τ
      · subst h
        simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, if_true]
        apply Complex.ext <;> simp
      · simp [Pi.single_apply, h]
    rw [Finset.sum_apply]
    simp only [hk]
    simp
  conv_lhs => rw [h1]
  rw [map_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [map_add, map_smul, map_smul]
  simp [Complex.mul_re, Complex.sub_re, Complex.sub_im]
  ring

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Assume the hypotheses and unpack their components.

Reduce the equality to equality of the corresponding arguments. Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components. It suffices to derive a contradiction. Reduce the conclusion to the remaining proof obligations.

It suffices to derive a contradiction. Reduce the conclusion to the remaining proof obligations. Reduce the equality to equality of the corresponding arguments. Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components.

Establish an intermediate fact. A detailed English derivation is pending.
-/
private theorem family_inj {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E)
    (him : (A.τ₀ (A.ω : E)).im ≠ 0) :
    Function.Injective (Sum.elim (fun τ : Phi A => (τ.1 : E →* ℂ))
      (fun τ : Phi A => ((ComplexEmbedding.conjugate τ.1 : E →+* ℂ) : E →* ℂ))) := by
  have hval : ∀ (τ τ' : Phi A), (∀ x, τ.1 x = (starRingEnd ℂ) (τ'.1 x)) → False := by
    intro τ τ' h
    have h1 := h (A.ω : E)
    rw [τ.2, τ'.2] at h1
    exact him (Complex.conj_eq_iff_im.1 h1.symm)
  rintro (τ | τ) (τ' | τ') h
  · congr 1
    apply Subtype.ext
    ext x
    exact congrArg (fun g : E →* ℂ => g x) h
  · exfalso
    refine hval τ τ' fun x => ?_
    exact congrArg (fun g : E →* ℂ => g x) h
  · exfalso
    refine hval τ' τ fun x => ?_
    exact (congrArg (fun g : E →* ℂ => g x) h).symm
  · congr 1
    apply Subtype.ext
    ext x
    have h1 : (starRingEnd ℂ) (τ.1 x) = (starRingEnd ℂ) (τ'.1 x) := congrArg (fun g : E →* ℂ => g x) h
    exact (starRingEnd ℂ).injective h1

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Establish an intermediate fact. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem UpperTheory.cmField_real_tensor_bijective_cmType :
    TraceType → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E), Function.Bijective (fun (z : ℝ ⊗[ℚ] E) (τ : Phi A) => ev1 τ.1 z) := by
  intro hT E _ _ _ A
  classical
  obtain ⟨-, -, h3, him⟩ := hT E A
  haveI : Fintype (Phi A) := Fintype.ofFinite _
  let L : ℝ ⊗[ℚ] E →ₗ[ℝ] (Phi A → ℂ) := LinearMap.pi (fun τ => (ev1 τ.1).toLinearMap)
  have hL : ∀ z τ, L z τ = ev1 τ.1 z := fun _ _ => rfl
  have hsurj : Function.Surjective L := by
    rw [← LinearMap.range_eq_top]
    by_contra hne
    obtain ⟨f, hf0, hf⟩ := (LinearMap.range L).exists_le_ker_of_lt_top (lt_top_iff_ne_top.2 hne)
    obtain ⟨a, ha⟩ := func_repr f
    have hzero : ∀ x : E, ∑ τ : Phi A, (a τ * τ.1 x).re = 0 := by
      intro x
      have h1 : f (L ((1 : ℝ) ⊗ₜ x)) = 0 := LinearMap.mem_ker.1 (hf ⟨_, rfl⟩)
      rw [ha] at h1
      simpa [hL, realTensorEvalAlgHom_tmul] using h1
    have hli := (linearIndependent_monoidHom E ℂ).comp _ (family_inj A him)
    have hc := Fintype.linearIndependent_iff.1 hli
      (Sum.elim a (fun τ => (starRingEnd ℂ) (a τ))) (by
        ext x
        rw [Finset.sum_apply, Fintype.sum_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr, Function.comp, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        have h2 : ∀ τ : Phi A, a τ * τ.1 x + (starRingEnd ℂ) (a τ) * (starRingEnd ℂ) (τ.1 x) =
            ((2 * (a τ * τ.1 x).re : ℝ) : ℂ) := by
          intro τ
          rw [← map_mul, Complex.add_conj]
        have h3 : ∑ τ : Phi A, (a τ * τ.1 x + (starRingEnd ℂ) (a τ) * (starRingEnd ℂ) (τ.1 x)) = 0 := by
          simp only [h2]
          rw [← Complex.ofReal_sum, ← Finset.mul_sum, hzero]
          simp
        rw [← h3, Finset.sum_add_distrib]
        rfl)
    apply hf0
    refine LinearMap.ext fun z => ?_
    rw [ha]
    have h0 : ∀ τ, a τ = 0 := fun τ => hc (Sum.inl τ)
    simp [h0]
  have hcard : Fintype.card (Phi A) = Fintype.card (InfinitePlace E) :=
    Fintype.card_congr (Equiv.ofBijective (fun τ : Phi A => InfinitePlace.mk τ.1)
      ⟨fun τ τ' h => (h3 _).unique rfl h.symm, fun v => (h3 v).exists⟩)
  have hdim : Module.finrank ℝ (ℝ ⊗[ℚ] E) = Module.finrank ℝ (Phi A → ℂ) := by
    rw [Module.finrank_baseChange, Module.finrank_pi_fintype]
    simp only [Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rw [hcard, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      ← InfinitePlace.card_add_two_mul_card_eq_rank, IsTotallyComplex.nrRealPlaces_eq_zero]
    ring
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hsurj, hsurj⟩
