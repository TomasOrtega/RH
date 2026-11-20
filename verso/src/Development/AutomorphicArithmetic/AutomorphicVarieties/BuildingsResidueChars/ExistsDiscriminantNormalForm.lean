import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.FixedPointCriteria.Cond

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.PK

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Assume the hypotheses and unpack their components.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Clear the denominators using the available nonvanishing facts. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.

Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts. Take a linear combination of the given relations to obtain the conclusion.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts. Take a linear combination of the given relations to obtain the conclusion. Rewrite the conclusion using the stated equalities.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.exists_discriminant_normal_form :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ → τ ^ 2 - 4 ≠ 0 → τ ∈ (algebraMap O K).range → ∀ (s : O) (ε : Oˣ), τ ^ 2 - 4 = algebraMap O K (ε * s ^ 2) → ∃ (π : O) (n : ℕ) (e : Oˣ) (h : O) (x : Etau K τ), Cond π n e h x ∧ Ideal.span {s} = Ideal.span {π ^ n} := by
  intro O K _ _ _ _ _ Δ τ hL hτ hτr s ε hs
  haveI := hL.frac
  have inj : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  obtain ⟨t, rfl⟩ := hτr
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply hτ
    rw [hs]
    simp
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, μ, hμ⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs0 hϖ
  have h2K : algebraMap O K (((hL.two.unit)⁻¹ : Oˣ) : O) * 2 = 1 := by
    have h1 : (((hL.two.unit)⁻¹ : Oˣ) : O) * 2 = 1 := hL.two.val_inv_mul
    have h3 := congrArg (algebraMap O K) h1
    rw [map_mul, map_one, map_ofNat] at h3
    exact h3
  have two_ne : (2 : K) ≠ 0 := by
    intro h
    rw [h, mul_zero] at h2K
    exact zero_ne_one h2K
  have hI : algebraMap O K (((hL.two.unit)⁻¹ : Oˣ) : O) = 2⁻¹ := by
    field_simp
    exact h2K
  have hP : algebraMap O K (ϖ ^ n) ≠ 0 := by
    rw [map_ne_zero_iff _ inj]
    exact pow_ne_zero _ hϖ.ne_zero
  have hrel : algebraMap O K t ^ 2 - 4
      = algebraMap O K ε * algebraMap O K μ ^ 2 * algebraMap O K (ϖ ^ n) ^ 2 := by
    rw [hs, hμ]
    simp only [map_mul, map_pow]
    ring
  set T := algebraMap O K t with hT
  set P := algebraMap O K (ϖ ^ n) with hPdef
  let x : Etau K T := ⟨-T / 2 / P, 1 / P⟩
  have hxre : x.re = -T / 2 / P := rfl
  have hxim : x.im = 1 / P := rfl
  have htr : trace x = 0 := by
    rw [trace_def, hxre, hxim]
    field_simp
    ring
  refine ⟨ϖ, n, ε * μ * μ * (hL.two.unit)⁻¹ * (hL.two.unit)⁻¹, t * (((hL.two.unit)⁻¹ : Oˣ) : O), x,
    ⟨hϖ, ⟨?_, ?_, ?_⟩, htr, ?_, ?_⟩, ?_⟩
  · rw [htr]
    exact ⟨0, map_zero _⟩
  · refine ⟨-((ε * μ * μ * (hL.two.unit)⁻¹ * (hL.two.unit)⁻¹ : Oˣ) : O), ?_⟩
    rw [norm_def, hxre, hxim]
    simp only [map_neg, Units.val_mul, map_mul, hI]
    field_simp
    linear_combination hrel
  · refine ⟨ε * μ * μ, ?_⟩
    rw [hxim, hrel]
    simp only [Units.val_mul, map_mul]
    field_simp
  · apply QuadraticAlgebra.ext
    · rw [algebraMap_etau, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.re_mul, hxre, hxim]
      simp only [Units.val_mul, map_mul, hI]
      field_simp
      linear_combination hrel
    · rw [algebraMap_etau, QuadraticAlgebra.algebraMap_im, QuadraticAlgebra.im_mul, hxre, hxim]
      field_simp
      ring
  · apply QuadraticAlgebra.ext
    · show (0 : K) = (algebraMap O (Etau K T) (t * (((hL.two.unit)⁻¹ : Oˣ) : O))).re + (yy ϖ n x).re
      rw [algebraMap_etau, QuadraticAlgebra.algebraMap_re]
      simp only [yy, QuadraticAlgebra.re_smul, smul_eq_mul, map_mul, hI, hxre]
      rw [← hT, ← hPdef]
      field_simp
      ring
    · show (1 : K) = (algebraMap O (Etau K T) (t * (((hL.two.unit)⁻¹ : Oˣ) : O))).im + (yy ϖ n x).im
      rw [algebraMap_etau, QuadraticAlgebra.algebraMap_im]
      simp only [yy, QuadraticAlgebra.im_smul, smul_eq_mul, hxim]
      rw [← hPdef]
      field_simp
      ring
  · rw [Ideal.span_singleton_eq_span_singleton, hμ]
    exact associated_unit_mul_left _ _ μ.isUnit
