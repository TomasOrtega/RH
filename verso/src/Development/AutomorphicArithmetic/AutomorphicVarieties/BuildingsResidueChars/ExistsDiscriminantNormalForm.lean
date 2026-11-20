import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.FixedPointCriteria.Cond

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.PK

/- English proof (translation)
Introduce `O K _ _ _ _ _ Δ τ hL hτ hτr s ε hs`. Use `haveI := hL.frac`. Establish `inj : Function.Injective (algebraMap O K)` using `IsFractionRing.injective O K`. Take `⟨t, rfl⟩` from `hτr`. Establish `hs0 : s ≠ 0`.

Introduce and unpack `rfl`. Apply `hτ` to reduce the goal to its premises. Rewrite using `[hs]`. Simplify using the standard rewrite rules. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`.

Take `⟨n, μ, hμ⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs0 hϖ`. Establish `h2K : algebraMap O K (((hL.two.unit)⁻¹ : Oˣ) : O) * 2 = 1`. Establish `h1 : (((hL.two.unit)⁻¹ : Oˣ) : O) * 2 = 1` using `hL.two.val_inv_mul`. Establish `h3` using `congrArg (algebraMap O K) h1`. Rewrite `h3` using `[map_mul, map_one, map_ofNat]`.

Conclude with `h3`. Establish `two_ne : (2 : K) ≠ 0`. Introduce `h`. Rewrite `h2K` using `[h, mul_zero]`. Conclude with `zero_ne_one h2K`.

Establish `hI : algebraMap O K (((hL.two.unit)⁻¹ : Oˣ) : O) = 2⁻¹`. Clear the denominators using the available nonvanishing facts. Conclude with `h2K`. Establish `hP : algebraMap O K (ϖ ^ n) ≠ 0`. Rewrite using `[map_ne_zero_iff _ inj]`.

Conclude with `pow_ne_zero _ hϖ.ne_zero`. Establish `hrel : algebraMap O K t ^ 2 - 4 = algebraMap O K ε * algebraMap O K μ ^ 2 * algebraMap O K (ϖ ^ n) ^ 2`. Rewrite using `[hs, hμ]`. Simplify using `only [map_mul, map_pow]`. Expand and normalize the polynomial expressions, which then agree.

Use `set T := algebraMap O K t with hT`. Use `set P := algebraMap O K (ϖ ^ n) with hPdef`. Set `x : Etau K T` to `⟨-T / 2 / P, 1 / P⟩`. Establish `hxre : x.re = -T / 2 / P` using `rfl`. Establish `hxim : x.im = 1 / P` using `rfl`.

Establish `htr : trace x = 0`. Rewrite using `[trace_def, hxre, hxim]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Use `⟨ϖ, n, ε * μ * μ * (hL.two.unit)⁻¹ * (hL.two.unit)⁻¹, t * (((hL.two.unit)⁻¹ : Oˣ) : O), x, ⟨hϖ, ⟨?_, ?_, ?_⟩, htr, ?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[htr]`. Conclude with `⟨0, map_zero _⟩`. Use `⟨-((ε * μ * μ * (hL.two.unit)⁻¹ * (hL.two.unit)⁻¹ : Oˣ) : O), ?_⟩` and prove the remaining obligations. Rewrite using `[norm_def, hxre, hxim]`. Simplify using `only [map_neg, Units.val_mul, map_mul, hI]`.

Clear the denominators using the available nonvanishing facts. Take the linear combination `hrel`. Use `⟨ε * μ * μ, ?_⟩` and prove the remaining obligations. Rewrite using `[hxim, hrel]`. Simplify using `only [Units.val_mul, map_mul]`.

Clear the denominators using the available nonvanishing facts. Apply `QuadraticAlgebra.ext` to reduce the goal to its premises. Rewrite using `[algebraMap_etau, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.re_mul, hxre, hxim]`. Simplify using `only [Units.val_mul, map_mul, hI]`. Clear the denominators using the available nonvanishing facts.

Take the linear combination `hrel`. Rewrite using `[algebraMap_etau, QuadraticAlgebra.algebraMap_im, QuadraticAlgebra.im_mul, hxre, hxim]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Apply `QuadraticAlgebra.ext` to reduce the goal to its premises.

Use `show (0 : K) = (algebraMap O (Etau K T) (t * (((hL.two.unit)⁻¹ : Oˣ) : O))).re + (yy ϖ n x).re`. Rewrite using `[algebraMap_etau, QuadraticAlgebra.algebraMap_re]`. Simplify using `only [yy, QuadraticAlgebra.re_smul, smul_eq_mul, map_mul, hI, hxre]`. Rewrite using `[← hT, ← hPdef]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Use `show (1 : K) = (algebraMap O (Etau K T) (t * (((hL.two.unit)⁻¹ : Oˣ) : O))).im + (yy ϖ n x).im`. Rewrite using `[algebraMap_etau, QuadraticAlgebra.algebraMap_im]`. Simplify using `only [yy, QuadraticAlgebra.im_smul, smul_eq_mul, hxim]`. Rewrite using `[← hPdef]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Ideal.span_singleton_eq_span_singleton, hμ]`. Conclude with `associated_unit_mul_left _ _ μ.isUnit`.
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
