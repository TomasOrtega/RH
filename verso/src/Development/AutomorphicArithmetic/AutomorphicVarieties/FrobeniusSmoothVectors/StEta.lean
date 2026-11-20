import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusSplitPrimeDatum

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

/- English proof (translation)
Introduce `Ω _ _ _ η D δ hD hδ hs σ hσ`. Take `⟨j, hj⟩` from `hσ`. Break down `Int.units_eq_one_or (η σ) with h | h` into its components or cases. It suffices to derive a contradiction. Establish `h1 : σ δ = δ` using `by rw [hs σ, h]; simp`.

Establish `h2 : j δ = starRingEnd ℂ (j δ)`. Use `hj δ` as an intermediate fact. Rewrite using `[← this]`. Conclude with `congrArg j h1.symm`. Establish `h3 : (j δ) ^ 2 = -(D : ℂ)`.

Rewrite using `[← map_pow, hδ]`. Simplify using the standard rewrite rules. Establish `him : (j δ).im = 0` using `Complex.conj_eq_iff_im.mp h2.symm`. Establish `h4` using `congrArg Complex.re h3`. Simplify using `[sq, him] at h4`.

Establish `hD' : (0 : ℝ) < D` using `by exact_mod_cast hD`. Use polynomial arithmetic with `[mul_self_nonneg (j δ).re]`. Conclude with `h`.
-/
theorem UpperTheory.V.Fr.st_eta :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (η : G ℚ Ω →* ℤˣ) (D : ℕ) (δ : Ω), 0 < D → δ ^ 2 = -(D : Ω) → (∀ s : G ℚ Ω, s δ = (η s : ℤ) • δ) → ∀ σ : G ℚ Ω, IsCC σ → η σ = -1 := by
  intro Ω _ _ _ η D δ hD hδ hs σ hσ
  obtain ⟨j, hj⟩ := hσ
  rcases Int.units_eq_one_or (η σ) with h | h
  · exfalso
    have h1 : σ δ = δ := by rw [hs σ, h]; simp
    have h2 : j δ = starRingEnd ℂ (j δ) := by
      have := hj δ
      rw [← this]
      exact congrArg j h1.symm
    have h3 : (j δ) ^ 2 = -(D : ℂ) := by
      rw [← map_pow, hδ]; simp
    have him : (j δ).im = 0 := Complex.conj_eq_iff_im.mp h2.symm
    have h4 := congrArg Complex.re h3
    simp [sq, him] at h4
    have hD' : (0 : ℝ) < D := by exact_mod_cast hD
    nlinarith [mul_self_nonneg (j δ).re]
  · exact h
