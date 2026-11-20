import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusSplitPrimeDatum

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

/- English proof (translation)
Introduce `Ω _ _ _ η D δ hD hδ hη`. Establish `hDq : (0 : ℚ) < D` using `by exact_mod_cast hD`. Establish `hDr : (0 : ℝ) < D` using `by exact_mod_cast hD`. Establish `hδ0 : δ ≠ 0`. Introduce and unpack `rfl`.

Establish `h0 : ((D : ℕ) : Ω) = 0`. Use `hδ.symm` as an intermediate fact. Simplify using `using this`. Conclude with `hD.ne' (by exact_mod_cast h0)`. Use `set p : Polynomial ℚ := Polynomial.X ^ 2 + Polynomial.C (D : ℚ) with hp`.

Establish `hmon : p.Monic` using `Polynomial.monic_X_pow_add_C _ two_ne_zero`. Establish `hdeg : p.natDegree = 2` using `Polynomial.natDegree_X_pow_add_C`. Establish `hroot : Polynomial.aeval δ p = 0`. Simplify using `[hp, hδ]`. Establish `hirr : Irreducible p`.

Use `Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; decide) ?_` and prove the remaining obligations. Introduce `x hx`. Simplify using `only [hp, Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hx`. Use polynomial arithmetic with `[sq_nonneg x]`. Establish `hmin : p = minpoly ℚ δ` using `minpoly.eq_of_irreducible_of_monic hirr hroot hmon`.

Establish `hint : IsIntegral ℚ δ` using `⟨p, hmon, by rw [← Polynomial.aeval_def]; exact hroot⟩`. Use `haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ ({δ} : Set Ω)) := IntermediateField.adjoin.finiteDimensional hint`. Use `haveI : NumberField (IntermediateField.adjoin ℚ ({δ} : Set Ω)) := by constructor`. Use `⟨IntermediateField.adjoin ℚ ({δ} : Set Ω), inferInstance, inferInstance, inferInstance, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[IntermediateField.adjoin.finrank hint, ← hmin, hdeg]`.

Use `⟨fun v => ?_⟩` and prove the remaining obligations. Rewrite using `[NumberField.InfinitePlace.isComplex_iff]`. Introduce `hr`. Rewrite `hr` using `[NumberField.ComplexEmbedding.isReal_iff]`. Use `set φ := v.embedding`.

Set `d : IntermediateField.adjoin ℚ ({δ} : Set Ω)` to `⟨δ, IntermediateField.mem_adjoin_simple_self ℚ δ⟩`. Establish `hd : d ^ 2 = -(D : IntermediateField.adjoin ℚ ({δ} : Set Ω))` using `Subtype.ext (by simpa [d] using hδ)`. Establish `hz : (φ d) ^ 2 = -(D : ℂ)`. Use `congrArg φ hd` as an intermediate fact. Simplify using `using this`.

Establish `hc : (starRingEnd ℂ) (φ d) = φ d`. Use `RingHom.congr_fun hr d` as an intermediate fact. Simplify using `using this`. Establish `him : (φ d).im = 0` using `Complex.conj_eq_iff_im.mp hc`. Establish `hre` using `congrArg Complex.re hz`.

Simplify using `[pow_two, him] at hre`. Use polynomial arithmetic with `[mul_self_nonneg (φ d).re]`. Use extensionality with `σ`. Rewrite using `[mem_galOf, MonoidHom.mem_ker]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Establish `h1 : σ δ = δ` using `h ⟨δ, IntermediateField.mem_adjoin_simple_self ℚ δ⟩`. Rewrite `h1` using `[hη σ]`. Break down `Int.units_eq_one_or (η σ) with h2 | h2` into its components or cases. Conclude with `h2`.

It suffices to derive a contradiction. Rewrite `h1` using `[h2]`. Simplify using `only [Units.val_neg, Units.val_one, neg_smul, one_smul] at h1`. Establish `: (2 : Ω) * δ = 0` using `by linear_combination -h1`. Break down `mul_eq_zero.mp this with h3 | h3` into its components or cases.

Conclude with `two_ne_zero h3`. Conclude with `hδ0 h3`. Introduce `h x`. Establish `hσδ : σ δ = δ` using `by rw [hη σ, h]; simp`. Establish `hext : ((σ : Ω →ₐ[ℚ] Ω).comp (IntermediateField.val _) : IntermediateField.adjoin ℚ ({δ} : Set Ω) →ₐ[ℚ] Ω) = IntermediateField.val _` using `IntermediateField.algHom_ext_of_eq_adjoin ℚ rfl (by`.

Introduce `y hy`. Rewrite `hy` using `[Set.mem_singleton_iff]`. Substitute `hy` using the available equality. Conclude with `hσδ)`. Conclude with `AlgHom.congr_fun hext x`.
-/
theorem UpperTheory.V.Fr.sc_quad :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (η : G ℚ Ω →* ℤˣ) (D : ℕ) (δ : Ω), 0 < D → δ ^ 2 = -(D : Ω) → (∀ s : G ℚ Ω, s δ = (η s : ℤ) • δ) → ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : Algebra K Ω), Module.finrank ℚ K = 2 ∧ IsTotallyComplex K ∧ galOf ℚ K Ω = η.ker := by
  intro Ω _ _ _ η D δ hD hδ hη
  have hDq : (0 : ℚ) < D := by exact_mod_cast hD
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    have h0 : ((D : ℕ) : Ω) = 0 := by
      have := hδ.symm
      simpa using this
    exact hD.ne' (by exact_mod_cast h0)
  set p : Polynomial ℚ := Polynomial.X ^ 2 + Polynomial.C (D : ℚ) with hp
  have hmon : p.Monic := Polynomial.monic_X_pow_add_C _ two_ne_zero
  have hdeg : p.natDegree = 2 := Polynomial.natDegree_X_pow_add_C
  have hroot : Polynomial.aeval δ p = 0 := by
    simp [hp, hδ]
  have hirr : Irreducible p := by
    refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; decide) ?_
    intro x hx
    simp only [hp, Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C] at hx
    nlinarith [sq_nonneg x]
  have hmin : p = minpoly ℚ δ := minpoly.eq_of_irreducible_of_monic hirr hroot hmon
  have hint : IsIntegral ℚ δ := ⟨p, hmon, by rw [← Polynomial.aeval_def]; exact hroot⟩
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ ({δ} : Set Ω)) :=
    IntermediateField.adjoin.finiteDimensional hint
  haveI : NumberField (IntermediateField.adjoin ℚ ({δ} : Set Ω)) := by constructor
  refine ⟨IntermediateField.adjoin ℚ ({δ} : Set Ω), inferInstance, inferInstance, inferInstance, ?_, ?_, ?_⟩
  · rw [IntermediateField.adjoin.finrank hint, ← hmin, hdeg]
  · refine ⟨fun v => ?_⟩
    rw [NumberField.InfinitePlace.isComplex_iff]
    intro hr
    rw [NumberField.ComplexEmbedding.isReal_iff] at hr
    set φ := v.embedding
    let d : IntermediateField.adjoin ℚ ({δ} : Set Ω) := ⟨δ, IntermediateField.mem_adjoin_simple_self ℚ δ⟩
    have hd : d ^ 2 = -(D : IntermediateField.adjoin ℚ ({δ} : Set Ω)) := Subtype.ext (by simpa [d] using hδ)
    have hz : (φ d) ^ 2 = -(D : ℂ) := by
      have := congrArg φ hd
      simpa using this
    have hc : (starRingEnd ℂ) (φ d) = φ d := by
      have := RingHom.congr_fun hr d
      simpa using this
    have him : (φ d).im = 0 := Complex.conj_eq_iff_im.mp hc
    have hre := congrArg Complex.re hz
    simp [pow_two, him] at hre
    nlinarith [mul_self_nonneg (φ d).re]
  · ext σ
    rw [mem_galOf, MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : σ δ = δ := h ⟨δ, IntermediateField.mem_adjoin_simple_self ℚ δ⟩
      rw [hη σ] at h1
      rcases Int.units_eq_one_or (η σ) with h2 | h2
      · exact h2
      · exfalso
        rw [h2] at h1
        simp only [Units.val_neg, Units.val_one, neg_smul, one_smul] at h1
        have : (2 : Ω) * δ = 0 := by linear_combination -h1
        rcases mul_eq_zero.mp this with h3 | h3
        · exact two_ne_zero h3
        · exact hδ0 h3
    · intro h x
      have hσδ : σ δ = δ := by rw [hη σ, h]; simp
      have hext : ((σ : Ω →ₐ[ℚ] Ω).comp (IntermediateField.val _) :
          IntermediateField.adjoin ℚ ({δ} : Set Ω) →ₐ[ℚ] Ω) = IntermediateField.val _ :=
        IntermediateField.algHom_ext_of_eq_adjoin ℚ rfl (by
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          subst hy
          exact hσδ)
      exact AlgHom.congr_fun hext x
