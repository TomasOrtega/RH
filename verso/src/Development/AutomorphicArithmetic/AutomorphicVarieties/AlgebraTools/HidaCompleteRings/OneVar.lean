import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Weier
open IsLocalRing

/- English proof (translation)
Introduce `O K _ _ _ _ _ ι hι g Z hZ h`. Assume the negation of the conclusion as `hg`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Take `⟨m, P, U, -, hP, -, hU, hfac⟩` from `UpperTheory.V.abelian₂.weier O ϖ hϖ g hg`. Establish `hmon : (P.map ι).Monic` using `hP.monic.map ι`.

Establish `hϖ0 : ι ϖ ≠ 0` using `fun h0 => hϖ.ne_zero (hι (by rw [h0, map_zero]))`. Use `hmon.ne_zero (Polynomial.eq_zero_of_infinite_isRoot _ (hZ.mono ?_))` and prove the remaining obligations. Introduce `z hz`. Take `⟨y, hyC, hyX, hy0⟩` from `h z hz`. Establish `hyP : y (P : PowerSeries O) = (P.map ι).eval z`.

Establish `e : y.comp Polynomial.coeToPowerSeries.ringHom = Polynomial.eval₂RingHom ι z`. Apply `Polynomial.ringHom_ext` to reduce the goal to its premises. Introduce `a`. Simplify using `[hyC]`. Simplify using `[hyX]`.

Use `RingHom.congr_fun e P` as an intermediate fact. Simplify `this` using `[Polynomial.eval_map]`. Rewrite `hy0` using `[hfac, map_mul, map_mul, map_pow, hyC, hyP]`. Establish `hyU : y U ≠ 0` using `(hU.map y).ne_zero`. Use `show (P.map ι).IsRoot z`.

Break down `mul_eq_zero.1 hy0 with h1 | h1` into its components or cases. Break down `mul_eq_zero.1 h1 with h2 | h2` into its components or cases. Conclude with `absurd h2 (pow_ne_zero m hϖ0)`. Conclude with `h2`. Conclude with `absurd h1 hyU`.
-/
theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.oneVar :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [Field K] (ι : O →+* K), Function.Injective ι → ∀ (g : PowerSeries O) (Z : Set K), Z.Infinite → (∀ z ∈ Z, ∃ y : PowerSeries O →+* K, (∀ a, y (PowerSeries.C a) = ι a) ∧ y PowerSeries.X = z ∧ y g = 0) → g = 0 := by
  intro O K _ _ _ _ _ ι hι g Z hZ h
  by_contra hg
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨m, P, U, -, hP, -, hU, hfac⟩ := UpperTheory.V.abelian₂.weier O ϖ hϖ g hg
  have hmon : (P.map ι).Monic := hP.monic.map ι
  have hϖ0 : ι ϖ ≠ 0 := fun h0 => hϖ.ne_zero (hι (by rw [h0, map_zero]))
  refine hmon.ne_zero (Polynomial.eq_zero_of_infinite_isRoot _ (hZ.mono ?_))
  intro z hz
  obtain ⟨y, hyC, hyX, hy0⟩ := h z hz
  have hyP : y (P : PowerSeries O) = (P.map ι).eval z := by
    have e : y.comp Polynomial.coeToPowerSeries.ringHom = Polynomial.eval₂RingHom ι z := by
      apply Polynomial.ringHom_ext
      · intro a
        simp [hyC]
      · simp [hyX]
    have := RingHom.congr_fun e P
    simpa [Polynomial.eval_map] using this
  rw [hfac, map_mul, map_mul, map_pow, hyC, hyP] at hy0
  have hyU : y U ≠ 0 := (hU.map y).ne_zero
  show (P.map ι).IsRoot z
  rcases mul_eq_zero.1 hy0 with h1 | h1
  · rcases mul_eq_zero.1 h1 with h2 | h2
    · exact absurd h2 (pow_ne_zero m hϖ0)
    · exact h2
  · exact absurd h1 hyU
