import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Entire
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ComplexOrder

/- English proof (translation)
Introduce `p N hp`. Establish `hpr : Prime (p : 𝓞 ℚ)`. Establish `e : (p : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm (p : ℤ)` using `by simp`. Rewrite using `[e]`. Conclude with `(MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr (Nat.prime_iff_prime_int.1 hp)`.

Establish `hne : Ideal.span {(p : 𝓞 ℚ)} ≠ ⊥`. Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`. Conclude with `hpr.ne_zero`. Use `⟨⟨Ideal.span {(p : 𝓞 ℚ)}, (Ideal.span_singleton_prime hpr.ne_zero).2 hpr, hne⟩, ?_, ?_⟩` and prove the remaining obligations. Establish `h : ∀ w : HeightOneSpectrum (𝓞 ℚ), normV w = Ideal.absNorm w.asIdeal` using `fun w => by`.

Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Both sides reduce to the same expression. Rewrite using `[h]`. Express the relevant statement in the definitionally equal form `Ideal.absNorm (Ideal.span {(p : 𝓞 ℚ)}) = p`. Rewrite using `[Ideal.absNorm_span_natCast, RingOfIntegers.rank, Module.finrank_self, pow_one]`.

Express the relevant statement in the definitionally equal form `(N : 𝓞 ℚ) ∈ Ideal.span {(p : 𝓞 ℚ)} ↔ p ∣ N`. Rewrite using `[Ideal.mem_span_singleton, ← map_dvd_iff Rat.ringOfIntegersEquiv, map_natCast, map_natCast, Int.natCast_dvd_natCast]`.
-/
theorem UpperTheory.exists_rat_heightOneSpectrum_normV_eq_prime_bad_iff_dvd :
    ∀ (p N : ℕ), p.Prime → ∃ v : H.P ℚ, normV v = p ∧ (Bad N v ↔ p ∣ N) := by
  intro p N hp
  have hpr : Prime (p : 𝓞 ℚ) := by
    have e : (p : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm (p : ℤ) := by simp
    rw [e]
    exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr (Nat.prime_iff_prime_int.1 hp)
  have hne : Ideal.span {(p : 𝓞 ℚ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hpr.ne_zero
  refine ⟨⟨Ideal.span {(p : 𝓞 ℚ)}, (Ideal.span_singleton_prime hpr.ne_zero).2 hpr, hne⟩, ?_, ?_⟩
  · have h : ∀ w : HeightOneSpectrum (𝓞 ℚ), normV w = Ideal.absNorm w.asIdeal := fun w => by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
    rw [h]
    change Ideal.absNorm (Ideal.span {(p : 𝓞 ℚ)}) = p
    rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, Module.finrank_self, pow_one]
  · change (N : 𝓞 ℚ) ∈ Ideal.span {(p : 𝓞 ℚ)} ↔ p ∣ N
    rw [Ideal.mem_span_singleton, ← map_dvd_iff Rat.ringOfIntegersEquiv, map_natCast, map_natCast,
      Int.natCast_dvd_natCast]
