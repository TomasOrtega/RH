import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg

open Polynomial UpperTheory.V.W

/- English proof (translation)
Introduce `Γ R _ _ _ _ I hI f`. Rewrite `hI` using `[isAdic_iff]`. Take `⟨hopen, hsmall⟩` from `hI`. Unfold `UpperTheory.V.Alg.AdicCont`. Prove the components needed by the constructor for the conclusion.

Introduce `hf`. Rewrite using `[continuous_iff_continuousAt]`. Introduce `g`. Rewrite using `[ContinuousAt, tendsto_sub_nhds_zero_iff.symm]`. Introduce `s hs`.

Take `⟨N, hN⟩` from `hsmall s hs`. Establish `hloc` using `(IsLocallyConstant.iff_eventually_eq _).mp (hf N) g`. Rewrite using `[Filter.mem_map]`. Use `filter_upwards [hloc] with y hy`. Conclude with `hN (Ideal.Quotient.eq.mp hy)`.

Introduce `hf N`. Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `g`. Establish `hO : IsOpen {r : R | r - f g ∈ I ^ N}` using `(hopen N).preimage (continuous_id.sub continuous_const)`. Establish `hmem : f g ∈ {r : R | r - f g ∈ I ^ N}`.

Simplify using the standard rewrite rules. Use `filter_upwards [hf.continuousAt (hO.mem_nhds hmem)] with y hy`. Conclude with `Ideal.Quotient.eq.mpr hy`.
-/
theorem UpperTheory.V.AlgebraTools.Det.adicContIff :
    ∀ {Γ R : Type} [TopologicalSpace Γ] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (I : Ideal R), IsAdic I →
    ∀ f : Γ → R, UpperTheory.V.Alg.AdicCont I f ↔ Continuous f := by
  intro Γ R _ _ _ _ I hI f
  rw [isAdic_iff] at hI
  obtain ⟨hopen, hsmall⟩ := hI
  unfold UpperTheory.V.Alg.AdicCont
  constructor
  · intro hf
    rw [continuous_iff_continuousAt]
    intro g
    rw [ContinuousAt, tendsto_sub_nhds_zero_iff.symm]
    intro s hs
    obtain ⟨N, hN⟩ := hsmall s hs
    have hloc := (IsLocallyConstant.iff_eventually_eq _).mp (hf N) g
    rw [Filter.mem_map]
    filter_upwards [hloc] with y hy
    exact hN (Ideal.Quotient.eq.mp hy)
  · intro hf N
    rw [IsLocallyConstant.iff_eventually_eq]
    intro g
    have hO : IsOpen {r : R | r - f g ∈ I ^ N} :=
      (hopen N).preimage (continuous_id.sub continuous_const)
    have hmem : f g ∈ {r : R | r - f g ∈ I ^ N} := by
      simp
    filter_upwards [hf.continuousAt (hO.mem_nhds hmem)] with y hy
    exact Ideal.Quotient.eq.mpr hy
