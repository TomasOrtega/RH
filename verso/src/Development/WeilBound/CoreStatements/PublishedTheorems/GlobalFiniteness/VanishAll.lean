import ReciprocityTheory.Hypotheses.GalCoh
import GroundTheory.ProfiniteCohomology.RestrictedRamification.Dimension
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CohomologicalDimensionTopologicalIsoStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConstantTermFrameKTypeCoefficientsStatement
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GelfandSpectralNormalisation.NormalisedInvariants.PoitouTateExactSecond
import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalFiniteness.Transport

noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global ReciprocityTheory.Gal Formalism.ConjugateSelfDual
open GlobalTheory.CompanionTheory.GSCd.Transport

namespace PositivityTheory.Lit1.GFVanish

/- English proof (translation)
Establish `: IsGalois F Ω` using `IsAlgClosure.isGalois F Ω`. Take `⟨K, ψ, e, he⟩` from `exists_embedded F Ω`. Use `⟨K, S.map (placeEquiv (RingOfIntegers.mapRingEquiv ψ)).toEmbedding, ?_, ⟨ψ⟩, nonempty_gal ψ e he ?_⟩` and prove the remaining obligations. Introduce `w hw`. Establish `hv : (placeEquiv (RingOfIntegers.mapRingEquiv ψ)).symm w ∈ S`.

Apply `hS` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `RingOfIntegers.mapRingEquiv ψ (l : 𝓞 F) ∈ w.asIdeal`. Rewrite using `[map_natCast]`. Conclude with `hw`. Conclude with `Finset.mem_map.2 ⟨_, hv, (placeEquiv _).apply_symm_apply w⟩`.

Introduce `v`. Simplify using the standard rewrite rules.
-/
theorem exists_gs_transport_field (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : ContainsAbove S l) :
    ∃ (K : FiniteSubfield) (S' : Finset (HeightOneSpectrum (𝓞 K.1))), ContainsAbove S' l ∧
      Nonempty (F ≃+* K.1) ∧
      Nonempty (galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F))) ≃ₜ*
        galUnramifiedOutside K.1 (AlgebraicClosure ℚ) (S' : Set (HeightOneSpectrum (𝓞 K.1)))) := by
  have : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  obtain ⟨K, ψ, e, he⟩ := exists_embedded F Ω
  classical
  refine ⟨K, S.map (placeEquiv (RingOfIntegers.mapRingEquiv ψ)).toEmbedding, ?_, ⟨ψ⟩,
    nonempty_gal ψ e he ?_⟩
  · intro w hw
    have hv : (placeEquiv (RingOfIntegers.mapRingEquiv ψ)).symm w ∈ S := by
      apply hS
      change RingOfIntegers.mapRingEquiv ψ (l : 𝓞 F) ∈ w.asIdeal
      rw [map_natCast]
      exact hw
    exact Finset.mem_map.2 ⟨_, hv, (placeEquiv _).apply_symm_apply w⟩
  · intro v
    simp

/- English proof (translation)
Take `⟨K, S', hS', ⟨ψ⟩, ⟨e⟩⟩` from `exists_gs_transport_field F Ω l S hS`. Rewrite using `[GlobalTheory.T.cohomological_dimension_topological_iso _ _ l e]`. Use `cdp_galUnramifiedOutside_le_two K (S' : Set (HeightOneSpectrum (𝓞 K.1))) Fact.out (fun v hv => hS' v hv) (hK.imp id fun h => ?_)` and prove the remaining obligations. Establish `: IsTotallyComplex F` using `h`. Set `_ : Algebra F K.1` to `ψ.toRingHom.toAlgebra`.

Conclude with `isTotallyComplex_of_algebra F K.1`.
-/
theorem cdp_gal_le_two_gen (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ContainsAbove S l) (hK : l ≠ 2 ∨ IsTotallyComplex F) :
    cdp l (galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F)))) ≤ 2 := by
  obtain ⟨K, S', hS', ⟨ψ⟩, ⟨e⟩⟩ := exists_gs_transport_field F Ω l S hS
  rw [GlobalTheory.T.cohomological_dimension_topological_iso _ _ l e]
  refine cdp_galUnramifiedOutside_le_two K (S' : Set (HeightOneSpectrum (𝓞 K.1))) Fact.out
    (fun v hv => hS' v hv) (hK.imp id fun h => ?_)
  have : IsTotallyComplex F := h
  let _ : Algebra F K.1 := ψ.toRingHom.toAlgebra
  exact isTotallyComplex_of_algebra F K.1

/- English proof (translation)
Establish `hp : l.Prime` using `Fact.out`. Establish `hcd` using `cdp_gal_le_two_gen F Ω l S hS hK`. Use `subsingleton_cohomology_of_cdp_le_two (n := l ^ r) (pow_ne_zero r hp.ne_zero) (fun q hq hqd => ?_) A hA hn` and prove the remaining obligations. Establish `hql : q = l` using `(Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow hqd)`. Substitute `hql` using the available equality.

Conclude with `hcd`.
-/
theorem subsingleton_hn_gen (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ContainsAbove S l) (hK : l ≠ 2 ∨ IsTotallyComplex F)
    (A : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F)))))
    [IsDiscreteRep A] (hA : ∀ a : A.V, (l ^ r) • a = 0) (n : ℕ) (hn : 3 ≤ n) :
    Subsingleton (cohomology A n) := by
  have hp : l.Prime := Fact.out
  have hcd := cdp_gal_le_two_gen F Ω l S hS hK
  refine subsingleton_cohomology_of_cdp_le_two (n := l ^ r) (pow_ne_zero r hp.ne_zero)
    (fun q hq hqd => ?_) A hA hn
  have hql : q = l := (Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow hqd)
  subst hql
  exact hcd

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ l _ r hK _ S hS M _ _ _ _ _ ρ hc n hn`. Take `⟨A, _, _, hA, -, -, hAn⟩` from `PositivityTheory.Lit1.GFTransport.cohDict S ρ hc`. Take `⟨en⟩` from `hAn n`. Establish `: Subsingleton (cohomology A n)` using `subsingleton_hn_gen F Ω l r S hS hK A hA n hn`. Conclude with `en.toEquiv.subsingleton`.
-/
theorem vanishAll : PositivityTheory.PoitouTateConclusion.VanishAll := by
  intro F Ω _ _ _ _ _ l _ r hK _ S hS M _ _ _ _ _ ρ hc n hn
  obtain ⟨A, _, _, hA, -, -, hAn⟩ := PositivityTheory.Lit1.GFTransport.cohDict S ρ hc
  obtain ⟨en⟩ := hAn n
  have : Subsingleton (cohomology A n) := subsingleton_hn_gen F Ω l r S hS hK A hA n hn
  exact en.toEquiv.subsingleton

end PositivityTheory.Lit1.GFVanish
