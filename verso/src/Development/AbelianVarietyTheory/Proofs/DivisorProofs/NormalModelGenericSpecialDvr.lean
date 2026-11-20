import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroPresZeroMod
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsLocalizedModuleGermLinearPointOfPrime
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfHomPull
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.HigherDirectImagesVanishOfIsAffineHom

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open GlobalTheory GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.FrobFilt

namespace GlobalTheory.GenSpecialDvr

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Establish `hm : ϖ ∈ maximalIdeal O` using `hϖ.not_isUnit`. Establish `hg` using `B.gen_eq_basicOpen hϖ.ne_zero hm`. Take `⟨W, hW, h, -⟩` from `exists_isAffineOpen_mem_and_subset (U := ⊤) (x := η) trivial`. Establish `: Nonempty W` using `⟨⟨η, h⟩⟩`.

Establish `: IsNoetherianRing Γ(B.X, W)` using `IsLocallyNoetherian.component_noetherian ⟨W, hW⟩`. Set `a : Γ(B.X, W)` to `B.X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (B.const ϖ)`. Establish `hD : B.X.basicOpen a = W ⊓ B.gen`. Rewrite using `[hg]`. Conclude with `Scheme.basicOpen_res _ _ _`.

Establish `hin : ∀ r : PrimeSpectrum Γ(B.X, W), hW.fromSpec r ∈ W` using `fun r => by`. Establish `: hW.fromSpec r ∈ Set.range hW.fromSpec` using `⟨r, rfl⟩`. Rewrite `this` using `[hW.range_fromSpec]`. Then use the resulting hypothesis. Establish `key : ∀ r : PrimeSpectrum Γ(B.X, W), hW.fromSpec r ∈ B.gen ↔ a ∉ r.asIdeal` using `fun r => by`. Establish `h1 : hW.fromSpec r ∈ B.X.basicOpen a ↔ a ∉ r.asIdeal`.

Express the relevant statement in the definitionally equal form `r ∈ hW.fromSpec ⁻¹ᵁ B.X.basicOpen a ↔ _`. Rewrite using `[hW.fromSpec_preimage_basicOpen]`. Both sides reduce to the same expression. Rewrite using `[← h1, hD]`. Conclude with `⟨fun h => ⟨hin r, h⟩, fun h => h.2⟩`.

Set `q : PrimeSpectrum Γ(B.X, W)` to `hW.primeIdealOf ⟨η, h⟩`. Establish `hq : hW.fromSpec q = η` using `hW.fromSpec_primeIdealOf ⟨η, h⟩`. Establish `haq : a ∈ q.asIdeal`. Assume the negation of the conclusion as `H`. Conclude with `hη.1 (hq ▸ (key q).2 H)`.

Establish `ha : a ≠ 0` using `fun H => by`. Establish `h0 : genericPoint B.X ∈ W ⊓ B.gen` using `⟨((genericPoint_spec B.X).specializes trivial).mem_open W.isOpen h, B.genericPoint_mem_gen⟩`. Rewrite `h0` using `[← hD, H, Scheme.basicOpen_zero]`. Conclude with `h0`. Establish `hmin : q.asIdeal ∈ (Ideal.span {a}).minimalPrimes`.

Use `⟨⟨q.isPrime, (Ideal.span_singleton_le_iff_mem _).2 haq⟩, fun P hP hle => ?_⟩` and prove the remaining obligations. Set `r : PrimeSpectrum Γ(B.X, W)` to `⟨P, hP.1⟩`. Establish `h1 : hW.fromSpec r ∉ B.gen` using `fun H => (key r).1 H ((Ideal.span_singleton_le_iff_mem _).1 hP.2)`. Establish `h2 : hW.fromSpec r ⤳ hW.fromSpec q` using `((PrimeSpectrum.le_iff_specializes r q).1 hle).map hW.fromSpec.continuous`. Establish `h3 : hW.fromSpec r = hW.fromSpec q` using `(hη.2 _ h1 (hq ▸ h2)).trans hq.symm`.

Establish `h4 : r = q` using `hW.fromSpec.isOpenEmbedding.injective h3`. Conclude with `(congrArg PrimeSpectrum.asIdeal h4).ge`. Establish `hle : q.asIdeal.height ≤ 1` using `Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hmin`. Establish `hne : q.asIdeal.height ≠ 0` using `fun H => by`. Use `q.isPrime` as an intermediate fact.

Establish `hb : q.asIdeal = ⊥`. Simplify using `using H`. Conclude with `ha (by simpa [hb] using haq)`. Establish `h1 : q.asIdeal.height = 1` using `le_antisymm hle (Order.one_le_iff_ne_zero.2 hne)`. Use `letI : Algebra Γ(B.X, W) (B.X.presheaf.stalk η) := TopCat.Presheaf.algebra_section_stalk B.X.presheaf (⟨η, h⟩ : W)`.

Establish `hl : IsLocalization.AtPrime (B.X.presheaf.stalk η) q.asIdeal` using `hW.isLocalization_stalk ⟨η, h⟩`. Establish `hd` using `IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal (B.X.presheaf.stalk η)`. Rewrite `hd` using `[ringKrullDim_stalk_eq_coheight, h1]`. Conclude with `hd` after adjusting the coercions.
-/
theorem coheight_eq_one (B : GlobalTheory.Vert.Model O) (η : B.X) (hη : IsGenSpecial B η) :
    Order.coheight η = 1 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hm : ϖ ∈ maximalIdeal O := hϖ.not_isUnit
  have hg := B.gen_eq_basicOpen hϖ.ne_zero hm
  obtain ⟨W, hW, h, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := η) trivial
  have : Nonempty W := ⟨⟨η, h⟩⟩
  have : IsNoetherianRing Γ(B.X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  let a : Γ(B.X, W) := B.X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (B.const ϖ)
  have hD : B.X.basicOpen a = W ⊓ B.gen := by
    rw [hg]; exact Scheme.basicOpen_res _ _ _
  have hin : ∀ r : PrimeSpectrum Γ(B.X, W), hW.fromSpec r ∈ W := fun r => by
    have : hW.fromSpec r ∈ Set.range hW.fromSpec := ⟨r, rfl⟩
    rwa [hW.range_fromSpec] at this
  have key : ∀ r : PrimeSpectrum Γ(B.X, W), hW.fromSpec r ∈ B.gen ↔ a ∉ r.asIdeal := fun r => by
    have h1 : hW.fromSpec r ∈ B.X.basicOpen a ↔ a ∉ r.asIdeal := by
      change r ∈ hW.fromSpec ⁻¹ᵁ B.X.basicOpen a ↔ _
      rw [hW.fromSpec_preimage_basicOpen]
      rfl
    rw [← h1, hD]
    exact ⟨fun h => ⟨hin r, h⟩, fun h => h.2⟩
  let q : PrimeSpectrum Γ(B.X, W) := hW.primeIdealOf ⟨η, h⟩
  have hq : hW.fromSpec q = η := hW.fromSpec_primeIdealOf ⟨η, h⟩
  have haq : a ∈ q.asIdeal := by
    by_contra H
    exact hη.1 (hq ▸ (key q).2 H)
  have ha : a ≠ 0 := fun H => by
    have h0 : genericPoint B.X ∈ W ⊓ B.gen :=
      ⟨((genericPoint_spec B.X).specializes trivial).mem_open W.isOpen h, B.genericPoint_mem_gen⟩
    rw [← hD, H, Scheme.basicOpen_zero] at h0
    exact h0
  have hmin : q.asIdeal ∈ (Ideal.span {a}).minimalPrimes := by
    refine ⟨⟨q.isPrime, (Ideal.span_singleton_le_iff_mem _).2 haq⟩, fun P hP hle => ?_⟩
    let r : PrimeSpectrum Γ(B.X, W) := ⟨P, hP.1⟩
    have h1 : hW.fromSpec r ∉ B.gen := fun H =>
      (key r).1 H ((Ideal.span_singleton_le_iff_mem _).1 hP.2)
    have h2 : hW.fromSpec r ⤳ hW.fromSpec q :=
      ((PrimeSpectrum.le_iff_specializes r q).1 hle).map hW.fromSpec.continuous
    have h3 : hW.fromSpec r = hW.fromSpec q := (hη.2 _ h1 (hq ▸ h2)).trans hq.symm
    have h4 : r = q := hW.fromSpec.isOpenEmbedding.injective h3
    exact (congrArg PrimeSpectrum.asIdeal h4).ge
  have hle : q.asIdeal.height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hmin
  have hne : q.asIdeal.height ≠ 0 := fun H => by
    have := q.isPrime
    have hb : q.asIdeal = ⊥ := by
      simpa using H
    exact ha (by simpa [hb] using haq)
  have h1 : q.asIdeal.height = 1 := le_antisymm hle (Order.one_le_iff_ne_zero.2 hne)
  letI : Algebra Γ(B.X, W) (B.X.presheaf.stalk η) :=
    TopCat.Presheaf.algebra_section_stalk B.X.presheaf (⟨η, h⟩ : W)
  have hl : IsLocalization.AtPrime (B.X.presheaf.stalk η) q.asIdeal :=
    hW.isLocalization_stalk ⟨η, h⟩
  have hd := IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal (B.X.presheaf.stalk η)
  rw [ringKrullDim_stalk_eq_coheight, h1] at hd
  exact_mod_cast hd

/- English proof (translation)
Introduce `_ _ _ _ B _ η hη` and use `GlobalTheory.IsNormalScheme.isDiscreteValuationRing_stalk (coheight_eq_one B η hη)`.
-/
theorem isDiscreteValuationRing_stalk : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ η : B.X, IsGenSpecial B η → IsDiscreteValuationRing (B.X.presheaf.stalk η) :=
  fun _ _ _ _ B _ η hη =>
    GlobalTheory.IsNormalScheme.isDiscreteValuationRing_stalk (coheight_eq_one B η hη)

end GlobalTheory.GenSpecialDvr
