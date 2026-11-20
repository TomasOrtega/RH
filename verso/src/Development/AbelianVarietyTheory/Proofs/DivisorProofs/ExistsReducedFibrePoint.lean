import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SpecialFibreUnits
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits GlobalTheory.Cartier

namespace GlobalTheory

/- English proof (translation)
Introduce `O _ _ _ ϖ hϖ Z f z hz`. Establish `h1 : ϖ ∈ (f z).asIdeal`. Establish `: z ∉ f ⁻¹ᵁ (Spec (.of O)).basicOpen ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)`. Rewrite using `[Scheme.preimage_basicOpen_top]` and apply the resulting hypothesis. Establish `h2 : f z ∉ (Spec (.of O)).basicOpen ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)` using `this`.

Rewrite `h2` using `[basicOpen_eq_of_affine (R := CommRingCat.of O) ϖ]`. Assume the negation of the conclusion as `h`. Conclude with `h2 ((PrimeSpectrum.mem_basicOpen _ _).2 h)`. Establish `hmax : (f z).asIdeal = IsLocalRing.maximalIdeal O`. Apply `le_antisymm` to reduce the goal to its premises.

Conclude with `IsLocalRing.le_maximalIdeal (f z).isPrime.ne_top`. Rewrite using `[(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.span_le]`. Simplify using `using h1`. Set `k` to `IsLocalRing.ResidueField O`. Set `pt : Spec (.of k)` to `(⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum k)`.

Establish `hpt : f z = Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)) pt`. Apply `PrimeSpectrum.ext` to reduce the goal to its premises. Rewrite using `[hmax]`. Use `show IsLocalRing.maximalIdeal O = Ideal.comap (IsLocalRing.residue O) ⊥`. Rewrite using `[← RingHom.ker_eq_comap_bot, IsLocalRing.ker_residue]`.

Take `⟨p, hp, -⟩` from `Scheme.Pullback.exists_preimage_pullback (f := f) z pt hpt`. Establish `hsupp : p ∈ Set.range (specialFibre f).nilradical.subschemeι`. Rewrite using `[Scheme.IdealSheafData.range_subschemeι, Scheme.support_nilradical]`. Discharge the goal by the elementary cases of `trivial`. Take `⟨y, hy⟩` from `hsupp`.

Use `⟨y, ?_⟩` and prove the remaining obligations. Use `show (specialι f) ((specialFibre f).nilradical.subschemeι y) = z`. Rewrite using `[hy]`. Conclude with `hp`.
-/
theorem exists_reducedSpecialFibre_of_not_mem_basicOpen : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (Z : Scheme.{0}) (f : Z ⟶ Spec (.of O)) (z : Z),
  z ∉ Z.basicOpen (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) → ∃ y : reducedSpecialFibre f, reducedSpecialι f y = z := by
  intro O _ _ _ ϖ hϖ Z f z hz
  have h1 : ϖ ∈ (f z).asIdeal := by
    have : z ∉ f ⁻¹ᵁ (Spec (.of O)).basicOpen ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ) := by
      rwa [Scheme.preimage_basicOpen_top]
    have h2 : f z ∉ (Spec (.of O)).basicOpen ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ) := this
    rw [basicOpen_eq_of_affine (R := CommRingCat.of O) ϖ] at h2
    by_contra h
    exact h2 ((PrimeSpectrum.mem_basicOpen _ _).2 h)
  have hmax : (f z).asIdeal = IsLocalRing.maximalIdeal O := by
    apply le_antisymm
    · exact IsLocalRing.le_maximalIdeal (f z).isPrime.ne_top
    · rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.span_le]
      simpa using h1
  let k := IsLocalRing.ResidueField O
  let pt : Spec (.of k) := (⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum k)
  have hpt : f z = Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)) pt := by
    apply PrimeSpectrum.ext
    rw [hmax]
    show IsLocalRing.maximalIdeal O = Ideal.comap (IsLocalRing.residue O) ⊥
    rw [← RingHom.ker_eq_comap_bot, IsLocalRing.ker_residue]
  obtain ⟨p, hp, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) z pt hpt
  have hsupp : p ∈ Set.range (specialFibre f).nilradical.subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.support_nilradical]
    trivial
  obtain ⟨y, hy⟩ := hsupp
  refine ⟨y, ?_⟩
  show (specialι f) ((specialFibre f).nilradical.subschemeι y) = z
  rw [hy]
  exact hp

end GlobalTheory
