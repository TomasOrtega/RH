import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Divisors.PreUMono
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyBasisBijectiveStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

/- English proof (translation)
Introduce `R' _ X X' φ _ s'`. Establish `hB : ∀ {U : TopologicalSpace.Opens X} {x : X}, x ∈ U → ∃ U' ∈ X.affineOpens, x ∈ U' ∧ U' ≤ U` using `TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens`. Use `GlobalTheory.T.structureSheafCohomology_basis_bijective R' X' s' X.affineOpens (preU φ) (preU_mono φ) ?_ ?_` and prove the remaining obligations. Introduce `U x hx`. Take `⟨W, hW, hWU⟩` from `(φ.isClosedEmbedding).isInducing.isOpen_iff.mp U.1.2`.

Establish `hxW : φ.base x ∈ W`. Establish `: x ∈ φ.base ⁻¹' W` using `by rw [hWU]; exact hx`. Conclude with `this`. Take `⟨V, hV, hxV, hVW⟩` from `hB (U := ⟨W, hW⟩) hxW`. Use `⟨⟨V, hV⟩, hxV, ?_⟩` and prove the remaining obligations.

Introduce `y hy`. Establish `: y ∈ φ.base ⁻¹' W` using `hVW hy`. Rewrite `this` using `[hWU]`. Conclude with `this`. Introduce `a b x ha hb`.

Take `⟨V, hV, hxV, hVW⟩` from `hB (U := a.1 ⊓ b.1) ⟨ha, hb⟩`. Conclude with `⟨⟨V, hV⟩, fun y hy ↦ (hVW hy).1, fun y hy ↦ (hVW hy).2, hxV⟩`.
-/
theorem preRes_bijective : ∀ (R' : Type) [CommRing R'] (X X' : Scheme.{0}) (φ : X' ⟶ X) [IsClosedImmersion φ] (s' : X' ⟶ Sp R'), Function.Bijective (preRes φ s').pull1 ∧ Function.Bijective (preRes φ s').pull2 ∧ (CohomZeroIsConstants (OAff s') → CohomZeroIsConstants (OPre φ s')) := by
  intro R' _ X X' φ _ s'
  have hB : ∀ {U : TopologicalSpace.Opens X} {x : X}, x ∈ U → ∃ U' ∈ X.affineOpens, x ∈ U' ∧ U' ≤ U :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
  refine GlobalTheory.T.structureSheafCohomology_basis_bijective R' X' s' X.affineOpens (preU φ) (preU_mono φ) ?_ ?_
  · intro U x hx
    obtain ⟨W, hW, hWU⟩ := (φ.isClosedEmbedding).isInducing.isOpen_iff.mp U.1.2
    have hxW : φ.base x ∈ W := by
      have : x ∈ φ.base ⁻¹' W := by rw [hWU]; exact hx
      exact this
    obtain ⟨V, hV, hxV, hVW⟩ := hB (U := ⟨W, hW⟩) hxW
    refine ⟨⟨V, hV⟩, hxV, ?_⟩
    intro y hy
    have : y ∈ φ.base ⁻¹' W := hVW hy
    rw [hWU] at this
    exact this
  · intro a b x ha hb
    obtain ⟨V, hV, hxV, hVW⟩ := hB (U := a.1 ⊓ b.1) ⟨ha, hb⟩
    exact ⟨⟨V, hV⟩, fun y hy ↦ (hVW hy).1, fun y hy ↦ (hVW hy).2, hxV⟩

end GlobalTheory.AbCoh
