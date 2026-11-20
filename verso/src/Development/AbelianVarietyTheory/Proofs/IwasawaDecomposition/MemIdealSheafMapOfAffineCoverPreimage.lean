import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkIdComapOfAffine
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open scoped TensorProduct

namespace GlobalTheory.IdealPushCover

/- English proof (translation)
Introduce `X Y' ρ _ I U ι W hW hcov b hb`. Establish `hk : ∀ V : Y'.affineOpens, I.ideal V = RingHom.ker (I.subschemeι.app V.1).hom` using `fun V => by`. Rewrite using `[← Scheme.Hom.ker_apply, Scheme.IdealSheafData.ker_subschemeι]`. Rewrite using `[Scheme.IdealSheafData.map, Scheme.Hom.ker_apply, RingHom.mem_ker, Scheme.Hom.comp_app]`. Express the relevant statement in the definitionally equal form `(I.subschemeι.app (ρ ⁻¹ᵁ U.1)).hom ((ρ.app U.1).hom b) = 0`.

Use `GlobalTheory.Cartier.ext_germ fun z hz => ?_` and prove the remaining obligations. Rewrite using `[map_zero]`. Establish `hz' : I.subschemeι z ∈ ⨆ i, (W i : Y'.Opens)` using `hcov hz`. Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.1 hz'`. Establish `hzi : z ∈ I.subschemeι ⁻¹ᵁ (W i : Y'.Opens)` using `hi`.

Establish `h0 : (I.subschemeι.app (W i).1).hom ((ρ.appLE U (W i) (hW i)).hom b) = 0`. Use `hb i` as an intermediate fact. Rewrite `this` using `[hk, RingHom.mem_ker]`. Conclude with `this`. Establish `e1 : (ρ.appLE U (W i) (hW i)).hom b = resG Y' (hW i) ((ρ.app U.1).hom b)` using `rfl`.

Rewrite `h0` using `[e1, GlobalTheory.Cartier.app_resG]`. Rewrite using `[← GlobalTheory.Cartier.germ_resG (I.subschemeι.preimage_mono (hW i)) z hzi, h0, map_zero]`.
-/
theorem mem_map_ideal_of_cover : ∀ {X Y' : Scheme.{0}} (ρ : Y' ⟶ X) [QuasiCompact ρ] (I : Y'.IdealSheafData) (U : X.affineOpens) {ι : Type} (W : ι → Y'.affineOpens) (hW : ∀ i, (W i : Y'.Opens) ≤ ρ ⁻¹ᵁ (U : X.Opens)), ρ ⁻¹ᵁ (U : X.Opens) ≤ ⨆ i, (W i : Y'.Opens) → ∀ b : Γ(X, U), (∀ i, (ρ.appLE U (W i) (hW i)).hom b ∈ I.ideal (W i)) → b ∈ (I.map ρ).ideal U := by
  intro X Y' ρ _ I U ι W hW hcov b hb
  have hk : ∀ V : Y'.affineOpens, I.ideal V = RingHom.ker (I.subschemeι.app V.1).hom := fun V => by
    rw [← Scheme.Hom.ker_apply, Scheme.IdealSheafData.ker_subschemeι]
  rw [Scheme.IdealSheafData.map, Scheme.Hom.ker_apply, RingHom.mem_ker, Scheme.Hom.comp_app]
  change (I.subschemeι.app (ρ ⁻¹ᵁ U.1)).hom ((ρ.app U.1).hom b) = 0
  refine GlobalTheory.Cartier.ext_germ fun z hz => ?_
  rw [map_zero]
  have hz' : I.subschemeι z ∈ ⨆ i, (W i : Y'.Opens) := hcov hz
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz'
  have hzi : z ∈ I.subschemeι ⁻¹ᵁ (W i : Y'.Opens) := hi
  have h0 : (I.subschemeι.app (W i).1).hom ((ρ.appLE U (W i) (hW i)).hom b) = 0 := by
    have := hb i
    rw [hk, RingHom.mem_ker] at this
    exact this
  have e1 : (ρ.appLE U (W i) (hW i)).hom b = resG Y' (hW i) ((ρ.app U.1).hom b) := rfl
  rw [e1, GlobalTheory.Cartier.app_resG] at h0
  rw [← GlobalTheory.Cartier.germ_resG (I.subschemeι.preimage_mono (hW i)) z hzi, h0, map_zero]

end GlobalTheory.IdealPushCover
