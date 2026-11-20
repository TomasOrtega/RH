import Development.EtaleCohomology.EtaleSheaves.ChowCut
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing

open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.E.ImgPf

/- English proof (translation)
Introduce `A _ Z X h p _ hh hZ`. Use `hh` as an intermediate fact. Use `hZ` as an intermediate fact. Establish `: QuasiCompact h` using `inferInstance`. Establish `: IsIntegralHom (h.toImage ≫ h.imageι)` using `by rw [Scheme.Hom.toImage_imageι]; exact hh`.

Use `⟨h.image, h.toImage, h.imageι ≫ p, inferInstance, inferInstance, IsIntegralHom.of_comp h.toImage h.imageι, inferInstance, ?_⟩` and prove the remaining obligations. Rewrite using `[Scheme.Hom.toImage_imageι_assoc]`.
-/
theorem Img_of : LateralTheory.E.ChowCut.Img := by
  intro A _ Z X h p _ hh hZ
  have := hh
  have := hZ
  have : QuasiCompact h := inferInstance
  have : IsIntegralHom (h.toImage ≫ h.imageι) := by rw [Scheme.Hom.toImage_imageι]; exact hh
  refine ⟨h.image, h.toImage, h.imageι ≫ p, inferInstance, inferInstance,
    IsIntegralHom.of_comp h.toImage h.imageι, inferInstance, ?_⟩
  rw [Scheme.Hom.toImage_imageι_assoc]

end LateralTheory.E.ImgPf
