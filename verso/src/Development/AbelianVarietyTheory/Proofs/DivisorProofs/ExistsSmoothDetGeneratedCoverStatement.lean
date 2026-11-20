import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothDetGeneratedCover
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RealMult.Obj.exists_detGen_away` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsSmoothDetGeneratedCover.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.exists_smooth_det_generated_cover : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (B : Type) [CommRing B] [Algebra ℂ B]
    [Algebra.Smooth ℂ B] (R : Type) [CommRing R] [Algebra ℂ R] [IsLocalRing R] (j : B →ₐ[ℂ] R) (X : Obj F 𝔠 (Sp B)),
    ∃ (B' : Type) (_ : CommRing B') (_ : Algebra ℂ B') (_ : Algebra.Smooth ℂ B') (X₁ : Obj F 𝔠 (Sp B'))
      (_ : X₁.DetGen) (k : B →ₐ[ℂ] B') (j' : B' →ₐ[ℂ] R) (q : X₁.A.left ⟶ X.A.left),
      X₁.IsPullBy X (spMap (k : B →+* B')) q ∧ j'.comp k = j := by
  first | exact @GlobalTheory.RealMult.Obj.exists_detGen_away | exact GlobalTheory.RealMult.Obj.exists_detGen_away | (intros; apply GlobalTheory.RealMult.Obj.exists_detGen_away <;> assumption)
