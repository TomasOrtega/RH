import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalAffineDeterminantGenerator
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitObj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLocalAffineDeterminantGenerator.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.local_affine_determinant_generator : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (M : Scheme.{0}) (U : Obj F 𝔠 M) (y : M),
    ∃ (W : M.Opens) (hW : IsAffineOpen W), y ∈ W ∧ ∃ (Y : Obj F 𝔠 (Sp Γ(M, W))) (φ : Y.A.left ⟶ U.A.left),
      Y.IsPullBy U hW.fromSpec φ ∧ Nonempty Y.DetGen := by
  first | exact @GlobalTheory.RealMult.Obj.exists_affine_nbhd_detGen_basicOpen | exact GlobalTheory.RealMult.Obj.exists_affine_nbhd_detGen_basicOpen | (intros; apply GlobalTheory.RealMult.Obj.exists_affine_nbhd_detGen_basicOpen <;> assumption)
