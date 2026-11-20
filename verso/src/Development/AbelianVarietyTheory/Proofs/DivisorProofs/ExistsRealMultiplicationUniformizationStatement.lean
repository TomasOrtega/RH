import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealMultiplicationUniformization
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RealMult.Obj.exists_holUnif_ringHom_lift` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsRealMultiplicationUniformization.lean&line=180#L180)
-/
theorem _root_.GlobalTheory.T.exists_real_multiplication_uniformization : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (X : Obj F 𝔠 (Sp ℂ)), ∃ (L : LB X.A.left) (u : HolUnif X.A L (Module.finrank ℚ F)) (Fa : 𝓞 F →+* Module.End ℂ (Fin (Module.finrank ℚ F) → ℂ)), ∀ (a : 𝓞 F) (z : Fin (Module.finrank ℚ F) → ℂ), u.ex (Fa a z) = u.ex z ≫ X.rm.act a := by
  first | exact @GlobalTheory.RealMult.Obj.exists_holUnif_ringHom_lift | exact GlobalTheory.RealMult.Obj.exists_holUnif_ringHom_lift | (intros; apply GlobalTheory.RealMult.Obj.exists_holUnif_ringHom_lift <;> assumption)
