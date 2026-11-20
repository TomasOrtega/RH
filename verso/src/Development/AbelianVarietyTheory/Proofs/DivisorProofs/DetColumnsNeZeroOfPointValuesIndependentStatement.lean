import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetColumnsNeZeroOfPointValuesIndependent
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianMultiplicationFlatColumnsEvalStatement
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDetColumnsNeZeroOfPointValuesIndependent.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.det_columns_ne_zero_of_pointValues_independent : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (E A' : Type) [Field E] [Algebra F E] [AddCommGroup A'] [Module E A'] (s : Fin S.D → Fin S.N → E) (δ : ℕ) (Φ : S.Flat E A' s δ) (d : ℕ) (b : Module.Basis (Fin d) F (S.V S.T)) (c : Fin d → A →ₗ[F] F), S.IsCo b c → ∀ (col : Fin d → S.Col) (u : Fin (S.D + 1) × Fin S.N → E), LinearIndependent E (fun k => word Φ.mul (fun q j => u ((col k).β q, j)) (Φ.ι (col k).x)) → S.det c col ≠ 0 := by
  first | exact @GlobalTheory.HSShort.DetNe.det_ne_zero_of_indep | exact GlobalTheory.HSShort.DetNe.det_ne_zero_of_indep | (intros; apply GlobalTheory.HSShort.DetNe.det_ne_zero_of_indep <;> assumption)
