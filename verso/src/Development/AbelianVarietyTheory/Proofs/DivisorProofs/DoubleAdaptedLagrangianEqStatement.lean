import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleAdaptedLagrangianEq
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtVecMulVecRight
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchSch GlobalTheory.ArchSchB
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDoubleAdaptedLagrangianEq.lean&line=119#L119)
-/
theorem _root_.GlobalTheory.T.double_adapted_lagrangian_eq : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E) {n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} (M : Model σ X W) (M₁ : Model σ X₁ W₁) (H : Plane E n n₁) (H' : Plane E d d₁),
    B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → H.IsAdapted σ B X X₁ i₀ i₁ → H'.IsAdapted σ B W W₁ j₀ j₁ →
    ∀ l ∈ lagSetB M M₁ H H', ∀ l' ∈ lagSetB M M₁ H H', trP F _ l.1 l'.2 = trP F _ l'.1 l.2 := by
  first | exact @GlobalTheory.ArchSchB.lagSetB_isotropic | exact GlobalTheory.ArchSchB.lagSetB_isotropic | (intros; apply GlobalTheory.ArchSchB.lagSetB_isotropic <;> assumption)
