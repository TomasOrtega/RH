import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviElementUnique
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLeviLeviElt
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThKCtFin

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LeviUniq.levi_unique` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLeviElementUnique.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.levi_element_unique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (d r s : ℕ) (W : Spc F E d), W.IsSkew σ B r s → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ (t : (AE F E)ˣ) (m m' : UA σ W.J), IsLevi (W₁ := W₁) H' t 1 m → IsLevi (W₁ := W₁) H' t 1 m' → m = m' := by
  first | exact @GlobalTheory.LeviUniq.levi_unique | exact GlobalTheory.LeviUniq.levi_unique | (intros; apply GlobalTheory.LeviUniq.levi_unique <;> assumption)
