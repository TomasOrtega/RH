import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FerrandPushoutGoodBasicOpen
import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSchemeOfThickenings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageUpOpen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FerrandPush.basicOpen_fibπ_mem_good` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFerrandPushoutGoodBasicOpen.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.ferrand_pushout_good_basic_open : ∀ {Y₀ Y₁ Y₂ : Scheme.{0}} (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂) [IsClosedImmersion i₁] [Surjective i₁] [IsClosedImmersion i₂] [Surjective i₂], ∀ U ∈ GlobalTheory.FerrandPush.good i₁ i₂, ∀ a : (GlobalTheory.FerrandPush.fib i₁ i₂).obj (op U), Y₀.basicOpen (((GlobalTheory.FerrandPush.fibπ i₁ i₂).app (op U)).hom a) ∈ GlobalTheory.FerrandPush.good i₁ i₂ := by
  first | exact @GlobalTheory.FerrandPush.basicOpen_fibπ_mem_good | exact GlobalTheory.FerrandPush.basicOpen_fibπ_mem_good | (intros; apply GlobalTheory.FerrandPush.basicOpen_fibπ_mem_good; all_goals assumption)
