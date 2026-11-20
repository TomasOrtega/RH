import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticCharacterExtendsToIdeleClass
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsToQuadraticSignPowOfRestrictsToQuadrati
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemNormGroupIffEverywhereNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryCharOfOpenSubgroupAndHom
import Formalism.UnipotentAdelicQuotients.ThmBInHecke
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsNontrivialHeckeChar
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ArchSignChar.exists_arch_sign_char` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FQuadraticCharacterExtendsToIdeleClass.lean&line=140#L140)
-/
theorem _root_.GlobalTheory.T.quadratic_character_extends_to_idele_class : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ η : (AdeleRing (𝓞 F) F)ˣ →* Circle, Continuous η → (∀ b, η (b * b) = 1) →
    ∃ ψ : (AdeleRing (𝓞 F) F ⊗[F] E)ˣ →* Circle, Continuous ψ ∧ (∀ b, ψ (ideleMap F E b) = 1 ∨ ψ (ideleMap F E b) = -1) ∧
      ∀ b : (AdeleRing (𝓞 F) F)ˣ, (b : AdeleRing (𝓞 F) F).2 = 1 → ψ (ideleMap F E b) = η b := by
  first | exact @GlobalTheory.ArchSignChar.exists_arch_sign_char | exact GlobalTheory.ArchSignChar.exists_arch_sign_char | (intros; apply GlobalTheory.ArchSignChar.exists_arch_sign_char <;> assumption)
