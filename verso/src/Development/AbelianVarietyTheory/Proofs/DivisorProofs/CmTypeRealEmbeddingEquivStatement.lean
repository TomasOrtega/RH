import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeRealEmbeddingEquiv
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
open NumberField GlobalTheory.CMVal GlobalTheory.LatJet GlobalTheory.RealMult
open GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex (latMod polMod dualLat TrInt bar)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCmTypeRealEmbeddingEquiv.lean&line=64#L64)
-/
theorem _root_.GlobalTheory.T.cm_type_real_embedding_equiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ →
    ∃ (e : Fin (Module.finrank ℚ (FR E)) ≃ I) (e' : Fin (Module.finrank ℚ (FR E)) ≃ (FR E →+* ℝ)),
      ∀ j (x : FR E), ((e' j x : ℝ) : ℂ) = φ (e j) (x : E) := by
  first | exact @GlobalTheory.CMEquiv.cmType_equiv | exact GlobalTheory.CMEquiv.cmType_equiv | (intros; apply GlobalTheory.CMEquiv.cmType_equiv <;> assumption)
