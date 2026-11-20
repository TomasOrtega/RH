import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsArchAdeleTensorEquivComplexCmType
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mem.VolInfIso.exists_infAdele_equiv` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsArchAdeleTensorEquivComplexCmType.lean&line=76#L76)
-/
theorem _root_.GlobalTheory.T.exists_archAdeleTensor_equiv_complex_cmType : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (I : Type) [Fintype I] (τ : I → (E →+* ℂ)) (θ : I → (Ainf F ⊗[F] E →+* ℂ)), IsCMExt F E σ → IsCMFam τ → (∀ i, IsInfEmb (τ i) (θ i)) → ∃ e : (Ainf F ⊗[F] E) ≃+* (I → ℂ), (∀ x i, e x i = θ i x) ∧ Continuous e ∧ Continuous e.symm ∧ ∀ x i, e (sigR (Ainf F) σ x) i = star (e x i) := by
  first | exact @GlobalTheory.Mem.VolInfIso.exists_infAdele_equiv | exact GlobalTheory.Mem.VolInfIso.exists_infAdele_equiv | (intros; apply GlobalTheory.Mem.VolInfIso.exists_infAdele_equiv <;> assumption)
