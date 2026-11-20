import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionHermitianLinearFormFgModule
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FormSection.exists_section` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsSectionHermitianLinearFormFgModule.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.exists_section_hermitianLinearForm_fg_module : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)), L.FG →
    ∀ x : Fin n → E, (∃ z ∈ L, form σ J z x ≠ 0) →
    ∃ y₀ : Fin n → E, form σ J y₀ x = 1 ∧ ∀ z ∈ L, form σ J z x • y₀ ∈ L := by
  first | exact @GlobalTheory.FormSection.exists_section | exact GlobalTheory.FormSection.exists_section | (intros; apply GlobalTheory.FormSection.exists_section <;> assumption)
