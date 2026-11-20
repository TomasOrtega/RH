import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSpecialUnitaryMem
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarProd
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Filter Topology
open scoped TensorProduct ENNReal
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdLat GlobalTheory.Published GlobalTheory.TamUnf
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRationalSpecialUnitaryMem.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.rational_special_unitary_mem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E)
    (Ψ : Finset (E →+* ℂ)) (θ : Ψ → (Ainf (maximalRealSubfield E) ⊗[maximalRealSubfield E] E →+* ℂ)),
    (∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) → (∀ ρ : Ψ, IsInfEmb ρ.1 (θ ρ)) →
    ∀ γ : SUAdelic (IsCMField.complexConj E).toAlgHom Gᵀ,
      γ ∈ (SURat (IsCMField.complexConj E).toAlgHom Gᵀ).subgroupOf (SUAdelic (IsCMField.complexConj E).toAlgHom Gᵀ) →
      ∃ δ : Matrix (Fin r) (Fin r) E, IsSA G (GlobalTheory.UCls.ratM (maximalRealSubfield E) δ) ∧
        (∀ ρ : Ψ, infMat (IsCMField.complexConj E).toAlgHom Gᵀ (θ ρ) γ.1 = δ.map ρ.1) ∧
        finMat (IsCMField.complexConj E).toAlgHom Gᵀ γ.1 = GlobalTheory.UCls.ratM (maximalRealSubfield E) δ := by
  first | exact @GlobalTheory.TamUnf.RatIn.exists_rat | exact GlobalTheory.TamUnf.RatIn.exists_rat | (intros; apply GlobalTheory.TamUnf.RatIn.exists_rat <;> assumption)
