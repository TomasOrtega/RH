import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsConjPolynomialDefiniteUnitaryRational
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UnitaryBC.exists_conj_polyFun` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FExistsConjPolynomialDefiniteUnitaryRational.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.exists_conj_polynomial_definiteUnitary_rational : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (σ : ℂ ≃+* ℂ), ∀ p ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}, ∃ p' ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}, ∀ γ ∈ ratU E n, ∀ k : infU E n, cInf k.1 = cInf γ → p' k = σ (p k) := by
  first | exact @GlobalTheory.UnitaryBC.exists_conj_polyFun | exact GlobalTheory.UnitaryBC.exists_conj_polyFun | (intros; apply GlobalTheory.UnitaryBC.exists_conj_polyFun <;> assumption)
