import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.TopContDiffOn
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiGelfand
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Integr
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ToMKMulInv
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EqZeroOfDatumEmbeddingEqZero
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiFor

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

/- English proof (translation)
Introduce `_ε _lam T μ hμ Y _g hg` and use `psiM_capelli T μ hμ Y hg`.
-/
theorem psiCapelli : PsiCapelliStatement n := fun _ε _lam T μ hμ Y _g hg => psiM_capelli T μ hμ Y hg

/- English proof (translation)
Introduce `ε lam h T hlam hgap hq`. Take `⟨μ, hμ⟩` from `exists_mu hlam`. Use `⟨PsiM T μ, fun k₁ k₂ g hg => psiM_equiv T μ k₁ k₂ hg, psiM_one T μ, psiM_smooth T μ hμ, fun g hg => psiM_casimir T μ hμ hg, fun k X hX => psiM_dec T μ hμ hlam hgap hq k hX, fun ν hν => ?_, fun k g hg => psiM_gelfand T μ hμ k hg, fun μ' hμ' X hX => ?_, fun Y g hg => psiM_capelli T …` and prove the remaining obligations. Use `hν` as an intermediate fact. Conclude with `psiM_integrable T μ hμ hlam hgap hq ν`.

Rewrite using `[isMu_unique hμ hμ']`. Conclude with `psiM_exp_formula T μ hX`.
-/
theorem psiAllCap : PsiAllCapStatement n := by
  intro ε lam h T hlam hgap hq
  obtain ⟨μ, hμ⟩ := exists_mu hlam
  refine ⟨PsiM T μ, fun k₁ k₂ g hg => psiM_equiv T μ k₁ k₂ hg, psiM_one T μ, psiM_smooth T μ hμ,
    fun g hg => psiM_casimir T μ hμ hg, fun k X hX => psiM_dec T μ hμ hlam hgap hq k hX,
    fun ν hν => ?_, fun k g hg => psiM_gelfand T μ hμ k hg, fun μ' hμ' X hX => ?_,
    fun Y g hg => psiM_capelli T μ hμ Y hg⟩
  · have := hν
    exact psiM_integrable T μ hμ hlam hgap hq ν
  · rw [isMu_unique hμ hμ']
    exact psiM_exp_formula T μ hX

end ReciprocityTheory.ChartRestriction.DS.S7
