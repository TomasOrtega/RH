import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.HlamStable
import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.DegreeGapNorms.DegPsi
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.FormalDegreeG2.FdCons
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.FormulaF
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.IsDSSigLam
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiFor
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.NormSubOneLeOfHsdA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Exists

noncomputable section

open Finset MeasureTheory Matrix
open scoped InnerProductSpace

namespace PositivityTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

/- English proof (translation)
Introduce `n ε hp hq`. Use `⟨G2.thrS ε + 2, fun lam hlam hgap T μ hμ => ?_⟩` and prove the remaining obligations. Establish `hh : G2.thrS ε + 1 < G2.thrS ε + 2` using `by linarith`. Establish `hq0` using `G2.one_le_q0_of_p_q_pos hp hq`. Establish `h8` using `G2.fdc_eight hh`.

Establish `hP : IsPsiFor ε lam T (PsiM T μ)` using `(S7.isPsiFor_psiM ε lam _ T μ hlam hμ hgap hq0 h8).1`. Establish `hgap'` using `G2.fdc_stdGap hlam hgap hh`. Establish `hw` using `G2.fdc_w_ne T`. Establish `hDS` using `G2.isDS_sigLam hgap' hP hw`. Establish `: CompleteSpace (Hlam ε (PsiM T μ) T.w)` using `hDS.1`.

Establish `: Nontrivial (Hlam ε (PsiM T μ) T.w)` using `hDS.2.1`. Take `⟨d, hd⟩` from `G2.fdcGood_of_isDS hDS`. Take `⟨x, hx⟩` from `exists_ne (0 : Hlam ε (PsiM T μ) T.w)`. Establish `hΨ : ∀ μ' : Fin n → ℝ, IsHCParam μ' → GapAtLeast ε μ' (G2.thrS ε + 2) → ∃ (T' : KType ε (lowK ε μ')) (Ψ : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)), IsPsiFor ε μ' T' Ψ`. Introduce `μ' hμ' hg'`.

Take `⟨T'⟩` from `HW.kType_exists ε μ' hμ'`. Take `⟨m', -, hP'⟩` from `G2.fdc_model hp hq hμ' hg' hh T'`. Conclude with `⟨T', _, hP'⟩`. Establish `hdeg` using `G2.fdCons_cd hp hq hlam hgap hh hΨ hDS hx`. Rewrite `hdeg` using `[fdegOf_of_isFdeg' hd hx]`.

Substitute `hdeg` using the available equality. Use `set C : ℝ := ‖uniformisationL2 ε (PsiM T μ) T.w T.w‖ ^ 2 with hC`. Establish `hC0 : 0 < C`. Use `G2.datumEmbedding_highest_ne_zero hgap' hP hw` as an intermediate fact. Check the signs of the components of the expression.

Establish `h1 : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε` using `umat_mem_UJset ε 1`. Use `hD n ε T.V (PsiM T μ) (Hlam ε (PsiM T μ) T.w) (sigLam ε (PsiM T μ) T.w) (fun v => ⟨uniformisationL2 ε (PsiM T μ) T.w v, datumEmbedding_mem_Hlam hP v⟩) C (dimVlam lam) (muCD ε) hC0 (fun v v' => ?_) (fun g v v' => ?_) hd` and prove the remaining obligations. Establish `e` using `G2.formulaF_sigLam hgap' hP hw h1 v v'`. Rewrite `e` using `[hP.2.1]`. Simplify using `only [ContinuousLinearMap.one_apply] at e`.

Rewrite using `[← e, (G2.sigLam_isURepOn hgap' hP hw).1.1]`. Both sides reduce to the same expression. Conclude with `G2.formulaF_sigLam hgap' hP hw (umat_mem_UJset ε g) v v'`.
-/
theorem gapNorm_of (hD : DegPsi) : GapNorm := by
  intro n ε hp hq
  refine ⟨G2.thrS ε + 2, fun lam hlam hgap T μ hμ => ?_⟩
  have hh : G2.thrS ε + 1 < G2.thrS ε + 2 := by linarith
  have hq0 := G2.one_le_q0_of_p_q_pos hp hq
  have h8 := G2.fdc_eight hh
  have hP : IsPsiFor ε lam T (PsiM T μ) := (S7.isPsiFor_psiM ε lam _ T μ hlam hμ hgap hq0 h8).1
  have hgap' := G2.fdc_stdGap hlam hgap hh
  have hw := G2.fdc_w_ne T
  have hDS := G2.isDS_sigLam hgap' hP hw
  have : CompleteSpace (Hlam ε (PsiM T μ) T.w) := hDS.1
  have : Nontrivial (Hlam ε (PsiM T μ) T.w) := hDS.2.1
  obtain ⟨d, hd⟩ := G2.fdcGood_of_isDS hDS
  obtain ⟨x, hx⟩ := exists_ne (0 : Hlam ε (PsiM T μ) T.w)
  have hΨ : ∀ μ' : Fin n → ℝ, IsHCParam μ' → GapAtLeast ε μ' (G2.thrS ε + 2) →
      ∃ (T' : KType ε (lowK ε μ')) (Ψ : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)), IsPsiFor ε μ' T' Ψ := by
    intro μ' hμ' hg'
    obtain ⟨T'⟩ := HW.kType_exists ε μ' hμ'
    obtain ⟨m', -, hP'⟩ := G2.fdc_model hp hq hμ' hg' hh T'
    exact ⟨T', _, hP'⟩
  have hdeg := G2.fdCons_cd hp hq hlam hgap hh hΨ hDS hx
  rw [fdegOf_of_isFdeg' hd hx] at hdeg
  subst hdeg
  set C : ℝ := ‖uniformisationL2 ε (PsiM T μ) T.w T.w‖ ^ 2 with hC
  have hC0 : 0 < C := by
    have := G2.datumEmbedding_highest_ne_zero hgap' hP hw
    positivity
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := umat_mem_UJset ε 1
  refine hD n ε T.V (PsiM T μ) (Hlam ε (PsiM T μ) T.w) (sigLam ε (PsiM T μ) T.w)
    (fun v => ⟨uniformisationL2 ε (PsiM T μ) T.w v, datumEmbedding_mem_Hlam hP v⟩) C (dimVlam lam) (muCD ε) hC0 (fun v v' => ?_) (fun g v v' => ?_) hd
  · have e := G2.formulaF_sigLam hgap' hP hw h1 v v'
    rw [hP.2.1] at e
    simp only [ContinuousLinearMap.one_apply] at e
    rw [← e, (G2.sigLam_isURepOn hgap' hP hw).1.1]
    rfl
  · exact G2.formulaF_sigLam hgap' hP hw (umat_mem_UJset ε g) v v'

end PositivityTheory.RgFd
