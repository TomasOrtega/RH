import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DensCut
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.ResidueFieldCard

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.HermitianLattices.Ext.L3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def EtaLocD : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (p : PlF D),
    (if ∀ x : (D.s.atP p).Ep, x ≠ 0 → IsUnit x then (-1 : ℝ) else 1) = etaF D.host.E D.host.F p.asIdeal

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Use linear arithmetic over natural numbers and integers. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.
-/
theorem alpha_split' {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    (𝔭 : Ideal (𝓞 F)) {a b : ℕ} (hab : a ≤ b) :
    alphaStd K 𝔭 b = alphaStd K 𝔭 a *
      ∏ i ∈ Finset.Icc (a + 1) b, (1 - etaF K F 𝔭 ^ i * (Ideal.absNorm 𝔭 : ℝ) ^ (-(i : ℤ))) := by
  unfold alphaStd
  rw [← Finset.prod_union]
  · congr 1
    ext i
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  · rw [Finset.disjoint_left]
    intro i hi hi'
    simp only [Finset.mem_Icc] at hi hi'
    omega

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Replace the relevant objects with their definitions. Rewrite the hypotheses and the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem densProdVal_of (hη : EtaLocD) : DensProdVal := by
  intro D δ M _ p c hc
  obtain ⟨hK, hF, -⟩ := field_dictionary_holds D
  have hm := Formalism.L2.SG.Pf.NcArithG.rm_eq D
  have hk5 : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hq := PI.UnitaryGroupMassFormula.CntFormula.residue_field_card D p
  have hmax : p.asIdeal.IsMaximal := p.isMaximal
  have hpos := alphaStd_pos hK hF hmax (D.R.k - 1 - c)
  rw [eq_div_iff hpos.ne', alpha_split' (K := D.host.E) p.asIdeal (show D.R.k - 1 - c ≤ D.R.r by omega), mul_comm]
  congr 1
  unfold Formalism.L2.SG.DensExact.densProd
  rw [hq, hη D p, show D.R.r + 1 - (2 * (D.R.rS + 1) + c) = D.R.k - 1 - c + 1 by omega]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [zpow_neg, zpow_natCast]

end Formalism.L2.SG.Pf.Cnt
