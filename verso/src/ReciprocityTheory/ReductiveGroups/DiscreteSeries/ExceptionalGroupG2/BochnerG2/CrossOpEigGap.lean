import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CrossOpEigGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.Numerics

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.G2
variable {n : ℕ}

section OneBAux

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the hypotheses and the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the hypotheses and the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Substitute using the available equality.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact.

Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation. A detailed English derivation is pending.
-/
theorem crossOp_eig_gap (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : 2 * (n : ℝ) < h) {θ : ℝ} {y : Big n 1 M}
    (hy : y ∈ Module.End.eigenspace (crossOp ε E 1 0) (θ : ℂ) ⊓ ncV ε V 1) (hy0 : y ≠ 0) :
    (0 < h - n + 1 ∧ h - n + 1 ≤ θ) ∨ (θ ≤ -h - 1 ∧ -h - 1 < 0) := by
  classical
  set S : Submodule ℂ (Big n 1 M) :=
    Module.End.eigenspace (crossOp ε E 1 0) (θ : ℂ) ⊓ ncV ε V 1 with hSdef
  haveI hfdN : FiniteDimensional ℂ (ncV ε V 1) :=
    ReciprocityTheory.ChartRestriction.DS.finiteDimensional_ncV hV.1 1
  haveI hfd : FiniteDimensional ℂ S :=
    Submodule.finiteDimensional_of_le (inf_le_right : S ≤ ncV ε V 1)

  have hS : ReciprocityTheory.ChartRestriction.DS.IsKStableSub ε (ReciprocityTheory.ChartRestriction.DS.bAct E 1) S := by
    intro a b hab v hv
    rw [Submodule.mem_inf] at hv ⊢
    refine ⟨?_, ReciprocityTheory.ChartRestriction.DS.ncV_kStable hV.2.1 1 a b hab v hv.2⟩
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    have hc : crossOp ε E 1 0 (ReciprocityTheory.ChartRestriction.DS.bAct E 1 a b v) =
        ReciprocityTheory.ChartRestriction.DS.bAct E 1 a b (crossOp ε E 1 0 v) :=
      LinearMap.congr_fun (ReciprocityTheory.ChartRestriction.DS.crossOp_comm hE 1 0 hab) v
    rw [hc, hv.1, map_smul]
  have hne : S ≠ ⊥ := by
    intro h0
    apply hy0
    have hyS : y ∈ S := hy
    rw [h0] at hyS
    exact (Submodule.mem_bot ℂ).1 hyS

  obtain ⟨w, hwS, hw0, μ, hμ⟩ :=
    ReciprocityTheory.ChartRestriction.DS.exists_khw (ReciprocityTheory.ChartRestriction.DS.bAct_isGlRep hE 1)
      (ReciprocityTheory.ChartRestriction.DS.bAct_isKUnitary hU 1) hfd hS hne
  have hwS' := Submodule.mem_inf.1 hwS
  obtain ⟨r, s, hrs, hμeq, h2⟩ :=
    ReciprocityTheory.ChartRestriction.DS.crossOp_khw hE hU hV hwS'.2 hw0 hμ
  have hθw : crossOp ε E 1 0 w = (θ : ℂ) • w := Module.End.mem_eigenspace_iff.1 hwS'.1
  rw [hθw, smul_smul] at h2
  have hc : ((2 : ℂ) * (θ : ℂ)) =
      ((ReciprocityTheory.ChartRestriction.DS.casValK ε μ - n -
        ReciprocityTheory.ChartRestriction.DS.casValK ε (ReciprocityTheory.ChartRestriction.DS.lowK ε lam) : ℝ) : ℂ) :=
    smul_left_injective ℂ hw0 h2
  have hcR : 2 * θ = ReciprocityTheory.ChartRestriction.DS.casValK ε μ - n -
      ReciprocityTheory.ChartRestriction.DS.casValK ε (ReciprocityTheory.ChartRestriction.DS.lowK ε lam) := by
    exact_mod_cast hc
  subst hμeq
  have hgap := ReciprocityTheory.ChartRestriction.DS.G2.gap_gt hrs hbig
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hne' : r ≠ s := fun h => hrs (congrArg ε h)
  rcases lt_or_gt_of_ne hne' with hlt | hgt
  · left
    have hp := ReciprocityTheory.ChartRestriction.DS.crossVal_pos hmono hh hlt hrs
    constructor <;> linarith [hgap.2]
  · right
    have hq := ReciprocityTheory.ChartRestriction.DS.crossVal_neg hmono hh hgt hrs.symm
    constructor <;> linarith

end OneBAux

end ReciprocityTheory.ChartRestriction.DS.G2
