import Development.AutomorphicArithmetic.ResidueCharacters.RowGlue
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NRowDef
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BoundAtTwoThreeFamilyFon

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
namespace UpperTheory.N
variable {D : D7}
end UpperTheory.N
/- English proof (translation)
Introduce `h eps Fm`. Take `⟨x0, h0⟩` from `h Fm`. Take `⟨C0, x1, hC0, hpar⟩` from `GlobalTheory.T.admissible_parameters_family_const Fm`. Use `⟨18 * A * C0 + 2 * B * (3 * C0 + 9) + 5 * C0 + 1, max 3 (max x0 x1), fun x hxx hx i HW F Cm X C₂ hS k hTw hs h2 π hπ => ?_⟩` and prove the remaining obligations. Establish `h3 : 3 ≤ x` using `(le_max_left _ _).trans hxx`.

Establish `hb` using `h0 x (((le_max_left _ _).trans (le_max_right _ _)).trans hxx) hx i HW F Cm X C₂ hS k hTw hs h2 π hπ`. Take `⟨-, -, -, hn, ht, -⟩` from `hpar x (((le_max_right _ _).trans (le_max_right _ _)).trans hxx) hx i`. Establish `hlog : 1 ≤ Real.log (Fm.L x i).sc.x`. Rewrite using `[Fm.L_x x i hx, Real.le_log_iff_exp_le (by linarith)]`. Combine the linear relations using `[Real.exp_one_lt_d9]`.

Establish `hc : UpperTheory.N.costC (Fm.L x i) A B ((Fm.D x i).nd.l k) ≤ midF (Fm.L x i) (18 * A * C0 + 2 * B * (3 * C0 + 9) + 5 * C0 + 1)` using `UpperTheory.N.Num.cost_le (Fm.L x i) (Fm.params x hx i) hA hB hC0 hlog hn ht hs le_rfl`. Unfold `Bd at hb ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem UpperTheory.N.starSF_of_rowC_alt (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) : _root_.UpperTheory.N.RowCAlt A B → _root_.UpperTheory.N.StarSelfDualCondition := by
  intro h eps Fm
  obtain ⟨x0, h0⟩ := h Fm
  obtain ⟨C0, x1, hC0, hpar⟩ := GlobalTheory.T.admissible_parameters_family_const Fm
  refine ⟨18 * A * C0 + 2 * B * (3 * C0 + 9) + 5 * C0 + 1, max 3 (max x0 x1),
    fun x hxx hx i HW F Cm X C₂ hS k hTw hs h2 π hπ => ?_⟩
  have h3 : 3 ≤ x := (le_max_left _ _).trans hxx
  have hb := h0 x (((le_max_left _ _).trans (le_max_right _ _)).trans hxx) hx i HW F Cm X C₂ hS k hTw hs h2 π hπ
  obtain ⟨-, -, -, hn, ht, -⟩ := hpar x (((le_max_right _ _).trans (le_max_right _ _)).trans hxx) hx i
  have hlog : 1 ≤ Real.log (Fm.L x i).sc.x := by
    rw [Fm.L_x x i hx, Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hc : UpperTheory.N.costC (Fm.L x i) A B ((Fm.D x i).nd.l k) ≤
      midF (Fm.L x i) (18 * A * C0 + 2 * B * (3 * C0 + 9) + 5 * C0 + 1) :=
    UpperTheory.N.Num.cost_le (Fm.L x i) (Fm.params x hx i) hA hB hC0 hlog hn ht hs le_rfl
  unfold Bd at hb ⊢
  linarith
end
end
