import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.MirabolicColumnBlock

noncomputable section

open MeasureTheory Matrix GlobalTheory.CuspGeneric Topology
open scoped ContDiff

namespace PositivityTheory.jumpWindows

namespace ExistsLogarithmLinear

/- English proof (translation)
Introduce a local definition for the expression. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Supply the required witnesses or components.
-/
theorem exists_log_lin {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (χ : AddChar V ℂ) (hχ : Continuous χ)
    (h0 : ∀ z, χ z ≠ 0) : ∃ L : V →L[ℝ] ℂ, ∀ z, χ z = Complex.exp (L z) := by
  let f : C(V, {z : ℂ // z ≠ 0}) := ⟨fun z => ⟨χ z, h0 z⟩, hχ.subtype_mk _⟩
  obtain ⟨F, ⟨hF0, hF⟩, -⟩ := Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts f 0 0
    (Subtype.ext (by simp [f]))
  have hF' : ∀ z, Complex.exp (F z) = χ z := fun z => congrArg Subtype.val (congrFun hF z)
  have hadd : ∀ x y, F (x + y) = F x + F y := by
    intro x y
    have hc : Continuous fun y => F (x + y) - F y := by fun_prop
    have := Complex.isCoveringMap_exp.const_of_comp hc (fun y y' => Subtype.ext (by
      simp only [Complex.exp_sub, hF', AddChar.map_add_eq_mul]
      rw [mul_div_assoc, mul_div_assoc, div_self (h0 _), div_self (h0 _)])) y 0
    simp only [add_zero, hF0, sub_zero] at this
    rw [← this]; ring
  exact ⟨(AddMonoidHom.mk' F hadd).toRealLinearMap F.continuous, fun z => (hF' z).symm⟩

end ExistsLogarithmLinear

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply the first step, then apply the next step to every resulting obligation. A detailed English derivation is pending.
-/
theorem exists_logarithm_linear : S8 := by
  intro ι _ χ hχ h1
  obtain ⟨L, hL⟩ := ExistsLogarithmLinear.exists_log_lin χ hχ (fun z h => by simpa [h] using h1 z)
  refine ⟨Complex.imCLM.comp L, fun z => ?_⟩
  have hre : (L z).re = 0 := by
    have := h1 z
    rw [hL z, Complex.norm_exp] at this
    exact Real.exp_eq_one_iff _ |>.1 this
  rw [hL z]
  congr 1
  apply Complex.ext <;> simp [hre]

end PositivityTheory.jumpWindows

end
