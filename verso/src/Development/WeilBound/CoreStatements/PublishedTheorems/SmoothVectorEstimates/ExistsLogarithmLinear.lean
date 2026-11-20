import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.MirabolicColumnBlock

noncomputable section

open MeasureTheory Matrix GlobalTheory.CuspGeneric Topology
open scoped ContDiff

namespace PositivityTheory.jumpWindows

namespace ExistsLogarithmLinear

/- English proof (translation)
Set `f : C(V, {z : ℂ // z ≠ 0})` to `⟨fun z => ⟨χ z, h0 z⟩, hχ.subtype_mk _⟩`. Take `⟨F, ⟨hF0, hF⟩, -⟩` from `Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts f 0 0 (Subtype.ext (by simp [f]))`. Establish `hF' : ∀ z, Complex.exp (F z) = χ z` using `fun z => congrArg Subtype.val (congrFun hF z)`. Establish `hadd : ∀ x y, F (x + y) = F x + F y`. Introduce `x y`.

Establish `hc : Continuous fun y => F (x + y) - F y` using `by fun_prop`. Use `Complex.isCoveringMap_exp.const_of_comp hc (fun y y' => Subtype.ext (by` as an intermediate fact. Simplify using `only [Complex.exp_sub, hF', AddChar.map_add_eq_mul]`. Rewrite using `[mul_div_assoc, mul_div_assoc, div_self (h0 _), div_self (h0 _)])) y 0`. Simplify using `only [add_zero, hF0, sub_zero] at this`.

Rewrite using `[← this]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `⟨(AddMonoidHom.mk' F hadd).toRealLinearMap F.continuous, fun z => (hF' z).symm⟩`.
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
Introduce `ι _ χ hχ h1`. Take `⟨L, hL⟩` from `ExistsLogarithmLinear.exists_log_lin χ hχ (fun z h => by simpa [h] using h1 z)`. Use `⟨Complex.imCLM.comp L, fun z => ?_⟩` and prove the remaining obligations. Establish `hre : (L z).re = 0`. Use `h1 z` as an intermediate fact.

Rewrite `this` using `[hL z, Complex.norm_exp]`. Conclude with `Real.exp_eq_one_iff _ |>.1 this`. Rewrite using `[hL z]`. Use `congr 1`. Apply the tactic sequence `apply Complex.ext <;> simp [hre]`.
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
