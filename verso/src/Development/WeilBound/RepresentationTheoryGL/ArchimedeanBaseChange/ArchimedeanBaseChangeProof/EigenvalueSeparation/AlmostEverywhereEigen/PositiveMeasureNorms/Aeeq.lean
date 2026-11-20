import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.OneStepOf
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2
namespace PositivityTheory.Rg.BcB.E2.P

open MeasureTheory
open scoped Pointwise

/- English proof (translation)
Introduce `X u u' hu hu' hi hi' hae`. Establish `: MeasurableConstSMul X.Γ X.G` using `⟨fun γ => measurable_const_mul (γ : X.G)⟩`. Establish `: SMulInvariantMeasure X.Γ X.G X.μ` using `⟨fun γ s _ => measure_preimage_mul _ γ.1 s⟩`. Use `set A : Set X.G := {x | u x ≠ u' x} with hA`. Establish `hAo : IsOpen A` using `isOpen_ne_fun hu hu'`.

Establish `hAF : X.μ (A ∩ X.F) = 0`. Establish `h1 : X.ν A = 0` using `ae_iff.1 hae`. Rewrite `h1` using `[Ctx.ν, Measure.restrict_apply hAo.measurableSet]`. Conclude with `h1`. Establish `hinv : ∀ γ : X.Γ, γ • A = A`.

Introduce `γ`. Use extensionality with `x`. Rewrite using `[Set.mem_smul_set_iff_inv_smul_mem]`. Use `show u (((γ⁻¹ : X.Γ) : X.G) * x) ≠ u' (((γ⁻¹ : X.Γ) : X.G) * x) ↔ u x ≠ u' x`. Rewrite using `[hi _ (γ⁻¹).2, hi' _ (γ⁻¹).2]`.

Establish `hμA : X.μ A = 0` using `X.fd.measure_zero_of_invariant A hinv hAF`. Establish `hAe : A = ∅` using `(hAo.measure_eq_zero_iff X.μ).1 hμA`. Use function extensionality and compare the values at `x`. Assume the negation of the conclusion as `h`. Establish `hx : x ∈ A` using `h`.

Rewrite `hx` using `[hAe]`. Conclude with `hx`.
-/
theorem aeeq : AeEq := by
  intro X u u' hu hu' hi hi' hae
  have : MeasurableConstSMul X.Γ X.G := ⟨fun γ => measurable_const_mul (γ : X.G)⟩
  have : SMulInvariantMeasure X.Γ X.G X.μ := ⟨fun γ s _ => measure_preimage_mul _ γ.1 s⟩
  set A : Set X.G := {x | u x ≠ u' x} with hA
  have hAo : IsOpen A := isOpen_ne_fun hu hu'
  have hAF : X.μ (A ∩ X.F) = 0 := by
    have h1 : X.ν A = 0 := ae_iff.1 hae
    rw [Ctx.ν, Measure.restrict_apply hAo.measurableSet] at h1
    exact h1
  have hinv : ∀ γ : X.Γ, γ • A = A := by
    intro γ
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    show u (((γ⁻¹ : X.Γ) : X.G) * x) ≠ u' (((γ⁻¹ : X.Γ) : X.G) * x) ↔ u x ≠ u' x
    rw [hi _ (γ⁻¹).2, hi' _ (γ⁻¹).2]
  have hμA : X.μ A = 0 := X.fd.measure_zero_of_invariant A hinv hAF
  have hAe : A = ∅ := (hAo.measure_eq_zero_iff X.μ).1 hμA
  funext x
  by_contra h
  have hx : x ∈ A := h
  rw [hAe] at hx
  exact hx

end PositivityTheory.Rg.BcB.E2.P
