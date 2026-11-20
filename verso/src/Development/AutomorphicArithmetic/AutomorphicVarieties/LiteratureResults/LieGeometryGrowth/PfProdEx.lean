import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PairDefs

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit.Geo

section

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

/- English proof (translation)
Use function extensionality and compare the values at `y`. Unfold `chart`. Apply the tactic sequence `split_ifs <;> simp`.
-/
private theorem chart_conj_mul (f h : GA E a → ℂ) (g : GA E a) :
    chart (fun x => starRingEnd ℂ (f x) * h x) g = fun y => Complex.conjCLE (chart f g y) * chart h g y := by
  funext y
  unfold chart
  split_ifs <;> simp

end

/- English proof (translation)
Introduce `E _ _ _ a φ ψ`. Use `⟨⟨fun x => starRingEnd ℂ (φ.1 x) * ψ.1 x, fun g => ?_⟩, fun _ => rfl, fun X g => ?_⟩` and prove the remaining obligations. Rewrite using `[chart_conj_mul]`. Conclude with `(Complex.conjCLE.contDiff.comp_contDiffOn (φ.2 g)).mul (ψ.2 g)`. Establish `hv : ∀ f : GA E a → ℂ, chart f g (oneL E a) = f g` using `fun f => by`.

Simplify using `using chart_val f g 1`. Express the relevant statement in the definitionally equal form `fderiv ℝ (chart (fun x => starRingEnd ℂ (φ.1 x) * ψ.1 x) g) (oneL E a) X = starRingEnd ℂ (fderiv ℝ (chart φ.1 g) (oneL E a) X) * ψ.1 g + starRingEnd ℂ (φ.1 g) * fderiv ℝ (chart ψ.1 g) (oneL E a) X`. Establish `h1` using `(Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp (oneL E a) (differentiableAt_chart φ.2 g).hasFDerivAt).fun_mul (differentiableAt_chart ψ.2 g).hasFDerivAt`. Rewrite using `[chart_conj_mul]`. Use `(congrArg (fun L => L X) h1.fderiv).trans ?_` and prove the remaining obligations.

Simplify using `[hv, mul_comm, add_comm]`.
-/
theorem UpperTheory.V.Lit.Geo.Pf.prodEx :
    UpperTheory.V.Lit.Geo.Pf.ProdEx := by
  intro E _ _ _ a φ ψ
  refine ⟨⟨fun x => starRingEnd ℂ (φ.1 x) * ψ.1 x, fun g => ?_⟩, fun _ => rfl, fun X g => ?_⟩
  · rw [chart_conj_mul]
    exact (Complex.conjCLE.contDiff.comp_contDiffOn (φ.2 g)).mul (ψ.2 g)
  · have hv : ∀ f : GA E a → ℂ, chart f g (oneL E a) = f g := fun f => by
      simpa using chart_val f g 1
    change fderiv ℝ (chart (fun x => starRingEnd ℂ (φ.1 x) * ψ.1 x) g) (oneL E a) X =
      starRingEnd ℂ (fderiv ℝ (chart φ.1 g) (oneL E a) X) * ψ.1 g +
        starRingEnd ℂ (φ.1 g) * fderiv ℝ (chart ψ.1 g) (oneL E a) X
    have h1 := (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp (oneL E a)
      (differentiableAt_chart φ.2 g).hasFDerivAt).fun_mul (differentiableAt_chart ψ.2 g).hasFDerivAt
    rw [chart_conj_mul]
    refine (congrArg (fun L => L X) h1.fderiv).trans ?_
    simp [hv, mul_comm, add_comm]
