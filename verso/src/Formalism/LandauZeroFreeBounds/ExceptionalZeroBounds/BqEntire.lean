import Formalism.LandauZeroFreeBounds.SameCharacterLFunctionOne

open Complex Filter Topology

noncomputable section

namespace Formalism.ZeroFreeDirichlet

def zetaSubPole : ℂ → ℂ :=
  Function.update (fun s : ℂ => riemannZeta s - 1 / (s - 1)) 1 (Real.eulerMascheroniConstant : ℂ)

/- English proof (translation)
Rewrite using `[← differentiableOn_univ, ← Complex.differentiableOn_compl_singleton_and_continuousAt_iff (c := 1) Filter.univ_mem]`. Use `⟨fun s hs => ?_, ?_⟩` and prove the remaining obligations. Establish `hs1 : s ≠ 1` using `hs.2`. Establish `hev : zetaSubPole =ᶠ[𝓝 s] fun z => riemannZeta z - 1 / (z - 1)` using `by filter_upwards [isOpen_ne.mem_nhds hs1] with z hz`. Conclude with `Function.update_of_ne hz _ _`.

Establish `hd : DifferentiableAt ℂ (fun z => riemannZeta z - 1 / (z - 1)) s` using `(differentiableAt_riemannZeta hs1).sub ((differentiableAt_const _).div (differentiableAt_id.sub_const 1) (sub_ne_zero.mpr hs1))`. Conclude with `(hd.congr_of_eventuallyEq hev).differentiableWithinAt`. Unfold `zetaSubPole`. Conclude with `continuousAt_update_same.mpr tendsto_riemannZeta_sub_one_div`.
-/
theorem zeta_sub_pole_differentiable : Differentiable ℂ zetaSubPole := by
  rw [← differentiableOn_univ,
    ← Complex.differentiableOn_compl_singleton_and_continuousAt_iff (c := 1) Filter.univ_mem]
  refine ⟨fun s hs => ?_, ?_⟩
  · have hs1 : s ≠ 1 := hs.2
    have hev : zetaSubPole =ᶠ[𝓝 s] fun z => riemannZeta z - 1 / (z - 1) := by
      filter_upwards [isOpen_ne.mem_nhds hs1] with z hz
      exact Function.update_of_ne hz _ _
    have hd : DifferentiableAt ℂ (fun z => riemannZeta z - 1 / (z - 1)) s :=
      (differentiableAt_riemannZeta hs1).sub
        ((differentiableAt_const _).div (differentiableAt_id.sub_const 1) (sub_ne_zero.mpr hs1))
    exact (hd.congr_of_eventuallyEq hev).differentiableWithinAt
  · unfold zetaSubPole
    exact continuousAt_update_same.mpr tendsto_riemannZeta_sub_one_div

/- English proof (translation)
Unfold `zetaSubPole`. Conclude with `Function.update_of_ne hs _ _`.
-/
theorem zeta_minus_pole_eq {s : ℂ} (hs : s ≠ 1) : zetaSubPole s = riemannZeta s - 1 / (s - 1) := by
  unfold zetaSubPole
  exact Function.update_of_ne hs _ _

/- English proof (translation)
Introduce `q₁ q₂ _ _ _ χ₁ χ₂ ψ h₁ h₂ hψ`. Take `⟨P, hP⟩ : ∃ P : ℂ → ℂ, P = fun s => DirichletCharacter.LFunction χ₁ s * DirichletCharacter.LFunction χ₂ s * DirichletCharacter.LFunction ψ s` from `⟨_, rfl⟩`. Establish `hPd : Differentiable ℂ P`. Rewrite using `[hP]`. Conclude with `((DirichletCharacter.differentiable_LFunction h₁).mul (DirichletCharacter.differentiable_LFunction h₂)).mul (DirichletCharacter.differentiable_LFunction hψ)`.

Establish `hds : Differentiable ℂ (dslope P 1)`. Rewrite using `[← differentiableOn_univ, Complex.differentiableOn_dslope Filter.univ_mem]`. Conclude with `hPd.differentiableOn`. Use `⟨fun s => zetaSubPole s * P s + dslope P 1 s, (zeta_sub_pole_differentiable.mul hPd).add hds, fun s hs => ?_⟩` and prove the remaining obligations. Establish `hs' : s - 1 ≠ 0` using `sub_ne_zero.mpr hs`.

Use `show _ = zetaSubPole s * P s + dslope P 1 s + _`. Rewrite using `[dslope_of_ne _ hs, slope_def_field, zeta_minus_pole_eq hs]`. Simplify using `only [Fbq, lamBq, hP]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dirichlet_product_entire : BqEntire := by
  intro q₁ q₂ _ _ _ χ₁ χ₂ ψ h₁ h₂ hψ
  obtain ⟨P, hP⟩ : ∃ P : ℂ → ℂ, P = fun s => DirichletCharacter.LFunction χ₁ s *
      DirichletCharacter.LFunction χ₂ s * DirichletCharacter.LFunction ψ s := ⟨_, rfl⟩
  have hPd : Differentiable ℂ P := by
    rw [hP]
    exact ((DirichletCharacter.differentiable_LFunction h₁).mul
      (DirichletCharacter.differentiable_LFunction h₂)).mul
      (DirichletCharacter.differentiable_LFunction hψ)
  have hds : Differentiable ℂ (dslope P 1) := by
    rw [← differentiableOn_univ, Complex.differentiableOn_dslope Filter.univ_mem]
    exact hPd.differentiableOn
  refine ⟨fun s => zetaSubPole s * P s + dslope P 1 s,
    (zeta_sub_pole_differentiable.mul hPd).add hds, fun s hs => ?_⟩
  have hs' : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  show _ = zetaSubPole s * P s + dslope P 1 s + _
  rw [dslope_of_ne _ hs, slope_def_field, zeta_minus_pole_eq hs]
  simp only [Fbq, lamBq, hP]
  field_simp
  ring

end Formalism.ZeroFreeDirichlet
