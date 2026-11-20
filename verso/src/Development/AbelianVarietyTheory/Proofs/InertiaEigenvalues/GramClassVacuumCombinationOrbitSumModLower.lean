import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumEqConstMulPeterssonStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypeOrthOfAvTied
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.TypeOrthClassSum

/- English proof (translation)
Introduce `D M V i hC`. Take `⟨hbd, β, T, c, hβ, hT, hc, hin⟩` from `hC`. Take `⟨B, hB, hBc⟩` from `GlobalTheory.T.class_sum_eq_const_mul_petersson D.host.E D.R.nV (M.loc i).wt β hβ`. Take `⟨c', hc', hcc⟩` from `hBc (M.loc i).J (M.loc i).χ T hbd (M.loc i).J_open hT`. Establish `hreal : ∀ x, (M.loc i).real x ∈ NG.TypeSp (M.loc i).wt.ρ (M.loc i).J (M.loc i).χ` using `fun x => by`.

Rewrite using `[← (M.loc i).real_range]`. Conclude with `LinearMap.mem_range_self _ x`. Use `set r : ℝ := c * c' with hr`. Establish `hr0 : 0 < r` using `mul_pos hc hc'`. Establish `hsmul : ∀ f f', (((r : ℂ) • B) f f') = (r : ℂ) * B f f'` using `fun f f' => by`.

Simplify using `[LinearMap.smul_apply]`. Establish `hcls : ∃ T' : Finset (GAf D.host.E D.R.nV), ∀ g : GAf D.host.E D.R.nV, ∃ (γ : ReciprocityTheory.Aut.GQ D.host.E D.R.nV) (t : GAf D.host.E D.R.nV) (u : GAf D.host.E D.R.nV), t ∈ T' ∧ u ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV ∧ g = (γ : GAf D.host.E D.R.nV) * t * u` using `by classical`. Take `⟨F, hF⟩` from `hbd`. Use `⟨(T ×ˢ F).image (fun p => p.1 * p.2), fun g => ?_⟩` and prove the remaining obligations. Take `⟨t, ⟨htT, γ, κ, hκ, hg⟩, -⟩` from `hT g`.

Take `⟨f, hfF, hu⟩` from `hF κ hκ`. Use `⟨γ, t * f, f⁻¹ * κ, Finset.mem_image.2 ⟨(t, f), Finset.mem_product.2 ⟨htT, hfF⟩, rfl⟩, hu, ?_⟩` and prove the remaining obligations. Rewrite using `[hg]`. Use `group`. Establish `key` using `GlobalTheory.ThetaExh.typeOrth_of_avTied D M V i ((r : ℂ) • B) ?_ ?_ ?_`.

Conclude with `key`. Introduce `f hf f' hf'`. Take `⟨h1, h2, h3⟩` from `hB f hf f' hf'`. Use `⟨?_, fun hne => ?_, fun h => ?_⟩` and prove the remaining obligations. Rewrite using `[hsmul, hsmul, h1, map_mul, Complex.conj_ofReal]`.

Rewrite using `[hsmul, Complex.re_ofReal_mul]`. Conclude with `mul_pos hr0 (h2 hne)`. Rewrite using `[hsmul, hsmul, h3]`. Introduce `x y`. Rewrite using `[hin, hsmul, hcc _ (hreal x) _ (hreal y), hr]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Introduce `N hN`. Conclude with `GlobalTheory.AlgFormsFin.finiteDimensional_forms D D.R.nV (M.loc i).wt hcls N hN`.
-/
theorem typeOrth_of_classSum : ∀ (D : D7) (M : MtFam D), AVTied D M → ∀ i : D.nd.Loc, ClassSum (M.loc i) → TypeOrth D i := by
  intro D M V i hC
  obtain ⟨hbd, β, T, c, hβ, hT, hc, hin⟩ := hC
  obtain ⟨B, hB, hBc⟩ := GlobalTheory.T.class_sum_eq_const_mul_petersson D.host.E D.R.nV (M.loc i).wt β hβ
  obtain ⟨c', hc', hcc⟩ := hBc (M.loc i).J (M.loc i).χ T hbd (M.loc i).J_open hT
  have hreal : ∀ x, (M.loc i).real x ∈ NG.TypeSp (M.loc i).wt.ρ (M.loc i).J (M.loc i).χ := fun x => by
    rw [← (M.loc i).real_range]; exact LinearMap.mem_range_self _ x
  set r : ℝ := c * c' with hr
  have hr0 : 0 < r := mul_pos hc hc'
  have hsmul : ∀ f f', (((r : ℂ) • B) f f') = (r : ℂ) * B f f' := fun f f' => by
    simp [LinearMap.smul_apply]

  have hcls : ∃ T' : Finset (GAf D.host.E D.R.nV), ∀ g : GAf D.host.E D.R.nV, ∃ (γ : ReciprocityTheory.Aut.GQ D.host.E D.R.nV)
      (t : GAf D.host.E D.R.nV) (u : GAf D.host.E D.R.nV), t ∈ T' ∧ u ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV ∧
      g = (γ : GAf D.host.E D.R.nV) * t * u := by
    classical
    obtain ⟨F, hF⟩ := hbd
    refine ⟨(T ×ˢ F).image (fun p => p.1 * p.2), fun g => ?_⟩
    obtain ⟨t, ⟨htT, γ, κ, hκ, hg⟩, -⟩ := hT g
    obtain ⟨f, hfF, hu⟩ := hF κ hκ
    refine ⟨γ, t * f, f⁻¹ * κ, Finset.mem_image.2 ⟨(t, f), Finset.mem_product.2 ⟨htT, hfF⟩, rfl⟩, hu, ?_⟩
    rw [hg]; group
  have key := GlobalTheory.ThetaExh.typeOrth_of_avTied D M V i ((r : ℂ) • B) ?_ ?_ ?_
  · exact key
  · intro f hf f' hf'
    obtain ⟨h1, h2, h3⟩ := hB f hf f' hf'
    refine ⟨?_, fun hne => ?_, fun h => ?_⟩
    · rw [hsmul, hsmul, h1, map_mul, Complex.conj_ofReal]
    · rw [hsmul, Complex.re_ofReal_mul]; exact mul_pos hr0 (h2 hne)
    · rw [hsmul, hsmul, h3]
  · intro x y
    rw [hin, hsmul, hcc _ (hreal x) _ (hreal y), hr]
    push_cast; ring
  · intro N hN
    exact GlobalTheory.AlgFormsFin.finiteDimensional_forms D D.R.nV (M.loc i).wt hcls N hN

end GlobalTheory.TypeOrthClassSum
