import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumLieCoord

noncomputable section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW

namespace GlobalTheory.JSW.KerCusp

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

/- English proof (translation)
Establish `hn : Continuous (fun x : BlockIx a r → Ad E => (nilM x : Matrix (Fin a) (Fin a) (Ad E)))`. Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Simplify using `only [nilM, Matrix.of_apply]`. Use `split_ifs`. Conclude with `continuous_apply _`.

Conclude with `continuous_const`. Use `Units.continuous_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `continuous_const.add hn`. Conclude with `continuous_const.sub hn`.
-/
theorem continuous_unip {r : ℕ} : Continuous (fun x : BlockIx a r → Ad E => (unip x : GA E a)) := by
  have hn : Continuous (fun x : BlockIx a r → Ad E => (nilM x : Matrix (Fin a) (Fin a) (Ad E))) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [nilM, Matrix.of_apply]
    split_ifs
    · exact continuous_apply _
    · exact continuous_const
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact continuous_const.add hn
  · exact continuous_const.sub hn

/- English proof (translation)
Set `Φ : invSet E a → (BlockIx a r → Ad E) → ℂ` to `fun y u => chart φ.1 (unip u * g) y.1`. Establish `hΦ : Measurable (Function.uncurry Φ)`. Use `measurable_uncurry_of_continuous_of_measurable (fun u => ?_) (fun y => ?_)` and prove the remaining obligations. Conclude with `((φ.2 (unip u * g)).continuousOn).restrict`. Establish `e : Φ y = fun u => φ.1 (unip u * g * infGL E a y.2.unit)`.

Use function extensionality and compare the values at `u`. Conclude with `dif_pos y.2`. Rewrite using `[e]`. Conclude with `(hc.comp ((continuous_unip.mul continuous_const).mul continuous_const)).measurable`. Establish `hy : Measurable (fun x : X => (⟨toL (γ x).val, val_mem_invSet (γ x)⟩ : invSet E a))` using `Measurable.subtype_mk hγ`.

Establish `e : (Function.uncurry fun (u : BlockIx a r → Ad E) (x : X) => k x * φ.1 (unip u * g * infGL E a (γ x))) = fun p => k p.2 * Function.uncurry Φ (⟨toL (γ p.2).val, val_mem_invSet (γ p.2)⟩, p.1)`. Use function extensionality and compare the values at `p`. Break down `p with ⟨u, x⟩` into its components or cases. Simplify using `only [Function.uncurry_apply_pair, Φ, chart_val]`. Rewrite using `[e]`.

Conclude with `(hk.comp measurable_snd).mul (hΦ.comp ((hy.comp measurable_snd).prodMk measurable_fst))`.
-/
theorem measurable_integrand {r : ℕ} [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)]
    {X : Type} [MeasurableSpace X] {k : X → ℂ} {γ : X → GL (Fin a) (Cinf E)} (hk : Measurable k)
    (hγ : Measurable (fun x => (γ x : Matrix (Fin a) (Fin a) (Cinf E)))) (φ : Sm E a)
    (hc : Continuous φ.1) (g : GA E a) :
    Measurable (Function.uncurry fun (u : BlockIx a r → Ad E) (x : X) => k x * φ.1 (unip u * g * infGL E a (γ x))) := by
  let Φ : invSet E a → (BlockIx a r → Ad E) → ℂ := fun y u => chart φ.1 (unip u * g) y.1
  have hΦ : Measurable (Function.uncurry Φ) := by
    refine measurable_uncurry_of_continuous_of_measurable (fun u => ?_) (fun y => ?_)
    · exact ((φ.2 (unip u * g)).continuousOn).restrict
    · have e : Φ y = fun u => φ.1 (unip u * g * infGL E a y.2.unit) := by
        funext u; exact dif_pos y.2
      rw [e]
      exact (hc.comp ((continuous_unip.mul continuous_const).mul continuous_const)).measurable
  have hy : Measurable (fun x : X => (⟨toL (γ x).val, val_mem_invSet (γ x)⟩ : invSet E a)) :=
    Measurable.subtype_mk hγ
  have e : (Function.uncurry fun (u : BlockIx a r → Ad E) (x : X) => k x * φ.1 (unip u * g * infGL E a (γ x))) =
      fun p => k p.2 * Function.uncurry Φ (⟨toL (γ p.2).val, val_mem_invSet (γ p.2)⟩, p.1) := by
    funext p
    rcases p with ⟨u, x⟩
    simp only [Function.uncurry_apply_pair, Φ, chart_val]
  rw [e]
  exact (hk.comp measurable_snd).mul (hΦ.comp ((hy.comp measurable_snd).prodMk measurable_fst))

end GlobalTheory.JSW.KerCusp

namespace GlobalTheory.JSW

/- English proof (translation)
Introduce `E _ _ _ a X _ ν _ k γ hk φ hφ r h0 h1 _ _ μ 𝓕 hμ hF g`. Use `haveI := hμ`. Establish `hfin` using `covol_lt_top μ 𝓕 hF`. Use `haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩`. Take `⟨C, hC⟩` from `hφ.bdd`.

Establish `hk0 : Integrable (fun x => ‖k x‖) ν` using `by simpa using hk.2.2 0`. Establish `hm` using `KerCusp.measurable_integrand (r := r) hk.1 hk.2.1 φ hφ.cont g`. Establish `hint : Integrable (Function.uncurry fun (u : BlockIx a r → Ad E) (x : X) => k x * φ.1 (unip u * g * infGL E a (γ x))) ((μ.restrict 𝓕).prod ν)`. Use `Integrable.mono' ((integrable_const C).mul_prod hk0) hm.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)` and prove the remaining obligations. Break down `p with ⟨u, x⟩` into its components or cases.

Simplify using `only [Function.uncurry_apply_pair, norm_mul]`. Rewrite using `[mul_comm C]`. Conclude with `mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)`. Express the relevant statement in the definitionally equal form `∫ u in 𝓕, (∫ x, k x * φ.1 (unip u * g * infGL E a (γ x)) ∂ν) ∂μ = 0`. Rewrite using `[integral_integral_swap hint]`.

Use `(integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)).trans (integral_zero X ℂ)` and prove the remaining obligations. Rewrite using `[integral_const_mul]`. Establish `e : ∀ u : BlockIx a r → Ad E, unip u * g * infGL E a (γ x) = unip u * (g * infGL E a (γ x))` using `fun u => mul_assoc _ _ _`. Simplify using `only [e]`. Rewrite using `[hφ.cusp r h0 h1 μ 𝓕 hμ hF _, mul_zero]`.
-/
theorem isCuspidal_kerOp : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (X : Type) [MeasurableSpace X] (ν : Measure X)
    [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)), IsRapidInf ν k γ → ∀ φ : Sm E a, IsBCC φ.1 →
      IsCuspidal (kerOp ν k γ φ.1) := by
  intro E _ _ _ a X _ ν _ k γ hk φ hφ r h0 h1 _ _ μ 𝓕 hμ hF g
  haveI := hμ
  have hfin := covol_lt_top μ 𝓕 hF
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  obtain ⟨C, hC⟩ := hφ.bdd
  have hk0 : Integrable (fun x => ‖k x‖) ν := by simpa using hk.2.2 0
  have hm := KerCusp.measurable_integrand (r := r) hk.1 hk.2.1 φ hφ.cont g
  have hint : Integrable (Function.uncurry fun (u : BlockIx a r → Ad E) (x : X) =>
      k x * φ.1 (unip u * g * infGL E a (γ x))) ((μ.restrict 𝓕).prod ν) := by
    refine Integrable.mono' ((integrable_const C).mul_prod hk0) hm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    rcases p with ⟨u, x⟩
    simp only [Function.uncurry_apply_pair, norm_mul]
    rw [mul_comm C]
    exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
  change ∫ u in 𝓕, (∫ x, k x * φ.1 (unip u * g * infGL E a (γ x)) ∂ν) ∂μ = 0
  rw [integral_integral_swap hint]
  refine (integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)).trans (integral_zero X ℂ)
  rw [integral_const_mul]
  have e : ∀ u : BlockIx a r → Ad E, unip u * g * infGL E a (γ x) = unip u * (g * infGL E a (γ x)) :=
    fun u => mul_assoc _ _ _
  simp only [e]
  rw [hφ.cusp r h0 h1 μ 𝓕 hμ hF _, mul_zero]

end GlobalTheory.JSW
