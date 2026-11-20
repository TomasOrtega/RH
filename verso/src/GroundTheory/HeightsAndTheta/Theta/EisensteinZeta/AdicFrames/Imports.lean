import Mathlib

namespace GroundTheory.Heights₂.Theta

namespace FibreMeasure

open MeasureTheory

section Shear

variable {G P : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
  [AddCommGroup P] [MeasurableSpace P] [MeasurableAdd₂ P] [MeasurableNeg P]

/- English proof (translation)
Establish `hf : Measurable (fun X ↦ X + ζ (t X))` using `measurable_id.add (hζ.comp ht)`. Use `⟨hf, ?_⟩` and prove the remaining obligations. Use `set ρ : P → ENNReal := B.indicator (fun _ ↦ (ν B)⁻¹) with hρdef`. Establish `hρ : Measurable ρ` using `measurable_const.indicator hB`. Establish `hρ1 : ∫⁻ d, ρ d ∂ν = 1`.

Rewrite using `[hρdef, lintegral_indicator hB, setLIntegral_const, ENNReal.inv_mul_cancel hB0 hBt]`. Establish `hρsh : ∀ c : P, ∫⁻ d, ρ (d - c) ∂ν = 1` using `fun c ↦ by`. Rewrite using `[← hρ1]`. Repeatedly rewrite using `[sub_eq_add_neg]`. Conclude with `lintegral_add_right_eq_self ρ (-c)`.

Establish `key : ∀ g : G → ENNReal, Measurable g → ∫⁻ X, g (X + ζ (t X)) ∂μ = ∫⁻ X, g X ∂μ`. Introduce `g hg`. Establish `hm1 : Measurable (Function.uncurry fun (d : P) (X : G) ↦ ρ d * g (X + ζ (d + t X)))`. Use `(hρ.comp measurable_fst).mul (hg.comp ?_)` and prove the remaining obligations. Conclude with `measurable_snd.add (hζ.comp (measurable_fst.add (ht.comp measurable_snd)))`.

Establish `hm2 : Measurable (Function.uncurry fun (X : G) (d : P) ↦ ρ (d - t X) * g (X + ζ d))`. Use `(hρ.comp (measurable_snd.sub (ht.comp measurable_fst))).mul (hg.comp ?_)` and prove the remaining obligations. Conclude with `measurable_fst.add (hζ.comp measurable_snd)`. Establish `hm3 : Measurable (Function.uncurry fun (d : P) (X : G) ↦ ρ (d - t X) * g X)`. Conclude with `(hρ.comp (measurable_fst.sub (ht.comp measurable_snd))).mul (hg.comp measurable_snd)`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[lintegral_mul_const _ hρ, hρ1, one_mul]`. Use `_ = ∫⁻ d, ∫⁻ X, ρ d * g (X + ζ (d + t X)) ∂μ ∂ν := by`. Use `lintegral_congr fun d ↦ ?_` and prove the remaining obligations. Establish `h1 : ∫⁻ X, g (X + ζ (d + t X)) ∂μ = ∫⁻ X, g (X + ζ (t X)) ∂μ`.

Rewrite using `[← lintegral_add_right_eq_self (μ := μ) (fun X ↦ g (X + ζ (t X))) (ζ d)]`. Use `lintegral_congr fun X ↦ ?_` and prove the remaining obligations. Simplify using `only [htζ, map_add]`. Use `congr 1`. Normalize the expressions using the abelian group laws.

Rewrite using `[lintegral_const_mul (ρ d) (f := fun X ↦ g (X + ζ (d + t X))) (hg.comp (measurable_id.add (hζ.comp (measurable_const.add ht)))), h1]`. Use `_ = ∫⁻ X, ∫⁻ d, ρ d * g (X + ζ (d + t X)) ∂ν ∂μ := lintegral_lintegral_swap hm1.aemeasurable`. Use `_ = ∫⁻ X, ∫⁻ d, ρ (d - t X) * g (X + ζ d) ∂ν ∂μ := by`. Use `lintegral_congr fun X ↦ ?_` and prove the remaining obligations. Rewrite using `[← lintegral_add_right_eq_self (μ := ν) (fun d ↦ ρ (d - t X) * g (X + ζ d)) (t X)]`.

Simplify using the standard rewrite rules. Use `_ = ∫⁻ d, ∫⁻ X, ρ (d - t X) * g (X + ζ d) ∂μ ∂ν := lintegral_lintegral_swap hm2.aemeasurable`. Use `_ = ∫⁻ d, ∫⁻ X, ρ (d - t X) * g X ∂μ ∂ν := by`. Use `lintegral_congr fun d ↦ ?_` and prove the remaining obligations. Use `lintegral_add_right_eq_self (μ := μ) (fun X ↦ ρ (d - t X) * g X) (ζ d)` as an intermediate fact.

Simplify using `only [htζ] at this`. Conclude with `this`. Use `_ = ∫⁻ X, ∫⁻ d, ρ (d - t X) * g X ∂ν ∂μ := lintegral_lintegral_swap hm3.aemeasurable`. Use `_ = ∫⁻ X, g X ∂μ := by`. Use `lintegral_congr fun X ↦ ?_` and prove the remaining obligations.

Rewrite using `[lintegral_mul_const (r := g X) (f := fun d ↦ ρ (d - t X)) (hρ.comp (measurable_id.sub measurable_const)), hρsh, one_mul]`. Use extensionality with `A hA`. Rewrite using `[Measure.map_apply hf hA, ← lintegral_indicator_one (hf hA), ← lintegral_indicator_one hA]`. Conclude with `key (A.indicator 1) (measurable_one.indicator hA)`.
-/
theorem measurePreserving_shear (μ : Measure G) [μ.IsAddLeftInvariant] [SFinite μ]
    (ν : Measure P) [ν.IsAddLeftInvariant] [SFinite ν] {B : Set P} (hB : MeasurableSet B)
    (hB0 : ν B ≠ 0) (hBt : ν B ≠ ⊤) (ζ : P →+ G) (hζ : Measurable ζ) (t : G → P)
    (ht : Measurable t) (htζ : ∀ X d, t (X + ζ d) = t X) :
    MeasurePreserving (fun X ↦ X + ζ (t X)) μ μ := by
  have hf : Measurable (fun X ↦ X + ζ (t X)) := measurable_id.add (hζ.comp ht)
  refine ⟨hf, ?_⟩
  set ρ : P → ENNReal := B.indicator (fun _ ↦ (ν B)⁻¹) with hρdef
  have hρ : Measurable ρ := measurable_const.indicator hB
  have hρ1 : ∫⁻ d, ρ d ∂ν = 1 := by
    rw [hρdef, lintegral_indicator hB, setLIntegral_const, ENNReal.inv_mul_cancel hB0 hBt]
  have hρsh : ∀ c : P, ∫⁻ d, ρ (d - c) ∂ν = 1 := fun c ↦ by
    rw [← hρ1]
    simp_rw [sub_eq_add_neg]
    exact lintegral_add_right_eq_self ρ (-c)
  have key : ∀ g : G → ENNReal, Measurable g →
      ∫⁻ X, g (X + ζ (t X)) ∂μ = ∫⁻ X, g X ∂μ := by
    intro g hg
    have hm1 : Measurable (Function.uncurry fun (d : P) (X : G) ↦ ρ d * g (X + ζ (d + t X))) := by
      refine (hρ.comp measurable_fst).mul (hg.comp ?_)
      exact measurable_snd.add (hζ.comp (measurable_fst.add (ht.comp measurable_snd)))
    have hm2 : Measurable (Function.uncurry fun (X : G) (d : P) ↦ ρ (d - t X) * g (X + ζ d)) := by
      refine (hρ.comp (measurable_snd.sub (ht.comp measurable_fst))).mul (hg.comp ?_)
      exact measurable_fst.add (hζ.comp measurable_snd)
    have hm3 : Measurable (Function.uncurry fun (d : P) (X : G) ↦ ρ (d - t X) * g X) := by
      exact (hρ.comp (measurable_fst.sub (ht.comp measurable_snd))).mul (hg.comp measurable_snd)
    calc ∫⁻ X, g (X + ζ (t X)) ∂μ
        = ∫⁻ d, ρ d * ∫⁻ X, g (X + ζ (t X)) ∂μ ∂ν := by
          rw [lintegral_mul_const _ hρ, hρ1, one_mul]
      _ = ∫⁻ d, ∫⁻ X, ρ d * g (X + ζ (d + t X)) ∂μ ∂ν := by
          refine lintegral_congr fun d ↦ ?_
          have h1 : ∫⁻ X, g (X + ζ (d + t X)) ∂μ = ∫⁻ X, g (X + ζ (t X)) ∂μ := by
            rw [← lintegral_add_right_eq_self (μ := μ) (fun X ↦ g (X + ζ (t X))) (ζ d)]
            refine lintegral_congr fun X ↦ ?_
            simp only [htζ, map_add]
            congr 1
            abel
          rw [lintegral_const_mul (ρ d) (f := fun X ↦ g (X + ζ (d + t X)))
            (hg.comp (measurable_id.add (hζ.comp (measurable_const.add ht)))), h1]
      _ = ∫⁻ X, ∫⁻ d, ρ d * g (X + ζ (d + t X)) ∂ν ∂μ :=
          lintegral_lintegral_swap hm1.aemeasurable
      _ = ∫⁻ X, ∫⁻ d, ρ (d - t X) * g (X + ζ d) ∂ν ∂μ := by
          refine lintegral_congr fun X ↦ ?_
          rw [← lintegral_add_right_eq_self (μ := ν) (fun d ↦ ρ (d - t X) * g (X + ζ d)) (t X)]
          simp
      _ = ∫⁻ d, ∫⁻ X, ρ (d - t X) * g (X + ζ d) ∂μ ∂ν :=
          lintegral_lintegral_swap hm2.aemeasurable
      _ = ∫⁻ d, ∫⁻ X, ρ (d - t X) * g X ∂μ ∂ν := by
          refine lintegral_congr fun d ↦ ?_
          have := lintegral_add_right_eq_self (μ := μ) (fun X ↦ ρ (d - t X) * g X) (ζ d)
          simp only [htζ] at this
          exact this
      _ = ∫⁻ X, ∫⁻ d, ρ (d - t X) * g X ∂ν ∂μ :=
          lintegral_lintegral_swap hm3.aemeasurable
      _ = ∫⁻ X, g X ∂μ := by
          refine lintegral_congr fun X ↦ ?_
          rw [lintegral_mul_const (r := g X) (f := fun d ↦ ρ (d - t X))
            (hρ.comp (measurable_id.sub measurable_const)), hρsh, one_mul]
  ext A hA
  rw [Measure.map_apply hf hA, ← lintegral_indicator_one (hf hA), ← lintegral_indicator_one hA]
  exact key (A.indicator 1) (measurable_one.indicator hA)

end Shear

end FibreMeasure

end GroundTheory.Heights₂.Theta
