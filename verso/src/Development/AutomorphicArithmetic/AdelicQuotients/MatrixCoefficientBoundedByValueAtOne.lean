import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SchurStep
import Development.WeilBound.ThetaLifts.LatticeBasics.EulerProd
import Development.WeilBound.ThetaLifts.LatticeBasics.BadFactor
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SqShift

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions UpperTheory.TP

namespace UpperTheory.MatrixCoefficientBound

open scoped Pointwise

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {Γ : Subgroup G} [Countable Γ] {D : Set G}

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Qk59.sq_shift hD hi g`.
-/
private theorem sq_shift (hD : IsFundamentalDomain Γ D μ) {f : G → ℝ} (hi : ∀ γ ∈ Γ, ∀ y, f (γ * y) = f y) (g : G) :
    ∫ y in D, f (y * g) ∂μ = ∫ y in D, f y ∂μ :=
  _root_.UpperTheory.Reformulated.B.Qk59.sq_shift hD hi g

/- English proof (translation)
Establish `hb : ∀ {ψ : G → ℂ}, Continuous ψ → (∀ y, ‖ψ y‖ ≤ C) → IntegrableOn (fun y => ‖ψ y‖ ^ 2) D μ` using `fun {ψ} h1 h2 => Measure.integrableOn_of_bounded (M := C ^ 2) hfin.ne (h1.norm.pow 2).aestronglyMeasurable (Eventually.of_forall fun y => by`. Rewrite using `[norm_pow, norm_norm]`. Conclude with `pow_le_pow_left₀ (norm_nonneg _) (h2 y) 2)`. Establish `hcg : Continuous fun y => φ (y * g)` using `hc.comp (continuous_mul_right g)`. Establish `i1` using `hb hcg fun y => hC _`.

Establish `i2` using `hb hc hC`. Establish `e` using `sq_shift (μ := μ) hD (f := fun y => ‖φ y‖ ^ 2) (fun γ hγ y => by simp only [hi γ hγ y]) g`. Combine the equalities or inequalities in the displayed calculation. Use `integral_mono_of_nonneg (Eventually.of_forall fun y => norm_nonneg _) ((i1.add i2).div_const 2) (Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Simplify using `only [norm_mul, norm_star]`.

Use polynomial arithmetic with `[sq_nonneg (‖φ (y * g)‖ - ‖φ y‖)]`. Use `_ = ∫ y in D, ‖φ y‖ ^ 2 ∂μ := by`. Rewrite using `[integral_div, integral_add i1 i2, e]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem coef_le (hfin : μ D < ⊤) (hD : IsFundamentalDomain Γ D μ) {φ : G → ℂ} (hc : Continuous φ)
    (hi : ∀ γ ∈ Γ, ∀ y, φ (γ * y) = φ y) {C : ℝ} (hC : ∀ y, ‖φ y‖ ≤ C) (g : G) :
    ‖∫ y in D, φ (y * g) * star (φ y) ∂μ‖ ≤ ∫ y in D, ‖φ y‖ ^ 2 ∂μ := by
  have hb : ∀ {ψ : G → ℂ}, Continuous ψ → (∀ y, ‖ψ y‖ ≤ C) → IntegrableOn (fun y => ‖ψ y‖ ^ 2) D μ := fun {ψ} h1 h2 =>
    Measure.integrableOn_of_bounded (M := C ^ 2) hfin.ne (h1.norm.pow 2).aestronglyMeasurable
      (Eventually.of_forall fun y => by
        rw [norm_pow, norm_norm]; exact pow_le_pow_left₀ (norm_nonneg _) (h2 y) 2)
  have hcg : Continuous fun y => φ (y * g) := hc.comp (continuous_mul_right g)
  have i1 := hb hcg fun y => hC _
  have i2 := hb hc hC
  have e := sq_shift (μ := μ) hD (f := fun y => ‖φ y‖ ^ 2) (fun γ hγ y => by simp only [hi γ hγ y]) g
  calc ‖∫ y in D, φ (y * g) * star (φ y) ∂μ‖ ≤ ∫ y in D, ‖φ (y * g) * star (φ y)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ y in D, (‖φ (y * g)‖ ^ 2 + ‖φ y‖ ^ 2) / 2 ∂μ := by
      refine integral_mono_of_nonneg (Eventually.of_forall fun y => norm_nonneg _) ((i1.add i2).div_const 2) (Eventually.of_forall fun y => ?_)
      simp only [norm_mul, norm_star]
      nlinarith [sq_nonneg (‖φ (y * g)‖ - ‖φ y‖)]
    _ = ∫ y in D, ‖φ y‖ ^ 2 ∂μ := by
      rw [integral_div, integral_add i1 i2, e]
      ring

end UpperTheory.MatrixCoefficientBound

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n d X W M hK hμ hD φ hφ h0`. Use `haveI := hK.cnt`. Use `haveI := hK.right M.μ hμ`. Take `⟨C, hC⟩` from `hK.bdd hφ.1 hφ.2`. Establish `e1 : mc M φ 1 = ((∫ y in M.dom, ‖φ y‖ ^ 2 ∂M.μ : ℝ) : ℂ)`.

Rewrite using `[← integral_complex_ofReal]`. Simplify using `only [mc, pet, mul_one]`. Conclude with `integral_congr_ae (Eventually.of_forall fun y => by simpa using Complex.mul_conj' (φ y))`. Establish `hp : (∫ y in M.dom, ‖φ y‖ ^ 2 ∂M.μ) ≠ 0` using `fun h => h0 <| hK.eq_zero hμ hD hφ.1 hφ.2 (by`. Establish `: pet M.μ M.dom φ φ = mc M φ 1` using `by simp [mc]`.

Rewrite using `[this, e1, h]`. Use the proof step `simp)`. Use `⟨_, lt_of_le_of_ne (integral_nonneg fun y => by positivity) hp.symm, e1, fun g => ?_⟩` and prove the remaining obligations. Conclude with `UpperTheory.MatrixCoefficientBound.coef_le (hK.fin M.μ M.dom hμ hD) hD hφ.1 hφ.2 hC g`.
-/
theorem UpperTheory.matrix_coefficient_bounded_by_value_at_one :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W}, Cpt σ X.J → M.μ.IsHaarMeasure → IsFundamentalDomain (ratU σ X.J) M.dom M.μ → ∀ {φ : UA σ X.J → ℂ}, IsFn φ → φ ≠ 0 → ∃ r : ℝ, 0 < r ∧ mc M φ 1 = r ∧ ∀ g, ‖mc M φ g‖ ≤ r := by
  intro F E _ _ _ _ _ σ n d X W M hK hμ hD φ hφ h0
  haveI := hK.cnt
  haveI := hK.right M.μ hμ
  obtain ⟨C, hC⟩ := hK.bdd hφ.1 hφ.2
  have e1 : mc M φ 1 = ((∫ y in M.dom, ‖φ y‖ ^ 2 ∂M.μ : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    simp only [mc, pet, mul_one]
    exact integral_congr_ae (Eventually.of_forall fun y => by simpa using Complex.mul_conj' (φ y))
  have hp : (∫ y in M.dom, ‖φ y‖ ^ 2 ∂M.μ) ≠ 0 := fun h => h0 <| hK.eq_zero hμ hD hφ.1 hφ.2 (by
    have : pet M.μ M.dom φ φ = mc M φ 1 := by simp [mc]
    rw [this, e1, h]; simp)
  refine ⟨_, lt_of_le_of_ne (integral_nonneg fun y => by positivity) hp.symm, e1, fun g => ?_⟩
  exact UpperTheory.MatrixCoefficientBound.coef_le (hK.fin M.μ M.dom hμ hD) hD hφ.1 hφ.2 hC g
