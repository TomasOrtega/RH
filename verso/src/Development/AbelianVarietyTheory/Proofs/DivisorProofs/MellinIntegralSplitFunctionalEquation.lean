import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CompletedLStripBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormWt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussZero
open NumberField MeasureTheory

namespace GlobalTheory

/- English proof (translation)
Set `L : (I → ℝ) →ₗ[ℝ] ℝ` to `∑ i, LinearMap.proj i`. Establish `hL : ∀ y, L y = ∑ i, y i` using `by intro y; simp [L]`. Establish `hset : {y : I → ℝ | ∑ i, y i = 0} = (LinearMap.ker L : Set (I → ℝ))`. Use extensionality with `y`. Simplify using `[hL]`.

Rewrite using `[hset]`. Apply `Measure.addHaar_submodule` to reduce the goal to its premises. Introduce `htop`. Take `⟨i⟩` from `(inferInstance : Nonempty I)`. Establish `hmem : Pi.single i (1:ℝ) ∈ LinearMap.ker L` using `htop ▸ Submodule.mem_top`.

Rewrite `hmem` using `[LinearMap.mem_ker, hL]`. Simplify using `at hmem`.
-/
theorem mellinSplit_hyperplane_null (I : Type) [Fintype I] [Nonempty I] :
    (volume : Measure (I → ℝ)) {y : I → ℝ | ∑ i, y i = 0} = 0 := by
  let L : (I → ℝ) →ₗ[ℝ] ℝ := ∑ i, LinearMap.proj i
  have hL : ∀ y, L y = ∑ i, y i := by intro y; simp [L]
  have hset : {y : I → ℝ | ∑ i, y i = 0} = (LinearMap.ker L : Set (I → ℝ)) := by
    ext y; simp [hL]
  rw [hset]
  apply Measure.addHaar_submodule
  intro htop
  classical
  obtain ⟨i⟩ := (inferInstance : Nonempty I)
  have hmem : Pi.single i (1:ℝ) ∈ LinearMap.ker L := htop ▸ Submodule.mem_top
  rw [LinearMap.mem_ker, hL] at hmem
  simp at hmem

/- English proof (translation)
Use `set f : (I → ℝ) → ℂ := fun y => (p y : ℂ) * θ y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ)) with hf`. Use `set g : (I → ℝ) → ℂ := fun y => (p (-y) : ℂ) * θ' y * Complex.exp ((1 - s) * ((∑ i, y i : ℝ) : ℂ)) with hg`. Use `set S : Set (I → ℝ) := {y | 0 ≤ ∑ i, y i} with hS`. Use `set P : Set (I → ℝ) := {y | 0 < ∑ i, y i} with hP`. Establish `hcont : Continuous (fun y : I → ℝ => ∑ i, y i)` using `continuous_finset_sum _ fun i _ => continuous_apply i`.

Establish `hSm : MeasurableSet S` using `(isClosed_le continuous_const hcont).measurableSet`. Establish `hsumneg : ∀ y : I → ℝ, ∑ i, (-y) i = -∑ i, y i`. Introduce `y`. Simplify using `[Finset.sum_neg_distrib]`. Establish `hfg : ∀ y, f y = κ * g (-y)`.

Introduce `y`. Simplify using `only [hf, hg, hθ, neg_neg, hsumneg]`. Establish `e : Complex.exp (-((∑ i, y i : ℝ) : ℂ)) * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ)) = Complex.exp ((1 - s) * ((-∑ i, y i : ℝ) : ℂ))`. Rewrite using `[← Complex.exp_add]`. Use `push_cast`.

Put the polynomial expressions in normal form. Establish `e2 : ((Real.exp (-∑ i, y i) : ℝ) : ℂ) = Complex.exp (-((∑ i, y i : ℝ) : ℂ))` using `by push_cast; rfl`. Rewrite using `[e2]`. Take the linear combination `((p y : ℂ) * κ * θ' (-y)) * e`. Establish `hpre : (Neg.neg : (I → ℝ) → (I → ℝ)) ⁻¹' P = Sᶜ`.

Use extensionality with `y`. Simplify using `[hP, hS, hsumneg]`. Establish `hmp : MeasurePreserving (Neg.neg : (I → ℝ) → (I → ℝ)) volume volume` using `Measure.measurePreserving_neg _`. Establish `hemb : MeasurableEmbedding (Neg.neg : (I → ℝ) → (I → ℝ))` using `(MeasurableEquiv.neg (I → ℝ)).measurableEmbedding`. Establish `hPS : P =ᵐ[volume] S`.

Rewrite using `[ae_eq_set]`. Prove the components needed by the constructor for the conclusion. Establish `: P \ S = ∅` using `Set.diff_eq_empty.mpr (fun y (hy : 0 < ∑ i, y i) => (le_of_lt hy : 0 ≤ ∑ i, y i))`. Rewrite using `[this, measure_empty]`. Apply `measure_mono_null _ (mellinSplit_hyperplane_null I)` to reduce the goal to its premises.

Introduce `y hy`. Simplify using `only [hP, hS, Set.mem_diff, Set.mem_setOf_eq, not_lt] at hy`. Conclude with `le_antisymm hy.2 hy.1`. Establish `hgP : IntegrableOn g P volume` using `IntegrableOn.congr_set_ae (show IntegrableOn g S volume from h2) hPS`. Establish `hfc : IntegrableOn f Sᶜ volume`.

Use `(hmp.integrableOn_comp_preimage hemb).2 hgP` as an intermediate fact. Rewrite `this` using `[hpre]`. Establish `h3` using `this.const_mul κ`. Use `IntegrableOn.congr_fun h3 (fun y _ => ?_) hSm.compl` and prove the remaining obligations. Simplify using `[hfg y]`.

Establish `hfint : Integrable f volume`. Use `IntegrableOn.union (show IntegrableOn f S volume from h1) hfc` as an intermediate fact. Rewrite `this` using `[Set.union_compl_self, integrableOn_univ]`. Then use the resulting hypothesis. Rewrite using `[← integral_add_compl hSm hfint]`. Use `congr 1`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hpre, hmp.setIntegral_preimage_emb hemb]`. Use `_ = κ * ∫ y in S, g y := by rw [setIntegral_congr_set hPS]`.
-/
theorem mellinSplit_neg (I : Type) [Fintype I] [Nonempty I] (p : (I → ℝ) → ℝ) (θ θ' : (I → ℝ) → ℂ) (κ s : ℂ)
    (hθ : ∀ y, θ y = κ * (Real.exp (-∑ i, y i) : ℂ) * θ' (-y))
    (h1 : MeasureTheory.Integrable (fun y => (p y : ℂ) * θ y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ))) (MeasureTheory.volume.restrict {y : I → ℝ | 0 ≤ ∑ i, y i}))
    (h2 : MeasureTheory.Integrable (fun y => (p (-y) : ℂ) * θ' y * Complex.exp ((1 - s) * ((∑ i, y i : ℝ) : ℂ))) (MeasureTheory.volume.restrict {y : I → ℝ | 0 ≤ ∑ i, y i})) :
    ∫ y, (p y : ℂ) * θ y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ)) = (∫ y in {y : I → ℝ | 0 ≤ ∑ i, y i}, (p y : ℂ) * θ y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ))) + κ * ∫ y in {y : I → ℝ | 0 ≤ ∑ i, y i}, (p (-y) : ℂ) * θ' y * Complex.exp ((1 - s) * ((∑ i, y i : ℝ) : ℂ)) := by
  set f : (I → ℝ) → ℂ := fun y => (p y : ℂ) * θ y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ)) with hf
  set g : (I → ℝ) → ℂ := fun y => (p (-y) : ℂ) * θ' y * Complex.exp ((1 - s) * ((∑ i, y i : ℝ) : ℂ)) with hg
  set S : Set (I → ℝ) := {y | 0 ≤ ∑ i, y i} with hS
  set P : Set (I → ℝ) := {y | 0 < ∑ i, y i} with hP
  have hcont : Continuous (fun y : I → ℝ => ∑ i, y i) :=
    continuous_finset_sum _ fun i _ => continuous_apply i
  have hSm : MeasurableSet S := (isClosed_le continuous_const hcont).measurableSet
  have hsumneg : ∀ y : I → ℝ, ∑ i, (-y) i = -∑ i, y i := by
    intro y; simp [Finset.sum_neg_distrib]
  have hfg : ∀ y, f y = κ * g (-y) := by
    intro y
    simp only [hf, hg, hθ, neg_neg, hsumneg]
    have e : Complex.exp (-((∑ i, y i : ℝ) : ℂ)) * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ))
        = Complex.exp ((1 - s) * ((-∑ i, y i : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]; push_cast; ring_nf
    have e2 : ((Real.exp (-∑ i, y i) : ℝ) : ℂ) = Complex.exp (-((∑ i, y i : ℝ) : ℂ)) := by
      push_cast; rfl
    rw [e2]
    linear_combination ((p y : ℂ) * κ * θ' (-y)) * e
  have hpre : (Neg.neg : (I → ℝ) → (I → ℝ)) ⁻¹' P = Sᶜ := by
    ext y; simp [hP, hS, hsumneg]
  have hmp : MeasurePreserving (Neg.neg : (I → ℝ) → (I → ℝ)) volume volume :=
    Measure.measurePreserving_neg _
  have hemb : MeasurableEmbedding (Neg.neg : (I → ℝ) → (I → ℝ)) :=
    (MeasurableEquiv.neg (I → ℝ)).measurableEmbedding
  have hPS : P =ᵐ[volume] S := by
    rw [ae_eq_set]
    constructor
    · have : P \ S = ∅ := Set.diff_eq_empty.mpr (fun y (hy : 0 < ∑ i, y i) => (le_of_lt hy : 0 ≤ ∑ i, y i))
      rw [this, measure_empty]
    · apply measure_mono_null _ (mellinSplit_hyperplane_null I)
      intro y hy
      simp only [hP, hS, Set.mem_diff, Set.mem_setOf_eq, not_lt] at hy
      exact le_antisymm hy.2 hy.1
  have hgP : IntegrableOn g P volume :=
    IntegrableOn.congr_set_ae (show IntegrableOn g S volume from h2) hPS
  have hfc : IntegrableOn f Sᶜ volume := by
    have := (hmp.integrableOn_comp_preimage hemb).2 hgP
    rw [hpre] at this
    have h3 := this.const_mul κ
    refine IntegrableOn.congr_fun h3 (fun y _ => ?_) hSm.compl
    simp [hfg y]
  have hfint : Integrable f volume := by
    have := IntegrableOn.union (show IntegrableOn f S volume from h1) hfc
    rwa [Set.union_compl_self, integrableOn_univ] at this
  rw [← integral_add_compl hSm hfint]
  congr 1
  calc ∫ y in Sᶜ, f y = ∫ y in Sᶜ, κ * g (-y) := by simp_rw [hfg]
    _ = κ * ∫ y in Sᶜ, g (-y) := integral_const_mul _ _
    _ = κ * ∫ y in P, g y := by
        rw [← hpre, hmp.setIntegral_preimage_emb hemb]
    _ = κ * ∫ y in S, g y := by rw [setIntegral_congr_set hPS]

end GlobalTheory
