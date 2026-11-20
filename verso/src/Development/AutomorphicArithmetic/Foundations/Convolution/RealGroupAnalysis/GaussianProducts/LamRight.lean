import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.LintegralUnipotentQuotientRightInvariant

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

open scoped Pointwise in

/- English proof (translation)
Establish `hD` using `isAddFundamentalDomain_fundamentalSet F`. Use `haveI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)`. Use `haveI : Countable (AdeleRing.principalSubgroup (𝓞 F) F) := by`. Use `(Set.countable_range (fun ξ : F => (rt ξ : A F))).mono ?_ |>.to_subtype` and prove the remaining obligations. Introduce and unpack `_ ⟨ξ, rfl⟩`.

Conclude with `⟨ξ, rfl⟩`. Establish `hT` using `hD.vadd_of_comm a`. Establish `hp` using `measurePreserving_add_right (adeleMeasure F) a`. Establish `e : (fun b : A F => b + a) ⁻¹' (a +ᵥ fundamentalSet F) = fundamentalSet F`. Use extensionality with `x`.

Simplify using `[Set.mem_vadd_set, add_comm]`. Establish `h1` using `hp.setLIntegral_comp_preimage_emb (MeasurableEquiv.addRight a).measurableEmbedding h (a +ᵥ fundamentalSet F)`. Rewrite `h1` using `[e]`. Rewrite using `[h1]`. Use `hT.setLIntegral_eq hD h ?_` and prove the remaining obligations.

Introduce and unpack `⟨_, k, rfl⟩ x`. Conclude with `hh k x`.
-/
private theorem lint_add {F : Type} [Field F] [NumberField F] {h : A F → ℝ≥0∞}
    (hh : ∀ (k : F) x, h (rt k + x) = h x) (a : A F) :
    ∫⁻ b in fundamentalSet F, h (b + a) ∂(adeleMeasure F) = ∫⁻ b in fundamentalSet F, h b ∂(adeleMeasure F) := by
  have hD := isAddFundamentalDomain_fundamentalSet F
  haveI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  haveI : Countable (AdeleRing.principalSubgroup (𝓞 F) F) := by
    refine (Set.countable_range (fun ξ : F => (rt ξ : A F))).mono ?_ |>.to_subtype
    rintro _ ⟨ξ, rfl⟩
    exact ⟨ξ, rfl⟩
  have hT := hD.vadd_of_comm a
  have hp := measurePreserving_add_right (adeleMeasure F) a
  have e : (fun b : A F => b + a) ⁻¹' (a +ᵥ fundamentalSet F) = fundamentalSet F := by
    ext x
    simp [Set.mem_vadd_set, add_comm]
  have h1 := hp.setLIntegral_comp_preimage_emb (MeasurableEquiv.addRight a).measurableEmbedding h (a +ᵥ fundamentalSet F)
  rw [e] at h1
  rw [h1]
  refine hT.setLIntegral_eq hD h ?_
  rintro ⟨_, k, rfl⟩ x
  exact hh k x

/- English proof (translation)
Introduce `F _ _ _ M₀ u hu c g₀`. Establish `hnU : Measurable (nU : A F → G1 F)` using `M.continuous_nU.measurable`. Use `set U : G1 F → ℝ≥0∞ := fun g => ∫⁻ b in fundamentalSet F, ‖u (nU b * g)‖ₑ ∂(adeleMeasure F) with hUdef`. Establish `hUm : Measurable U` using `Measurable.lintegral_prod_right' (ν := (adeleMeasure F).restrict (fundamentalSet F)) (f := fun q : G1 F × A F => ‖u (nU q.2 * q.1)‖ₑ) (hu.1.comp ((hnU.comp measurable_snd).mul measurable_fst)).enorm`. Establish `hUi : ∀ b g, U (nU b * g) = U g`.

Introduce `a g`. Use `lint_add (F := F) (h := fun b => ‖u (nU b * g)‖ₑ) (fun k x => by` as an intermediate fact. Simplify using `only [M.nU_add, mul_assoc, hu.2]) a`. Simplify using `only [hUdef]`. Rewrite using `[← this]`.

Simplify using `only [M.nU_add, mul_assoc]`. Establish `hc : ‖c‖ₑ ≠ ⊤` using `enorm_ne_top`. Establish `hJ` using `M.lintegral_unipotent_quotient_right_invariant F M₀ U hUm hUi g₀`. Establish `hL : abelian₂ M₀ (fun g => c * u (g * g₀)) = ‖c‖ₑ * M.J0 M₀ (fun g => U (g * g₀))`. Simplify using `only [abelian₂, M.J0]`.

Rewrite using `[← lintegral_const_mul' _ _ hc]`. Use `lintegral_congr fun p => ?_` and prove the remaining obligations. Establish `: ∫⁻ b in fundamentalSet F, ‖c * u (nU b * (mD p.1 * p.2) * g₀)‖ₑ ∂(adeleMeasure F) = ‖c‖ₑ * U (mD p.1 * p.2 * g₀)`. Simplify using `only [hUdef, enorm_mul, mul_assoc]`. Conclude with `lintegral_const_mul' _ _ hc`.

Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hL, hJ]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.ConvolutionTheory.R2.G.lamRight :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (M : Meas F) (u : G1 F → ℂ), NInv u → ∀ (c : ℂ) (g₀ : G1 F), abelian₂ M (fun g => c * u (g * g₀)) = ‖c‖ₑ * abelian₂ M u := by
  intro F _ _ _ M₀ u hu c g₀
  have hnU : Measurable (nU : A F → G1 F) := M.continuous_nU.measurable
  set U : G1 F → ℝ≥0∞ := fun g => ∫⁻ b in fundamentalSet F, ‖u (nU b * g)‖ₑ ∂(adeleMeasure F) with hUdef
  have hUm : Measurable U :=
    Measurable.lintegral_prod_right' (ν := (adeleMeasure F).restrict (fundamentalSet F))
      (f := fun q : G1 F × A F => ‖u (nU q.2 * q.1)‖ₑ)
      (hu.1.comp ((hnU.comp measurable_snd).mul measurable_fst)).enorm
  have hUi : ∀ b g, U (nU b * g) = U g := by
    intro a g
    have := lint_add (F := F) (h := fun b => ‖u (nU b * g)‖ₑ) (fun k x => by
      simp only [M.nU_add, mul_assoc, hu.2]) a
    simp only [hUdef]
    rw [← this]
    simp only [M.nU_add, mul_assoc]
  have hc : ‖c‖ₑ ≠ ⊤ := enorm_ne_top
  have hJ := M.lintegral_unipotent_quotient_right_invariant F M₀ U hUm hUi g₀
  have hL : abelian₂ M₀ (fun g => c * u (g * g₀)) = ‖c‖ₑ * M.J0 M₀ (fun g => U (g * g₀)) := by
    simp only [abelian₂, M.J0]
    rw [← lintegral_const_mul' _ _ hc]
    refine lintegral_congr fun p => ?_
    have : ∫⁻ b in fundamentalSet F, ‖c * u (nU b * (mD p.1 * p.2) * g₀)‖ₑ ∂(adeleMeasure F) =
        ‖c‖ₑ * U (mD p.1 * p.2 * g₀) := by
      simp only [hUdef, enorm_mul, mul_assoc]
      exact lintegral_const_mul' _ _ hc
    rw [this]
    ring
  rw [hL, hJ]
  rfl
