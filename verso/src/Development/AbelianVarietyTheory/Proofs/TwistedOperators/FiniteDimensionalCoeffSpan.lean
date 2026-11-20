import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsGrowthSobNeTopOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.KTypeExtension
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite

namespace GlobalTheory.CoefficientSpanFiniteDimensional

/- English proof (translation)
Use `conv_lhs => rw [← b.sum_repr w]`. Rewrite using `[map_sum, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, map_smul]`. Use `conv_lhs => rw [← b.sum_repr (A (b j))]`.

Rewrite using `[map_sum, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, smul_eq_mul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dual_apply_eq_sum {W ι : Type} [AddCommGroup W] [Module ℂ W] [Fintype ι] (b : Module.Basis ι ℂ W)
    (ℓ : Module.Dual ℂ W) (w : W) (A : W →ₗ[ℂ] W) :
    ℓ (A w) = ∑ j, ∑ i, (b.repr w j * ℓ (b i)) * b.repr (A (b j)) i := by
  conv_lhs => rw [← b.sum_repr w]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, map_smul]
  conv_lhs => rw [← b.sum_repr (A (b j))]
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul, smul_eq_mul]
  ring

/- English proof (translation)
Set `b` to `Module.finBasis ℂ W`. Set `e : Fin (Module.finrank ℂ W) × Fin (Module.finrank ℂ W) → (K → ℂ)` to `fun p k => b.repr (ρ k (b p.2)) p.1`. Use `haveI : FiniteDimensional ℂ ↥(Submodule.span ℂ (Set.range e)) := FiniteDimensional.span_of_finite ℂ (Set.finite_range e)`. Use `Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range e)) (Submodule.span_le.mpr ?_)` and prove the remaining obligations. Introduce and unpack `f ⟨ℓ, w, rfl⟩`.

Establish `h : (fun k => ℓ (ρ k w)) = ∑ j, ∑ i, (b.repr w j * ℓ (b i)) • e (i, j)`. Use function extensionality and compare the values at `k`. Rewrite using `[dual_apply_eq_sum b ℓ w (ρ k)]`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, e]`. Rewrite using `[h]`.

Conclude with `Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, j), rfl⟩)`.
-/
theorem finiteDimensional_coeffSpan {K W : Type} [Group K] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ K W) : FiniteDimensional ℂ ↥(GlobalTheory.Published.AutFin.coeffSpan ρ) := by
  classical
  let b := Module.finBasis ℂ W
  let e : Fin (Module.finrank ℂ W) × Fin (Module.finrank ℂ W) → (K → ℂ) :=
    fun p k => b.repr (ρ k (b p.2)) p.1
  haveI : FiniteDimensional ℂ ↥(Submodule.span ℂ (Set.range e)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range e)
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range e)) (Submodule.span_le.mpr ?_)
  rintro f ⟨ℓ, w, rfl⟩
  have h : (fun k => ℓ (ρ k w)) = ∑ j, ∑ i, (b.repr w j * ℓ (b i)) • e (i, j) := by
    funext k
    rw [dual_apply_eq_sum b ℓ w (ρ k)]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, e]
  rw [h]
  exact Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, j), rfl⟩)

end GlobalTheory.CoefficientSpanFiniteDimensional
