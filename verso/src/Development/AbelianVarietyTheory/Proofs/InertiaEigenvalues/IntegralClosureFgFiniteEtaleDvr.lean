import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.NormDetMulProdSqLeOfEntryLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiscrMulMemOfIsIntegral

namespace GlobalTheory.IntegralClosureFG

/- English proof (translation)
Set `b0` to `Module.finBasis E A`. Establish `hex : ∀ i, ∃ d : O, d ≠ 0 ∧ IsIntegral O (d • b0 i)`. Introduce `i`. Establish `h : IsAlgebraic E (b0 i)` using `Algebra.IsAlgebraic.isAlgebraic _`. Establish `h' : IsAlgebraic O (b0 i)` using `(IsFractionRing.isAlgebraic_iff O E A).2 h`.

Take `⟨d, hd, hi⟩` from `h'.exists_integral_multiple`. Conclude with `⟨d, hd, hi⟩`. Use `choose d hd0 hdi using hex`. Establish `hu : ∀ i, IsUnit (algebraMap O E (d i))` using `fun i => isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective O E)).2 (hd0 i))`. Set `b` to `b0.isUnitSMul hu`.

Establish `hb : ∀ i, IsIntegral O (b i)`. Introduce `i`. Rewrite using `[Module.Basis.isUnitSMul_apply, algebraMap_smul]`. Conclude with `hdi i`. Set `D : E` to `(Algebra.traceMatrix E b).det`.

Establish `hD : D ≠ 0`. Establish `h1` using `(GlobalTheory.discr_ne_zero_iff_of_etale (K := E) (A := A) (by simp) (b : Fin (Module.finrank E A) → A)).2 b.linearIndependent`. Rewrite `h1` using `[Algebra.discr_def]`. Then use the resulting hypothesis. Establish `hint : ∀ e : E, IsIntegral O e → ∃ u : O, algebraMap O E u = e`. Introduce `e he`.

Conclude with `IsIntegrallyClosed.isIntegral_iff.1 he`. Set `S : Submodule O A` to `Submodule.span O (Set.range fun j => D⁻¹ • b j)`. Establish `hS : S.FG` using `Submodule.fg_span (Set.finite_range _)`. Establish `hle : Subalgebra.toSubmodule (integralClosure O A) ≤ S`. Introduce `x hx`.

Establish `hx' : IsIntegral O x` using `hx`. Take `⟨v, hv⟩` from `GlobalTheory.DiscConductor.det_smul_eq_sum O E A (Fin (Module.finrank E A)) b x (fun i j => hint _ (GlobalTheory.DiscConductor.isIntegral_trace_of_isIntegral O E A _ ((hb i).mul (hb j)))) (fun i => hint _ (GlobalTheory.DiscConductor.isIntegral_trace_of_isIntegral O E A _ (hx'.mul …`. Establish `hx2 : x = ∑ j, v j • (D⁻¹ • b j)`. Establish `: x = D⁻¹ • (D • x)` using `by rw [smul_smul, inv_mul_cancel₀ hD, one_smul]`. Rewrite using `[this, hv, Finset.smul_sum]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul, ← algebraMap_smul E (v j) (D⁻¹ • b j), smul_smul, mul_comm]`. Rewrite using `[hx2]`. Conclude with `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)`. Use `haveI : IsNoetherian O S := isNoetherian_of_fg_of_noetherian S hS`.

Conclude with `isNoetherian_submodule.1 this _ hle`.
-/
theorem integralClosure_fg (O E A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A]
    [IsScalarTower O E A] [Module.Finite E A] [Algebra.Etale E A] :
    (Subalgebra.toSubmodule (integralClosure O A)).FG := by
  classical
  let b0 := Module.finBasis E A
  have hex : ∀ i, ∃ d : O, d ≠ 0 ∧ IsIntegral O (d • b0 i) := by
    intro i
    have h : IsAlgebraic E (b0 i) := Algebra.IsAlgebraic.isAlgebraic _
    have h' : IsAlgebraic O (b0 i) := (IsFractionRing.isAlgebraic_iff O E A).2 h
    obtain ⟨d, hd, hi⟩ := h'.exists_integral_multiple
    exact ⟨d, hd, hi⟩
  choose d hd0 hdi using hex
  have hu : ∀ i, IsUnit (algebraMap O E (d i)) := fun i =>
    isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective O E)).2 (hd0 i))
  let b := b0.isUnitSMul hu
  have hb : ∀ i, IsIntegral O (b i) := by
    intro i
    rw [Module.Basis.isUnitSMul_apply, algebraMap_smul]
    exact hdi i
  let D : E := (Algebra.traceMatrix E b).det
  have hD : D ≠ 0 := by
    have h1 := (GlobalTheory.discr_ne_zero_iff_of_etale (K := E) (A := A)
      (by simp) (b : Fin (Module.finrank E A) → A)).2 b.linearIndependent
    rwa [Algebra.discr_def] at h1
  have hint : ∀ e : E, IsIntegral O e → ∃ u : O, algebraMap O E u = e := by
    intro e he
    exact IsIntegrallyClosed.isIntegral_iff.1 he
  let S : Submodule O A := Submodule.span O (Set.range fun j => D⁻¹ • b j)
  have hS : S.FG := Submodule.fg_span (Set.finite_range _)
  have hle : Subalgebra.toSubmodule (integralClosure O A) ≤ S := by
    intro x hx
    have hx' : IsIntegral O x := hx
    obtain ⟨v, hv⟩ := GlobalTheory.DiscConductor.det_smul_eq_sum O E A (Fin (Module.finrank E A)) b x
      (fun i j => hint _ (GlobalTheory.DiscConductor.isIntegral_trace_of_isIntegral O E A _
        ((hb i).mul (hb j))))
      (fun i => hint _ (GlobalTheory.DiscConductor.isIntegral_trace_of_isIntegral O E A _
        (hx'.mul (hb i))))
    have hx2 : x = ∑ j, v j • (D⁻¹ • b j) := by
      have : x = D⁻¹ • (D • x) := by rw [smul_smul, inv_mul_cancel₀ hD, one_smul]
      rw [this, hv, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul, ← algebraMap_smul E (v j) (D⁻¹ • b j), smul_smul, mul_comm]
    rw [hx2]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  haveI : IsNoetherian O S := isNoetherian_of_fg_of_noetherian S hS
  exact isNoetherian_submodule.1 this _ hle

end GlobalTheory.IntegralClosureFG
