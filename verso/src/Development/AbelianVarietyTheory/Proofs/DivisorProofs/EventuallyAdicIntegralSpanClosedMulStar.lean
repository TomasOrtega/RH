import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntBTmulBasis
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.AdicSpan

/- English proof (translation)
Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := ℤ) x`. Establish `hb0 : b ≠ 0` using `nonZeroDivisors.ne_zero hb`. Establish `hI : Ideal.span {b} ≠ (0 : Ideal ℤ)`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `hb0`.

Use `Filter.eventually_cofinite.2 ((Ideal.finite_factors hI).subset fun w hw => ?_)` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq] at hw ⊢`. Assume the negation of the conclusion as `hd`. Apply `hw` to reduce the goal to its premises. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers]`.

Use `(HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _).trans_le ?_` and prove the remaining obligations. Establish `h1 : w.valuation ℚ (algebraMap ℤ ℚ b) = 1` using `le_antisymm (w.valuation_le_one b) (not_lt.1 fun h => hd ((w.valuation_lt_one_iff_dvd b).1 h))`. Simplify using `only [Algebra.algebraMap_self, RingHom.id_apply]`. Rewrite using `[map_div₀, h1, div_one]`. Conclude with `w.valuation_le_one a`.
-/
theorem rat_mem_adicCompletionIntegers_eventually (x : ℚ) :
    ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite,
      algebraMap ℚ (v.adicCompletion ℚ) x ∈ v.adicCompletionIntegers ℚ := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := ℤ) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hI : Ideal.span {b} ≠ (0 : Ideal ℤ) := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hb0
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors hI).subset fun w hw => ?_)
  simp only [Set.mem_setOf_eq] at hw ⊢
  by_contra hd
  apply hw
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  refine (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _).trans_le ?_
  have h1 : w.valuation ℚ (algebraMap ℤ ℚ b) = 1 :=
    le_antisymm (w.valuation_le_one b) (not_lt.1 fun h => hd ((w.valuation_lt_one_iff_dvd b).1 h))
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  rw [map_div₀, h1, div_one]
  exact w.valuation_le_one a

section

variable {C : Type} [Ring C] [Algebra ℚ C] {κ : Type} (b : Module.Basis κ ℚ C) (v : HeightOneSpectrum ℤ)

/- English proof (translation)
Rewrite using `[Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]`.
-/
theorem repr_tmul_apply (a : v.adicCompletion ℚ) (x : C) (k : κ) :
    (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b).repr (a ⊗ₜ[ℚ] x) k =
      a * algebraMap ℚ (v.adicCompletion ℚ) (b.repr x k) := by
  rw [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]

/- English proof (translation)
Use `conv_lhs => rw [← (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b).sum_repr y]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]`.
-/
theorem eq_sum_tmul [Fintype κ] (y : v.adicCompletion ℚ ⊗[ℚ] C) :
    y = ∑ i, (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b).repr y i ⊗ₜ[ℚ] b i := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b).sum_repr y]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end

/- English proof (translation)
Introduce `C _ _ _ σ κ b`. Use `haveI : Fintype κ := FiniteDimensional.fintypeBasisIndex b`. Establish `hc : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ t : κ × κ × κ, algebraMap ℚ (v.adicCompletion ℚ) (b.repr (b t.1 * b t.2.1) t.2.2) ∈ v.adicCompletionIntegers ℚ` using `Filter.eventually_all.2 fun t => rat_mem_adicCompletionIntegers_eventually _`. Establish `hs : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ t : κ × κ, algebraMap ℚ (v.adicCompletion ℚ) (b.repr (σ (b t.1)).unop t.2) ∈ v.adicCompletionIntegers ℚ` using `Filter.eventually_all.2 fun t => rat_mem_adicCompletionIntegers_eventually _`. Establish `hfin` using `Filter.eventually_cofinite.1 (hc.and hs)`.

Use `⟨hfin.toFinset, fun v hv => ?_⟩` and prove the remaining obligations. Rewrite `hv` using `[Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not]`. Take `⟨hcv, hsv⟩` from `hv`. Use `⟨fun y z hy hz k => ?_, fun y hy k => ?_⟩` and prove the remaining obligations. Rewrite using `[eq_sum_tmul b v y, eq_sum_tmul b v z, Finset.sum_mul_sum, map_sum, Finsupp.finset_sum_apply]`.

Use `sum_mem fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_sum, Finsupp.finset_sum_apply]`. Use `sum_mem fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, repr_tmul_apply]`. Conclude with `mul_mem (mul_mem (hy i) (hz j)) (hcv (i, j, k))`.

Establish `hu : ∀ (f : κ → (v.adicCompletion ℚ ⊗[ℚ] C)ᵐᵒᵖ), (∑ i, f i).unop = ∑ i, (f i).unop` using `fun f => map_sum (MulOpposite.opAddEquiv : v.adicCompletion ℚ ⊗[ℚ] C ≃+ _).symm f Finset.univ`. Rewrite using `[eq_sum_tmul b v y, map_sum, hu, map_sum, Finsupp.finset_sum_apply]`. Use `sum_mem fun i _ => ?_` and prove the remaining obligations. Rewrite using `[starT_tmul, repr_tmul_apply]`. Conclude with `mul_mem (hy i) (hsv (i, k))`.
-/
theorem isIntB_mul_star_eventually : ∀ (C : Type) [Ring C] [Algebra ℚ C] [FiniteDimensional ℚ C] (σ : C →+* Cᵐᵒᵖ) (κ : Type)
    (b : Module.Basis κ ℚ C), ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S,
      (∀ y z, IsIntB v b y → IsIntB v b z → IsIntB v b (y * z)) ∧
      (∀ y, IsIntB v b y → IsIntB v b (starT σ (v.adicCompletion ℚ) y).unop) := by
  intro C _ _ _ σ κ b
  haveI : Fintype κ := FiniteDimensional.fintypeBasisIndex b
  have hc : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ t : κ × κ × κ,
      algebraMap ℚ (v.adicCompletion ℚ) (b.repr (b t.1 * b t.2.1) t.2.2) ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun t => rat_mem_adicCompletionIntegers_eventually _
  have hs : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ t : κ × κ,
      algebraMap ℚ (v.adicCompletion ℚ) (b.repr (σ (b t.1)).unop t.2) ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun t => rat_mem_adicCompletionIntegers_eventually _
  have hfin := Filter.eventually_cofinite.1 (hc.and hs)
  refine ⟨hfin.toFinset, fun v hv => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hv
  obtain ⟨hcv, hsv⟩ := hv
  refine ⟨fun y z hy hz k => ?_, fun y hy k => ?_⟩
  · rw [eq_sum_tmul b v y, eq_sum_tmul b v z, Finset.sum_mul_sum, map_sum, Finsupp.finset_sum_apply]
    refine sum_mem fun i _ => ?_
    rw [map_sum, Finsupp.finset_sum_apply]
    refine sum_mem fun j _ => ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul, repr_tmul_apply]
    exact mul_mem (mul_mem (hy i) (hz j)) (hcv (i, j, k))
  · have hu : ∀ (f : κ → (v.adicCompletion ℚ ⊗[ℚ] C)ᵐᵒᵖ), (∑ i, f i).unop = ∑ i, (f i).unop :=
      fun f => map_sum (MulOpposite.opAddEquiv : v.adicCompletion ℚ ⊗[ℚ] C ≃+ _).symm f Finset.univ
    rw [eq_sum_tmul b v y, map_sum, hu, map_sum, Finsupp.finset_sum_apply]
    refine sum_mem fun i _ => ?_
    rw [starT_tmul, repr_tmul_apply]
    exact mul_mem (hy i) (hsv (i, k))

end GlobalTheory.AdicSpan
