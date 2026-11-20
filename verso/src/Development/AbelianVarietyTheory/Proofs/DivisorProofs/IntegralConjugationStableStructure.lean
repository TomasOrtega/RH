import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntCZero

noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical
open IsDedekindDomain

namespace GlobalTheory.FinClsLoc

/- English proof (translation)
Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := ℤ) x`. Establish `hb0 : b ≠ 0` using `nonZeroDivisors.ne_zero hb`. Establish `hI : Ideal.span {b} ≠ (0 : Ideal ℤ)`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `hb0`.

Use `Filter.eventually_cofinite.2 ((Ideal.finite_factors hI).subset fun w hw => ?_)` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq] at hw ⊢`. Assume the negation of the conclusion as `hd`. Apply `hw` to reduce the goal to its premises. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers]`.

Use `(HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _).trans_le ?_` and prove the remaining obligations. Establish `h1 : w.valuation ℚ (algebraMap ℤ ℚ b) = 1` using `le_antisymm (w.valuation_le_one b) (not_lt.1 fun h => hd ((w.valuation_lt_one_iff_dvd b).1 h))`. Simplify using `only [Algebra.algebraMap_self, RingHom.id_apply]`. Rewrite using `[map_div₀, h1, div_one]`. Conclude with `w.valuation_le_one a`.
-/
theorem ratInt_eventually (x : ℚ) :
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

/- English proof (translation)
The claim follows from `(Subtype.val_injective.tendsto_cofinite).eventually (ratInt_eventually x)`.
-/
theorem ratInt_eventually_away {p : ℕ} (x : ℚ) :
    ∀ᶠ w : AwayP p in Filter.cofinite,
      algebraMap ℚ (w.1.adicCompletion ℚ) x ∈ w.1.adicCompletionIntegers ℚ :=
  (Subtype.val_injective.tendsto_cofinite).eventually (ratInt_eventually x)

section

variable {C : Type} [Ring C] [Algebra ℚ C] {κ : Type} [Fintype κ] (b : Module.Basis κ ℚ C)
  (v : HeightOneSpectrum ℤ)

/- English proof (translation)
Rewrite using `[Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]`.
-/
theorem repr_tmul_apply' (a : v.adicCompletion ℚ) (x : C) (k : κ) :
    (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b).repr (a ⊗ₜ[ℚ] x) k =
      a * algebraMap ℚ (v.adicCompletion ℚ) (b.repr x k) := by
  rw [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]

/- English proof (translation)
Use `conv_lhs => rw [← (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b).sum_repr y]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]`.
-/
theorem eq_sum_tmul' (y : v.adicCompletion ℚ ⊗[ℚ] C) :
    y = ∑ i, (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b).repr y i ⊗ₜ[ℚ] b i := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b).sum_repr y]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end

/- English proof (translation)
Introduce `p _ G β`. Use `set bb := Module.finBasis ℚ G.C`. Establish `hc : ∀ᶠ w : AwayP p in Filter.cofinite, ∀ t : Fin (Module.finrank ℚ G.C) × Fin (Module.finrank ℚ G.C) × Fin (Module.finrank ℚ G.C), algebraMap ℚ (w.1.adicCompletion ℚ) (bb.repr (bb t.1 * bb t.2.1) t.2.2) ∈ w.1.adicCompletionIntegers ℚ` using `Filter.eventually_all.2 fun t => ratInt_eventually_away _`. Establish `hs : ∀ᶠ w : AwayP p in Filter.cofinite, ∀ t : Fin (Module.finrank ℚ G.C) × Fin (Module.finrank ℚ G.C), algebraMap ℚ (w.1.adicCompletion ℚ) (bb.repr (G.star (bb t.1)).unop t.2) ∈ w.1.adicCompletionIntegers ℚ` using `Filter.eventually_all.2 fun t => ratInt_eventually_away _`. Establish `hb : ∀ x : G.C, ∀ᶠ w : AwayP p in Filter.cofinite, ∀ k : Fin (Module.finrank ℚ G.C), algebraMap ℚ (w.1.adicCompletion ℚ) (bb.repr x k) ∈ w.1.adicCompletionIntegers ℚ` using `fun x => Filter.eventually_all.2 fun k => ratInt_eventually_away _`.

Establish `hin : ∀ (w : AwayP p) (x : G.C), (∀ k, algebraMap ℚ (w.1.adicCompletion ℚ) (bb.repr x k) ∈ w.1.adicCompletionIntegers ℚ) → IntC G w (inC G (w.1.adicCompletion ℚ) x)`. Introduce `w x hx k`. Express the relevant statement in the definitionally equal form `(Algebra.TensorProduct.basis (w.1.adicCompletion ℚ) bb).repr ((1 : w.1.adicCompletion ℚ) ⊗ₜ[ℚ] x) k ∈ _`. Rewrite using `[repr_tmul_apply', one_mul]`. Conclude with `hx k`.

Use `filter_upwards [hc, hs, hb (β : G.C), hb ((β⁻¹ : G.Cˣ) : G.C)] with w hcv hsv hbv hbv'`. Use `⟨fun y z hy hz k => ?_, fun y hy k => ?_, hin w _ hbv, hin w _ hbv'⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(Algebra.TensorProduct.basis (w.1.adicCompletion ℚ) bb).repr (y * z) k ∈ _`. Rewrite using `[eq_sum_tmul' bb w.1 y, eq_sum_tmul' bb w.1 z, Finset.sum_mul_sum, map_sum, Finsupp.finset_sum_apply]`. Use `sum_mem fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[map_sum, Finsupp.finset_sum_apply]`. Use `sum_mem fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, repr_tmul_apply']`. Conclude with `mul_mem (mul_mem (hy i) (hz j)) (hcv (i, j, k))`. Establish `hu : ∀ (f : Fin (Module.finrank ℚ G.C) → (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ᵐᵒᵖ), (∑ i, f i).unop = ∑ i, (f i).unop` using `fun f => map_sum (MulOpposite.opAddEquiv : w.1.adicCompletion ℚ ⊗[ℚ] G.C ≃+ _).symm f Finset.univ`.

Express the relevant statement in the definitionally equal form `(Algebra.TensorProduct.basis (w.1.adicCompletion ℚ) bb).repr _ k ∈ _`. Rewrite using `[eq_sum_tmul' bb w.1 y, map_sum, hu, map_sum, Finsupp.finset_sum_apply]`. Use `sum_mem fun i _ => ?_` and prove the remaining obligations. Rewrite using `[starT_tmul, repr_tmul_apply']`. Conclude with `mul_mem (hy i) (hsv (i, k))`.
-/
theorem intC_stab : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ), ∀ᶠ w : AwayP p in Filter.cofinite,
    (∀ a b : (w.1.adicCompletion ℚ ⊗[ℚ] G.C), IntC G w a → IntC G w b → IntC G w (a * b)) ∧
    (∀ a : (w.1.adicCompletion ℚ ⊗[ℚ] G.C), IntC G w a → IntC G w (starT G.star (w.1.adicCompletion ℚ) a).unop) ∧
    IntC G w (inC G (w.1.adicCompletion ℚ) (β : G.C)) ∧ IntC G w (inC G (w.1.adicCompletion ℚ) ((β⁻¹ : G.Cˣ) : G.C)) := by
  intro p _ G β
  set bb := Module.finBasis ℚ G.C
  have hc : ∀ᶠ w : AwayP p in Filter.cofinite, ∀ t : Fin (Module.finrank ℚ G.C) × Fin (Module.finrank ℚ G.C) ×
      Fin (Module.finrank ℚ G.C),
      algebraMap ℚ (w.1.adicCompletion ℚ) (bb.repr (bb t.1 * bb t.2.1) t.2.2) ∈ w.1.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun t => ratInt_eventually_away _
  have hs : ∀ᶠ w : AwayP p in Filter.cofinite, ∀ t : Fin (Module.finrank ℚ G.C) × Fin (Module.finrank ℚ G.C),
      algebraMap ℚ (w.1.adicCompletion ℚ) (bb.repr (G.star (bb t.1)).unop t.2) ∈ w.1.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun t => ratInt_eventually_away _
  have hb : ∀ x : G.C, ∀ᶠ w : AwayP p in Filter.cofinite, ∀ k : Fin (Module.finrank ℚ G.C),
      algebraMap ℚ (w.1.adicCompletion ℚ) (bb.repr x k) ∈ w.1.adicCompletionIntegers ℚ :=
    fun x => Filter.eventually_all.2 fun k => ratInt_eventually_away _
  have hin : ∀ (w : AwayP p) (x : G.C), (∀ k, algebraMap ℚ (w.1.adicCompletion ℚ) (bb.repr x k) ∈
      w.1.adicCompletionIntegers ℚ) → IntC G w (inC G (w.1.adicCompletion ℚ) x) := by
    intro w x hx k
    change (Algebra.TensorProduct.basis (w.1.adicCompletion ℚ) bb).repr ((1 : w.1.adicCompletion ℚ) ⊗ₜ[ℚ] x) k ∈ _
    rw [repr_tmul_apply', one_mul]
    exact hx k
  filter_upwards [hc, hs, hb (β : G.C), hb ((β⁻¹ : G.Cˣ) : G.C)] with w hcv hsv hbv hbv'
  refine ⟨fun y z hy hz k => ?_, fun y hy k => ?_, hin w _ hbv, hin w _ hbv'⟩
  · change (Algebra.TensorProduct.basis (w.1.adicCompletion ℚ) bb).repr (y * z) k ∈ _
    rw [eq_sum_tmul' bb w.1 y, eq_sum_tmul' bb w.1 z, Finset.sum_mul_sum, map_sum, Finsupp.finset_sum_apply]
    refine sum_mem fun i _ => ?_
    rw [map_sum, Finsupp.finset_sum_apply]
    refine sum_mem fun j _ => ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul, repr_tmul_apply']
    exact mul_mem (mul_mem (hy i) (hz j)) (hcv (i, j, k))
  · have hu : ∀ (f : Fin (Module.finrank ℚ G.C) → (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ᵐᵒᵖ),
        (∑ i, f i).unop = ∑ i, (f i).unop :=
      fun f => map_sum (MulOpposite.opAddEquiv : w.1.adicCompletion ℚ ⊗[ℚ] G.C ≃+ _).symm f Finset.univ
    change (Algebra.TensorProduct.basis (w.1.adicCompletion ℚ) bb).repr _ k ∈ _
    rw [eq_sum_tmul' bb w.1 y, map_sum, hu, map_sum, Finsupp.finset_sum_apply]
    refine sum_mem fun i _ => ?_
    rw [starT_tmul, repr_tmul_apply']
    exact mul_mem (hy i) (hsv (i, k))

end GlobalTheory.FinClsLoc
