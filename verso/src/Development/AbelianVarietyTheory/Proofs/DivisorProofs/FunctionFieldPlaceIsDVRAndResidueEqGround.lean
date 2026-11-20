import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldOneVariableTranscendentalFiniteAndEStatement

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef

/- English proof (translation)
Establish `hn : Nontrivial (MonoidWithZeroHom.valueGroup (MonoidWithZeroHom.ofClass v.1))`. Take `⟨z, hz⟩` from `v.2.1 ((Multiplicative.ofAdd (1:ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))`. Set `u : (WithZero (Multiplicative ℤ))ˣ` to `Units.mk0 ((Multiplicative.ofAdd (1:ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) WithZero.coe_ne_zero`. Use `⟨⟨1, ⟨u, MonoidWithZeroHom.mem_valueGroup _ ⟨z, hz⟩⟩, ?_⟩⟩` and prove the remaining obligations. Introduce `h`.

Use `congrArg (fun u => ((u : _ ˣ) : WithZero (Multiplicative ℤ))) (congrArg Subtype.val h)` as an intermediate fact. Establish `h2 : (Multiplicative.ofAdd (1:ℤ)) = 1` using `WithZero.coe_injective (by simpa [u] using this.symm)`. Simplify using `at h2`. Conclude with `Valuation.valuationSubring_isDiscreteValuationRing v.1`.
-/
theorem isDiscreteValuationRing_functionFieldPlace_ring {k F : Type} [Field k] [Field F] [Algebra k F] (v : Place k F) :
    IsDiscreteValuationRing v.O := by
  have hn : Nontrivial (MonoidWithZeroHom.valueGroup (MonoidWithZeroHom.ofClass v.1)) := by
    obtain ⟨z, hz⟩ := v.2.1 ((Multiplicative.ofAdd (1:ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
    let u : (WithZero (Multiplicative ℤ))ˣ :=
      Units.mk0 ((Multiplicative.ofAdd (1:ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) WithZero.coe_ne_zero
    refine ⟨⟨1, ⟨u, MonoidWithZeroHom.mem_valueGroup _ ⟨z, hz⟩⟩, ?_⟩⟩
    intro h
    have := congrArg (fun u => ((u : _ ˣ) : WithZero (Multiplicative ℤ))) (congrArg Subtype.val h)
    have h2 : (Multiplicative.ofAdd (1:ℤ)) = 1 := WithZero.coe_injective (by simpa [u] using this.symm)
    simp at h2
  exact Valuation.valuationSubring_isDiscreteValuationRing v.1

/- English proof (translation)
Distinguish the cases in `hc : c = 0`. Simplify using `[hc]`. Conclude with `(v.2.2 c hc).le`.
-/
theorem place_le_one_const {k F : Type} [Field k] [Field F] [Algebra k F] (v : Place k F) (c : k) :
    v.1 (algebraMap k F c) ≤ 1 := by
  by_cases hc : c = 0
  · simp [hc]
  · exact (v.2.2 c hc).le

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Establish `h1 : ∀ c : k, v.1 (x - algebraMap k F c) = 1` using `fun c => le_antisymm ((v.1.map_sub _ _).trans (max_le hx (place_le_one_const v c))) (hne c)`. Establish `hq : ∀ q : k[X], q ≠ 0 → v.1 (Polynomial.aeval x q) = 1`. Introduce `q hq0`.

Establish `hs` using `Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C (p := q) IsAlgClosed.card_roots_eq_natDegree`. Rewrite using `[← hs, map_mul, map_multiset_prod, Multiset.map_map, map_mul, map_multiset_prod]`. Simplify using `only [Polynomial.aeval_C, Function.comp_def, map_sub, Polynomial.aeval_X, Multiset.map_map]`. Rewrite using `[(v.2.2 _ (Polynomial.leadingCoeff_ne_zero.mpr hq0)), one_mul]`. Simplify using `[h1]`.

Establish `htr : Transcendental k x`. Introduce and unpack `⟨q, hq0, hqx⟩`. Use `hq q hq0` as an intermediate fact. Rewrite `this` using `[hqx, map_zero]`. Conclude with `zero_ne_one this`.

Use `haveI hfin : FiniteDimensional k⟮x⟯ F := (GlobalTheory.T.functionFieldOneVariable_transcendental_finite_and_ext k F hF).1 x htr`. Establish `hK : ∀ y ∈ k⟮x⟯, v.1 y ≤ 1`. Introduce `y hy`. Take `⟨r, s, rfl⟩` from `(IntermediateField.mem_adjoin_simple_iff k y).1 hy`. Establish `hle : ∀ q : k[X], v.1 (Polynomial.aeval x q) ≤ 1` using `fun q => by`.

Distinguish the cases in `h0 : q = 0`. Simplify using `[h0]`. Conclude with `(hq q h0).le`. Distinguish the cases in `hs0 : s = 0`. Simplify using `[hs0]`.

Rewrite using `[map_div₀, hq s hs0, div_one]`. Conclude with `hle r`. Establish `hint : ∀ y : F, v.1 y ≤ 1`. Introduce `y`. Take `⟨f, hm, hf⟩` from `Algebra.IsIntegral.isIntegral (R := k⟮x⟯) y`.

Establish `hc : ∀ i, v.1 (algebraMap k⟮x⟯ F (f.coeff i)) ≤ 1` using `fun i => hK _ (f.coeff i).2`. Distinguish the cases in `hn : f.natDegree = 0`. Rewrite `hn` using `[Polynomial.natDegree_eq_zero]`. Take `⟨c, rfl⟩` from `hn`. Simplify using `[hm.ne_zero_of_C] at hf`.

Simplify using `only [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hm.coeff_natDegree, map_one, one_mul, add_eq_zero_iff_eq_neg] at hf`. Use `apply_fun v.1 at hf`. Rewrite `hf` using `[Valuation.map_neg, Valuation.map_pow]`. Use `contrapose! hf`. Use `ne_of_lt (v.1.map_sum_lt ?_ ?_)` and prove the remaining obligations.

Simplify using `[hn, (hf.trans' (zero_lt_one)).ne']`. Introduce `i hi`. Rewrite `hi` using `[Finset.mem_range]`. Rewrite using `[Valuation.map_mul, Valuation.map_pow]`. Conclude with `mul_lt_of_le_one_of_lt (hc _) <| pow_lt_pow_right₀ hf hi`.

Take `⟨z, hz⟩` from `v.2.1 ((Multiplicative.ofAdd (1:ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))`. Use `hint z` as an intermediate fact. Rewrite `this` using `[hz]`. Conclude with `absurd this (by decide)`.
-/
theorem functionFieldPlace_exists_const_sub_lt_one {k F : Type} [Field k] [IsAlgClosed k] [Field F] [Algebra k F]
    (hF : IsFF k F) (v : Place k F) (x : F) (hx : v.1 x ≤ 1) :
    ∃ c : k, v.1 (x - algebraMap k F c) < 1 := by
  by_contra hne
  push_neg at hne
  have h1 : ∀ c : k, v.1 (x - algebraMap k F c) = 1 := fun c =>
    le_antisymm ((v.1.map_sub _ _).trans (max_le hx (place_le_one_const v c))) (hne c)
  have hq : ∀ q : k[X], q ≠ 0 → v.1 (Polynomial.aeval x q) = 1 := by
    intro q hq0
    have hs := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C (p := q) IsAlgClosed.card_roots_eq_natDegree
    rw [← hs, map_mul, map_multiset_prod, Multiset.map_map, map_mul, map_multiset_prod]
    simp only [Polynomial.aeval_C, Function.comp_def, map_sub, Polynomial.aeval_X, Multiset.map_map]
    rw [(v.2.2 _ (Polynomial.leadingCoeff_ne_zero.mpr hq0)), one_mul]
    simp [h1]
  have htr : Transcendental k x := by
    rintro ⟨q, hq0, hqx⟩
    have := hq q hq0
    rw [hqx, map_zero] at this
    exact zero_ne_one this
  haveI hfin : FiniteDimensional k⟮x⟯ F := (GlobalTheory.T.functionFieldOneVariable_transcendental_finite_and_ext k F hF).1 x htr
  have hK : ∀ y ∈ k⟮x⟯, v.1 y ≤ 1 := by
    intro y hy
    obtain ⟨r, s, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff k y).1 hy
    have hle : ∀ q : k[X], v.1 (Polynomial.aeval x q) ≤ 1 := fun q => by
      by_cases h0 : q = 0
      · simp [h0]
      · exact (hq q h0).le
    by_cases hs0 : s = 0
    · simp [hs0]
    · rw [map_div₀, hq s hs0, div_one]
      exact hle r
  have hint : ∀ y : F, v.1 y ≤ 1 := by
    intro y
    obtain ⟨f, hm, hf⟩ := Algebra.IsIntegral.isIntegral (R := k⟮x⟯) y
    have hc : ∀ i, v.1 (algebraMap k⟮x⟯ F (f.coeff i)) ≤ 1 := fun i => hK _ (f.coeff i).2
    by_cases hn : f.natDegree = 0
    · rw [Polynomial.natDegree_eq_zero] at hn
      obtain ⟨c, rfl⟩ := hn
      simp [hm.ne_zero_of_C] at hf
    simp only [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hm.coeff_natDegree, map_one,
      one_mul, add_eq_zero_iff_eq_neg] at hf
    apply_fun v.1 at hf
    rw [Valuation.map_neg, Valuation.map_pow] at hf
    contrapose! hf
    refine ne_of_lt (v.1.map_sum_lt ?_ ?_)
    · simp [hn, (hf.trans' (zero_lt_one)).ne']
    · intro i hi
      rw [Finset.mem_range] at hi
      rw [Valuation.map_mul, Valuation.map_pow]
      exact mul_lt_of_le_one_of_lt (hc _) <| pow_lt_pow_right₀ hf hi
  obtain ⟨z, hz⟩ := v.2.1 ((Multiplicative.ofAdd (1:ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
  have := hint z
  rw [hz] at this
  exact absurd this (by decide)

/- English proof (translation)
Introduce `k F _ _ _ _ _ hF v`. Conclude with `⟨isDiscreteValuationRing_functionFieldPlace_ring v, fun x hx => functionFieldPlace_exists_const_sub_lt_one hF v x hx⟩`.
-/
theorem place_isDVR_residue : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ v : Place k F, IsDiscreteValuationRing v.O ∧ ∀ x : F, v.1 x ≤ 1 → ∃ c : k, v.1 (x - algebraMap k F c) < 1 := by
  intro k F _ _ _ _ _ hF v
  exact ⟨isDiscreteValuationRing_functionFieldPlace_ring v, fun x hx => functionFieldPlace_exists_const_sub_lt_one hF v x hx⟩

end GlobalTheory.Nef
