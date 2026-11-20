import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

namespace GlobalTheory.AdLat

/- English proof (translation)
The claim follows from `one_ne_zero`.
-/
theorem one_ne_zero_fracIdeal (F : Type) [Field F] [NumberField F] :
    (1 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := one_ne_zero

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h v`. Establish `hv` using `h v`. Unfold `GlobalTheory.Idele.localIdeal at hv`. Use `revert hv`.

Generalize the expression as in `a v = y`. Introduce `hv`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨k, hk, rfl⟩` from `hx`.

Take `⟨r, rfl⟩` from `(FractionalIdeal.mem_one_iff _).1 hk`. Conclude with `HeightOneSpectrum.coe_algebraMap_mem (R := 𝓞 F) (K := F) (v := v) r`. Consider the case `zero => exact zero_mem _`. Consider the case `add x y _ _ hx hy => exact add_mem hx hy`. Consider the case `smul c x _ hx`.

Rewrite using `[show c • x = (c : v.adicCompletion F) * x from rfl]`. Conclude with `mul_mem c.2 hx`. Introduce `h v`. Unfold `GlobalTheory.Idele.localIdeal`. Rewrite using `[← mul_one (a v), show a v * 1 = (⟨a v, h v⟩ : v.adicCompletionIntegers F) • (1 : v.adicCompletion F) from rfl]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩, map_one _⟩)`.
-/
theorem mem_adelicIdeal_one_iff_integral (F : Type) [Field F] [NumberField F]
    (a : FiniteAdeleRing (𝓞 F) F) :
    a ∈ GlobalTheory.Idele.adelicIdeal (1 : FractionalIdeal (𝓞 F)⁰ F) ↔
      ∀ v, a v ∈ v.adicCompletionIntegers F := by
  constructor
  · intro h v
    have hv := h v
    unfold GlobalTheory.Idele.localIdeal at hv
    revert hv
    generalize a v = y
    intro hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hk
      exact HeightOneSpectrum.coe_algebraMap_mem (R := 𝓞 F) (K := F) (v := v) r
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul c x _ hx =>
      rw [show c • x = (c : v.adicCompletion F) * x from rfl]
      exact mul_mem c.2 hx
  · intro h v
    unfold GlobalTheory.Idele.localIdeal
    rw [← mul_one (a v), show a v * 1 = (⟨a v, h v⟩ : v.adicCompletionIntegers F) •
      (1 : v.adicCompletion F) from rfl]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨1, (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩, map_one _⟩)

/- English proof (translation)
Take `⟨b, hb⟩` from `IsLocalization.exist_integer_multiples (𝓞 F)⁰ T c`. Use `set d : 𝓞 F := (b : 𝓞 F) with hd_def`. Establish `hd0 : d ≠ 0` using `nonZeroDivisors.ne_zero b.2`. Establish `hdK : algebraMap (𝓞 F) F d ≠ 0`. Rewrite using `[Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]` and apply the resulting hypothesis.

Establish `hex : ∀ v : HeightOneSpectrum (𝓞 F), ∃ r : 𝓞 F, algebraMap (𝓞 F) F r = algebraMap (𝓞 F) F d * (if v ∈ T then c v else 0)`. Introduce `v`. Distinguish the cases in `hv : v ∈ T`. Take `⟨r, hr⟩` from `RingHom.mem_rangeS.1 (hb v hv)`. Use `⟨r, ?_⟩` and prove the remaining obligations.

Rewrite using `[if_pos hv, hr, Algebra.smul_def]`. Conclude with `⟨0, by simp [hv]⟩`. Use `choose g hg using hex`. Establish `hfin : {v : HeightOneSpectrum (𝓞 F) | v.asIdeal ∣ Ideal.span {d}}.Finite` using `Ideal.finite_factors (by`. Simplify `hd0)` using `only [Submodule.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot]`.

Use `set S : Finset (HeightOneSpectrum (𝓞 F)) := T ∪ hfin.toFinset with hS`. Take `⟨r, hr⟩` from `IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) (fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal) (fun v : HeightOneSpectrum (𝓞 F) => (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {d} : Ideal (𝓞 F))).factors) (fun v _ => v.prime) (fun i _ j _ hij h => hij (HeightO …`. Establish `key : ∀ v ∈ S, v.valuation F (algebraMap (𝓞 F) F r / algebraMap (𝓞 F) F d - (if v ∈ T then c v else 0)) ≤ 1`. Introduce `v hv`. Establish `h1 : algebraMap (𝓞 F) F r / algebraMap (𝓞 F) F d - (if v ∈ T then c v else 0) = algebraMap (𝓞 F) F (r - g v) / algebraMap (𝓞 F) F d`.

Rewrite using `[map_sub, hg v, sub_div, mul_div_cancel_left₀ _ hdK]`. Rewrite using `[h1, map_div₀, div_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff (v.valuation F)).2 hdK)), HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap, v.intValuation_if_neg hd0]`. Conclude with `(v.intValuation_le_pow_iff_mem _ _).2 (hr v hv)`. Use `⟨algebraMap (𝓞 F) F r / algebraMap (𝓞 F) F d, fun v hv => ?_, fun v hv => ?_⟩` and prove the remaining obligations. Establish `h` using `key v (Finset.mem_union_left _ hv)`.

Rewrite `h` using `[if_pos hv]`. Then use the resulting hypothesis. Distinguish the cases in `hvS : v ∈ S`. Establish `h` using `key v hvS`. Rewrite `h` using `[if_neg hv, sub_zero]`. Then use the resulting hypothesis. Establish `hnd : ¬ v.asIdeal ∣ Ideal.span {d}` using `fun h => hvS (Finset.mem_union_right _ (hfin.mem_toFinset.2 h))`.

Establish `hd1 : v.valuation F (algebraMap (𝓞 F) F d) = 1`. Rewrite using `[HeightOneSpectrum.valuation_of_algebraMap]`. Conclude with `le_antisymm (v.intValuation_le_one d) (not_lt.1 (fun h => hnd ((v.intValuation_lt_one_iff_dvd d).1 h)))`. Rewrite using `[map_div₀, hd1, div_one, HeightOneSpectrum.valuation_of_algebraMap]`. Conclude with `v.intValuation_le_one r`.
-/
private theorem exists_valuation_sub_lt_of_injective (F : Type) [Field F] [NumberField F]
    (T : Finset (HeightOneSpectrum (𝓞 F))) (c : HeightOneSpectrum (𝓞 F) → F) :
    ∃ w : F, (∀ v ∈ T, v.valuation F (w - c v) ≤ 1) ∧ ∀ v ∉ T, v.valuation F w ≤ 1 := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (𝓞 F)⁰ T c
  set d : 𝓞 F := (b : 𝓞 F) with hd_def
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero b.2
  have hdK : algebraMap (𝓞 F) F d ≠ 0 := by
    rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]
  have hex : ∀ v : HeightOneSpectrum (𝓞 F), ∃ r : 𝓞 F,
      algebraMap (𝓞 F) F r = algebraMap (𝓞 F) F d * (if v ∈ T then c v else 0) := by
    intro v
    by_cases hv : v ∈ T
    · obtain ⟨r, hr⟩ := RingHom.mem_rangeS.1 (hb v hv)
      refine ⟨r, ?_⟩
      rw [if_pos hv, hr, Algebra.smul_def]
    · exact ⟨0, by simp [hv]⟩
  choose g hg using hex
  have hfin : {v : HeightOneSpectrum (𝓞 F) | v.asIdeal ∣ Ideal.span {d}}.Finite :=
    Ideal.finite_factors (by
      simpa only [Submodule.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot] using hd0)
  set S : Finset (HeightOneSpectrum (𝓞 F)) := T ∪ hfin.toFinset with hS
  obtain ⟨r, hr⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S)
    (fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal)
    (fun v : HeightOneSpectrum (𝓞 F) =>
      (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {d} : Ideal (𝓞 F))).factors)
    (fun v _ => v.prime) (fun i _ j _ hij h => hij (HeightOneSpectrum.ext h)) (fun i => g i)
  have key : ∀ v ∈ S, v.valuation F (algebraMap (𝓞 F) F r / algebraMap (𝓞 F) F d -
      (if v ∈ T then c v else 0)) ≤ 1 := by
    intro v hv
    have h1 : algebraMap (𝓞 F) F r / algebraMap (𝓞 F) F d - (if v ∈ T then c v else 0)
        = algebraMap (𝓞 F) F (r - g v) / algebraMap (𝓞 F) F d := by
      rw [map_sub, hg v, sub_div, mul_div_cancel_left₀ _ hdK]
    rw [h1, map_div₀, div_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff (v.valuation F)).2 hdK)),
      HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
      v.intValuation_if_neg hd0]
    exact (v.intValuation_le_pow_iff_mem _ _).2 (hr v hv)
  refine ⟨algebraMap (𝓞 F) F r / algebraMap (𝓞 F) F d, fun v hv => ?_, fun v hv => ?_⟩
  · have h := key v (Finset.mem_union_left _ hv)
    rwa [if_pos hv] at h
  · by_cases hvS : v ∈ S
    · have h := key v hvS
      rwa [if_neg hv, sub_zero] at h
    · have hnd : ¬ v.asIdeal ∣ Ideal.span {d} := fun h =>
        hvS (Finset.mem_union_right _ (hfin.mem_toFinset.2 h))
      have hd1 : v.valuation F (algebraMap (𝓞 F) F d) = 1 := by
        rw [HeightOneSpectrum.valuation_of_algebraMap]
        exact le_antisymm (v.intValuation_le_one d)
          (not_lt.1 (fun h => hnd ((v.intValuation_lt_one_iff_dvd d).1 h)))
      rw [map_div₀, hd1, div_one, HeightOneSpectrum.valuation_of_algebraMap]
      exact v.intValuation_le_one r

/- English proof (translation)
Establish `hfin : {v : HeightOneSpectrum (𝓞 F) | ¬ z v ∈ v.adicCompletionIntegers F}.Finite` using `Filter.eventually_cofinite.1 z.2`. Establish `hc : ∀ v : HeightOneSpectrum (𝓞 F), ∃ c : F, z v - (c : v.adicCompletion F) ∈ v.adicCompletionIntegers F`. Introduce `v`. Establish `hdense : DenseRange (fun c : F => (c : v.adicCompletion F))` using `HeightOneSpectrum.denseRange_algebraMap (K := F) (v := v)`. Establish `hopen : IsOpen {t : v.adicCompletion F | z v - t ∈ v.adicCompletionIntegers F}` using `(Valued.isOpen_valuationSubring _).preimage (continuous_const.sub continuous_id)`.

Establish `hne : z v ∈ {t : v.adicCompletion F | z v - t ∈ v.adicCompletionIntegers F}` using `by show z v - z v ∈ v.adicCompletionIntegers F`. Rewrite using `[sub_self]`. Conclude with `zero_mem _`. Conclude with `hdense.exists_mem_open hopen ⟨z v, hne⟩`. Use `choose c hc using hc`.

Take `⟨w, hw1, hw2⟩` from `exists_valuation_sub_lt_of_injective F hfin.toFinset c`. Use `⟨w, fun v => ?_⟩` and prove the remaining obligations. Rewrite using `[FiniteAdeleRing.algebraMap_apply]`. Distinguish the cases in `hv : v ∈ hfin.toFinset`. Establish `h1 : ((c v : F) : v.adicCompletion F) = ((c v - w : F) : v.adicCompletion F) + (w : v.adicCompletion F)`.

Rewrite using `[← HeightOneSpectrum.adicCompletion.coe_add, sub_add_cancel]`. Establish `h2 : z v - (w : v.adicCompletion F) = (z v - (c v : v.adicCompletion F)) + ((c v - w : F) : v.adicCompletion F)`. Rewrite using `[h1]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h2]`.

Use `add_mem (hc v) ?_` and prove the remaining obligations. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', Valuation.map_sub_swap]`. Conclude with `hw1 v hv`. Establish `hz : z v ∈ v.adicCompletionIntegers F`. Assume the negation of the conclusion as `h`.

Conclude with `hv (hfin.mem_toFinset.2 h)`. Use `sub_mem hz ?_` and prove the remaining obligations. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']`. Conclude with `hw2 v hv`.
-/
private theorem exists_sub_mem_adicCompletionIntegers' (F : Type) [Field F] [NumberField F]
    (z : FiniteAdeleRing (𝓞 F) F) :
    ∃ w : F, ∀ v, z v - algebraMap F (FiniteAdeleRing (𝓞 F) F) w v ∈
      v.adicCompletionIntegers F := by
  classical
  have hfin : {v : HeightOneSpectrum (𝓞 F) | ¬ z v ∈ v.adicCompletionIntegers F}.Finite :=
    Filter.eventually_cofinite.1 z.2
  have hc : ∀ v : HeightOneSpectrum (𝓞 F), ∃ c : F,
      z v - (c : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
    intro v
    have hdense : DenseRange (fun c : F => (c : v.adicCompletion F)) :=
      HeightOneSpectrum.denseRange_algebraMap (K := F) (v := v)
    have hopen : IsOpen {t : v.adicCompletion F | z v - t ∈ v.adicCompletionIntegers F} :=
      (Valued.isOpen_valuationSubring _).preimage (continuous_const.sub continuous_id)
    have hne : z v ∈ {t : v.adicCompletion F | z v - t ∈ v.adicCompletionIntegers F} := by
      show z v - z v ∈ v.adicCompletionIntegers F
      rw [sub_self]
      exact zero_mem _
    exact hdense.exists_mem_open hopen ⟨z v, hne⟩
  choose c hc using hc
  obtain ⟨w, hw1, hw2⟩ := exists_valuation_sub_lt_of_injective F hfin.toFinset c
  refine ⟨w, fun v => ?_⟩
  rw [FiniteAdeleRing.algebraMap_apply]
  by_cases hv : v ∈ hfin.toFinset
  · have h1 : ((c v : F) : v.adicCompletion F) =
        ((c v - w : F) : v.adicCompletion F) + (w : v.adicCompletion F) := by
      rw [← HeightOneSpectrum.adicCompletion.coe_add, sub_add_cancel]
    have h2 : z v - (w : v.adicCompletion F) =
        (z v - (c v : v.adicCompletion F)) + ((c v - w : F) : v.adicCompletion F) := by
      rw [h1]; ring
    rw [h2]
    refine add_mem (hc v) ?_
    rw [HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation', Valuation.map_sub_swap]
    exact hw1 v hv
  · have hz : z v ∈ v.adicCompletionIntegers F := by
      by_contra h
      exact hv (hfin.mem_toFinset.2 h)
    refine sub_mem hz ?_
    rw [HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hw2 v hv

/- English proof (translation)
Establish `hN' : (N : F) ≠ 0` using `Nat.cast_ne_zero.2 hN.ne'`. Take `⟨w, hw⟩` from `exists_sub_mem_adicCompletionIntegers' F (algebraMap F (FiniteAdeleRing (𝓞 F) F) (N : F)⁻¹ * y)`. Use `⟨N * w, algebraMap F (FiniteAdeleRing (𝓞 F) F) (N : F)⁻¹ * y - algebraMap F (FiniteAdeleRing (𝓞 F) F) w, fun v => hw v, ?_⟩` and prove the remaining obligations. Establish `hA : (N : FiniteAdeleRing (𝓞 F) F) * algebraMap F (FiniteAdeleRing (𝓞 F) F) (N : F)⁻¹ = 1`. Rewrite using `[← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)) N, ← map_mul, mul_inv_cancel₀ hN', map_one]`.

Rewrite using `[nsmul_eq_mul, map_mul, map_natCast]`. Take the linear combination `(-y) * hA`.
-/
theorem exists_eq_algebraMap_add_nsmul (F : Type) [Field F] [NumberField F] (N : ℕ) (hN : 0 < N)
    (y : FiniteAdeleRing (𝓞 F) F) :
    ∃ (x : F) (a : FiniteAdeleRing (𝓞 F) F), (∀ v, a v ∈ v.adicCompletionIntegers F) ∧
      y = algebraMap F _ x + N • a := by
  have hN' : (N : F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  obtain ⟨w, hw⟩ := exists_sub_mem_adicCompletionIntegers' F
    (algebraMap F (FiniteAdeleRing (𝓞 F) F) (N : F)⁻¹ * y)
  refine ⟨N * w, algebraMap F (FiniteAdeleRing (𝓞 F) F) (N : F)⁻¹ * y -
    algebraMap F (FiniteAdeleRing (𝓞 F) F) w, fun v => hw v, ?_⟩
  have hA : (N : FiniteAdeleRing (𝓞 F) F) * algebraMap F (FiniteAdeleRing (𝓞 F) F) (N : F)⁻¹ = 1 := by
    rw [← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)) N, ← map_mul,
      mul_inv_cancel₀ hN', map_one]
  rw [nsmul_eq_mul, map_mul, map_natCast]
  linear_combination (-y) * hA

/- English proof (translation)
Introduce `F _ _ N hN`. Use `⟨exists_eq_algebraMap_add_nsmul F N hN, fun y hy => ?_⟩` and prove the remaining obligations. Take `⟨x, a, ha, rfl⟩` from `exists_eq_algebraMap_add_nsmul F N hN y`. Establish `hx : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F x ≤ 1`. Introduce `v`.

Establish `hNa : (N • a) v ∈ v.adicCompletionIntegers F`. Rewrite using `[show (N • a) v = N • a v from rfl]`. Conclude with `nsmul_mem (ha v) N`. Establish `e : (algebraMap F (FiniteAdeleRing (𝓞 F) F) x + N • a) v = algebraMap F (FiniteAdeleRing (𝓞 F) F) x v + (N • a) v` using `rfl`. Establish `h` using `sub_mem (hy v) hNa`.

Rewrite `h` using `[e, add_sub_cancel_right, FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']`. Conclude with `h`. Take `⟨r, hr⟩` from `HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) (K := F) x hx`. Substitute `hr` using the available equality. Conclude with `⟨r, a, ha, rfl⟩`.
-/
theorem strong_approximation_mod_nat : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ), 0 < N → (∀ y : FiniteAdeleRing (𝓞 F) F, ∃ (x : F) (a : FiniteAdeleRing (𝓞 F) F), (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ y = algebraMap F _ x + N • a) ∧ ∀ y : FiniteAdeleRing (𝓞 F) F, (∀ v, y v ∈ v.adicCompletionIntegers F) → ∃ (x : 𝓞 F) (a : FiniteAdeleRing (𝓞 F) F), (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ y = algebraMap F _ (x : F) + N • a := by
  intro F _ _ N hN
  refine ⟨exists_eq_algebraMap_add_nsmul F N hN, fun y hy => ?_⟩
  obtain ⟨x, a, ha, rfl⟩ := exists_eq_algebraMap_add_nsmul F N hN y
  have hx : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F x ≤ 1 := by
    intro v
    have hNa : (N • a) v ∈ v.adicCompletionIntegers F := by
      rw [show (N • a) v = N • a v from rfl]
      exact nsmul_mem (ha v) N
    have e : (algebraMap F (FiniteAdeleRing (𝓞 F) F) x + N • a) v =
        algebraMap F (FiniteAdeleRing (𝓞 F) F) x v + (N • a) v := rfl
    have h := sub_mem (hy v) hNa
    rw [e, add_sub_cancel_right, FiniteAdeleRing.algebraMap_apply,
      HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h
    exact h
  obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) (K := F) x hx
  subst hr
  exact ⟨r, a, ha, rfl⟩

end GlobalTheory.AdLat
