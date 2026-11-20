import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.DomValInt

/- English proof (translation)
Establish `hcl : IsIntegrallyClosedIn (integralClosure W F).toSubring F` using `inferInstanceAs (IsIntegrallyClosedIn (integralClosure W F) F)`. Assume the negation of the conclusion as `hn`. Establish `hsn : y ∉ (integralClosure W F).toSubring` using `hn`. Take `⟨V, hV, hyV⟩` from `Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn hsn`. Conclude with `hyV (hy V fun w => hV (Subalgebra.algebraMap_mem _ w))`.
-/
theorem isIntegral_of_forall_valuationSubring (W : Type) [CommRing W] (F : Type) [Field F]
    [Algebra W F] (y : F)
    (hy : ∀ V : ValuationSubring F, (∀ w : W, algebraMap W F w ∈ V) → y ∈ V) :
    IsIntegral W y := by
  have hcl : IsIntegrallyClosedIn (integralClosure W F).toSubring F :=
    inferInstanceAs (IsIntegrallyClosedIn (integralClosure W F) F)
  by_contra hn
  have hsn : y ∉ (integralClosure W F).toSubring := hn
  obtain ⟨V, hV, hyV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn hsn
  exact hyV (hy V fun w => hV (Subalgebra.algebraMap_mem _ w))

/- English proof (translation)
Rewrite using `[← hrel, show n + 1 = j + (n + 1 - j) by omega, Finset.sum_range_add, Finset.mul_sum, show j + (n + 1 - j) - j = n + 1 - j by omega]`. Use `congr 1`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[pow_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem split_rel {F : Type} [Field F] (c : ℕ → F) (x : F) (n j : ℕ) (hjn : j ≤ n)
    (hrel : ∑ i ∈ Finset.range (n + 1), c i * x ^ i = 0) :
    (∑ i ∈ Finset.range j, c i * x ^ i) +
      x ^ j * ∑ k ∈ Finset.range (n + 1 - j), c (j + k) * x ^ k = 0 := by
  rw [← hrel, show n + 1 = j + (n + 1 - j) by omega, Finset.sum_range_add, Finset.mul_sum,
    show j + (n + 1 - j) - j = n + 1 - j by omega]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pow_add]; ring

/- English proof (translation)
Establish `hsplit` using `split_rel c x n j hjn hrel`. Use `set s := ∑ k ∈ Finset.range (n + 1 - j), c (j + k) * x ^ k with hs`. Distinguish the cases in `hxV : x ∈ V`. Establish `: s ∈ V`. Rewrite using `[hs]`.

Conclude with `sum_mem fun k _ => mul_mem (hc _) (pow_mem hxV k)`. Conclude with `⟨this, mul_mem this hxV⟩`. Establish `hx0 : x ≠ 0` using `fun h => hxV (h ▸ V.zero_mem)`. Establish `hxi : x⁻¹ ∈ V` using `(V.mem_or_inv_mem x).resolve_left hxV`. Break down `j with _ | j'` into its components or cases.

Simplify using `at hsplit`. Rewrite using `[hsplit]`. Simplify using the standard rewrite rules. Use `set A' := ∑ i ∈ Finset.range (j' + 1), c i * x⁻¹ ^ (j' - i) with hA'`. Establish `hA'V : A' ∈ V` using `sum_mem fun i _ => mul_mem (hc _) (pow_mem hxi _)`.

Establish `hA'x : A' * x ^ j' = ∑ i ∈ Finset.range (j' + 1), c i * x ^ i`. Rewrite using `[hA', Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Establish `hi' : i ≤ j'` using `Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)`. Rewrite using `[show x ^ j' = x ^ (j' - i) * x ^ i by rw [← pow_add]; congr 1; omega, inv_pow]`.

Clear the denominators using the available nonvanishing facts. Establish `hsx : s * x = -A'`. Establish `hpow : x ^ j' ≠ 0` using `pow_ne_zero _ hx0`. Apply `mul_right_cancel₀ hpow` to reduce the goal to its premises. Rewrite using `[neg_mul, hA'x, _root_.mul_assoc, ← pow_succ']`.

Take the linear combination `hsplit`. Establish `htV : s * x ∈ V` using `by rw [hsx]; exact neg_mem hA'V`. Use `⟨?_, htV⟩` and prove the remaining obligations. Establish `: s = (s * x) * x⁻¹` using `by field_simp`. Rewrite using `[this]`.

Conclude with `mul_mem htV hxi`.
-/
theorem tail_mem {F' : Type} [Field F'] (V : ValuationSubring F') (c : ℕ → F') (hc : ∀ i, c i ∈ V) (x : F')
    (n j : ℕ) (hjn : j ≤ n) (hrel : ∑ i ∈ Finset.range (n + 1), c i * x ^ i = 0) :
    (∑ k ∈ Finset.range (n + 1 - j), c (j + k) * x ^ k) ∈ V ∧
      (∑ k ∈ Finset.range (n + 1 - j), c (j + k) * x ^ k) * x ∈ V := by
  have hsplit := split_rel c x n j hjn hrel
  set s := ∑ k ∈ Finset.range (n + 1 - j), c (j + k) * x ^ k with hs
  by_cases hxV : x ∈ V
  · have : s ∈ V := by
      rw [hs]
      exact sum_mem fun k _ => mul_mem (hc _) (pow_mem hxV k)
    exact ⟨this, mul_mem this hxV⟩
  have hx0 : x ≠ 0 := fun h => hxV (h ▸ V.zero_mem)
  have hxi : x⁻¹ ∈ V := (V.mem_or_inv_mem x).resolve_left hxV
  rcases j with _ | j'
  · simp at hsplit
    rw [hsplit]; simp
  · set A' := ∑ i ∈ Finset.range (j' + 1), c i * x⁻¹ ^ (j' - i) with hA'
    have hA'V : A' ∈ V := sum_mem fun i _ => mul_mem (hc _) (pow_mem hxi _)
    have hA'x : A' * x ^ j' = ∑ i ∈ Finset.range (j' + 1), c i * x ^ i := by
      rw [hA', Finset.sum_mul]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i ≤ j' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [show x ^ j' = x ^ (j' - i) * x ^ i by rw [← pow_add]; congr 1; omega, inv_pow]
      field_simp
    have hsx : s * x = -A' := by
      have hpow : x ^ j' ≠ 0 := pow_ne_zero _ hx0
      apply mul_right_cancel₀ hpow
      rw [neg_mul, hA'x, _root_.mul_assoc, ← pow_succ']
      linear_combination hsplit
    have htV : s * x ∈ V := by rw [hsx]; exact neg_mem hA'V
    refine ⟨?_, htV⟩
    have : s = (s * x) * x⁻¹ := by field_simp
    rw [this]; exact mul_mem htV hxi

end GlobalTheory.DomValInt

namespace GlobalTheory.DomValInt

/- English proof (translation)
Introduce `W _ _ _ F _ _ _ _ _ O hW hmax x hxO`. Establish `hK : ∀ a : FractionRing W, algebraMap (FractionRing W) F a ∈ O → ∃ w : W, algebraMap W F w = algebraMap (FractionRing W) F a`. Introduce `a ha`. Break down `ValuationRing.isInteger_or_isInteger W a with ⟨w, hw⟩ | ⟨w, hw⟩` into its components or cases. Conclude with `⟨w, by rw [IsScalarTower.algebraMap_apply W (FractionRing W) F, hw]⟩`.

Distinguish the cases in `ha0 : a = 0`. Conclude with `⟨0, by simp [ha0]⟩`. Distinguish the cases in `hu : IsUnit w`. Use `⟨↑hu.unit⁻¹, ?_⟩` and prove the remaining obligations. Establish `h1 : a⁻¹ * algebraMap W (FractionRing W) ↑hu.unit⁻¹ = 1`.

Rewrite using `[← hw, ← map_mul, IsUnit.mul_val_inv, map_one]`. Establish `h2` using `(inv_mul_eq_one₀ ha0).mp h1`. Rewrite using `[IsScalarTower.algebraMap_apply W (FractionRing W) F, ← h2]`. Establish `hwm : w ∈ maximalIdeal W` using `(mem_maximalIdeal _).mpr hu`. Establish `h2` using `(O.mem_nonunits_iff).mp (hmax w hwm)`.

Establish `h3` using `(O.valuation_le_one_iff _).mpr ha`. Establish `h4 : algebraMap (FractionRing W) F a * algebraMap W F w = 1`. Rewrite using `[IsScalarTower.algebraMap_apply W (FractionRing W) F, hw, ← map_mul, mul_inv_cancel₀ ha0, map_one]`. Establish `h5 : O.valuation (algebraMap (FractionRing W) F a * algebraMap W F w) < 1`. Rewrite using `[map_mul]`.

Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' h3) h2`. Rewrite `h5` using `[h4, map_one]`. Conclude with `absurd h5 (lt_irrefl _)`. Take `⟨p, hp0, hpx⟩` from `Algebra.IsAlgebraic.isAlgebraic (R := FractionRing W) x`. Use `set n := p.natDegree with hn`.

Use `set b : ℕ → F := fun i => algebraMap (FractionRing W) F (p.coeff i) with hb`. Use `set v := O.valuation with hv`. Take `⟨i0, hi0, hi0max⟩` from `Finset.exists_max_image (Finset.range (n + 1)) (fun i => v (b i)) ⟨0, by simp⟩`. Use `set M := v (b i0) with hM`. Use `set S := (Finset.range (n + 1)).filter (fun i => v (b i) = M) with hS`.

Take `⟨j, hjS, hjmax⟩` from `Finset.exists_max_image S id ⟨i0, Finset.mem_filter.mpr ⟨hi0, rfl⟩⟩`. Establish `hjn : j ≤ n` using `Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hjS).1)`. Establish `hjM : v (b j) = M` using `(Finset.mem_filter.mp hjS).2`. Establish `hcoeff0 : ∀ i, n < i → b i = 0` using `fun i hi => by`. Simplify using `[b, Polynomial.coeff_eq_zero_of_natDegree_lt (show p.natDegree < i by omega)]`.

Establish `hle : ∀ i, v (b i) ≤ M` using `fun i => by`. Distinguish the cases in `hi : i ≤ n`. Conclude with `hi0max i (Finset.mem_range.mpr (by omega))`. Rewrite using `[hcoeff0 i (by omega), map_zero]; exact zero_le'`. Establish `hM0 : M ≠ 0`.

Introduce `h`. Establish `h1 : v (b n) = 0` using `le_antisymm (h ▸ hle n) zero_le'`. Rewrite `h1` using `[Valuation.zero_iff]`. Establish `h2 : p.leadingCoeff = 0` using `(algebraMap (FractionRing W) F).injective (by rw [map_zero]; exact h1)`. Conclude with `hp0 (Polynomial.leadingCoeff_eq_zero.mp h2)`.

Establish `hlt : ∀ i, j < i → v (b i) < M`. Introduce `i hi`. Break down `lt_or_eq_of_le (hle i) with h | h` into its components or cases. Conclude with `h`. It suffices to derive a contradiction.

Distinguish the cases in `hin : i ≤ n`. Establish `hiS : i ∈ S` using `Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), h⟩`. Use `hjmax i hiS` as an intermediate fact. Simplify using `only [id] at this`. Use linear arithmetic over natural numbers and integers.

Rewrite `h` using `[hcoeff0 i (by omega), map_zero]`. Conclude with `hM0 h.symm`. Establish `hbj : b j ≠ 0` using `fun h => hM0 (by rw [← hjM, h, map_zero])`. Establish `hMpos : 0 < M` using `zero_lt_iff.mpr hM0`. Use `set c : ℕ → F := fun i => b i / b j with hc`.

Establish `hcle : ∀ i, v (c i) ≤ 1` using `fun i => by`. Simplify using `only [c, map_div₀, hjM]`. Conclude with `(div_le_one₀ hMpos).mpr (hle i)`. Establish `hclt : ∀ i, j < i → v (c i) < 1` using `fun i hi => by`. Simplify using `only [c, map_div₀, hjM]`.

Conclude with `(div_lt_one₀ hMpos).mpr (hlt i hi)`. Establish `hcW : ∀ i, ∃ w : W, algebraMap W F w = c i` using `fun i => by`. Establish `hci : c i = algebraMap (FractionRing W) F (p.coeff i / p.coeff j)`. Simplify using `[c, b, map_div₀]`. Rewrite using `[hci]`.

Conclude with `hK _ (by rw [← hci]; exact (O.valuation_le_one_iff _).mp (hcle i))`. Establish `hcj : c j = 1` using `div_self hbj`. Establish `hrel : ∑ i ∈ Finset.range (n + 1), c i * x ^ i = 0`. Establish `h` using `hpx`. Rewrite `h` using `[Polynomial.aeval_eq_sum_range]`.

Simplify using `only [c, div_mul_eq_mul_div, ← Finset.sum_div]`. Rewrite using `[div_eq_zero_iff]`. Use `left`. Simplify `h` using `[Algebra.smul_def, b]`. Use `set s := ∑ k ∈ Finset.range (n + 1 - j), c (j + k) * x ^ k with hs`.

Establish `hmemV : ∀ V : ValuationSubring F, (∀ w : W, algebraMap W F w ∈ V) → s ∈ V ∧ s * x ∈ V` using `fun V hV => tail_mem V c (fun i => by obtain ⟨w, hw⟩ := hcW i; rw [← hw]; exact hV w) x n j hjn hrel`. Use `⟨s, s * x, isIntegral_of_forall_valuationSubring W F s fun V hV => (hmemV V hV).1, isIntegral_of_forall_valuationSubring W F _ fun V hV => (hmemV V hV).2, ?_, rfl⟩` and prove the remaining obligations. Establish `hxle : v x ≤ 1` using `(O.valuation_le_one_iff x).mpr hxO`. Rewrite using `[hs, show n + 1 - j = (n - j) + 1 by omega, Finset.sum_range_succ', Nat.add_zero, pow_zero, _root_.mul_one, hcj, Valuation.map_add_eq_of_lt_right, map_one]`. Rewrite using `[map_one]`.

Apply `Valuation.map_sum_lt _ one_ne_zero` to reduce the goal to its premises. Introduce `k _`. Rewrite using `[map_mul, map_pow]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_right' (pow_le_one' hxle _)) (hclt _ (by omega))`.
-/
theorem exists_integral_quotient :
    ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (F : Type) [Field F]
    [Algebra (FractionRing W) F] [Algebra.IsAlgebraic (FractionRing W) F] [Algebra W F]
    [IsScalarTower W (FractionRing W) F] (O : ValuationSubring F),
    (∀ w : W, algebraMap W F w ∈ O) → (∀ w ∈ maximalIdeal W, algebraMap W F w ∈ O.nonunits) →
    ∀ x ∈ O, ∃ s t : F, IsIntegral W s ∧ IsIntegral W t ∧ O.valuation s = 1 ∧ s * x = t := by
  intro W _ _ _ F _ _ _ _ _ O hW hmax x hxO

  have hK : ∀ a : FractionRing W, algebraMap (FractionRing W) F a ∈ O →
      ∃ w : W, algebraMap W F w = algebraMap (FractionRing W) F a := by
    intro a ha
    rcases ValuationRing.isInteger_or_isInteger W a with ⟨w, hw⟩ | ⟨w, hw⟩
    · exact ⟨w, by rw [IsScalarTower.algebraMap_apply W (FractionRing W) F, hw]⟩
    · by_cases ha0 : a = 0
      · exact ⟨0, by simp [ha0]⟩
      by_cases hu : IsUnit w
      · refine ⟨↑hu.unit⁻¹, ?_⟩
        have h1 : a⁻¹ * algebraMap W (FractionRing W) ↑hu.unit⁻¹ = 1 := by
          rw [← hw, ← map_mul, IsUnit.mul_val_inv, map_one]
        have h2 := (inv_mul_eq_one₀ ha0).mp h1
        rw [IsScalarTower.algebraMap_apply W (FractionRing W) F, ← h2]
      · have hwm : w ∈ maximalIdeal W := (mem_maximalIdeal _).mpr hu
        have h2 := (O.mem_nonunits_iff).mp (hmax w hwm)
        have h3 := (O.valuation_le_one_iff _).mpr ha
        have h4 : algebraMap (FractionRing W) F a * algebraMap W F w = 1 := by
          rw [IsScalarTower.algebraMap_apply W (FractionRing W) F, hw, ← map_mul,
            mul_inv_cancel₀ ha0, map_one]
        have h5 : O.valuation (algebraMap (FractionRing W) F a * algebraMap W F w) < 1 := by
          rw [map_mul]
          exact lt_of_le_of_lt (mul_le_of_le_one_left' h3) h2
        rw [h4, map_one] at h5
        exact absurd h5 (lt_irrefl _)

  obtain ⟨p, hp0, hpx⟩ := Algebra.IsAlgebraic.isAlgebraic (R := FractionRing W) x
  set n := p.natDegree with hn
  set b : ℕ → F := fun i => algebraMap (FractionRing W) F (p.coeff i) with hb
  set v := O.valuation with hv
  obtain ⟨i0, hi0, hi0max⟩ := Finset.exists_max_image (Finset.range (n + 1))
    (fun i => v (b i)) ⟨0, by simp⟩
  set M := v (b i0) with hM
  set S := (Finset.range (n + 1)).filter (fun i => v (b i) = M) with hS
  obtain ⟨j, hjS, hjmax⟩ := Finset.exists_max_image S id
    ⟨i0, Finset.mem_filter.mpr ⟨hi0, rfl⟩⟩
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hjS).1)
  have hjM : v (b j) = M := (Finset.mem_filter.mp hjS).2
  have hcoeff0 : ∀ i, n < i → b i = 0 := fun i hi => by
    simp [b, Polynomial.coeff_eq_zero_of_natDegree_lt (show p.natDegree < i by omega)]
  have hle : ∀ i, v (b i) ≤ M := fun i => by
    by_cases hi : i ≤ n
    · exact hi0max i (Finset.mem_range.mpr (by omega))
    · rw [hcoeff0 i (by omega), map_zero]; exact zero_le'
  have hM0 : M ≠ 0 := by
    intro h
    have h1 : v (b n) = 0 := le_antisymm (h ▸ hle n) zero_le'
    rw [Valuation.zero_iff] at h1
    have h2 : p.leadingCoeff = 0 := (algebraMap (FractionRing W) F).injective (by rw [map_zero]; exact h1)
    exact hp0 (Polynomial.leadingCoeff_eq_zero.mp h2)
  have hlt : ∀ i, j < i → v (b i) < M := by
    intro i hi
    rcases lt_or_eq_of_le (hle i) with h | h
    · exact h
    exfalso
    by_cases hin : i ≤ n
    · have hiS : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), h⟩
      have := hjmax i hiS
      simp only [id] at this
      omega
    · rw [hcoeff0 i (by omega), map_zero] at h
      exact hM0 h.symm
  have hbj : b j ≠ 0 := fun h => hM0 (by rw [← hjM, h, map_zero])
  have hMpos : 0 < M := zero_lt_iff.mpr hM0
  set c : ℕ → F := fun i => b i / b j with hc
  have hcle : ∀ i, v (c i) ≤ 1 := fun i => by
    simp only [c, map_div₀, hjM]
    exact (div_le_one₀ hMpos).mpr (hle i)
  have hclt : ∀ i, j < i → v (c i) < 1 := fun i hi => by
    simp only [c, map_div₀, hjM]
    exact (div_lt_one₀ hMpos).mpr (hlt i hi)
  have hcW : ∀ i, ∃ w : W, algebraMap W F w = c i := fun i => by
    have hci : c i = algebraMap (FractionRing W) F (p.coeff i / p.coeff j) := by
      simp [c, b, map_div₀]
    rw [hci]
    exact hK _ (by rw [← hci]; exact (O.valuation_le_one_iff _).mp (hcle i))
  have hcj : c j = 1 := div_self hbj
  have hrel : ∑ i ∈ Finset.range (n + 1), c i * x ^ i = 0 := by
    have h := hpx
    rw [Polynomial.aeval_eq_sum_range] at h
    simp only [c, div_mul_eq_mul_div, ← Finset.sum_div]
    rw [div_eq_zero_iff]
    left
    simpa [Algebra.smul_def, b] using h
  set s := ∑ k ∈ Finset.range (n + 1 - j), c (j + k) * x ^ k with hs
  have hmemV : ∀ V : ValuationSubring F, (∀ w : W, algebraMap W F w ∈ V) → s ∈ V ∧ s * x ∈ V :=
    fun V hV => tail_mem V c (fun i => by obtain ⟨w, hw⟩ := hcW i; rw [← hw]; exact hV w)
      x n j hjn hrel
  refine ⟨s, s * x, isIntegral_of_forall_valuationSubring W F s fun V hV => (hmemV V hV).1,
    isIntegral_of_forall_valuationSubring W F _ fun V hV => (hmemV V hV).2, ?_, rfl⟩
  have hxle : v x ≤ 1 := (O.valuation_le_one_iff x).mpr hxO
  rw [hs, show n + 1 - j = (n - j) + 1 by omega, Finset.sum_range_succ', Nat.add_zero, pow_zero,
    _root_.mul_one, hcj, Valuation.map_add_eq_of_lt_right, map_one]
  rw [map_one]
  apply Valuation.map_sum_lt _ one_ne_zero
  intro k _
  rw [map_mul, map_pow]
  exact lt_of_le_of_lt (mul_le_of_le_one_right' (pow_le_one' hxle _)) (hclt _ (by omega))

end GlobalTheory.DomValInt
