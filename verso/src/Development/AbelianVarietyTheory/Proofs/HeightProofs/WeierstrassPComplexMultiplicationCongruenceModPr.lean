import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsWeierstrassPMulOde
import Development.AbelianVarietyTheory.Proofs.HeightProofs.QuotientEqLinearPowCharOfDerivativeEqZero
import Development.AbelianVarietyTheory.Proofs.HeightProofs.WeierstrassPTorsionIntegralAndDistinctMod
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ThreeDistinctRoots
open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.EisensteinCongruence

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.ThreeDistinctRoots.three_distinct_roots`. Consider the case `exact _root_.GlobalTheory.ThreeDistinctRoots.three_distinct_roots`. Consider the case `(apply _root_.GlobalTheory.ThreeDistinctRoots.three_distinct_roots <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.ThreeDistinctRoots.three_distinct_roots <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.ThreeDistinctRoots.three_distinct_roots <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.ThreeDistinctRoots.three_distinct_roots ..)`.
-/
lemma exists_three_roots {K : Type} [Field K] [IsAlgClosed K] (g₂ g₃ : K) (h2 : (2 : K) ≠ 0)
    (hd : g₂ ^ 3 - 27 * g₃ ^ 2 ≠ 0) :
    ∃ x y z : K, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ 4 * x ^ 3 - g₂ * x - g₃ = 0 ∧
      4 * y ^ 3 - g₂ * y - g₃ = 0 ∧ 4 * z ^ 3 - g₂ * z - g₃ = 0 := by
  first
  | exact @_root_.GlobalTheory.ThreeDistinctRoots.three_distinct_roots
  | exact _root_.GlobalTheory.ThreeDistinctRoots.three_distinct_roots
  | (apply _root_.GlobalTheory.ThreeDistinctRoots.three_distinct_roots <;> assumption)
  | (intros; apply _root_.GlobalTheory.ThreeDistinctRoots.three_distinct_roots <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ThreeDistinctRoots.three_distinct_roots <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ThreeDistinctRoots.three_distinct_roots ..)

/- English proof (translation)
Set `K` to `AlgebraicClosure k`. Set `ι : k →+* K` to `algebraMap k K`. Establish `hι : Function.Injective ι` using `ι.injective`. Use `haveI : CharP K p := charP_of_injective_ringHom hι p`. Establish `h2' : (2 : K) ≠ 0`.

Use `(map_ne_zero_iff ι hι).mpr h2` as an intermediate fact. Rewrite `this` using `[map_ofNat]`. Then use the resulting hypothesis. Establish `h3' : (3 : K) ≠ 0`. Use `(map_ne_zero_iff ι hι).mpr h3` as an intermediate fact. Rewrite `this` using `[map_ofNat]`. Then use the resulting hypothesis.

Establish `ha' : ι a ≠ 0` using `(map_ne_zero_iff ι hι).mpr ha`. Establish `hd' : ι g₂ ^ 3 - 27 * ι g₃ ^ 2 ≠ 0`. Use `(map_ne_zero_iff ι hι).mpr hd` as an intermediate fact. Simplify `this` using `[map_ofNat]`. Take `⟨x, y, z, hxy, hxz, hyz, hx, hy, hz⟩` from `exists_three_roots (ι g₂) (ι g₃) h2' hd'`.

Establish `key : ∀ e : K, 4 * e ^ 3 - ι g₂ * e - ι g₃ = 0 → 12 * ι a ^ 2 * ι b * (e ^ p) ^ 2 + (12 * ι a * ι b ^ 2 - ι g₂ * ι a + ι a ^ 3 * ι g₂ ^ p) * e ^ p + (4 * ι b ^ 3 - ι g₂ * ι b - ι g₃ + ι a ^ 3 * ι g₃ ^ p) = 0`. Introduce `e he`. Take `⟨q, hq⟩` from `hdvd`. Establish `e1` using `congrArg (Polynomial.eval₂RingHom ι e) hq`. Simplify using `only [map_mul, map_sub, map_add, map_pow, map_ofNat, coe_eval₂RingHom, eval₂_C, eval₂_X] at e1`.

Rewrite `e1` using `[he, zero_mul]`. Establish `e2` using `congrArg (frobenius K p) he`. Simplify using `only [map_mul, map_sub, map_pow, map_ofNat, map_zero] at e2`. Simplify using `only [frobenius_def] at e2`. Take the linear combination `e1 - ι a ^ 3 * e2`.

Establish `inj : ∀ u v : K, u ≠ v → u ^ p - v ^ p ≠ 0` using `fun u v h h' => h (frobenius_inj K p (sub_eq_zero.mp h'))`. Establish `kx` using `key x hx`. Establish `ky` using `key y hy`. Establish `kz` using `key z hz`. Establish `i1` using `inj x y hxy`.

Establish `i2` using `inj x z hxz`. Establish `i3` using `inj y z hyz`. Generalize the expression as in `x ^ p = u at *`. Generalize the expression as in `y ^ p = v at *`. Generalize the expression as in `z ^ p = w at *`.

Use `set c₂ := 12 * ι a ^ 2 * ι b with hc₂`. Use `set c₁ := 12 * ι a * ι b ^ 2 - ι g₂ * ι a + ι a ^ 3 * ι g₂ ^ p with hc₁`. Use `set c₀ := 4 * ι b ^ 3 - ι g₂ * ι b - ι g₃ + ι a ^ 3 * ι g₃ ^ p with hc₀`. Establish `j1 : c₂ * (u + v) + c₁ = 0`. Apply `mul_left_cancel₀ i1` to reduce the goal to its premises.

Take the linear combination `kx - ky`. Establish `j2 : c₂ * (u + w) + c₁ = 0`. Apply `mul_left_cancel₀ i2` to reduce the goal to its premises. Take the linear combination `kx - kz`. Establish `j3 : c₂ = 0`.

Apply `mul_left_cancel₀ i3` to reduce the goal to its premises. Take the linear combination `j1 - j2`. Establish `j4 : c₁ = 0` using `by linear_combination j1 - (u + v) * j3`. Establish `j5 : c₀ = 0` using `by linear_combination kx - u ^ 2 * j3 - u * j4`. Establish `h12 : (12 : K) ≠ 0`.

Establish `: (12 : K) = 2 * 2 * 3` using `by norm_num`. Rewrite using `[this]`. Conclude with `mul_ne_zero (mul_ne_zero h2' h2') h3'`. Establish `hb : ι b = 0`. Use `mul_eq_zero.mp (hc₂ ▸ j3)` as an intermediate fact.

Break down `this with h | h` into its components or cases. Conclude with `absurd h (mul_ne_zero h12 (pow_ne_zero _ ha'))`. Conclude with `h`. Rewrite `j4` using `[hc₁, hb]`. Rewrite `j5` using `[hc₀, hb]`.

Use `⟨hι (by rw [hb, map_zero]), hι ?_, hι ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_pow, map_pow]`. Apply `mul_left_cancel₀ ha'` to reduce the goal to its premises. Take the linear combination `-j4`. Rewrite using `[map_mul, map_pow, map_pow]`.

Take the linear combination `-j5`.
-/
lemma coeff_of_dvd {k : Type} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (g₂ g₃ a b : k)
    (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (hd : g₂ ^ 3 - 27 * g₃ ^ 2 ≠ 0) (ha : a ≠ 0)
    (hdvd : (4 * X ^ 3 - C g₂ * X - C g₃ : k[X]) ∣
      4 * (C a * X ^ p + C b) ^ 3 - C g₂ * (C a * X ^ p + C b) - C g₃) :
    b = 0 ∧ g₂ = a ^ 2 * g₂ ^ p ∧ g₃ = a ^ 3 * g₃ ^ p := by
  let K := AlgebraicClosure k
  let ι : k →+* K := algebraMap k K
  have hι : Function.Injective ι := ι.injective
  haveI : CharP K p := charP_of_injective_ringHom hι p
  have h2' : (2 : K) ≠ 0 := by
    have := (map_ne_zero_iff ι hι).mpr h2
    rwa [map_ofNat] at this
  have h3' : (3 : K) ≠ 0 := by
    have := (map_ne_zero_iff ι hι).mpr h3
    rwa [map_ofNat] at this
  have ha' : ι a ≠ 0 := (map_ne_zero_iff ι hι).mpr ha
  have hd' : ι g₂ ^ 3 - 27 * ι g₃ ^ 2 ≠ 0 := by
    have := (map_ne_zero_iff ι hι).mpr hd
    simpa [map_ofNat] using this
  obtain ⟨x, y, z, hxy, hxz, hyz, hx, hy, hz⟩ := exists_three_roots (ι g₂) (ι g₃) h2' hd'
  have key : ∀ e : K, 4 * e ^ 3 - ι g₂ * e - ι g₃ = 0 →
      12 * ι a ^ 2 * ι b * (e ^ p) ^ 2 + (12 * ι a * ι b ^ 2 - ι g₂ * ι a + ι a ^ 3 * ι g₂ ^ p) * e ^ p
        + (4 * ι b ^ 3 - ι g₂ * ι b - ι g₃ + ι a ^ 3 * ι g₃ ^ p) = 0 := by
    intro e he
    obtain ⟨q, hq⟩ := hdvd
    have e1 := congrArg (Polynomial.eval₂RingHom ι e) hq
    simp only [map_mul, map_sub, map_add, map_pow, map_ofNat, coe_eval₂RingHom, eval₂_C,
      eval₂_X] at e1
    rw [he, zero_mul] at e1
    have e2 := congrArg (frobenius K p) he
    simp only [map_mul, map_sub, map_pow, map_ofNat, map_zero] at e2
    simp only [frobenius_def] at e2
    linear_combination e1 - ι a ^ 3 * e2
  have inj : ∀ u v : K, u ≠ v → u ^ p - v ^ p ≠ 0 := fun u v h h' =>
    h (frobenius_inj K p (sub_eq_zero.mp h'))
  have kx := key x hx
  have ky := key y hy
  have kz := key z hz
  have i1 := inj x y hxy
  have i2 := inj x z hxz
  have i3 := inj y z hyz
  generalize x ^ p = u at *
  generalize y ^ p = v at *
  generalize z ^ p = w at *
  set c₂ := 12 * ι a ^ 2 * ι b with hc₂
  set c₁ := 12 * ι a * ι b ^ 2 - ι g₂ * ι a + ι a ^ 3 * ι g₂ ^ p with hc₁
  set c₀ := 4 * ι b ^ 3 - ι g₂ * ι b - ι g₃ + ι a ^ 3 * ι g₃ ^ p with hc₀
  have j1 : c₂ * (u + v) + c₁ = 0 := by
    apply mul_left_cancel₀ i1; linear_combination kx - ky
  have j2 : c₂ * (u + w) + c₁ = 0 := by
    apply mul_left_cancel₀ i2; linear_combination kx - kz
  have j3 : c₂ = 0 := by
    apply mul_left_cancel₀ i3; linear_combination j1 - j2
  have j4 : c₁ = 0 := by linear_combination j1 - (u + v) * j3
  have j5 : c₀ = 0 := by linear_combination kx - u ^ 2 * j3 - u * j4
  have h12 : (12 : K) ≠ 0 := by
    have : (12 : K) = 2 * 2 * 3 := by norm_num
    rw [this]; exact mul_ne_zero (mul_ne_zero h2' h2') h3'
  have hb : ι b = 0 := by
    have := mul_eq_zero.mp (hc₂ ▸ j3)
    rcases this with h | h
    · exact absurd h (mul_ne_zero h12 (pow_ne_zero _ ha'))
    · exact h
  rw [hc₁, hb] at j4
  rw [hc₀, hb] at j5
  refine ⟨hι (by rw [hb, map_zero]), hι ?_, hι ?_⟩
  · rw [map_mul, map_pow, map_pow]
    apply mul_left_cancel₀ ha'
    linear_combination -j4
  · rw [map_mul, map_pow, map_pow]
    linear_combination -j5

/- English proof (translation)
Establish `hD0 : D ≠ 0`. Introduce and unpack `rfl`. Establish `hA0 : A ≠ 0` using `by simpa using h0`. Apply `hA0` to reduce the goal to its premises. Apply `eq_zero_of_infinite_isRoot` to reduce the goal to its premises.

Use `(Set.infinite_range_of_injective hx).mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨j, rfl⟩`. Simplify using `using hxy j`. Establish `hf : (4 * X ^ 3 - C g₂ * X - C g₃ : k[X]) ≠ 0`. Introduce `h`.

Use `congrArg (fun q : k[X] => q.coeff 3) h` as an intermediate fact. Establish `h4 : (4 : k[X]) = C 4` using `rfl`. Simplify using `only [h4, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C, coeff_zero] at this`. Simplify using `at this`. Apply `mul_ne_zero h2 h2` to reduce the goal to its premises.

Take the linear combination `this`. Establish `hder : derivative A * D = A * derivative D` using `sub_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp ((mul_eq_zero.mp hode).resolve_right hf))`. Establish `hnc : ¬ ∃ c : k, A = C c * D`. Introduce and unpack `⟨c, rfl⟩`. Apply `hD0` to reduce the goal to its premises.

Apply `eq_zero_of_infinite_isRoot` to reduce the goal to its premises. Establish `hfin : {j | y j = c}.Finite` using `(Set.finite_singleton c).preimage hy.injOn`. Use `(hfin.infinite_compl.image hx.injOn).mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨j, hj, rfl⟩`. Establish `h` using `hxy j`.

Rewrite `h` using `[eval_mul, eval_C]`. Assume the negation of the conclusion as `hne`. Conclude with `hj (mul_right_cancel₀ hne h).symm`. Take `⟨a, b, c, ha, hc, rfl, rfl⟩` from `quotient_eq_linear_pow_char_of_derivative_eq_zero k p A D hD0 hA hD hder hnc`. Establish `hu : IsUnit (C c ^ 4 : k[X])` using `(isUnit_C.mpr (Ne.isUnit hc)).pow 4`.

Establish `: (4 * X ^ 3 - C g₂ * X - C g₃ : k[X]) ∣ 4 * (C a * X ^ p + C b) ^ 3 - C g₂ * (C a * X ^ p + C b) - C g₃`. Rewrite using `[← hu.dvd_mul_left]`. Use `hdvd using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Take `⟨rfl, e2, e3⟩` from `coeff_of_dvd p g₂ g₃ a b h2 h3 hd ha this`.

Conclude with `⟨a, c, ha, hc, rfl, by simp, e2, e3⟩`.
-/
lemma residue_form {k : Type} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (g₂ g₃ : k) (A D : k[X])
    (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (hd : g₂ ^ 3 - 27 * g₃ ^ 2 ≠ 0)
    (h0 : A ≠ 0 ∨ D ≠ 0) (hA : A.natDegree ≤ p) (hD : D.natDegree < p)
    (x y : ℕ → k) (hx : Function.Injective x) (hy : Function.Injective y)
    (hxy : ∀ j, A.eval (x j) = y j * D.eval (x j))
    (hode : (derivative A * D - A * derivative D) ^ 2 * (4 * X ^ 3 - C g₂ * X - C g₃) = 0)
    (hdvd : (4 * X ^ 3 - C g₂ * X - C g₃ : k[X]) ∣
      D * (4 * A ^ 3 - C g₂ * A * D ^ 2 - C g₃ * D ^ 3)) :
    ∃ a c : k, a ≠ 0 ∧ c ≠ 0 ∧ D = C c ∧ A = C c * (C a * X ^ p) ∧
      g₂ = a ^ 2 * g₂ ^ p ∧ g₃ = a ^ 3 * g₃ ^ p := by
  have hD0 : D ≠ 0 := by
    rintro rfl
    have hA0 : A ≠ 0 := by simpa using h0
    apply hA0
    apply eq_zero_of_infinite_isRoot
    refine (Set.infinite_range_of_injective hx).mono ?_
    rintro _ ⟨j, rfl⟩
    simpa using hxy j
  have hf : (4 * X ^ 3 - C g₂ * X - C g₃ : k[X]) ≠ 0 := by
    intro h
    have := congrArg (fun q : k[X] => q.coeff 3) h
    have h4 : (4 : k[X]) = C 4 := rfl
    simp only [h4, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C, coeff_zero] at this
    simp at this
    apply mul_ne_zero h2 h2
    linear_combination this
  have hder : derivative A * D = A * derivative D :=
    sub_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp ((mul_eq_zero.mp hode).resolve_right hf))
  have hnc : ¬ ∃ c : k, A = C c * D := by
    rintro ⟨c, rfl⟩
    apply hD0
    apply eq_zero_of_infinite_isRoot
    have hfin : {j | y j = c}.Finite := (Set.finite_singleton c).preimage hy.injOn
    refine (hfin.infinite_compl.image hx.injOn).mono ?_
    rintro _ ⟨j, hj, rfl⟩
    have h := hxy j
    rw [eval_mul, eval_C] at h
    by_contra hne
    exact hj (mul_right_cancel₀ hne h).symm
  obtain ⟨a, b, c, ha, hc, rfl, rfl⟩ :=
    quotient_eq_linear_pow_char_of_derivative_eq_zero k p A D hD0 hA hD hder hnc
  have hu : IsUnit (C c ^ 4 : k[X]) := (isUnit_C.mpr (Ne.isUnit hc)).pow 4
  have : (4 * X ^ 3 - C g₂ * X - C g₃ : k[X]) ∣
      4 * (C a * X ^ p + C b) ^ 3 - C g₂ * (C a * X ^ p + C b) - C g₃ := by
    rw [← hu.dvd_mul_left]
    convert hdvd using 1
    ring
  obtain ⟨rfl, e2, e3⟩ := coeff_of_dvd p g₂ g₃ a b h2 h3 hd ha this
  exact ⟨a, c, ha, hc, rfl, by simp, e2, e3⟩

/- English proof (translation)
Establish `hne : (A.coeffs ∪ D.coeffs).Nonempty` using `⟨D.leadingCoeff, Finset.mem_union_right _ (coeff_mem_coeffs (leadingCoeff_ne_zero.mpr hD))⟩`. Take `⟨s, hs, hmax⟩` from `Finset.exists_max_image _ W.valuation hne`. Establish `hs0 : s ≠ 0`. Introduce and unpack `rfl`. Simplify using `[mem_coeffs_iff] at hs`.

Use `grind`. Establish `lift : ∀ B : ℂ[X], B.coeffs ⊆ A.coeffs ∪ D.coeffs → ∃ B₀ : W[X], B₀.map W.subtype = C s⁻¹ * B ∧ (s ∈ B.coeffs → B₀.map (IsLocalRing.residue W) ≠ 0)`. Introduce `B hB`. Establish `: C s⁻¹ * B ∈ lifts W.subtype`. Rewrite using `[lifts_iff_coeff_lifts]`.

Introduce `n`. Rewrite using `[coeff_C_mul]`. Distinguish the cases in `h : B.coeff n = 0`. Conclude with `⟨0, by simp [h]⟩`. Establish `h1` using `hmax _ (hB (coeff_mem_coeffs h))`.

Use `⟨⟨s⁻¹ * B.coeff n, ?_⟩, rfl⟩` and prove the remaining obligations. Rewrite using `[← W.valuation_le_one_iff, map_mul, map_inv₀, inv_mul_le_one₀ (zero_lt_iff.mpr ((_root_.map_ne_zero _).mpr hs0))]`. Conclude with `h1`. Take `⟨B₀, hB₀⟩` from `(mem_lifts _).mp this`. Use `⟨B₀, hB₀, fun hsB h0 => ?_⟩` and prove the remaining obligations.

Take `⟨n, -, hn⟩` from `mem_coeffs_iff.mp hsB`. Establish `e1` using `congrArg (fun q => coeff q n) hB₀`. Establish `e2` using `congrArg (fun q => coeff q n) h0`. Simplify using `only [coeff_map, coeff_C_mul, ← hn, inv_mul_cancel₀ hs0, coeff_zero] at e1 e2`. Establish `: B₀.coeff n = 1` using `Subtype.ext e1`.

Rewrite `e2` using `[this, map_one]`. Conclude with `one_ne_zero e2`. Take `⟨A₀, hA₀, hA₁⟩` from `lift A Finset.subset_union_left`. Take `⟨D₀, hD₀, hD₁⟩` from `lift D Finset.subset_union_right`. Conclude with `⟨s⁻¹, A₀, D₀, inv_ne_zero hs0, hA₀, hD₀, (Finset.mem_union.mp hs).imp hA₁ hD₁⟩`.
-/
lemma exists_scaling (W : ValuationSubring ℂ) (A D : ℂ[X]) (hD : D ≠ 0) :
    ∃ (c : ℂ) (A₀ D₀ : W[X]), c ≠ 0 ∧ A₀.map W.subtype = C c * A ∧ D₀.map W.subtype = C c * D ∧
      (A₀.map (IsLocalRing.residue W) ≠ 0 ∨ D₀.map (IsLocalRing.residue W) ≠ 0) := by
  classical
  have hne : (A.coeffs ∪ D.coeffs).Nonempty :=
    ⟨D.leadingCoeff, Finset.mem_union_right _ (coeff_mem_coeffs (leadingCoeff_ne_zero.mpr hD))⟩
  obtain ⟨s, hs, hmax⟩ := Finset.exists_max_image _ W.valuation hne
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp [mem_coeffs_iff] at hs
    grind
  have lift : ∀ B : ℂ[X], B.coeffs ⊆ A.coeffs ∪ D.coeffs →
      ∃ B₀ : W[X], B₀.map W.subtype = C s⁻¹ * B ∧
        (s ∈ B.coeffs → B₀.map (IsLocalRing.residue W) ≠ 0) := by
    intro B hB
    have : C s⁻¹ * B ∈ lifts W.subtype := by
      rw [lifts_iff_coeff_lifts]
      intro n
      rw [coeff_C_mul]
      by_cases h : B.coeff n = 0
      · exact ⟨0, by simp [h]⟩
      · have h1 := hmax _ (hB (coeff_mem_coeffs h))
        refine ⟨⟨s⁻¹ * B.coeff n, ?_⟩, rfl⟩
        rw [← W.valuation_le_one_iff, map_mul, map_inv₀, inv_mul_le_one₀
          (zero_lt_iff.mpr ((_root_.map_ne_zero _).mpr hs0))]
        exact h1
    obtain ⟨B₀, hB₀⟩ := (mem_lifts _).mp this
    refine ⟨B₀, hB₀, fun hsB h0 => ?_⟩
    obtain ⟨n, -, hn⟩ := mem_coeffs_iff.mp hsB
    have e1 := congrArg (fun q => coeff q n) hB₀
    have e2 := congrArg (fun q => coeff q n) h0
    simp only [coeff_map, coeff_C_mul, ← hn, inv_mul_cancel₀ hs0, coeff_zero] at e1 e2
    have : B₀.coeff n = 1 := Subtype.ext e1
    rw [this, map_one] at e2
    exact one_ne_zero e2
  obtain ⟨A₀, hA₀, hA₁⟩ := lift A Finset.subset_union_left
  obtain ⟨D₀, hD₀, hD₁⟩ := lift D Finset.subset_union_right
  exact ⟨s⁻¹, A₀, D₀, inv_ne_zero hs0, hA₀, hD₀, (Finset.mem_union.mp hs).imp hA₁ hD₁⟩

/- English proof (translation)
Establish `hi` using `relIndex_mul_periodLattice L h0 hα`. Rewrite `hi` using `[hp, Nat.cast_inj]`. Establish `h1` using `AddSubgroup.nsmul_relIndex_mem (AddSubgroup.map (AddMonoidHom.mulLeft α) L.lattice.toAddSubgroup) (K := L.lattice.toAddSubgroup) (g := α * t) ht`. Rewrite `h1` using `[hi]`. Take `⟨l, hl, e⟩` from `h1`.

Establish `e' : l = p * t`. Apply `mul_left_cancel₀ h0` to reduce the goal to its premises. Simplify using `only [AddMonoidHom.coe_mulLeft, nsmul_eq_mul] at e`. Take the linear combination `e`. Take `⟨u, v, huv⟩` from `Nat.isCoprime_iff_coprime.mpr hc`.

Use `L.lattice.add_mem (L.lattice.smul_mem u hl) (L.lattice.smul_mem v hm)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Establish `huv'` using `congrArg (Int.cast : ℤ → ℂ) huv`. Move the coercions through the operations in `at huv'`. Simplify using `only [zsmul_eq_mul, e']`.

Take the linear combination `(-t) * huv'`.
-/
lemma mem_of_mul_mem (L : PeriodPair) {α : ℂ} {p m : ℕ} (h0 : α ≠ 0)
    (hα : ∀ l ∈ L.lattice, α * l ∈ L.lattice) (hp : ‖α‖ ^ 2 = p) (hc : p.Coprime m) {t : ℂ}
    (hm : (m : ℂ) * t ∈ L.lattice) (ht : α * t ∈ L.lattice) : t ∈ L.lattice := by
  have hi := relIndex_mul_periodLattice L h0 hα
  rw [hp, Nat.cast_inj] at hi
  have h1 := AddSubgroup.nsmul_relIndex_mem
    (AddSubgroup.map (AddMonoidHom.mulLeft α) L.lattice.toAddSubgroup)
    (K := L.lattice.toAddSubgroup) (g := α * t) ht
  rw [hi] at h1
  obtain ⟨l, hl, e⟩ := h1
  have e' : l = p * t := by
    apply mul_left_cancel₀ h0
    simp only [AddMonoidHom.coe_mulLeft, nsmul_eq_mul] at e
    linear_combination e
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hc
  have := L.lattice.add_mem (L.lattice.smul_mem u hl) (L.lattice.smul_mem v hm)
  convert this using 1
  have huv' := congrArg (Int.cast : ℤ → ℂ) huv
  push_cast at huv'
  simp only [zsmul_eq_mul, e']
  linear_combination (-t) * huv'

/- English proof (translation)
Introduce `h`. Use `(L.mul_ω₁_add_mul_ω₂_mem_lattice (α := 1 / 3) (β := 0)).mp (by` as an intermediate fact. Use `h using 1` and compare the differences between its conclusion and the goal. Use `push_cast`. Use the proof step `ring)`.

Evaluate the numerical expressions using `at this`.
-/
lemma third_notMem (L : PeriodPair) : L.ω₁ / 3 ∉ L.lattice := by
  intro h
  have := (L.mul_ω₁_add_mul_ω₂_mem_lattice (α := 1 / 3) (β := 0)).mp (by
    convert h using 1; push_cast; ring)
  norm_num at this

/- English proof (translation)
Rewrite using `[Ne, IsLocalRing.residue_eq_zero_iff, ← W.coe_mem_nonunits_iff, W.mem_nonunits_iff_or]`. Use `push Not`. Conclude with `⟨h0, h⟩`.
-/
lemma residue_ne_zero_of_inv_mem (W : ValuationSubring ℂ) (x : W) (h0 : (x : ℂ) ≠ 0)
    (h : (x : ℂ)⁻¹ ∈ W) : IsLocalRing.residue W x ≠ 0 := by
  rw [Ne, IsLocalRing.residue_eq_zero_iff, ← W.coe_mem_nonunits_iff, W.mem_nonunits_iff_or]
  push Not
  exact ⟨h0, h⟩

/- English proof (translation)
Rewrite using `[IsLocalRing.residue_eq_zero_iff, ← W.coe_mem_nonunits_iff]`.
-/
lemma residue_eq_zero_iff' (W : ValuationSubring ℂ) (x : W) :
    IsLocalRing.residue W x = 0 ↔ (x : ℂ) ∈ W.nonunits := by
  rw [IsLocalRing.residue_eq_zero_iff, ← W.coe_mem_nonunits_iff]

/- English proof (translation)
Set `i : W` to `⟨2⁻¹, h2⟩`. Establish `hi : (4 : W) * i ^ 2 = 1`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(4 : ℂ) * (2⁻¹) ^ 2 = 1`. Evaluate the numerical expressions.

Establish `hm : (X ^ 3 - (C (i ^ 2 * g₂) * X + C (i ^ 2 * g₃)) : W[X]).Monic`. Apply `monic_X_pow_sub` to reduce the goal to its premises. Conclude with `lt_of_le_of_lt degree_linear_le (by norm_num)`. Establish `e : (4 * X ^ 3 - C g₂ * X - C g₃ : W[X]) = C 4 * (X ^ 3 - (C (i ^ 2 * g₂) * X + C (i ^ 2 * g₃)))`. Establish `h4 : (4 : W[X]) = C 4` using `rfl`.

Establish `hi' : (C 4 * C i ^ 2 : W[X]) = 1` using `by rw [← map_pow, ← map_mul, hi, map_one]`. Rewrite using `[h4, map_mul, map_mul, map_pow]`. Take the linear combination `(C g₂ * X + C g₃) * hi'`. Establish `hu : IsUnit (C 4 : W[X])` using `isUnit_C.mpr (IsUnit.of_mul_eq_one _ hi)`. Rewrite using `[e, hu.mul_left_dvd, ← map_dvd_map W.subtype W.subtype_injective hm]`.

Use `dvd_trans ?_ h` and prove the remaining obligations. Use `congrArg (Polynomial.map W.subtype) e` as an intermediate fact. Rewrite `this` using `[Polynomial.map_mul]`. Use `⟨Polynomial.map W.subtype (C 4), ?_⟩` and prove the remaining obligations. Rewrite using `[mul_comm _ (Polynomial.map W.subtype (C 4)), ← this]`.

Simplify using the standard rewrite rules.
-/
lemma cubic_dvd (W : ValuationSubring ℂ) (h2 : (2 : ℂ)⁻¹ ∈ W) (g₂ g₃ : W) (F : W[X])
    (h : (4 * X ^ 3 - C (g₂ : ℂ) * X - C (g₃ : ℂ) : ℂ[X]) ∣ F.map W.subtype) :
    (4 * X ^ 3 - C g₂ * X - C g₃ : W[X]) ∣ F := by
  let i : W := ⟨2⁻¹, h2⟩
  have hi : (4 : W) * i ^ 2 = 1 := by
    apply Subtype.ext
    change (4 : ℂ) * (2⁻¹) ^ 2 = 1
    norm_num
  have hm : (X ^ 3 - (C (i ^ 2 * g₂) * X + C (i ^ 2 * g₃)) : W[X]).Monic := by
    apply monic_X_pow_sub
    exact lt_of_le_of_lt degree_linear_le (by norm_num)
  have e : (4 * X ^ 3 - C g₂ * X - C g₃ : W[X]) =
      C 4 * (X ^ 3 - (C (i ^ 2 * g₂) * X + C (i ^ 2 * g₃))) := by
    have h4 : (4 : W[X]) = C 4 := rfl
    have hi' : (C 4 * C i ^ 2 : W[X]) = 1 := by rw [← map_pow, ← map_mul, hi, map_one]
    rw [h4, map_mul, map_mul, map_pow]
    linear_combination (C g₂ * X + C g₃) * hi'
  have hu : IsUnit (C 4 : W[X]) := isUnit_C.mpr (IsUnit.of_mul_eq_one _ hi)
  rw [e, hu.mul_left_dvd, ← map_dvd_map W.subtype W.subtype_injective hm]
  refine dvd_trans ?_ h
  have := congrArg (Polynomial.map W.subtype) e
  rw [Polynomial.map_mul] at this
  refine ⟨Polynomial.map W.subtype (C 4), ?_⟩
  rw [mul_comm _ (Polynomial.map W.subtype (C 4)), ← this]
  simp

/- English proof (translation)
Introduce `L W α p h2 h3 hg₂ hg₃ hΔ hp hpW hαW hα hN`. Establish `hΔ0 : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 ≠ 0` using `TorsionIntegral.disc L`. Establish `h0 : α ≠ 0`. Introduce and unpack `rfl`. Simplify using `only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hN`.

Conclude with `hp.ne_zero (by exact_mod_cast hN.symm)`. Use `haveI : Fact p.Prime := ⟨hp⟩`. Use `set ρ := IsLocalRing.residue W with hρ`. Establish `hpk : (p : IsLocalRing.ResidueField W) = 0`. Rewrite using `[← map_natCast ρ, residue_eq_zero_iff']`.

Simplify using `using hpW`. Use `haveI : CharP (IsLocalRing.ResidueField W) p := (CharP.charP_iff_prime_eq_zero hp).mpr hpk`. Establish `hcop : ∀ m : ℕ, Odd m → (m : ℂ)⁻¹ ∈ W → p.Coprime m`. Introduce `m hm hmW`. Rewrite using `[hp.coprime_iff_not_dvd, ← CharP.cast_eq_zero_iff (IsLocalRing.ResidueField W) p, ← map_natCast ρ]`.

Apply `residue_ne_zero_of_inv_mem` to reduce the goal to its premises. Simplify using `using hm.pos.ne'`. Simplify using `using hmW`. Take `⟨A, D, hD, hAd, hDd, hev, hode⟩` from `exists_weierstrassP_mul_ode L α p h0 hα hN`. Take `⟨c, A₀, D₀, hc, hA₀, hD₀, hne⟩` from `exists_scaling W A D hD`.

Establish `hmul : ∀ (m : ℕ) (t : ℂ), (m : ℂ) * t ∈ L.lattice → (m : ℂ) * (α * t) ∈ L.lattice`. Introduce `m t h`. Use `hα _ h` as an intermediate fact. Rewrite `this` using `[mul_left_comm]`. Then use the resulting hypothesis. Establish `rel : ∀ (m : ℕ) (t : ℂ), Odd m → (m : ℂ)⁻¹ ∈ W → (m : ℂ) * t ∈ L.lattice → t ∉ L.lattice → ∃ x y : W, (x : ℂ) = L.weierstrassP t ∧ (y : ℂ) = L.weierstrassP (α * t) ∧ (A₀.map ρ).eval (ρ x) = ρ y * (D₀.map ρ).eval (ρ x)`.

Introduce `m t hm hmW hmt ht`. Establish `hαt : α * t ∉ L.lattice` using `fun h => ht (mem_of_mul_mem L h0 hα hN (hcop m hm hmW) hmt h)`. Establish `T` using `(TorsionIntegral.torsion_integral_distinct L W m h2 h3 hg₂ hg₃ hΔ hm hmW).1`. Use `⟨⟨_, T t hmt ht⟩, ⟨_, T _ (hmul m t hmt) hαt⟩, rfl, rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[eval_map_apply, eval_map_apply, ← map_mul]`.

Use `congr 1`. Apply `W.subtype_injective` to reduce the goal to its premises. Rewrite using `[map_mul, ← eval_map_apply, ← eval_map_apply, hA₀, hD₀]`. Take `⟨e1, e2⟩` from `hev t hαt`. Simplify using `only [eval_mul, eval_C, ValuationSubring.coe_subtype]`.

Rewrite using `[e2]`. Clear the denominators using the available nonvanishing facts. Establish `h3n : ∀ n : ℕ, ((3 ^ n : ℕ) : ℂ)⁻¹ ∈ W` using `fun n => by`. Rewrite using `[Nat.cast_pow, ← inv_pow]`. Conclude with `pow_mem (by simpa using h3) n`.

Establish `hodd : ∀ n : ℕ, Odd (3 ^ n)` using `fun n => Odd.pow (by decide)`. Establish `hpow : ∀ i j : ℕ, i + 1 ≤ j → ((3 ^ j : ℕ) : ℂ) * (L.ω₁ / 3 ^ (i + 1)) ∈ L.lattice`. Introduce `i j hij`. Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le hij`. Use `L.lattice.smul_mem ((3 : ℤ) ^ d) L.ω₁_mem_lattice using 1` and compare the differences between its conclusion and the goal.

Simplify using `only [zsmul_eq_mul]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hthird : ∀ j : ℕ, ((3 ^ j : ℕ) : ℂ) * (L.ω₁ / 3 ^ (j + 1)) = L.ω₁ / 3`.

Introduce `j`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hns : ∀ (n : ℕ) (z : ℂ), z ∈ L.lattice → (n : ℂ) * z ∈ L.lattice` using `fun n z hz => by`.

Simplify using `using L.lattice.smul_mem (n : ℤ) hz`. Establish `hnot : ∀ j : ℕ, L.ω₁ / 3 ^ (j + 1) ∉ L.lattice` using `fun j h => third_notMem L (hthird j ▸ hns _ _ h)`. Establish `h33 : ((3 : ℕ) : ℂ) * (L.ω₁ / 3) ∈ L.lattice` using `by simpa using hpow 0 1 le_rfl`. Establish `hαthird : α * (L.ω₁ / 3) ∉ L.lattice` using `fun h => third_notMem L (mem_of_mul_mem L h0 hα hN (hcop 3 (by decide) (by simpa using h3)) h33 h)`. Establish `dist : ∀ β : ℂ, (∀ l ∈ L.lattice, β * l ∈ L.lattice) → β * (L.ω₁ / 3) ∉ L.lattice → ∀ x : ℕ → W, (∀ j, (x j : ℂ) = L.weierstrassP (β * (L.ω₁ / 3 ^ (j + 1)))) → Function.Injective fun j => ρ (x j)`.

Introduce `β hβ hβ3 x hx`. Establish `hm : ∀ i j : ℕ, i + 1 ≤ j → ((3 ^ j : ℕ) : ℂ) * (β * (L.ω₁ / 3 ^ (i + 1))) ∈ L.lattice`. Introduce `i j hij`. Rewrite using `[mul_left_comm]`. Conclude with `hβ _ (hpow i j hij)`.

Establish `hn : ∀ j : ℕ, ((3 ^ j : ℕ) : ℂ) * (β * (L.ω₁ / 3 ^ (j + 1))) ∉ L.lattice`. Introduce `j`. Rewrite using `[mul_left_comm, hthird]`. Conclude with `hβ3`. Use `Function.Injective.of_lt_imp_ne fun i j hij h => ?_` and prove the remaining obligations.

Establish `T` using `(TorsionIntegral.torsion_integral_distinct L W (3 ^ (j + 1)) h2 h3 hg₂ hg₃ hΔ (hodd _) (h3n _)).2 _ _ (hm i _ (by omega)) (fun h => hn i (hns _ _ h)) (hm j _ le_rfl) (fun h => hn j (hns _ _ h)) (by`. Rewrite using `[← hx, ← hx]`. Establish `: ρ (x i - x j) = 0` using `by rw [map_sub]; exact sub_eq_zero.mpr h`. Conclude with `(residue_eq_zero_iff' W _).mp this)`. Apply `hn j` to reduce the goal to its premises.

Break down `T with T | T` into its components or cases. Use `L.lattice.sub_mem (hm i j hij) (hns (3 ^ j) _ T) using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Use `L.lattice.sub_mem (hns (3 ^ j) _ T) (hm i j hij) using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.

Use `choose x y hx hy hxy using fun j : ℕ => rel (3 ^ (j + 1)) (L.ω₁ / 3 ^ (j + 1)) (hodd _) (h3n _) (hpow j _ le_rfl) (hnot j)`. Establish `hxi` using `dist 1 (by simp) (by simpa using third_notMem L) x (by simpa using hx)`. Establish `hyi` using `dist α hα hαthird y hy`. Set `g₂ : W` to `⟨L.g₂, hg₂⟩`. Set `g₃ : W` to `⟨L.g₃, hg₃⟩`.

Set `α₀ : W` to `⟨α, W.nonunits_subset hαW⟩`. Establish `hode' : C (α ^ 2) * (C c * D) * (4 * (C c * A) ^ 3 - C L.g₂ * (C c * A) * (C c * D) ^ 2 - C L.g₃ * (C c * D) ^ 3) = (derivative (C c * A) * (C c * D) - (C c * A) * derivative (C c * D)) ^ 2 * (4 * X ^ 3 - C L.g₂ * X - C L.g₃)`. Simplify using `only [derivative_C_mul]`. Take the linear combination `C c ^ 4 * hode`. Establish `hode₀ : C (α₀ ^ 2) * D₀ * (4 * A₀ ^ 3 - C g₂ * A₀ * D₀ ^ 2 - C g₃ * D₀ ^ 3) = (derivative A₀ * D₀ - A₀ * derivative D₀) ^ 2 * (4 * X ^ 3 - C g₂ * X - C g₃)`.

Apply `Polynomial.map_injective W.subtype W.subtype_injective` to reduce the goal to its premises. Simplify using `only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow, map_C, map_X, Polynomial.map_ofNat, ← derivative_map, hA₀, hD₀]`. Conclude with `hode'`. Establish `hdvd₀ : (4 * X ^ 3 - C g₂ * X - C g₃ : W[X]) ∣ D₀ * (4 * A₀ ^ 3 - C g₂ * A₀ * D₀ ^ 2 - C g₃ * D₀ ^ 3)`. Apply `cubic_dvd W h2` to reduce the goal to its premises.

Simplify using `only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow, map_C, Polynomial.map_ofNat, hA₀, hD₀]`. Establish `hu : IsUnit (C (α ^ 2) : ℂ[X])` using `isUnit_C.mpr (Ne.isUnit (pow_ne_zero _ h0))`. Rewrite using `[← hu.dvd_mul_left, ← mul_assoc]`. Conclude with `Dvd.intro_left _ hode'.symm`. Establish `hdeg : ∀ (B₀ : W[X]) (B : ℂ[X]), B₀.map W.subtype = C c * B → (B₀.map ρ).natDegree ≤ B.natDegree`.

Introduce `B₀ B h`. Use `natDegree_map_le.trans ?_` and prove the remaining obligations. Rewrite using `[← natDegree_map_eq_of_injective W.subtype_injective, h, natDegree_C_mul hc]`. Establish `hα₀ : ρ α₀ = 0` using `(residue_eq_zero_iff' W _).mpr hαW`. Take `⟨a, d, ha, hd, eD, eA, e2, e3⟩` from `residue_form p (ρ g₂) (ρ g₃) (A₀.map ρ) (D₀.map ρ) (by`.

Rewrite using `[← map_ofNat ρ 2]`. Conclude with `residue_ne_zero_of_inv_mem W _ (two_ne_zero (α := ℂ)) h2)`. Use the proof step `(by`. Rewrite using `[← map_ofNat ρ 3]`. Conclude with `residue_ne_zero_of_inv_mem W _ (three_ne_zero (α := ℂ)) h3)`.

Use the proof step `(by`. Use `residue_ne_zero_of_inv_mem W (g₂ ^ 3 - 27 * g₃ ^ 2) hΔ0 hΔ` as an intermediate fact. Simplify `this)` using `[map_ofNat]`. Use `hne (hAd ▸ hdeg A₀ A hA₀) (lt_of_le_of_lt (hdeg D₀ D hD₀) (by omega))`. Use `_ _ hxi hyi hxy`.

Use the proof step `(by`. Use `congrArg (Polynomial.map ρ) hode₀` as an intermediate fact. Simplify using `only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow, map_C, map_X, Polynomial.map_ofNat, ← derivative_map, map_pow, hα₀, map_zero] at this`. Rewrite using `[← this]`. Use the proof step `ring)`.

Use the proof step `(by`. Use `Polynomial.map_dvd ρ hdvd₀` as an intermediate fact. Simplify `this)` using `only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow, map_C, map_X, Polynomial.map_ofNat]`. Take `⟨a₀, rfl⟩` from `IsLocalRing.residue_surjective a`. Establish `ha' : (a₀ : ℂ) ∉ W.nonunits` using `fun h => ha ((residue_eq_zero_iff' W _).mpr h)`.

Rewrite `ha'` using `[W.mem_nonunits_iff_or]`. Use `push Not at ha'`. Use `⟨a₀, a₀.2, ha'.2, ha'.1, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `(residue_eq_zero_iff' W (g₂ - a₀ ^ 2 * g₂ ^ p)).mp ?_` and prove the remaining obligations. Rewrite using `[map_sub, map_mul, map_pow, map_pow]`.

Conclude with `sub_eq_zero.mpr e2`. Use `(residue_eq_zero_iff' W (g₃ - a₀ ^ 3 * g₃ ^ p)).mp ?_` and prove the remaining obligations. Rewrite using `[map_sub, map_mul, map_pow, map_pow]`. Conclude with `sub_eq_zero.mpr e3`. Introduce `m t hm hmW hmt ht`.

Take `⟨u, v, hu, hv, huv⟩` from `rel m t hm hmW hmt ht`. Rewrite using `[← hu, ← hv]`. Use `(residue_eq_zero_iff' W (v - a₀ * u ^ p)).mp ?_` and prove the remaining obligations. Rewrite using `[map_sub, map_mul, map_pow]`. Rewrite `huv` using `[eA, eD]`.

Simplify using `only [eval_mul, eval_C, eval_pow, eval_X] at huv`. Apply `mul_left_cancel₀ hd` to reduce the goal to its premises. Take the linear combination `-huv`.
-/
theorem weierstrassP_mul_congr_pow : ∀ (L : PeriodPair) (W : ValuationSubring ℂ) (α : ℂ) (p : ℕ), (2 : ℂ)⁻¹ ∈ W → (3 : ℂ)⁻¹ ∈ W → L.g₂ ∈ W → L.g₃ ∈ W → (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)⁻¹ ∈ W → p.Prime → (p : ℂ) ∈ W.nonunits → α ∈ W.nonunits → (∀ l ∈ L.lattice, α * l ∈ L.lattice) → ‖α‖ ^ 2 = p → ∃ a : ℂ, a ∈ W ∧ a⁻¹ ∈ W ∧ a ≠ 0 ∧ L.g₂ - a ^ 2 * L.g₂ ^ p ∈ W.nonunits ∧ L.g₃ - a ^ 3 * L.g₃ ^ p ∈ W.nonunits ∧ ∀ (m : ℕ) (t : ℂ), Odd m → (m : ℂ)⁻¹ ∈ W → (m : ℂ) * t ∈ L.lattice → t ∉ L.lattice → L.weierstrassP (α * t) - a * L.weierstrassP t ^ p ∈ W.nonunits := by
  intro L W α p h2 h3 hg₂ hg₃ hΔ hp hpW hαW hα hN
  have hΔ0 : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 ≠ 0 := TorsionIntegral.disc L
  have h0 : α ≠ 0 := by
    rintro rfl
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hN
    exact hp.ne_zero (by exact_mod_cast hN.symm)
  haveI : Fact p.Prime := ⟨hp⟩
  set ρ := IsLocalRing.residue W with hρ
  have hpk : (p : IsLocalRing.ResidueField W) = 0 := by
    rw [← map_natCast ρ, residue_eq_zero_iff']
    simpa using hpW
  haveI : CharP (IsLocalRing.ResidueField W) p := (CharP.charP_iff_prime_eq_zero hp).mpr hpk
  have hcop : ∀ m : ℕ, Odd m → (m : ℂ)⁻¹ ∈ W → p.Coprime m := by
    intro m hm hmW
    rw [hp.coprime_iff_not_dvd, ← CharP.cast_eq_zero_iff (IsLocalRing.ResidueField W) p,
      ← map_natCast ρ]
    apply residue_ne_zero_of_inv_mem
    · simpa using hm.pos.ne'
    · simpa using hmW
  obtain ⟨A, D, hD, hAd, hDd, hev, hode⟩ := exists_weierstrassP_mul_ode L α p h0 hα hN
  obtain ⟨c, A₀, D₀, hc, hA₀, hD₀, hne⟩ := exists_scaling W A D hD
  have hmul : ∀ (m : ℕ) (t : ℂ), (m : ℂ) * t ∈ L.lattice → (m : ℂ) * (α * t) ∈ L.lattice := by
    intro m t h
    have := hα _ h
    rwa [mul_left_comm] at this

  have rel : ∀ (m : ℕ) (t : ℂ), Odd m → (m : ℂ)⁻¹ ∈ W → (m : ℂ) * t ∈ L.lattice →
      t ∉ L.lattice → ∃ x y : W, (x : ℂ) = L.weierstrassP t ∧ (y : ℂ) = L.weierstrassP (α * t) ∧
        (A₀.map ρ).eval (ρ x) = ρ y * (D₀.map ρ).eval (ρ x) := by
    intro m t hm hmW hmt ht
    have hαt : α * t ∉ L.lattice := fun h => ht (mem_of_mul_mem L h0 hα hN (hcop m hm hmW) hmt h)
    have T := (TorsionIntegral.torsion_integral_distinct L W m h2 h3 hg₂ hg₃ hΔ hm hmW).1
    refine ⟨⟨_, T t hmt ht⟩, ⟨_, T _ (hmul m t hmt) hαt⟩, rfl, rfl, ?_⟩
    rw [eval_map_apply, eval_map_apply, ← map_mul]
    congr 1
    apply W.subtype_injective
    rw [map_mul, ← eval_map_apply, ← eval_map_apply, hA₀, hD₀]
    obtain ⟨e1, e2⟩ := hev t hαt
    simp only [eval_mul, eval_C, ValuationSubring.coe_subtype]
    rw [e2]
    field_simp
  have h3n : ∀ n : ℕ, ((3 ^ n : ℕ) : ℂ)⁻¹ ∈ W := fun n => by
    rw [Nat.cast_pow, ← inv_pow]
    exact pow_mem (by simpa using h3) n
  have hodd : ∀ n : ℕ, Odd (3 ^ n) := fun n => Odd.pow (by decide)
  have hpow : ∀ i j : ℕ, i + 1 ≤ j → ((3 ^ j : ℕ) : ℂ) * (L.ω₁ / 3 ^ (i + 1)) ∈ L.lattice := by
    intro i j hij
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
    convert L.lattice.smul_mem ((3 : ℤ) ^ d) L.ω₁_mem_lattice using 1
    simp only [zsmul_eq_mul]
    push_cast
    field_simp
    ring
  have hthird : ∀ j : ℕ, ((3 ^ j : ℕ) : ℂ) * (L.ω₁ / 3 ^ (j + 1)) = L.ω₁ / 3 := by
    intro j
    push_cast
    field_simp
    ring
  have hns : ∀ (n : ℕ) (z : ℂ), z ∈ L.lattice → (n : ℂ) * z ∈ L.lattice := fun n z hz => by
    simpa using L.lattice.smul_mem (n : ℤ) hz
  have hnot : ∀ j : ℕ, L.ω₁ / 3 ^ (j + 1) ∉ L.lattice := fun j h =>
    third_notMem L (hthird j ▸ hns _ _ h)
  have h33 : ((3 : ℕ) : ℂ) * (L.ω₁ / 3) ∈ L.lattice := by simpa using hpow 0 1 le_rfl
  have hαthird : α * (L.ω₁ / 3) ∉ L.lattice := fun h => third_notMem L
    (mem_of_mul_mem L h0 hα hN (hcop 3 (by decide) (by simpa using h3)) h33 h)

  have dist : ∀ β : ℂ, (∀ l ∈ L.lattice, β * l ∈ L.lattice) → β * (L.ω₁ / 3) ∉ L.lattice →
      ∀ x : ℕ → W, (∀ j, (x j : ℂ) = L.weierstrassP (β * (L.ω₁ / 3 ^ (j + 1)))) →
      Function.Injective fun j => ρ (x j) := by
    intro β hβ hβ3 x hx
    have hm : ∀ i j : ℕ, i + 1 ≤ j →
        ((3 ^ j : ℕ) : ℂ) * (β * (L.ω₁ / 3 ^ (i + 1))) ∈ L.lattice := by
      intro i j hij
      rw [mul_left_comm]
      exact hβ _ (hpow i j hij)
    have hn : ∀ j : ℕ, ((3 ^ j : ℕ) : ℂ) * (β * (L.ω₁ / 3 ^ (j + 1))) ∉ L.lattice := by
      intro j
      rw [mul_left_comm, hthird]
      exact hβ3
    refine Function.Injective.of_lt_imp_ne fun i j hij h => ?_
    have T := (TorsionIntegral.torsion_integral_distinct L W (3 ^ (j + 1)) h2 h3 hg₂ hg₃ hΔ
      (hodd _) (h3n _)).2 _ _ (hm i _ (by omega)) (fun h => hn i (hns _ _ h))
      (hm j _ le_rfl) (fun h => hn j (hns _ _ h)) (by
        rw [← hx, ← hx]
        have : ρ (x i - x j) = 0 := by rw [map_sub]; exact sub_eq_zero.mpr h
        exact (residue_eq_zero_iff' W _).mp this)
    apply hn j
    rcases T with T | T
    · convert L.lattice.sub_mem (hm i j hij) (hns (3 ^ j) _ T) using 1
      ring
    · convert L.lattice.sub_mem (hns (3 ^ j) _ T) (hm i j hij) using 1
      ring
  choose x y hx hy hxy using fun j : ℕ =>
    rel (3 ^ (j + 1)) (L.ω₁ / 3 ^ (j + 1)) (hodd _) (h3n _) (hpow j _ le_rfl) (hnot j)
  have hxi := dist 1 (by simp) (by simpa using third_notMem L) x (by simpa using hx)
  have hyi := dist α hα hαthird y hy
  let g₂ : W := ⟨L.g₂, hg₂⟩
  let g₃ : W := ⟨L.g₃, hg₃⟩
  let α₀ : W := ⟨α, W.nonunits_subset hαW⟩
  have hode' : C (α ^ 2) * (C c * D) * (4 * (C c * A) ^ 3 - C L.g₂ * (C c * A) * (C c * D) ^ 2 -
      C L.g₃ * (C c * D) ^ 3) = (derivative (C c * A) * (C c * D) -
        (C c * A) * derivative (C c * D)) ^ 2 * (4 * X ^ 3 - C L.g₂ * X - C L.g₃) := by
    simp only [derivative_C_mul]
    linear_combination C c ^ 4 * hode
  have hode₀ : C (α₀ ^ 2) * D₀ * (4 * A₀ ^ 3 - C g₂ * A₀ * D₀ ^ 2 - C g₃ * D₀ ^ 3) =
      (derivative A₀ * D₀ - A₀ * derivative D₀) ^ 2 * (4 * X ^ 3 - C g₂ * X - C g₃) := by
    apply Polynomial.map_injective W.subtype W.subtype_injective
    simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow, map_C, map_X,
      Polynomial.map_ofNat, ← derivative_map, hA₀, hD₀]
    exact hode'
  have hdvd₀ : (4 * X ^ 3 - C g₂ * X - C g₃ : W[X]) ∣
      D₀ * (4 * A₀ ^ 3 - C g₂ * A₀ * D₀ ^ 2 - C g₃ * D₀ ^ 3) := by
    apply cubic_dvd W h2
    simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow, map_C,
      Polynomial.map_ofNat, hA₀, hD₀]
    have hu : IsUnit (C (α ^ 2) : ℂ[X]) := isUnit_C.mpr (Ne.isUnit (pow_ne_zero _ h0))
    rw [← hu.dvd_mul_left, ← mul_assoc]
    exact Dvd.intro_left _ hode'.symm
  have hdeg : ∀ (B₀ : W[X]) (B : ℂ[X]), B₀.map W.subtype = C c * B →
      (B₀.map ρ).natDegree ≤ B.natDegree := by
    intro B₀ B h
    refine natDegree_map_le.trans ?_
    rw [← natDegree_map_eq_of_injective W.subtype_injective, h, natDegree_C_mul hc]
  have hα₀ : ρ α₀ = 0 := (residue_eq_zero_iff' W _).mpr hαW
  obtain ⟨a, d, ha, hd, eD, eA, e2, e3⟩ := residue_form p (ρ g₂) (ρ g₃) (A₀.map ρ) (D₀.map ρ)
    (by
      rw [← map_ofNat ρ 2]
      exact residue_ne_zero_of_inv_mem W _ (two_ne_zero (α := ℂ)) h2)
    (by
      rw [← map_ofNat ρ 3]
      exact residue_ne_zero_of_inv_mem W _ (three_ne_zero (α := ℂ)) h3)
    (by
      have := residue_ne_zero_of_inv_mem W (g₂ ^ 3 - 27 * g₃ ^ 2) hΔ0 hΔ
      simpa [map_ofNat] using this)
    hne (hAd ▸ hdeg A₀ A hA₀) (lt_of_le_of_lt (hdeg D₀ D hD₀) (by omega))
    _ _ hxi hyi hxy
    (by
      have := congrArg (Polynomial.map ρ) hode₀
      simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow, map_C, map_X,
        Polynomial.map_ofNat, ← derivative_map, map_pow, hα₀, map_zero] at this
      rw [← this]
      ring)
    (by
      have := Polynomial.map_dvd ρ hdvd₀
      simpa only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow, map_C, map_X,
        Polynomial.map_ofNat] using this)
  obtain ⟨a₀, rfl⟩ := IsLocalRing.residue_surjective a
  have ha' : (a₀ : ℂ) ∉ W.nonunits := fun h => ha ((residue_eq_zero_iff' W _).mpr h)
  rw [W.mem_nonunits_iff_or] at ha'
  push Not at ha'
  refine ⟨a₀, a₀.2, ha'.2, ha'.1, ?_, ?_, ?_⟩
  · refine (residue_eq_zero_iff' W (g₂ - a₀ ^ 2 * g₂ ^ p)).mp ?_
    rw [map_sub, map_mul, map_pow, map_pow]
    exact sub_eq_zero.mpr e2
  · refine (residue_eq_zero_iff' W (g₃ - a₀ ^ 3 * g₃ ^ p)).mp ?_
    rw [map_sub, map_mul, map_pow, map_pow]
    exact sub_eq_zero.mpr e3
  · intro m t hm hmW hmt ht
    obtain ⟨u, v, hu, hv, huv⟩ := rel m t hm hmW hmt ht
    rw [← hu, ← hv]
    refine (residue_eq_zero_iff' W (v - a₀ * u ^ p)).mp ?_
    rw [map_sub, map_mul, map_pow]
    rw [eA, eD] at huv
    simp only [eval_mul, eval_C, eval_pow, eval_X] at huv
    apply mul_left_cancel₀ hd
    linear_combination -huv

end GlobalTheory.EisensteinCongruence
