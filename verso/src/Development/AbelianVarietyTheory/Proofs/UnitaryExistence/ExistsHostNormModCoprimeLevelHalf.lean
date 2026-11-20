import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt

namespace GlobalTheory.NormMod

section Finite

variable {R : Type*} [CommRing R] [Finite R]

/- English proof (translation)
Take `⟨j, hj⟩` from `hp.odd_of_ne_two hp2`. Establish `loc : ∀ m : MaximalSpectrum R, ∃ a b : R ⧸ m.asIdeal, a ^ 2 - Ideal.Quotient.mk _ D * b ^ 2 = Ideal.Quotient.mk _ ν`. Introduce `m`. Use `haveI := m.isMaximal`. Use `letI := Ideal.Quotient.field m.asIdeal`.

Use `haveI : Finite (R ⧸ m.asIdeal) := Finite.of_surjective _ Ideal.Quotient.mk_surjective`. Use `letI : Fintype (R ⧸ m.asIdeal) := Fintype.ofFinite _`. Establish `hp0 : (p : R ⧸ m.asIdeal) = 0`. Use `congrArg (Ideal.Quotient.mk m.asIdeal) h0` as an intermediate fact. Simplify using `using this`.

Establish `hchar : ringChar (R ⧸ m.asIdeal) ≠ 2`. Introduce `h`. Establish `h2 : ((2 : ℕ) : R ⧸ m.asIdeal) = 0` using `by rw [← h]; exact ringChar.Nat.cast_ringChar`. Rewrite `hp0` using `[hj]`. Move the coercions through the operations in `at hp0 h2`.

Rewrite `hp0` using `[h2]`. Simplify using `at hp0`. Establish `hD' : Ideal.Quotient.mk m.asIdeal D ≠ 0` using `(hD.map _).ne_zero`. Take `⟨a, b, hab⟩` from `FiniteField.exists_root_sum_quadratic (f := (Polynomial.X ^ 2 : Polynomial (R ⧸ m.asIdeal))) (g := Polynomial.C (-Ideal.Quotient.mk m.asIdeal D) * Polynomial.X ^ 2 + Polynomial.C 0 * Polynomial.X + Polynomial.C (-Ideal.Quotient.mk m.asIdeal ν)) (Polynomial.degree_X_pow 2) (Polyno …`. Use `⟨a, b, ?_⟩` and prove the remaining obligations.

Simplify using `only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hab`. Take the linear combination `hab`. Use `choose a b hab using loc`. Establish `hsurj : Function.Surjective (fun (x : R) (m : MaximalSpectrum R) => Ideal.Quotient.mk m.asIdeal x)` using `fun f => by`. Take `⟨x, hx⟩` from `Ideal.pi_quotient_surjective (I := fun m : MaximalSpectrum R => m.asIdeal) (fun m m' h => MaximalSpectrum.isCoprime_of_ne h) f`.

Conclude with `⟨x, funext hx⟩`. Take `⟨x, hx⟩` from `hsurj a`. Take `⟨y, hy⟩` from `hsurj b`. Establish `hnil : IsNilpotent (x ^ 2 - D * y ^ 2 - ν)`. Rewrite using `[nilpotent_iff_mem_prime]`.

Introduce `J hJ`. Establish `hm : J.IsMaximal` using `IsArtinianRing.isMaximal_of_isPrime J`. Use `hab ⟨J, hm⟩` as an intermediate fact. Rewrite `this` using `[← hx, ← hy]`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`.

Simplify using `only [map_sub, map_mul, map_pow]`. Conclude with `sub_eq_zero.2 this`. Take `⟨μ, hμ⟩` from `hν.exists_right_inv`. Take `⟨k, hk⟩` from `hnil`. Use `set e := μ * (x ^ 2 - D * y ^ 2 - ν) with he`.

Establish `hek : e ^ p ^ k = 0`. Take `⟨c, hc⟩` from `Nat.exists_eq_add_of_le (Nat.lt_pow_self (n := k) hp.one_lt).le`. Rewrite using `[hc, pow_add, he, mul_pow, hk]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨r, hr⟩` from `exists_add_pow_prime_pow_eq hp (1 : R) e k`.

Rewrite `hr` using `[h0, hek]`. Take `⟨i, hi⟩` from `(hp.odd_of_ne_two hp2).pow (n := k)`. Rewrite `hr` using `[hi]`. Use `⟨x * (1 + e) ^ i, y * (1 + e) ^ i, ?_⟩` and prove the remaining obligations. Establish `h1 : x ^ 2 - D * y ^ 2 = ν * (1 + e)`.

Rewrite using `[he]`. Take the linear combination `(-(x ^ 2 - D * y ^ 2 - ν)) * hμ`. Take the linear combination `((1 + e) ^ i) ^ 2 * h1 + ν * hr`.
-/
theorem exists_sq_sub_mul_sq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h0 : (p : R) = 0) {D ν : R}
    (hD : IsUnit D) (hν : IsUnit ν) : ∃ x y : R, x ^ 2 - D * y ^ 2 = ν := by
  obtain ⟨j, hj⟩ := hp.odd_of_ne_two hp2
  have loc : ∀ m : MaximalSpectrum R, ∃ a b : R ⧸ m.asIdeal,
      a ^ 2 - Ideal.Quotient.mk _ D * b ^ 2 = Ideal.Quotient.mk _ ν := by
    intro m
    haveI := m.isMaximal
    letI := Ideal.Quotient.field m.asIdeal
    haveI : Finite (R ⧸ m.asIdeal) := Finite.of_surjective _ Ideal.Quotient.mk_surjective
    letI : Fintype (R ⧸ m.asIdeal) := Fintype.ofFinite _
    have hp0 : (p : R ⧸ m.asIdeal) = 0 := by
      have := congrArg (Ideal.Quotient.mk m.asIdeal) h0
      simpa using this
    have hchar : ringChar (R ⧸ m.asIdeal) ≠ 2 := by
      intro h
      have h2 : ((2 : ℕ) : R ⧸ m.asIdeal) = 0 := by rw [← h]; exact ringChar.Nat.cast_ringChar
      rw [hj] at hp0
      push_cast at hp0 h2
      rw [h2] at hp0
      simp at hp0
    have hD' : Ideal.Quotient.mk m.asIdeal D ≠ 0 := (hD.map _).ne_zero
    obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic
      (f := (Polynomial.X ^ 2 : Polynomial (R ⧸ m.asIdeal)))
      (g := Polynomial.C (-Ideal.Quotient.mk m.asIdeal D) * Polynomial.X ^ 2
        + Polynomial.C 0 * Polynomial.X + Polynomial.C (-Ideal.Quotient.mk m.asIdeal ν))
      (Polynomial.degree_X_pow 2) (Polynomial.degree_quadratic (neg_ne_zero.2 hD'))
      (FiniteField.odd_card_of_char_ne_two hchar)
    refine ⟨a, b, ?_⟩
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C] at hab
    linear_combination hab
  choose a b hab using loc
  have hsurj : Function.Surjective
      (fun (x : R) (m : MaximalSpectrum R) => Ideal.Quotient.mk m.asIdeal x) :=
    fun f => by
      obtain ⟨x, hx⟩ := Ideal.pi_quotient_surjective
        (I := fun m : MaximalSpectrum R => m.asIdeal)
        (fun m m' h => MaximalSpectrum.isCoprime_of_ne h) f
      exact ⟨x, funext hx⟩
  obtain ⟨x, hx⟩ := hsurj a
  obtain ⟨y, hy⟩ := hsurj b
  have hnil : IsNilpotent (x ^ 2 - D * y ^ 2 - ν) := by
    rw [nilpotent_iff_mem_prime]
    intro J hJ
    have hm : J.IsMaximal := IsArtinianRing.isMaximal_of_isPrime J
    have := hab ⟨J, hm⟩
    rw [← hx, ← hy] at this
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simp only [map_sub, map_mul, map_pow]
    exact sub_eq_zero.2 this
  obtain ⟨μ, hμ⟩ := hν.exists_right_inv
  obtain ⟨k, hk⟩ := hnil
  set e := μ * (x ^ 2 - D * y ^ 2 - ν) with he
  have hek : e ^ p ^ k = 0 := by
    obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le (Nat.lt_pow_self (n := k) hp.one_lt).le
    rw [hc, pow_add, he, mul_pow, hk]
    ring
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hp (1 : R) e k
  rw [h0, hek] at hr
  obtain ⟨i, hi⟩ := (hp.odd_of_ne_two hp2).pow (n := k)
  rw [hi] at hr
  refine ⟨x * (1 + e) ^ i, y * (1 + e) ^ i, ?_⟩
  have h1 : x ^ 2 - D * y ^ 2 = ν * (1 + e) := by
    rw [he]; linear_combination (-(x ^ 2 - D * y ^ 2 - ν)) * hμ
  linear_combination ((1 + e) ^ i) ^ 2 * h1 + ν * hr

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨i, j, hij, h⟩ : ∃ i j : ℕ, i < j ∧ a ^ i = a ^ j := by`. Take `⟨i, j, hne, h⟩` from `Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => a ^ n)`. Break down `lt_or_gt_of_ne hne with h' | h'` into its components or cases. Conclude with `⟨i, j, h', h⟩`. Conclude with `⟨j, i, h', h.symm⟩`.

Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_lt hij`. Use `⟨k + 1, k.succ_pos, fun P hP ha => ?_⟩` and prove the remaining obligations. Establish `: a ^ i * (a ^ (k + 1) - 1) ∈ P`. Rewrite using `[show a ^ i * (a ^ (k + 1) - 1) = 0 by linear_combination -h]`. Conclude with `P.zero_mem`.

Conclude with `(hP.mem_or_mem this).resolve_left fun h => ha (hP.mem_of_pow_mem _ h)`.
-/
theorem exists_pow_sub_one_mem (a : R) :
    ∃ k, 0 < k ∧ ∀ P : Ideal R, P.IsPrime → a ∉ P → a ^ k - 1 ∈ P := by
  obtain ⟨i, j, hij, h⟩ : ∃ i j : ℕ, i < j ∧ a ^ i = a ^ j := by
    obtain ⟨i, j, hne, h⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => a ^ n)
    rcases lt_or_gt_of_ne hne with h' | h'
    · exact ⟨i, j, h', h⟩
    · exact ⟨j, i, h', h.symm⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hij
  refine ⟨k + 1, k.succ_pos, fun P hP ha => ?_⟩
  have : a ^ i * (a ^ (k + 1) - 1) ∈ P := by
    rw [show a ^ i * (a ^ (k + 1) - 1) = 0 by linear_combination -h]
    exact P.zero_mem
  exact (hP.mem_or_mem this).resolve_left fun h => ha (hP.mem_of_pow_mem _ h)

/- English proof (translation)
Establish `key : ∀ s : Finset R, (∀ a ∈ s, σ a = -a) → ∃ δ, σ δ = -δ ∧ ∀ P : Ideal R, P.IsPrime → δ ∈ P → ∀ a ∈ s, a ∈ P`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact fun _ => ⟨0, by simp, by simp⟩`. Consider the case `insert b s _ ih`.

Introduce `hs`. Take `⟨δ, hδ, hP⟩` from `ih fun a ha => hs a (Finset.mem_insert_of_mem ha)`. Establish `hb` using `hs b (Finset.mem_insert_self _ _)`. Take `⟨k, hk, hδk⟩` from `exists_pow_sub_one_mem (δ ^ 2)`. Use `⟨δ + (1 - (δ ^ 2) ^ k) * b, ?_, fun P hp h => ?_⟩` and prove the remaining obligations.

Simplify using `only [map_add, map_mul, map_sub, map_pow, map_one, hδ, hb, neg_sq]`. Expand and normalize the polynomial expressions, which then agree. Establish `h1 : δ ∈ P`. Assume the negation of the conclusion as `h1`. Establish `h2` using `hδk P hp fun h => h1 (hp.mem_of_pow_mem _ h)`.

Use `h1 ?_` and prove the remaining obligations. Use `P.add_mem h (P.mul_mem_right b h2)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : (δ ^ 2) ^ k ∈ P` using `P.pow_mem_of_mem (P.pow_mem_of_mem h1 2 two_pos) k hk`.

Establish `h3 : b ∈ P`. Use `P.add_mem (P.sub_mem h h1) (P.mul_mem_right b h2)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Introduce `a ha`.

Break down `Finset.mem_insert.1 ha with rfl | ha` into its components or cases. Conclude with `h3`. Conclude with `hP P hp h1 a ha`. Take `⟨δ, hδ, hP⟩` from `key (Set.toFinite {a | σ a = -a}).toFinset (by simp)`. Use `⟨δ, hδ, ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hu`. Take `⟨P, hmax, hmem⟩` from `exists_max_ideal_of_mem_nonunits hu`. Use `hmax.ne_top (top_le_iff.1 ?_)` and prove the remaining obligations. Rewrite using `[← htop, Ideal.span_le]`. Introduce `a ha`.

Conclude with `hP P hmax.isPrime hmem a (by simpa using ha)`.
-/
theorem exists_isUnit_neg (σ : R →+* R) (htop : Ideal.span {a | σ a = -a} = ⊤) :
    ∃ δ, σ δ = -δ ∧ IsUnit δ := by
  classical
  have key : ∀ s : Finset R, (∀ a ∈ s, σ a = -a) →
      ∃ δ, σ δ = -δ ∧ ∀ P : Ideal R, P.IsPrime → δ ∈ P → ∀ a ∈ s, a ∈ P := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact fun _ => ⟨0, by simp, by simp⟩
    | insert b s _ ih =>
      intro hs
      obtain ⟨δ, hδ, hP⟩ := ih fun a ha => hs a (Finset.mem_insert_of_mem ha)
      have hb := hs b (Finset.mem_insert_self _ _)
      obtain ⟨k, hk, hδk⟩ := exists_pow_sub_one_mem (δ ^ 2)
      refine ⟨δ + (1 - (δ ^ 2) ^ k) * b, ?_, fun P hp h => ?_⟩
      · simp only [map_add, map_mul, map_sub, map_pow, map_one, hδ, hb, neg_sq]
        ring
      · have h1 : δ ∈ P := by
          by_contra h1
          have h2 := hδk P hp fun h => h1 (hp.mem_of_pow_mem _ h)
          refine h1 ?_
          have := P.add_mem h (P.mul_mem_right b h2)
          convert this using 1
          ring
        have h2 : (δ ^ 2) ^ k ∈ P := P.pow_mem_of_mem (P.pow_mem_of_mem h1 2 two_pos) k hk
        have h3 : b ∈ P := by
          have := P.add_mem (P.sub_mem h h1) (P.mul_mem_right b h2)
          convert this using 1
          ring
        intro a ha
        rcases Finset.mem_insert.1 ha with rfl | ha
        · exact h3
        · exact hP P hp h1 a ha
  obtain ⟨δ, hδ, hP⟩ := key (Set.toFinite {a | σ a = -a}).toFinset (by simp)
  refine ⟨δ, hδ, ?_⟩
  by_contra hu
  obtain ⟨P, hmax, hmem⟩ := exists_max_ideal_of_mem_nonunits hu
  refine hmax.ne_top (top_le_iff.1 ?_)
  rw [← htop, Ideal.span_le]
  intro a ha
  exact hP P hmax.isPrime hmem a (by simpa using ha)

/- English proof (translation)
Take `⟨δ, hδ, hu⟩` from `exists_isUnit_neg σ htop`. Establish `unit : ∀ (a : R) (ha : σ a = a), IsUnit a → IsUnit (⟨a, ha⟩ : σ.eqLocus (RingHom.id R))`. Introduce `a ha h`. Take `⟨b, hb⟩` from `h.exists_right_inv`. Establish `h2` using `congrArg σ hb`.

Rewrite `h2` using `[map_mul, ha, map_one]`. Establish `h3 : σ b = b` using `by linear_combination b * h2 - σ b * hb`. Conclude with `IsUnit.of_mul_eq_one ⟨b, h3⟩ (Subtype.ext hb)`. Establish `hD : σ (δ ^ 2) = δ ^ 2` using `by rw [map_pow, hδ, neg_sq]`. Take `⟨⟨x, hx⟩, ⟨y, hy⟩, h⟩` from `exists_sq_sub_mul_sq hp hp2 (R := σ.eqLocus (RingHom.id R)) (Subtype.ext (by simpa using h0)) (unit _ hD (hu.pow 2)) (unit _ hfix hν)`.

Establish `hx' : σ x = x` using `hx`. Establish `hy' : σ y = y` using `hy`. Establish `h' : x ^ 2 - δ ^ 2 * y ^ 2 = ν` using `congrArg Subtype.val h`. Use `⟨x + y * δ, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_mul, hx', hy', hδ]`.

Take the linear combination `h'`.
-/
theorem exists_norm_eq (σ : R →+* R) (htop : Ideal.span {a | σ a = -a} = ⊤) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h0 : (p : R) = 0) {ν : R} (hν : IsUnit ν) (hfix : σ ν = ν) :
    ∃ t, t * σ t = ν := by
  obtain ⟨δ, hδ, hu⟩ := exists_isUnit_neg σ htop
  have unit : ∀ (a : R) (ha : σ a = a), IsUnit a →
      IsUnit (⟨a, ha⟩ : σ.eqLocus (RingHom.id R)) := by
    intro a ha h
    obtain ⟨b, hb⟩ := h.exists_right_inv
    have h2 := congrArg σ hb
    rw [map_mul, ha, map_one] at h2
    have h3 : σ b = b := by linear_combination b * h2 - σ b * hb
    exact IsUnit.of_mul_eq_one ⟨b, h3⟩ (Subtype.ext hb)
  have hD : σ (δ ^ 2) = δ ^ 2 := by rw [map_pow, hδ, neg_sq]
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, h⟩ := exists_sq_sub_mul_sq hp hp2
    (R := σ.eqLocus (RingHom.id R)) (Subtype.ext (by simpa using h0))
    (unit _ hD (hu.pow 2)) (unit _ hfix hν)
  have hx' : σ x = x := hx
  have hy' : σ y = y := hy
  have h' : x ^ 2 - δ ^ 2 * y ^ 2 = ν := congrArg Subtype.val h
  refine ⟨x + y * δ, ?_⟩
  rw [map_add, map_mul, hx', hy', hδ]
  linear_combination h'

end Finite

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HostModel
open scoped TensorProduct

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E)

/- English proof (translation)
Use `haveI := H.unram`. Set `σ` to `IsCMField.ringOfIntegersComplexConj E`. Establish `hσ : ∀ a, σ a = H.bar a` using `fun a => by`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Conclude with `(IsCMField.coe_ringOfIntegersComplexConj E a).trans (H.bar_eq a).symm`.

Set `L : 𝓞 E ⊗[𝓞 (maximalRealSubfield E)] 𝓞 E →ₐ[𝓞 (maximalRealSubfield E)] 𝓞 E` to `Algebra.TensorProduct.lift (AlgHom.id _ _) (σ : 𝓞 E →ₐ[_] 𝓞 E) fun _ _ => Commute.all _ _`. Establish `hL : ∀ x y, L (x ⊗ₜ y) = x * H.bar y` using `fun x y => by simp [L, hσ]`. Establish `h1 : ∀ z, Algebra.TensorProduct.lmul' (𝓞 (maximalRealSubfield E)) (S` using `𝓞 E) z - L z ∈ Ideal.span (Set.range fun b : 𝓞 E => b - H.bar b) := by`. Introduce `z`. Proceed by induction on `z using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul x y`. Rewrite using `[hL, Algebra.TensorProduct.lmul'_apply_tmul, ← mul_sub]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨y, rfl⟩)`. Consider the case `add x y hx hy`.

Rewrite using `[map_add, map_add]`. Use `Ideal.add_mem _ hx hy using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Establish `h2` using `congrArg L (Algebra.FormallyUnramified.one_tmul_mul_elem (R := 𝓞 (maximalRealSubfield E)) H.rt)`. Rewrite `h2` using `[map_mul, map_mul, hL, hL, bar_rt, map_one]`.

Establish `h3 : L (Algebra.FormallyUnramified.elem (𝓞 (maximalRealSubfield E)) (𝓞 E)) = 0`. Apply `mul_left_cancel₀ (mul_ne_zero (two_ne_zero : (2 : 𝓞 E) ≠ 0) (rt_ne_zero H))` to reduce the goal to its premises. Take the linear combination `-h2`. Establish `h4` using `h1 (Algebra.FormallyUnramified.elem (𝓞 (maximalRealSubfield E)) (𝓞 E))`. Rewrite `h4` using `[h3, Algebra.FormallyUnramified.lmul_elem, sub_zero]`.

Conclude with `(Ideal.eq_top_iff_one _).2 h4`.
-/
theorem span_sub_bar : Ideal.span (Set.range fun b : 𝓞 E => b - H.bar b) = ⊤ := by
  haveI := H.unram
  let σ := IsCMField.ringOfIntegersComplexConj E
  have hσ : ∀ a, σ a = H.bar a := fun a => by
    apply RingOfIntegers.ext
    exact (IsCMField.coe_ringOfIntegersComplexConj E a).trans (H.bar_eq a).symm
  let L : 𝓞 E ⊗[𝓞 (maximalRealSubfield E)] 𝓞 E →ₐ[𝓞 (maximalRealSubfield E)] 𝓞 E :=
    Algebra.TensorProduct.lift (AlgHom.id _ _) (σ : 𝓞 E →ₐ[_] 𝓞 E) fun _ _ => Commute.all _ _
  have hL : ∀ x y, L (x ⊗ₜ y) = x * H.bar y := fun x y => by simp [L, hσ]
  have h1 : ∀ z, Algebra.TensorProduct.lmul' (𝓞 (maximalRealSubfield E)) (S := 𝓞 E) z - L z ∈
      Ideal.span (Set.range fun b : 𝓞 E => b - H.bar b) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      rw [hL, Algebra.TensorProduct.lmul'_apply_tmul, ← mul_sub]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨y, rfl⟩)
    | add x y hx hy =>
      rw [map_add, map_add]
      convert Ideal.add_mem _ hx hy using 1
      ring
  have h2 := congrArg L
    (Algebra.FormallyUnramified.one_tmul_mul_elem (R := 𝓞 (maximalRealSubfield E)) H.rt)
  rw [map_mul, map_mul, hL, hL, bar_rt, map_one] at h2
  have h3 : L (Algebra.FormallyUnramified.elem (𝓞 (maximalRealSubfield E)) (𝓞 E)) = 0 := by
    apply mul_left_cancel₀ (mul_ne_zero (two_ne_zero : (2 : 𝓞 E) ≠ 0) (rt_ne_zero H))
    linear_combination -h2
  have h4 := h1 (Algebra.FormallyUnramified.elem (𝓞 (maximalRealSubfield E)) (𝓞 E))
  rw [h3, Algebra.FormallyUnramified.lmul_elem, sub_zero] at h4
  exact (Ideal.eq_top_iff_one _).2 h4

/- English proof (translation)
Distinguish the cases in `hp2 : p = 2`. Substitute `hp2` using the available equality. Choose the witnesses or unpack the hypotheses as in `⟨k, rfl⟩ : Odd ν := by`. Rewrite using `[← Int.isCoprime_two_right]`. Simplify using `using hν`.

Conclude with `⟨1, -k, by simp⟩`. Set `I : Ideal (𝓞 E)` to `Ideal.span {(p : 𝓞 E)}`. Establish `hI : I ≠ ⊥`. Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`. Conclude with `hp.ne_zero` after adjusting the coercions.

Use `haveI : Finite (𝓞 E ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI`. Set `σ : 𝓞 E ⧸ I →+* 𝓞 E ⧸ I` to `Ideal.quotientMap I (H.bar : 𝓞 E →+* 𝓞 E) (by`. Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ rfl`. Rewrite using `[SetLike.mem_coe, Ideal.mem_comap, map_natCast]`.

Conclude with `Ideal.mem_span_singleton_self _)`. Establish `hσ : ∀ a, σ (Ideal.Quotient.mk I a) = Ideal.Quotient.mk I (H.bar a)` using `fun a => rfl`. Establish `htop : Ideal.span {a | σ a = -a} = ⊤`. Rewrite using `[eq_top_iff, ← Ideal.map_top (Ideal.Quotient.mk I), ← span_sub_bar H, Ideal.map_span]`. Use `Ideal.span_mono ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨_, ⟨b, rfl⟩, rfl⟩`. Express the relevant statement in the definitionally equal form `σ _ = _`. Rewrite using `[hσ, map_sub H.bar, bar_bar, ← map_neg, neg_sub]`. Establish `h0 : (p : 𝓞 E ⧸ I) = 0`. Rewrite using `[← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `Ideal.mem_span_singleton_self _`. Establish `hu : IsUnit (ν : 𝓞 E ⧸ I)`. Take `⟨a, b, hab⟩` from `hν`. Use `congrArg (Int.cast : ℤ → 𝓞 E ⧸ I) hab` as an intermediate fact. Move the coercions through the operations in `at this`.

Rewrite `this` using `[h0]`. Conclude with `IsUnit.of_mul_eq_one (a : 𝓞 E ⧸ I) (by linear_combination this)`. Take `⟨t, ht⟩` from `exists_norm_eq σ htop hp hp2 h0 hu (map_intCast σ ν)`. Take `⟨t, rfl⟩` from `Ideal.Quotient.mk_surjective t`. Use `⟨t, ?_⟩` and prove the remaining obligations.

Rewrite using `[← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, ← hσ, ht, map_intCast, sub_self]`.
-/
theorem exists_norm_mod_prime {p : ℕ} (hp : p.Prime) {ν : ℤ} (hν : IsCoprime ν (p : ℤ)) :
    ∃ t : 𝓞 E, (p : 𝓞 E) ∣ t * H.bar t - (ν : 𝓞 E) := by
  by_cases hp2 : p = 2
  · subst hp2
    obtain ⟨k, rfl⟩ : Odd ν := by
      rw [← Int.isCoprime_two_right]; simpa using hν
    exact ⟨1, -k, by simp⟩
  let I : Ideal (𝓞 E) := Ideal.span {(p : 𝓞 E)}
  have hI : I ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  haveI : Finite (𝓞 E ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  let σ : 𝓞 E ⧸ I →+* 𝓞 E ⧸ I := Ideal.quotientMap I (H.bar : 𝓞 E →+* 𝓞 E) (by
    rw [Ideal.span_le]
    rintro _ rfl
    rw [SetLike.mem_coe, Ideal.mem_comap, map_natCast]
    exact Ideal.mem_span_singleton_self _)
  have hσ : ∀ a, σ (Ideal.Quotient.mk I a) = Ideal.Quotient.mk I (H.bar a) := fun a => rfl
  have htop : Ideal.span {a | σ a = -a} = ⊤ := by
    rw [eq_top_iff, ← Ideal.map_top (Ideal.Quotient.mk I), ← span_sub_bar H, Ideal.map_span]
    refine Ideal.span_mono ?_
    rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
    change σ _ = _
    rw [hσ, map_sub H.bar, bar_bar, ← map_neg, neg_sub]
  have h0 : (p : 𝓞 E ⧸ I) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  have hu : IsUnit (ν : 𝓞 E ⧸ I) := by
    obtain ⟨a, b, hab⟩ := hν
    have := congrArg (Int.cast : ℤ → 𝓞 E ⧸ I) hab
    push_cast at this
    rw [h0] at this
    exact IsUnit.of_mul_eq_one (a : 𝓞 E ⧸ I) (by linear_combination this)
  obtain ⟨t, ht⟩ := exists_norm_eq σ htop hp hp2 h0 hu (map_intCast σ ν)
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective t
  refine ⟨t, ?_⟩
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, ← hσ, ht,
    map_intCast, sub_self]

/- English proof (translation)
Take `⟨y, hy⟩` from `ht`. Distinguish the cases in `hpm : p ∣ m`. Take `⟨c, hc⟩` from `hpm`. Establish `hc' : (m : 𝓞 E) = p * c` using `by exact_mod_cast hc`. Establish `hy' : H.bar y = y`.

Establish `h` using `congrArg H.bar hy`. Rewrite `h` using `[map_sub, map_mul, bar_bar, map_intCast, map_mul, map_natCast]`. Apply `mul_left_cancel₀ (Nat.cast_ne_zero.2 hm : (m : 𝓞 E) ≠ 0)` to reduce the goal to its premises. Take the linear combination `hy - h`. Take `⟨a, b, hab⟩` from `hν`.

Establish `hab'` using `congrArg (Int.cast : ℤ → 𝓞 E) hab`. Move the coercions through the operations in `at hab'`. Use `⟨t * (1 - m * y * a * H.w0), ⟨y * b - c * y * y * a + c * (y * a) ^ 2 * (H.w0 * (1 - H.w0)) * (t * H.bar t), ?_⟩, ⟨-(t * y * a * H.w0), by ring⟩⟩` and prove the remaining obligations. Simplify using `only [map_mul, map_sub, map_one, map_natCast, map_intCast, hy', cmHost_bar_halfIntegerGenerator]`. Use `push_cast`.

Take the linear combination `(1 - m * y * a) * hy - m * y * hab' + (m * (-(y * y * a) + (y * a) ^ 2 * (H.w0 * (1 - H.w0)) * (t * H.bar t))) * hc'`. Take `⟨s, z, hz⟩` from `exists_norm_mod_prime H hp hν`. Establish `hco : IsCoprime (m : 𝓞 E) (p : 𝓞 E)` using `((Nat.coprime_comm.1 (hp.coprime_iff_not_dvd.2 hpm)).isCoprime.map (Int.castRingHom (𝓞 E))).imp fun a ⟨b, h⟩ => ⟨b, by simpa using h⟩`. Take `⟨a, b, hab⟩` from `id hco`. Establish `cong : ∀ (k : ℕ) (u v : 𝓞 E), (k : 𝓞 E) ∣ u - v → (k : 𝓞 E) ∣ v * H.bar v - ν → (k : 𝓞 E) ∣ u * H.bar u - ν`.

Introduce and unpack `k u v ⟨w, hw⟩ h`. Establish `h2` using `congrArg H.bar hw`. Rewrite `h2` using `[map_sub, map_mul, map_natCast]`. Use `dvd_add h (Dvd.intro (w * H.bar u + v * H.bar w) rfl : (k : 𝓞 E) ∣ _)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Take the linear combination `H.bar u * hw + v * h2`. Establish `d1 : (m : 𝓞 E) ∣ (b * p * t + a * m * s) - t` using `⟨a * (s - t), by linear_combination t * hab⟩`. Establish `d2 : (p : 𝓞 E) ∣ (b * p * t + a * m * s) - s` using `⟨b * (t - s), by linear_combination s * hab⟩`. Use `⟨b * p * t + a * m * s, ?_, d1⟩` and prove the remaining obligations. Use `push_cast`.

Conclude with `hco.mul_dvd (cong _ _ _ d1 ⟨y, hy⟩) (cong _ _ _ d2 ⟨z, hz⟩)`.
-/
theorem exists_norm_mod_mul_prime {m p : ℕ} (hm : m ≠ 0) (hp : p.Prime) {ν : ℤ}
    (hν : IsCoprime ν (p : ℤ)) {t : 𝓞 E} (ht : (m : 𝓞 E) ∣ t * H.bar t - (ν : 𝓞 E)) :
    ∃ s : 𝓞 E, ((m * p : ℕ) : 𝓞 E) ∣ s * H.bar s - (ν : 𝓞 E) ∧ (m : 𝓞 E) ∣ s - t := by
  obtain ⟨y, hy⟩ := ht
  by_cases hpm : p ∣ m
  · obtain ⟨c, hc⟩ := hpm
    have hc' : (m : 𝓞 E) = p * c := by exact_mod_cast hc
    have hy' : H.bar y = y := by
      have h := congrArg H.bar hy
      rw [map_sub, map_mul, bar_bar, map_intCast, map_mul, map_natCast] at h
      apply mul_left_cancel₀ (Nat.cast_ne_zero.2 hm : (m : 𝓞 E) ≠ 0)
      linear_combination hy - h
    obtain ⟨a, b, hab⟩ := hν
    have hab' := congrArg (Int.cast : ℤ → 𝓞 E) hab
    push_cast at hab'
    refine ⟨t * (1 - m * y * a * H.w0), ⟨y * b - c * y * y * a
      + c * (y * a) ^ 2 * (H.w0 * (1 - H.w0)) * (t * H.bar t), ?_⟩, ⟨-(t * y * a * H.w0), by ring⟩⟩
    simp only [map_mul, map_sub, map_one, map_natCast, map_intCast, hy', cmHost_bar_halfIntegerGenerator]
    push_cast
    linear_combination (1 - m * y * a) * hy - m * y * hab'
      + (m * (-(y * y * a) + (y * a) ^ 2 * (H.w0 * (1 - H.w0)) * (t * H.bar t))) * hc'
  · obtain ⟨s, z, hz⟩ := exists_norm_mod_prime H hp hν
    have hco : IsCoprime (m : 𝓞 E) (p : 𝓞 E) :=
      ((Nat.coprime_comm.1 (hp.coprime_iff_not_dvd.2 hpm)).isCoprime.map
        (Int.castRingHom (𝓞 E))).imp fun a ⟨b, h⟩ => ⟨b, by simpa using h⟩
    obtain ⟨a, b, hab⟩ := id hco
    have cong : ∀ (k : ℕ) (u v : 𝓞 E), (k : 𝓞 E) ∣ u - v → (k : 𝓞 E) ∣ v * H.bar v - ν →
        (k : 𝓞 E) ∣ u * H.bar u - ν := by
      rintro k u v ⟨w, hw⟩ h
      have h2 := congrArg H.bar hw
      rw [map_sub, map_mul, map_natCast] at h2
      have := dvd_add h (Dvd.intro (w * H.bar u + v * H.bar w) rfl : (k : 𝓞 E) ∣ _)
      convert this using 1
      linear_combination H.bar u * hw + v * h2
    have d1 : (m : 𝓞 E) ∣ (b * p * t + a * m * s) - t :=
      ⟨a * (s - t), by linear_combination t * hab⟩
    have d2 : (p : 𝓞 E) ∣ (b * p * t + a * m * s) - s :=
      ⟨b * (t - s), by linear_combination s * hab⟩
    refine ⟨b * p * t + a * m * s, ?_, d1⟩
    push_cast
    exact hco.mul_dvd (cong _ _ _ d1 ⟨y, hy⟩) (cong _ _ _ d2 ⟨z, hz⟩)

/- English proof (translation)
Proceed by induction on `k using induction_on_primes with`. Consider the case `zero => exact absurd rfl hk`. Consider the case `one => exact fun _ t ht => ⟨t, by simpa using ht, by simp⟩`. Consider the case `prime_mul p k hp ih`. Introduce `m hm t ht`.

Move the coercions through the operations in `at hν`. Take `⟨s, hs, hst⟩` from `exists_norm_mod_mul_prime H hm hp hν.of_mul_right_left ht`. Take `⟨u, hu, hus⟩` from `ih (right_ne_zero_of_mul hk) hν.of_mul_right_right (mul_ne_zero hm hp.ne_zero) hs`. Use `⟨u, by rwa [← mul_assoc], ?_⟩` and prove the remaining obligations. Move the coercions through the operations in `at hus`.

Simplify using `using dvd_add (dvd_of_mul_right_dvd hus) hst`.
-/
theorem exists_norm_mod_mul {k : ℕ} (hk : k ≠ 0) {ν : ℤ} (hν : IsCoprime ν (k : ℤ)) :
    ∀ {m : ℕ}, m ≠ 0 → ∀ {t : 𝓞 E}, (m : 𝓞 E) ∣ t * H.bar t - (ν : 𝓞 E) →
      ∃ s : 𝓞 E, ((m * k : ℕ) : 𝓞 E) ∣ s * H.bar s - (ν : 𝓞 E) ∧ (m : 𝓞 E) ∣ s - t := by
  induction k using induction_on_primes with
  | zero => exact absurd rfl hk
  | one => exact fun _ t ht => ⟨t, by simpa using ht, by simp⟩
  | prime_mul p k hp ih =>
    intro m hm t ht
    push_cast at hν
    obtain ⟨s, hs, hst⟩ := exists_norm_mod_mul_prime H hm hp hν.of_mul_right_left ht
    obtain ⟨u, hu, hus⟩ := ih (right_ne_zero_of_mul hk) hν.of_mul_right_right
      (mul_ne_zero hm hp.ne_zero) hs
    refine ⟨u, by rwa [← mul_assoc], ?_⟩
    push_cast at hus
    simpa using dvd_add (dvd_of_mul_right_dvd hus) hst

/- English proof (translation)
Take `⟨a, ha, b, hb, hab⟩` from `Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 l.coprime)`. Establish `ha' : H.bar a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)` using `Ideal.mem_map_of_mem _ ha`. Establish `hb' : H.bar b ∈ l.Mb`. Take `⟨c, hc, rfl⟩` from `(Ideal.mem_map_iff_of_surjective (H.bar : 𝓞 E →+* 𝓞 E) H.bar.surjective).1 hb`. Simplify using `using hc`.

Establish `hab'` using `congrArg H.bar hab`. Rewrite `hab'` using `[map_add, map_one]`. Use `⟨b + ν * a, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← Ideal.mem_span_singleton, ← l.prod]`. Establish `h` using `Ideal.add_mem _ (Ideal.mul_mem_left _ (1 - (ν : 𝓞 E)) (Ideal.mul_mem_mul hb' hb)) (Ideal.mul_mem_left _ ((ν : 𝓞 E) ^ 2 - ν) (Ideal.mul_mem_mul ha ha'))`.

Use `h using 1` and compare the differences between its conclusion and the goal. Rewrite using `[map_add, map_mul, map_intCast]`. Take the linear combination `(ν : 𝓞 E) * (H.bar a + H.bar b) * hab + (ν : 𝓞 E) * hab'`. Use `l.Mb.mul_mem_left ((ν : 𝓞 E) - 1) ha using 1` and compare the differences between its conclusion and the goal. Take the linear combination `hab`.
-/
theorem exists_norm_mod_level (l : Level H) (ν : ℤ) :
    ∃ t : 𝓞 E, (l.M : 𝓞 E) ∣ t * H.bar t - (ν : 𝓞 E) ∧ t - 1 ∈ l.Mb := by
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 l.coprime)
  have ha' : H.bar a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := Ideal.mem_map_of_mem _ ha
  have hb' : H.bar b ∈ l.Mb := by
    obtain ⟨c, hc, rfl⟩ := (Ideal.mem_map_iff_of_surjective (H.bar : 𝓞 E →+* 𝓞 E) H.bar.surjective).1 hb
    simpa using hc
  have hab' := congrArg H.bar hab
  rw [map_add, map_one] at hab'
  refine ⟨b + ν * a, ?_, ?_⟩
  · rw [← Ideal.mem_span_singleton, ← l.prod]
    have h := Ideal.add_mem _
      (Ideal.mul_mem_left _ (1 - (ν : 𝓞 E)) (Ideal.mul_mem_mul hb' hb))
      (Ideal.mul_mem_left _ ((ν : 𝓞 E) ^ 2 - ν) (Ideal.mul_mem_mul ha ha'))
    convert h using 1
    rw [map_add, map_mul, map_intCast]
    linear_combination (ν : 𝓞 E) * (H.bar a + H.bar b) * hab + (ν : 𝓞 E) * hab'
  · convert l.Mb.mul_mem_left ((ν : 𝓞 E) - 1) ha using 1
    linear_combination hab

/- English proof (translation)
Distinguish the cases in `hM : l.M ∣ n`. Take `⟨k, rfl⟩` from `hM`. Take `⟨t, ht, ht1⟩` from `exists_norm_mod_level H l ν`. Move the coercions through the operations in `at hν`. Take `⟨s, hs, c, hc⟩` from `exists_norm_mod_mul H (right_ne_zero_of_mul hn.ne') hν.of_mul_right_right (left_ne_zero_of_mul hn.ne') ht`.

Use `⟨s, hs, fun _ => ?_⟩` and prove the remaining obligations. Establish `hMb : (l.M : 𝓞 E) ∈ l.Mb`. Establish `h` using `Ideal.mem_span_singleton_self (l.M : 𝓞 E)`. Rewrite `h` using `[← l.prod]`. Conclude with `(Ideal.mul_le_inf (I := l.Mb) h).1`.

Use `l.Mb.add_mem ht1 (l.Mb.mul_mem_right c hMb) using 1` and compare the differences between its conclusion and the goal. Take the linear combination `hc`. Take `⟨s, hs, -⟩` from `exists_norm_mod_mul H hn.ne' hν (m := 1) one_ne_zero (t := 1) (by simp)`. Conclude with `⟨s, by simpa using hs, fun h => absurd h hM⟩`.
-/
theorem exists_norm_mod (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H)
    (n : ℕ) (ν : ℤ) (hn : 0 < n) (hν : IsCoprime ν (n : ℤ)) :
    ∃ t : 𝓞 E, (n : 𝓞 E) ∣ t * H.bar t - (ν : 𝓞 E) ∧ (l.M ∣ n → t - 1 ∈ l.Mb) := by
  by_cases hM : l.M ∣ n
  · obtain ⟨k, rfl⟩ := hM
    obtain ⟨t, ht, ht1⟩ := exists_norm_mod_level H l ν
    push_cast at hν
    obtain ⟨s, hs, c, hc⟩ := exists_norm_mod_mul H (right_ne_zero_of_mul hn.ne')
      hν.of_mul_right_right (left_ne_zero_of_mul hn.ne') ht
    refine ⟨s, hs, fun _ => ?_⟩
    have hMb : (l.M : 𝓞 E) ∈ l.Mb := by
      have h := Ideal.mem_span_singleton_self (l.M : 𝓞 E)
      rw [← l.prod] at h
      exact (Ideal.mul_le_inf (I := l.Mb) h).1
    convert l.Mb.add_mem ht1 (l.Mb.mul_mem_right c hMb) using 1
    linear_combination hc
  · obtain ⟨s, hs, -⟩ := exists_norm_mod_mul H hn.ne' hν (m := 1) one_ne_zero (t := 1) (by simp)
    exact ⟨s, by simpa using hs, fun h => absurd h hM⟩

end GlobalTheory.NormMod
