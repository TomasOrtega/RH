import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverExtAlgebraMap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem

noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial

/- English proof (translation)
Use `set v := IsDiscreteValuationRing.maximalIdeal K.O with hv`. Take `⟨a, rfl⟩` from `IsDiscreteValuationRing.exists_lift_of_le_one (A := K.O) (K := K.E) (x := x) (by rw [hx, ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num)`. Use `⟨a, rfl, ?_⟩` and prove the remaining obligations. Rewrite `hx` using `[IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]`. Establish `h1 : a ∈ v.asIdeal`.

Rewrite using `[← IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem, hx, ← WithZero.exp_zero, WithZero.exp_lt_exp]`. Evaluate the numerical expressions. Establish `h2 : a ∉ v.asIdeal ^ 2`. Rewrite using `[← IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem, hx, WithZero.exp_le_exp]`. Evaluate the numerical expressions.

Express the relevant statement in the definitionally equal form `a ∈ IsLocalRing.maximalIdeal K.O at h1`. Express the relevant statement in the definitionally equal form `a ∉ IsLocalRing.maximalIdeal K.O ^ 2 at h2`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible K.O`. Establish `hm` using `hϖ.maximalIdeal_eq`. Rewrite `h1`, `h2`, the goal using `[hm]`.

Take `⟨b, rfl⟩` from `Ideal.mem_span_singleton'.1 h1`. Establish `hb : IsUnit b`. Assume the negation of the conclusion as `hb`. Apply `h2` to reduce the goal to its premises. Establish `: b ∈ IsLocalRing.maximalIdeal K.O` using `(IsLocalRing.mem_maximalIdeal b).2 hb`.

Rewrite `this` using `[hm]`. Rewrite using `[Ideal.span_singleton_pow, Ideal.mem_span_singleton, pow_two]`. Conclude with `mul_dvd_mul (Ideal.mem_span_singleton.1 this) dvd_rfl`. Rewrite using `[Ideal.span_singleton_mul_left_unit hb]`.
-/
theorem exists_gen_of_valuation_eq (K : UQ) (x : K.E)
    (hx : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E x = WithZero.exp (-1)) :
    ∃ a : K.O, algebraMap K.O K.E a = x ∧ IsLocalRing.maximalIdeal K.O = Ideal.span {a} := by
  set v := IsDiscreteValuationRing.maximalIdeal K.O with hv
  obtain ⟨a, rfl⟩ := IsDiscreteValuationRing.exists_lift_of_le_one (A := K.O) (K := K.E)
    (x := x) (by rw [hx, ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num)
  refine ⟨a, rfl, ?_⟩
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap] at hx
  have h1 : a ∈ v.asIdeal := by
    rw [← IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem, hx, ← WithZero.exp_zero,
      WithZero.exp_lt_exp]; norm_num
  have h2 : a ∉ v.asIdeal ^ 2 := by
    rw [← IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem, hx, WithZero.exp_le_exp]; norm_num
  change a ∈ IsLocalRing.maximalIdeal K.O at h1
  change a ∉ IsLocalRing.maximalIdeal K.O ^ 2 at h2
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
  have hm := hϖ.maximalIdeal_eq
  rw [hm] at h1 h2 ⊢
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 h1
  have hb : IsUnit b := by
    by_contra hb
    apply h2
    have : b ∈ IsLocalRing.maximalIdeal K.O := (IsLocalRing.mem_maximalIdeal b).2 hb
    rw [hm] at this
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, pow_two]
    exact mul_dvd_mul (Ideal.mem_span_singleton.1 this) dvd_rfl
  rw [Ideal.span_singleton_mul_left_unit hb]

/- English proof (translation)
Take `⟨x, hx⟩` from `(IsDiscreteValuationRing.maximalIdeal K.O).valuation_exists_uniformizer K.E`. Establish `hx' : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E x = WithZero.exp (-1)` using `hx`. Take `⟨π, hπ, hm⟩` from `exists_gen_of_valuation_eq K x hx'`. Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hx'` using `[map_zero]`. Conclude with `WithZero.exp_ne_zero hx'.symm`. Establish `hv` using `h.2.2.1 x`. Unfold `val at hv`. Rewrite `hv` using `[hx', WithZero.log_exp]`.

Establish `hy0 : (IsDiscreteValuationRing.maximalIdeal K'.O).valuation K'.E (φ x) ≠ 0`. Simplify using `using (map_ne_zero φ).2 hx0`. Establish `hy : (IsDiscreteValuationRing.maximalIdeal K'.O).valuation K'.E (φ x) = WithZero.exp (-1)`. Rewrite using `[← WithZero.exp_log hy0]`. Use `congr 1`.

Use linear arithmetic over natural numbers and integers. Take `⟨π', hπ', hm'⟩` from `exists_gen_of_valuation_eq K' (φ x) hy`. Conclude with `⟨π, π', by rw [hπ', hπ], hm, hm'⟩`.
-/
theorem exists_unif (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E) (h : IsUnrExt K K' d φ) :
    ∃ π : K.O, ∃ π' : K'.O, algebraMap K'.O K'.E π' = φ (algebraMap K.O K.E π) ∧
      IsLocalRing.maximalIdeal K.O = Ideal.span {π} ∧ IsLocalRing.maximalIdeal K'.O = Ideal.span {π'} := by
  obtain ⟨x, hx⟩ := (IsDiscreteValuationRing.maximalIdeal K.O).valuation_exists_uniformizer K.E
  have hx' : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E x = WithZero.exp (-1) := hx
  obtain ⟨π, hπ, hm⟩ := exists_gen_of_valuation_eq K x hx'
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx'
    exact WithZero.exp_ne_zero hx'.symm
  have hv := h.2.2.1 x
  unfold val at hv
  rw [hx', WithZero.log_exp] at hv
  have hy0 : (IsDiscreteValuationRing.maximalIdeal K'.O).valuation K'.E (φ x) ≠ 0 := by
    simpa using (map_ne_zero φ).2 hx0
  have hy : (IsDiscreteValuationRing.maximalIdeal K'.O).valuation K'.E (φ x) = WithZero.exp (-1) := by
    rw [← WithZero.exp_log hy0]; congr 1; omega
  obtain ⟨π', hπ', hm'⟩ := exists_gen_of_valuation_eq K' (φ x) hy
  exact ⟨π, π', by rw [hπ', hπ], hm, hm'⟩

end GlobalTheory.UnitLemma.Unr
