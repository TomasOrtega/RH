import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.LocTower

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.Pst CrystallineSemistableComparison UpperTheory.Gal.Int.Geo

namespace UpperTheory.Gal.Seam

section Place

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}

/- English proof (translation)
Take `⟨n, d, hd, rfl⟩` from `IsFractionRing.div_surjective (A := 𝓞 E) x`. Establish `hd0 : d ≠ 0` using `nonZeroDivisors.ne_zero hd`. Establish `hd1 : algebraMap (𝓞 E) E d ≠ 0` using `by simpa using hd0`. Rewrite `hx` using `[map_div₀, div_le_one₀ (zero_lt_iff.2 (by simpa using hd1)), HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]`. Use `set k := (Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {d})).factors with hk`.

Establish `hv : w.intValuation d = WithZero.exp (-(k : ℤ))` using `w.intValuation_if_neg hd0`. Establish `h1 : d ∈ w.asIdeal ^ k` using `(w.intValuation_le_pow_iff_mem d k).1 hv.le`. Establish `h2 : n ∈ w.asIdeal ^ k` using `(w.intValuation_le_pow_iff_mem n k).1 (hx.trans hv.le)`. Establish `h3 : d ∉ w.asIdeal ^ (k + 1)` using `fun h => by`. Use `(w.intValuation_le_pow_iff_mem d (k + 1)).2 h` as an intermediate fact.

Rewrite `this` using `[hv, WithZero.exp_le_exp]`. Move the coercions through the operations in `at this`. Use linear arithmetic over natural numbers and integers. Take `⟨J, hJ⟩` from `Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 h1)`. Establish `h4 : ¬ J ≤ w.asIdeal` using `fun h => h3 <| by`.

Establish `: d ∈ Ideal.span {d}` using `Ideal.mem_span_singleton_self d`. Rewrite `this` using `[hJ]`. Rewrite using `[pow_succ]`. Conclude with `Ideal.mul_mono_right h this`. Take `⟨b, hbJ, hb⟩` from `SetLike.not_le_iff_exists.1 h4`.

Establish `h5 : n * b ∈ Ideal.span {d}` using `hJ ▸ Ideal.mul_mem_mul h2 hbJ`. Take `⟨a, ha⟩` from `Ideal.mem_span_singleton'.1 h5`. Use `⟨a, b, hb, ?_⟩` and prove the remaining obligations. Rewrite using `[div_mul_eq_mul_div, div_eq_iff hd1, ← map_mul, ← map_mul, ha]`.
-/
private theorem exists_den {x : E} (hx : w.valuation E x ≤ 1) :
    ∃ a b : 𝓞 E, b ∉ w.asIdeal ∧ x * algebraMap (𝓞 E) E b = algebraMap (𝓞 E) E a := by
  obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hd1 : algebraMap (𝓞 E) E d ≠ 0 := by simpa using hd0
  rw [map_div₀, div_le_one₀ (zero_lt_iff.2 (by simpa using hd1)), HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap] at hx
  set k := (Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {d})).factors with hk
  have hv : w.intValuation d = WithZero.exp (-(k : ℤ)) := w.intValuation_if_neg hd0
  have h1 : d ∈ w.asIdeal ^ k := (w.intValuation_le_pow_iff_mem d k).1 hv.le
  have h2 : n ∈ w.asIdeal ^ k := (w.intValuation_le_pow_iff_mem n k).1 (hx.trans hv.le)
  have h3 : d ∉ w.asIdeal ^ (k + 1) := fun h => by
    have := (w.intValuation_le_pow_iff_mem d (k + 1)).2 h
    rw [hv, WithZero.exp_le_exp] at this
    push_cast at this
    omega
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 h1)
  have h4 : ¬ J ≤ w.asIdeal := fun h => h3 <| by
    have : d ∈ Ideal.span {d} := Ideal.mem_span_singleton_self d
    rw [hJ] at this
    rw [pow_succ]
    exact Ideal.mul_mono_right h this
  obtain ⟨b, hbJ, hb⟩ := SetLike.not_le_iff_exists.1 h4
  have h5 : n * b ∈ Ideal.span {d} := hJ ▸ Ideal.mul_mem_mul h2 hbJ
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 h5
  refine ⟨a, b, hb, ?_⟩
  rw [div_mul_eq_mul_div, div_eq_iff hd1, ← map_mul, ← map_mul, ha]

/- English proof (translation)
Establish `h : IsIntegral A (algebraMap E Ω (algebraMap (𝓞 E) E a))` using `((RingOfIntegers.isIntegral_coe a).algebraMap (B := Ω)).tower_top`. Take `⟨y, hy⟩` from `IsIntegrallyClosed.isIntegral_iff.1 h`. Rewrite using `[← hy]`. Conclude with `y.2`.
-/
private theorem mem_of_int (a : 𝓞 E) : algebraMap E Ω (algebraMap (𝓞 E) E a) ∈ A := by
  have h : IsIntegral A (algebraMap E Ω (algebraMap (𝓞 E) E a)) :=
    ((RingOfIntegers.isIntegral_coe a).algebraMap (B := Ω)).tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  rw [← hy]
  exact y.2

/- English proof (translation)
The claim follows from `le_antisymm ((A.valuation_le_one_iff _).2 (mem_of_int b)) (not_lt.1 fun h => hb ((hA b).1 h))`.
-/
private theorem val_eq_one (hA : IsPlaceOver A w) {b : 𝓞 E} (hb : b ∉ w.asIdeal) :
    A.valuation (algebraMap E Ω (algebraMap (𝓞 E) E b)) = 1 :=
  le_antisymm ((A.valuation_le_one_iff _).2 (mem_of_int b)) (not_lt.1 fun h => hb ((hA b).1 h))

/- English proof (translation)
Take `⟨a, b, hb, e⟩` from `exists_den hx`. Rewrite using `[← A.valuation_le_one_iff]`. Establish `h` using `congrArg (fun y => A.valuation (algebraMap E Ω y)) e`. Simplify using `only [map_mul, val_eq_one hA hb, mul_one] at h`. Rewrite using `[h]`.

Conclude with `(A.valuation_le_one_iff _).2 (mem_of_int a)`.
-/
private theorem mem_of_le_one (hA : IsPlaceOver A w) {x : E} (hx : w.valuation E x ≤ 1) :
    algebraMap E Ω x ∈ A := by
  obtain ⟨a, b, hb, e⟩ := exists_den hx
  rw [← A.valuation_le_one_iff]
  have h := congrArg (fun y => A.valuation (algebraMap E Ω y)) e
  simp only [map_mul, val_eq_one hA hb, mul_one] at h
  rw [h]
  exact (A.valuation_le_one_iff _).2 (mem_of_int a)

/- English proof (translation)
Take `⟨a, b, hb, e⟩` from `exists_den hx.le`. Establish `hb1 : w.valuation E (algebraMap (𝓞 E) E b) = 1` using `le_antisymm (w.valuation_le_one b) (not_lt.1 fun h => hb ((w.valuation_lt_one_iff_mem b).1 h))`. Establish `ha : a ∈ w.asIdeal`. Rewrite using `[← w.valuation_lt_one_iff_mem (K := E)]`. Express the relevant statement in the definitionally equal form `w.valuation E (algebraMap (𝓞 E) E a) < 1`.

Rewrite using `[← e, map_mul, hb1, mul_one]`. Conclude with `hx`. Establish `h` using `congrArg (fun y => A.valuation (algebraMap E Ω y)) e`. Simplify using `only [map_mul, val_eq_one hA hb, mul_one] at h`. Rewrite using `[h]`.

Conclude with `(hA a).2 ha`.
-/
private theorem val_lt_one (hA : IsPlaceOver A w) {x : E} (hx : w.valuation E x < 1) :
    A.valuation (algebraMap E Ω x) < 1 := by
  obtain ⟨a, b, hb, e⟩ := exists_den hx.le
  have hb1 : w.valuation E (algebraMap (𝓞 E) E b) = 1 :=
    le_antisymm (w.valuation_le_one b) (not_lt.1 fun h => hb ((w.valuation_lt_one_iff_mem b).1 h))
  have ha : a ∈ w.asIdeal := by
    rw [← w.valuation_lt_one_iff_mem (K := E)]
    change w.valuation E (algebraMap (𝓞 E) E a) < 1
    rw [← e, map_mul, hb1, mul_one]
    exact hx
  have h := congrArg (fun y => A.valuation (algebraMap E Ω y)) e
  simp only [map_mul, val_eq_one hA hb, mul_one] at h
  rw [h]
  exact (hA a).2 ha

/- English proof (translation)
Assume the negation of the conclusion as `h`. Establish `h1 : 1 < w.valuation E x` using `not_le.1 h`. Establish `h0 : w.valuation E x ≠ 0` using `(zero_lt_one.trans h1).ne'`. Establish `h2 : w.valuation E x⁻¹ < 1`. Rewrite using `[map_inv₀]`.

Conclude with `inv_lt_one_of_one_lt₀ h1`. Establish `h3` using `val_lt_one hA h2`. Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`. Simplify using `at h0`.

Establish `h4 : A.valuation (algebraMap E Ω x) ≠ 0` using `by simpa using hx0`. Rewrite `h3` using `[map_inv₀, map_inv₀, inv_lt_one₀ (zero_lt_iff.2 h4)]`. Conclude with `absurd ((A.valuation_le_one_iff _).2 hx) (not_le.2 h3)`.
-/
private theorem le_one_of_mem (hA : IsPlaceOver A w) {x : E} (hx : algebraMap E Ω x ∈ A) :
    w.valuation E x ≤ 1 := by
  by_contra h
  have h1 : 1 < w.valuation E x := not_le.1 h
  have h0 : w.valuation E x ≠ 0 := (zero_lt_one.trans h1).ne'
  have h2 : w.valuation E x⁻¹ < 1 := by
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ h1
  have h3 := val_lt_one hA h2
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at h0
  have h4 : A.valuation (algebraMap E Ω x) ≠ 0 := by simpa using hx0
  rw [map_inv₀, map_inv₀, inv_lt_one₀ (zero_lt_iff.2 h4)] at h3
  exact absurd ((A.valuation_le_one_iff _).2 hx) (not_le.2 h3)

end Place

/- English proof (translation)
The claim follows from `GroundTheory.PAdicHodge.mem_normInteger`.
-/
private theorem mem_OK_iff {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (x : ↥K) :
    x ∈ OK l K ↔ ‖(x : PadicAlgCl l)‖ ≤ 1 :=
  GroundTheory.PAdicHodge.mem_normInteger

/- English proof (translation)
Establish `hmul : ∀ a b : ↥(OK l K), ‖(((a * b : ↥(OK l K)) : ↥K) : PadicAlgCl l)‖ = ‖((a : ↥K) : PadicAlgCl l)‖ * ‖((b : ↥K) : PadicAlgCl l)‖` using `fun a b => norm_mul _ _`. Establish `hle : ∀ a : ↥(OK l K), ‖((a : ↥K) : PadicAlgCl l)‖ ≤ 1` using `fun a => (mem_OK_iff _).1 a.2`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, rfl⟩`. Establish `h` using `hmul u (↑u⁻¹ : ↥(OK l K))`.

Rewrite `h` using `[Units.mul_inv]`. Establish `h1 : ‖(((1 : ↥(OK l K)) : ↥K) : PadicAlgCl l)‖ = 1` using `norm_one`. Rewrite `h` using `[h1]`. Establish `h2` using `hle u`. Establish `h3` using `hle (↑u⁻¹ : ↥(OK l K))`.

Establish `h4` using `norm_nonneg (((u : ↥(OK l K)) : ↥K) : PadicAlgCl l)`. Use the polynomial consequences of the given equalities and inequalities. Introduce `h`. Establish `hy0 : (y : ↥K) ≠ 0` using `fun h0 => by`. Rewrite `h` using `[h0]`.

Simplify using `at h`. Establish `hinv : (y : ↥K)⁻¹ ∈ OK l K`. Rewrite using `[mem_OK_iff]`. Express the relevant statement in the definitionally equal form `‖((y : ↥K) : PadicAlgCl l)⁻¹‖ ≤ 1`. Rewrite using `[norm_inv, h, inv_one]`.

Conclude with `IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext (mul_inv_cancel₀ hy0))`.
-/
private theorem isUnit_OK_iff {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (y : ↥(OK l K)) :
    IsUnit y ↔ ‖((y : ↥K) : PadicAlgCl l)‖ = 1 := by
  have hmul : ∀ a b : ↥(OK l K), ‖(((a * b : ↥(OK l K)) : ↥K) : PadicAlgCl l)‖ =
      ‖((a : ↥K) : PadicAlgCl l)‖ * ‖((b : ↥K) : PadicAlgCl l)‖ := fun a b => norm_mul _ _
  have hle : ∀ a : ↥(OK l K), ‖((a : ↥K) : PadicAlgCl l)‖ ≤ 1 := fun a => (mem_OK_iff _).1 a.2
  constructor
  · rintro ⟨u, rfl⟩
    have h := hmul u (↑u⁻¹ : ↥(OK l K))
    rw [Units.mul_inv] at h
    have h1 : ‖(((1 : ↥(OK l K)) : ↥K) : PadicAlgCl l)‖ = 1 := norm_one
    rw [h1] at h
    have h2 := hle u
    have h3 := hle (↑u⁻¹ : ↥(OK l K))
    have h4 := norm_nonneg (((u : ↥(OK l K)) : ↥K) : PadicAlgCl l)
    nlinarith
  · intro h
    have hy0 : (y : ↥K) ≠ 0 := fun h0 => by
      rw [h0] at h
      simp at h
    have hinv : (y : ↥K)⁻¹ ∈ OK l K := by
      rw [mem_OK_iff]
      change ‖((y : ↥K) : PadicAlgCl l)⁻¹‖ ≤ 1
      rw [norm_inv, h, inv_one]
    exact IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext (mul_inv_cancel₀ hy0))

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ l _ w A hA O _ _ _ Bw hj`. Use `haveI : IsDiscreteValuationRing (Ow w) := (w.valuation E).valuationSubring_isDiscreteValuationRing`. Establish `hmem : ∀ x : Ow w, algebraMap E Ω (algebraMap (Ow w) E x) ∈ A` using `fun x => mem_of_le_one hA ((Valuation.mem_valuationSubring_iff _ _).1 x.2)`. Establish `hφ : ∀ x : Ow w, ((kOf Bw).comp (algebraMap (Ow w) E)) x ∈ OK l Bw.Kw.1` using `fun x => (mem_OK_iff _).2 ((hj _).1 (hmem x))`. Use `⟨((kOf Bw).comp (algebraMap (Ow w) E)).codRestrict (OK l Bw.Kw.1) hφ, fun x => rfl, fun ϖ hϖ => ?_⟩` and prove the remaining obligations.

Set `ν : Ow w → ℝ` to `fun x => ‖Bw.j (algebraMap E Ω (algebraMap (Ow w) E x))‖`. Set `M : ↥(OK l Bw.Kw.1) → ℝ` to `fun y => ‖((y : ↥Bw.Kw.1) : PadicAlgCl l)‖`. Establish `hν1 : ∀ x, ν x ≤ 1` using `fun x => (hj _).1 (hmem x)`. Establish `hνmul : ∀ x y, ν (x * y) = ν x * ν y` using `fun x y => by simp only [ν, map_mul, norm_mul]`. Establish `hϖ0 : (algebraMap (Ow w) E ϖ) ≠ 0` using `fun h => hϖ.ne_zero (Subtype.ext h)`.

Establish `hϖw : w.valuation E (algebraMap (Ow w) E ϖ) < 1`. Assume the negation of the conclusion as `h`. Establish `h1 : w.valuation E (algebraMap (Ow w) E ϖ) = 1` using `le_antisymm ((Valuation.mem_valuationSubring_iff _ _).1 ϖ.2) (not_lt.1 h)`. Establish `hinv : (algebraMap (Ow w) E ϖ)⁻¹ ∈ (w.valuation E).valuationSubring`. Rewrite using `[Valuation.mem_valuationSubring_iff, map_inv₀, h1, inv_one]`.

Conclude with `hϖ.not_isUnit (IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext (mul_inv_cancel₀ hϖ0)))`. Establish `hϖ1 : ν ϖ < 1` using `(Induces.valuation_lt_one_iff hj _).1 (val_lt_one hA hϖw)`. Establish `hϖp : 0 < ν ϖ` using `norm_pos_iff.2 ((map_ne_zero _).2 ((map_ne_zero _).2 hϖ0))`. Establish `hbound : ∀ y : ↥(OK l Bw.Kw.1), M y < 1 → 0 < M y → M y ≤ ν ϖ`. Introduce `y hy hpos`.

Take `⟨_, ⟨x, rfl⟩, hx⟩` from `Metric.mem_closure_iff.1 (Bw.j_dense (y : ↥Bw.Kw.1).2) _ hpos`. Rewrite `hx` using `[dist_eq_norm]`. Use `set t : PadicAlgCl l := Bw.j (algebraMap E Ω x) with ht`. Use `set s : PadicAlgCl l := ((y : ↥Bw.Kw.1) : PadicAlgCl l) with hs`. Establish `hM : M y = ‖s‖` using `rfl`.

Rewrite `hy`, `hpos`, the goal using `[hM]`. Establish `h1 : ‖t‖ ≤ ‖s‖`. Establish `h` using `IsUltrametricDist.norm_add_le_max s (t - s)`. Rewrite `h` using `[add_sub_cancel, norm_sub_rev]`. Conclude with `h.trans (max_le le_rfl hx.le)`.

Establish `h2 : ‖s‖ ≤ ‖t‖`. Establish `h` using `IsUltrametricDist.norm_add_le_max t (s - t)`. Rewrite `h` using `[add_sub_cancel]`. Conclude with `(le_max_iff.1 h).resolve_right (not_le.2 hx)`. Establish `hxw : w.valuation E x ≤ 1` using `le_one_of_mem hA ((hj _).2 (h1.trans hy.le))`.

Set `ξ : Ow w` to `⟨x, (Valuation.mem_valuationSubring_iff _ _).2 hxw⟩`. Establish `hξ : ν ξ = ‖t‖` using `rfl`. Establish `hnu : ¬ IsUnit ξ`. Introduce and unpack `⟨u, hu⟩`. Establish `h3` using `hνmul u (↑u⁻¹ : Ow w)`.

Rewrite `h3` using `[Units.mul_inv, hu, hξ]`. Establish `h4 : ν 1 = 1` using `by simp [ν]`. Rewrite `h3` using `[h4]`. Establish `h5` using `hν1 (↑u⁻¹ : Ow w)`. Establish `h6` using `norm_nonneg t`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hmax : ξ ∈ Ideal.span {ϖ}`. Rewrite using `[← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ]`. Conclude with `(IsLocalRing.mem_maximalIdeal ξ).2 hnu`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.1 hmax`.

Establish `h3 : ν ξ = ν c * ν ϖ` using `by rw [← hc, hνmul]`. Establish `h4` using `hν1 c`. Establish `h5 : ‖t‖ ≤ ν ϖ`. Rewrite using `[← hξ, h3]`. Use the polynomial consequences of the given equalities and inequalities.

Conclude with `h2.trans h5`. Use `set φ := ((kOf Bw).comp (algebraMap (Ow w) E)).codRestrict (OK l Bw.Kw.1) hφ with hφdef`. Establish `hMϖ : M (φ ϖ) = ν ϖ` using `rfl`. Establish `hMmul : ∀ a b, M (a * b) = M a * M b` using `fun a b => norm_mul _ _`. Establish `hMle : ∀ a, M a ≤ 1` using `fun a => (mem_OK_iff _).1 a.2`.

Rewrite using `[irreducible_iff]`. Use `⟨fun h => ?_, fun a b hab => ?_⟩` and prove the remaining obligations. Use `(isUnit_OK_iff _).1 h` as an intermediate fact. Express the relevant statement in the definitionally equal form `M (φ ϖ) = 1 at this`. Rewrite `this` using `[hMϖ]`.

Conclude with `hϖ1.ne this`. Assume the negation of the conclusion as `hn`. Take `⟨ha, hb⟩` from `not_or.1 hn`. Establish `ha1 : M a < 1` using `lt_of_le_of_ne (hMle a) fun h => ha ((isUnit_OK_iff _).2 h)`. Establish `hb1 : M b < 1` using `lt_of_le_of_ne (hMle b) fun h => hb ((isUnit_OK_iff _).2 h)`.

Establish `hprod : ν ϖ = M a * M b` using `by rw [← hMϖ, hab, hMmul]`. Establish `ha0 : 0 ≤ M a` using `norm_nonneg _`. Establish `hb0 : 0 ≤ M b` using `norm_nonneg _`. Establish `hap : 0 < M a` using `lt_of_le_of_ne ha0 fun h => by`. Rewrite `hprod` using `[← h, zero_mul]`.

Conclude with `hϖp.ne' hprod`. Establish `hbp : 0 < M b` using `lt_of_le_of_ne hb0 fun h => by`. Rewrite `hprod` using `[← h, mul_zero]`. Conclude with `hϖp.ne' hprod`. Establish `h1` using `hbound a ha1 hap`.

Establish `h2` using `hbound b hb1 hbp`. Establish `h3 : M a * M b ≤ ν ϖ * ν ϖ` using `mul_le_mul h1 h2 hb0 hϖp.le`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem intMap : IntMap := by
  intro E Ω _ _ _ _ _ l _ w A hA O _ _ _ Bw hj
  haveI : IsDiscreteValuationRing (Ow w) := (w.valuation E).valuationSubring_isDiscreteValuationRing
  have hmem : ∀ x : Ow w, algebraMap E Ω (algebraMap (Ow w) E x) ∈ A := fun x =>
    mem_of_le_one hA ((Valuation.mem_valuationSubring_iff _ _).1 x.2)
  have hφ : ∀ x : Ow w, ((kOf Bw).comp (algebraMap (Ow w) E)) x ∈ OK l Bw.Kw.1 := fun x =>
    (mem_OK_iff _).2 ((hj _).1 (hmem x))
  refine ⟨((kOf Bw).comp (algebraMap (Ow w) E)).codRestrict (OK l Bw.Kw.1) hφ, fun x => rfl, fun ϖ hϖ => ?_⟩
  let ν : Ow w → ℝ := fun x => ‖Bw.j (algebraMap E Ω (algebraMap (Ow w) E x))‖
  let M : ↥(OK l Bw.Kw.1) → ℝ := fun y => ‖((y : ↥Bw.Kw.1) : PadicAlgCl l)‖
  have hν1 : ∀ x, ν x ≤ 1 := fun x => (hj _).1 (hmem x)
  have hνmul : ∀ x y, ν (x * y) = ν x * ν y := fun x y => by simp only [ν, map_mul, norm_mul]
  have hϖ0 : (algebraMap (Ow w) E ϖ) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hϖw : w.valuation E (algebraMap (Ow w) E ϖ) < 1 := by
    by_contra h
    have h1 : w.valuation E (algebraMap (Ow w) E ϖ) = 1 :=
      le_antisymm ((Valuation.mem_valuationSubring_iff _ _).1 ϖ.2) (not_lt.1 h)
    have hinv : (algebraMap (Ow w) E ϖ)⁻¹ ∈ (w.valuation E).valuationSubring := by
      rw [Valuation.mem_valuationSubring_iff, map_inv₀, h1, inv_one]
    exact hϖ.not_isUnit (IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext (mul_inv_cancel₀ hϖ0)))
  have hϖ1 : ν ϖ < 1 := (Induces.valuation_lt_one_iff hj _).1 (val_lt_one hA hϖw)
  have hϖp : 0 < ν ϖ := norm_pos_iff.2 ((map_ne_zero _).2 ((map_ne_zero _).2 hϖ0))
  have hbound : ∀ y : ↥(OK l Bw.Kw.1), M y < 1 → 0 < M y → M y ≤ ν ϖ := by
    intro y hy hpos
    obtain ⟨_, ⟨x, rfl⟩, hx⟩ := Metric.mem_closure_iff.1 (Bw.j_dense (y : ↥Bw.Kw.1).2) _ hpos
    rw [dist_eq_norm] at hx
    set t : PadicAlgCl l := Bw.j (algebraMap E Ω x) with ht
    set s : PadicAlgCl l := ((y : ↥Bw.Kw.1) : PadicAlgCl l) with hs
    have hM : M y = ‖s‖ := rfl
    rw [hM] at hy hpos ⊢
    have h1 : ‖t‖ ≤ ‖s‖ := by
      have h := IsUltrametricDist.norm_add_le_max s (t - s)
      rw [add_sub_cancel, norm_sub_rev] at h
      exact h.trans (max_le le_rfl hx.le)
    have h2 : ‖s‖ ≤ ‖t‖ := by
      have h := IsUltrametricDist.norm_add_le_max t (s - t)
      rw [add_sub_cancel] at h
      exact (le_max_iff.1 h).resolve_right (not_le.2 hx)
    have hxw : w.valuation E x ≤ 1 := le_one_of_mem hA ((hj _).2 (h1.trans hy.le))
    let ξ : Ow w := ⟨x, (Valuation.mem_valuationSubring_iff _ _).2 hxw⟩
    have hξ : ν ξ = ‖t‖ := rfl
    have hnu : ¬ IsUnit ξ := by
      rintro ⟨u, hu⟩
      have h3 := hνmul u (↑u⁻¹ : Ow w)
      rw [Units.mul_inv, hu, hξ] at h3
      have h4 : ν 1 = 1 := by simp [ν]
      rw [h4] at h3
      have h5 := hν1 (↑u⁻¹ : Ow w)
      have h6 := norm_nonneg t
      nlinarith
    have hmax : ξ ∈ Ideal.span {ϖ} := by
      rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ]
      exact (IsLocalRing.mem_maximalIdeal ξ).2 hnu
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hmax
    have h3 : ν ξ = ν c * ν ϖ := by rw [← hc, hνmul]
    have h4 := hν1 c
    have h5 : ‖t‖ ≤ ν ϖ := by
      rw [← hξ, h3]
      nlinarith
    exact h2.trans h5
  set φ := ((kOf Bw).comp (algebraMap (Ow w) E)).codRestrict (OK l Bw.Kw.1) hφ with hφdef
  have hMϖ : M (φ ϖ) = ν ϖ := rfl
  have hMmul : ∀ a b, M (a * b) = M a * M b := fun a b => norm_mul _ _
  have hMle : ∀ a, M a ≤ 1 := fun a => (mem_OK_iff _).1 a.2
  rw [irreducible_iff]
  refine ⟨fun h => ?_, fun a b hab => ?_⟩
  · have := (isUnit_OK_iff _).1 h
    change M (φ ϖ) = 1 at this
    rw [hMϖ] at this
    exact hϖ1.ne this
  · by_contra hn
    obtain ⟨ha, hb⟩ := not_or.1 hn
    have ha1 : M a < 1 := lt_of_le_of_ne (hMle a) fun h => ha ((isUnit_OK_iff _).2 h)
    have hb1 : M b < 1 := lt_of_le_of_ne (hMle b) fun h => hb ((isUnit_OK_iff _).2 h)
    have hprod : ν ϖ = M a * M b := by rw [← hMϖ, hab, hMmul]
    have ha0 : 0 ≤ M a := norm_nonneg _
    have hb0 : 0 ≤ M b := norm_nonneg _
    have hap : 0 < M a := lt_of_le_of_ne ha0 fun h => by
      rw [← h, zero_mul] at hprod
      exact hϖp.ne' hprod
    have hbp : 0 < M b := lt_of_le_of_ne hb0 fun h => by
      rw [← h, mul_zero] at hprod
      exact hϖp.ne' hprod
    have h1 := hbound a ha1 hap
    have h2 := hbound b hb1 hbp
    have h3 : M a * M b ≤ ν ϖ * ν ϖ := mul_le_mul h1 h2 hb0 hϖp.le
    nlinarith

end UpperTheory.Gal.Seam
