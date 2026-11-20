import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowDvdDifferentIdealIffPowSuccDvdMap
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

namespace GlobalTheory.CodimDual

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => exact fun y _ => ⟨y, 1, (Ideal.ne_top_iff_one Q).1 hQ.ne_top, by simp⟩`. Consider the case `succ n ih`. Introduce `y hy`. Rewrite `hy` using `[pow_succ]`.

Use `Submodule.mul_induction_on hy ?_ ?_` and prove the remaining obligations. Introduce `m hm x hx`. Take `⟨c, r, hr, e⟩` from `ih m hm`. Take `⟨c', r', hr', e'⟩` from `hs x hx`. Use `⟨c * c', r * r', fun h => (hQ.mem_or_mem h).elim hr hr', ?_⟩` and prove the remaining obligations.

Take the linear combination `(r' * x) * e + (c * s ^ n) * e'`. Introduce and unpack `x x' ⟨c, r, hr, e⟩ ⟨c', r', hr', e'⟩`. Use `⟨r' * c + r * c', r * r', fun h => (hQ.mem_or_mem h).elim hr hr', ?_⟩` and prove the remaining obligations. Take the linear combination `r' * e + r * e'`.
-/
theorem loc_pow {B : Type} [CommRing B] (Q : Ideal B) [hQ : Q.IsPrime] (s : B)
    (hs : ∀ y ∈ Q, ∃ c r : B, r ∉ Q ∧ r * y = c * s) (n : ℕ) :
    ∀ y ∈ Q ^ n, ∃ c r : B, r ∉ Q ∧ r * y = c * s ^ n := by
  induction n with
  | zero => exact fun y _ => ⟨y, 1, (Ideal.ne_top_iff_one Q).1 hQ.ne_top, by simp⟩
  | succ n ih =>
    intro y hy
    rw [pow_succ] at hy
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro m hm x hx
      obtain ⟨c, r, hr, e⟩ := ih m hm
      obtain ⟨c', r', hr', e'⟩ := hs x hx
      refine ⟨c * c', r * r', fun h => (hQ.mem_or_mem h).elim hr hr', ?_⟩
      linear_combination (r' * x) * e + (c * s ^ n) * e'
    · rintro x x' ⟨c, r, hr, e⟩ ⟨c', r', hr', e'⟩
      refine ⟨r' * c + r * c', r * r', fun h => (hQ.mem_or_mem h).elim hr hr', ?_⟩
      linear_combination r' * e + r * e'

/- English proof (translation)
Use `⟨(Ideal.IsPrime.mul_mem_pow Q (a := r) ?_).resolve_left hr, fun hx => ?_⟩` and prove the remaining obligations. Rewrite using `[h]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hsQ e)`. Establish `h1 : s ^ e ∈ Q ^ (e + 1)` using `(Ideal.IsPrime.mul_mem_pow Q (a := a) (h ▸ Ideal.mul_mem_left _ _ hx)).resolve_left ha`. Use `(Ideal.pow_succ_lt_pow h0 e).not_ge fun y hy => ?_` and prove the remaining obligations.

Take `⟨c', r', hr', e'⟩` from `loc_pow Q s hs e y hy`. Conclude with `(Ideal.IsPrime.mul_mem_pow Q (a := r') (e' ▸ Ideal.mul_mem_left _ _ h1)).resolve_left hr'`.
-/
theorem exact_exponent {B : Type} [CommRing B] [IsDedekindDomain B] (Q : Ideal B) [hQ : Q.IsPrime] (h0 : Q ≠ ⊥)
    (s : B) (hsQ : s ∈ Q) (hs : ∀ y ∈ Q, ∃ c r : B, r ∉ Q ∧ r * y = c * s) (e : ℕ) (x a r : B)
    (ha : a ∉ Q) (hr : r ∉ Q) (h : r * x = a * s ^ e) : x ∈ Q ^ e ∧ x ∉ Q ^ (e + 1) := by
  refine ⟨(Ideal.IsPrime.mul_mem_pow Q (a := r) ?_).resolve_left hr, fun hx => ?_⟩
  · rw [h]; exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hsQ e)
  · have h1 : s ^ e ∈ Q ^ (e + 1) :=
      (Ideal.IsPrime.mul_mem_pow Q (a := a) (h ▸ Ideal.mul_mem_left _ _ hx)).resolve_left ha
    refine (Ideal.pow_succ_lt_pow h0 e).not_ge fun y hy => ?_
    obtain ⟨c', r', hr', e'⟩ := loc_pow Q s hs e y hy
    exact (Ideal.IsPrime.mul_mem_pow Q (a := r') (e' ▸ Ideal.mul_mem_left _ _ h1)).resolve_left hr'

section Core

variable {A B : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDedekindDomain B]
  [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B] [CharZero (IsLocalRing.ResidueField A)]

/- English proof (translation)
Establish `hπ0 : π ≠ 0`. Introduce and unpack `rfl`. Conclude with `IsDiscreteValuationRing.not_a_field A (by simpa using hπ)`. Establish `hπQ : algebraMap A B π ∈ Q` using `(hQ.mem_or_mem (x := r) (h ▸ Q.mul_mem_left _ (Q.pow_mem_of_mem hsQ e he))).resolve_left hr`. Establish `h0 : Q ≠ ⊥`.

Introduce and unpack `rfl`. Conclude with `hπ0 ((FaithfulSMul.algebraMap_injective A B) (by simpa using hπQ))`. Use `haveI : Q.IsMaximal := hQ.isMaximal h0`. Use `haveI : Q.LiesOver (IsLocalRing.maximalIdeal A) := ⟨(IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q)).symm⟩`. Take `⟨h1, h2⟩` from `exact_exponent Q h0 s hsQ hs e _ a r ha hr h`.

Rewrite using `[GlobalTheory.TameDifferent.pow_dvd_differentIdeal_iff_pow_succ_dvd_map A B Q, GlobalTheory.TameDifferent.pow_dvd_differentIdeal_iff_pow_succ_dvd_map A B Q, hπ, Ideal.map_span, Set.image_singleton, Nat.sub_add_cancel he, Ideal.dvd_span_singleton, Ideal.dvd_span_singleton]`. Conclude with `⟨h1, h2⟩`.
-/
theorem different_exponent (π : A) (hπ : IsLocalRing.maximalIdeal A = Ideal.span {π}) (Q : Ideal B) [hQ : Q.IsPrime]
    (s : B) (e : ℕ) (he : 1 ≤ e) (hsQ : s ∈ Q) (hs : ∀ y ∈ Q, ∃ c r : B, r ∉ Q ∧ r * y = c * s) (a r : B)
    (ha : a ∉ Q) (hr : r ∉ Q) (h : r * algebraMap A B π = a * s ^ e) :
    Q ^ (e - 1) ∣ differentIdeal A B ∧ ¬ Q ^ e ∣ differentIdeal A B := by
  have hπ0 : π ≠ 0 := by
    rintro rfl
    exact IsDiscreteValuationRing.not_a_field A (by simpa using hπ)
  have hπQ : algebraMap A B π ∈ Q := (hQ.mem_or_mem (x := r)
    (h ▸ Q.mul_mem_left _ (Q.pow_mem_of_mem hsQ e he))).resolve_left hr
  have h0 : Q ≠ ⊥ := by
    rintro rfl
    exact hπ0 ((FaithfulSMul.algebraMap_injective A B) (by simpa using hπQ))
  haveI : Q.IsMaximal := hQ.isMaximal h0
  haveI : Q.LiesOver (IsLocalRing.maximalIdeal A) :=
    ⟨(IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q)).symm⟩
  obtain ⟨h1, h2⟩ := exact_exponent Q h0 s hsQ hs e _ a r ha hr h
  rw [GlobalTheory.TameDifferent.pow_dvd_differentIdeal_iff_pow_succ_dvd_map A B Q, GlobalTheory.TameDifferent.pow_dvd_differentIdeal_iff_pow_succ_dvd_map A B Q, hπ, Ideal.map_span, Set.image_singleton, Nat.sub_add_cancel he,
    Ideal.dvd_span_singleton, Ideal.dvd_span_singleton]
  exact ⟨h1, h2⟩

variable (F K : Type) [Field F] [Field K] [Algebra A F] [IsFractionRing A F] [Algebra B K] [IsFractionRing B K]
  [Algebra F K] [Algebra A K] [IsScalarTower A F K] [IsScalarTower A B K] [FiniteDimensional F K]
  [Algebra.IsSeparable F K]

omit [CharZero (IsLocalRing.ResidueField A)] in

/- English proof (translation)
Use `haveI : IsIntegralClosure B A K := IsIntegralClosure.of_isIntegrallyClosed B A K`. Establish `h1 : (∀ b : B, Algebra.trace F K (z * algebraMap B K b) ∈ (algebraMap A F).range) ↔ z ∈ FractionalIdeal.dual A F (1 : FractionalIdeal (nonZeroDivisors B) K)`. Rewrite using `[FractionalIdeal.mem_dual (I := (1 : FractionalIdeal (nonZeroDivisors B) K)) one_ne_zero]`. Prove the components needed by the constructor for the conclusion. Introduce `h a ha`.

Take `⟨b, rfl⟩` from `(FractionalIdeal.mem_one_iff _).1 ha`. Conclude with `h b`. Introduce `h b`. Conclude with `h _ ((FractionalIdeal.mem_one_iff _).2 ⟨b, rfl⟩)`. Establish `h2` using `coeIdeal_differentIdeal A F K B`.

Establish `h3 : ((differentIdeal A B : Ideal B) : FractionalIdeal (nonZeroDivisors B) K) ≠ 0`. Rewrite using `[h2]`. Conclude with `inv_ne_zero (FractionalIdeal.dual_ne_zero A F one_ne_zero)`. Rewrite using `[h1, ← inv_inv (FractionalIdeal.dual A F (1 : FractionalIdeal (nonZeroDivisors B) K)), ← h2, FractionalIdeal.mem_inv_iff h3]`. Prove the components needed by the constructor for the conclusion.

Introduce `h d hd`. Conclude with `(FractionalIdeal.mem_one_iff _).1 (h _ (FractionalIdeal.mem_coeIdeal_of_mem _ hd))`. Introduce `h y hy`. Take `⟨d, hd, rfl⟩` from `(FractionalIdeal.mem_coeIdeal _).1 hy`. Conclude with `(FractionalIdeal.mem_one_iff _).2 (h d hd)`.
-/
theorem trace_mem_iff (z : K) :
    (∀ b : B, Algebra.trace F K (z * algebraMap B K b) ∈ (algebraMap A F).range) ↔
      ∀ d ∈ differentIdeal A B, ∃ c : B, algebraMap B K c = z * algebraMap B K d := by
  haveI : IsIntegralClosure B A K := IsIntegralClosure.of_isIntegrallyClosed B A K
  have h1 : (∀ b : B, Algebra.trace F K (z * algebraMap B K b) ∈ (algebraMap A F).range) ↔
      z ∈ FractionalIdeal.dual A F (1 : FractionalIdeal (nonZeroDivisors B) K) := by
    rw [FractionalIdeal.mem_dual (I := (1 : FractionalIdeal (nonZeroDivisors B) K)) one_ne_zero]
    constructor
    · intro h a ha
      obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
      exact h b
    · intro h b
      exact h _ ((FractionalIdeal.mem_one_iff _).2 ⟨b, rfl⟩)
  have h2 := coeIdeal_differentIdeal A F K B
  have h3 : ((differentIdeal A B : Ideal B) : FractionalIdeal (nonZeroDivisors B) K) ≠ 0 := by
    rw [h2]; exact inv_ne_zero (FractionalIdeal.dual_ne_zero A F one_ne_zero)
  rw [h1, ← inv_inv (FractionalIdeal.dual A F (1 : FractionalIdeal (nonZeroDivisors B) K)), ← h2,
    FractionalIdeal.mem_inv_iff h3]
  constructor
  · intro h d hd
    exact (FractionalIdeal.mem_one_iff _).1 (h _ (FractionalIdeal.mem_coeIdeal_of_mem _ hd))
  · intro h y hy
    obtain ⟨d, hd, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    exact (FractionalIdeal.mem_one_iff _).2 (h d hd)

/- English proof (translation)
Take `⟨⟨J, hJ⟩, h2⟩` from `different_exponent π hπ Q s e he hsQ hs a r ha hr h`. Establish `hJQ : ¬ J ≤ Q` using `fun hle => h2 (by`. Rewrite using `[hJ]`. Use `nth_rewrite 1 [← Nat.sub_add_cancel he]`. Rewrite using `[pow_succ]`.

Conclude with `mul_dvd_mul_left _ (Ideal.dvd_iff_le.2 hle))`. Take `⟨j, hj, hjQ⟩` from `SetLike.not_le_iff_exists.1 hJQ`. Take `⟨c, hc⟩` from `(trace_mem_iff F K z).1 hz (s ^ (e - 1) * j) (hJ ▸ Ideal.mul_mem_mul (Ideal.pow_mem_pow hsQ _) hj)`. Use `⟨c, j, hjQ, ?_⟩` and prove the remaining obligations. Rewrite using `[hc, map_mul, map_pow]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem core_mp (π : A) (hπ : IsLocalRing.maximalIdeal A = Ideal.span {π}) (z : K)
    (hz : ∀ b : B, Algebra.trace F K (z * algebraMap B K b) ∈ (algebraMap A F).range) (Q : Ideal B) [hQ : Q.IsPrime]
    (s : B) (e : ℕ) (he : 1 ≤ e) (hsQ : s ∈ Q) (hs : ∀ y ∈ Q, ∃ c r : B, r ∉ Q ∧ r * y = c * s) (a r : B)
    (ha : a ∉ Q) (hr : r ∉ Q) (h : r * algebraMap A B π = a * s ^ e) :
    ∃ c r : B, r ∉ Q ∧ algebraMap B K r * (algebraMap B K s ^ (e - 1) * z) = algebraMap B K c := by
  obtain ⟨⟨J, hJ⟩, h2⟩ := different_exponent π hπ Q s e he hsQ hs a r ha hr h
  have hJQ : ¬ J ≤ Q := fun hle => h2 (by
    rw [hJ]
    nth_rewrite 1 [← Nat.sub_add_cancel he]
    rw [pow_succ]
    exact mul_dvd_mul_left _ (Ideal.dvd_iff_le.2 hle))
  obtain ⟨j, hj, hjQ⟩ := SetLike.not_le_iff_exists.1 hJQ
  obtain ⟨c, hc⟩ := (trace_mem_iff F K z).1 hz (s ^ (e - 1) * j)
    (hJ ▸ Ideal.mul_mem_mul (Ideal.pow_mem_pow hsQ _) hj)
  refine ⟨c, j, hjQ, ?_⟩
  rw [hc, map_mul, map_pow]; ring

/- English proof (translation)
Rewrite using `[trace_mem_iff (A := A) F K z]`. Introduce `d hd`. Set `I : Ideal B` to `(LinearMap.range (Algebra.linearMap B K)).comap (LinearMap.toSpanSingleton B K (z * algebraMap B K d))`. Establish `hI : ∀ r : B, r ∈ I ↔ ∃ c : B, algebraMap B K c = algebraMap B K r * (z * algebraMap B K d)`. Introduce `r`.

Simplify using `only [I, Submodule.mem_comap, LinearMap.mem_range, LinearMap.toSpanSingleton_apply, Algebra.smul_def, Algebra.linearMap_apply]`. Establish `htop : I = ⊤`. Assume the negation of the conclusion as `hne`. Take `⟨Q, hQ, hle⟩` from `Ideal.exists_le_maximal I hne`. Take `⟨s, e, he, hsQ, hs, ⟨a, r, ha, hr, h⟩, c, r', hr', hc⟩` from `hz Q hQ`.

Take `⟨h1, -⟩` from `different_exponent π hπ Q s e he hsQ hs a r ha hr h`. Take `⟨c', r'', hr'', e'⟩` from `loc_pow Q s hs (e - 1) d (Ideal.dvd_iff_le.1 h1 hd)`. Use `(hQ.isPrime.mem_or_mem (hle ((hI (r' * r'')).2 ⟨c * c', ?_⟩))).elim hr' hr''` and prove the remaining obligations. Establish `e2` using `congrArg (algebraMap B K) e'`. Simplify using `only [map_mul, map_pow] at e2 ⊢`.

Take the linear combination `(-algebraMap B K c') * hc - (algebraMap B K r' * z) * e2`. Take `⟨c, hc⟩` from `(hI 1).1 (htop ▸ Submodule.mem_top)`. Conclude with `⟨c, by simpa using hc⟩`.
-/
theorem core_mpr (π : A) (hπ : IsLocalRing.maximalIdeal A = Ideal.span {π}) (z : K)
    (hz : ∀ Q : Ideal B, Q.IsMaximal → ∃ (s : B) (e : ℕ), 1 ≤ e ∧ s ∈ Q ∧ (∀ y ∈ Q, ∃ c r : B, r ∉ Q ∧ r * y = c * s) ∧
      (∃ a r : B, a ∉ Q ∧ r ∉ Q ∧ r * algebraMap A B π = a * s ^ e) ∧
      ∃ c r : B, r ∉ Q ∧ algebraMap B K r * (algebraMap B K s ^ (e - 1) * z) = algebraMap B K c) :
    ∀ b : B, Algebra.trace F K (z * algebraMap B K b) ∈ (algebraMap A F).range := by
  rw [trace_mem_iff (A := A) F K z]
  intro d hd
  let I : Ideal B := (LinearMap.range (Algebra.linearMap B K)).comap
    (LinearMap.toSpanSingleton B K (z * algebraMap B K d))
  have hI : ∀ r : B, r ∈ I ↔ ∃ c : B, algebraMap B K c = algebraMap B K r * (z * algebraMap B K d) := by
    intro r
    simp only [I, Submodule.mem_comap, LinearMap.mem_range, LinearMap.toSpanSingleton_apply, Algebra.smul_def,
      Algebra.linearMap_apply]
  have htop : I = ⊤ := by
    by_contra hne
    obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal I hne
    obtain ⟨s, e, he, hsQ, hs, ⟨a, r, ha, hr, h⟩, c, r', hr', hc⟩ := hz Q hQ
    obtain ⟨h1, -⟩ := different_exponent π hπ Q s e he hsQ hs a r ha hr h
    obtain ⟨c', r'', hr'', e'⟩ := loc_pow Q s hs (e - 1) d (Ideal.dvd_iff_le.1 h1 hd)
    refine (hQ.isPrime.mem_or_mem (hle ((hI (r' * r'')).2 ⟨c * c', ?_⟩))).elim hr' hr''
    have e2 := congrArg (algebraMap B K) e'
    simp only [map_mul, map_pow] at e2 ⊢
    linear_combination (-algebraMap B K c') * hc - (algebraMap B K r' * z) * e2
  obtain ⟨c, hc⟩ := (hI 1).1 (htop ▸ Submodule.mem_top)
  exact ⟨c, by simpa using hc⟩

end Core

section Transfer

variable {B B' : Type} [CommRing B] [CommRing B'] [Algebra B B'] (M : Submonoid B) [IsLocalization M B']

include M in

/- English proof (translation)
Introduce `y hy`. Take `⟨⟨b, m⟩, hb⟩` from `IsLocalization.surj M y`. Take `⟨c, r, hr, e⟩` from `hs b (by`. Rewrite using `[Ideal.under_def, Ideal.mem_comap, ← hb]`. Conclude with `Q'.mul_mem_right _ hy)`.

Use `⟨algebraMap B B' c, algebraMap B B' r * algebraMap B B' m, fun h => (hQ.mem_or_mem h).elim hr fun hm => ?_, ?_⟩` and prove the remaining obligations. Conclude with `hQ.ne_top (Q'.eq_top_of_isUnit_mem hm (IsLocalization.map_units B' m))`. Establish `e2` using `congrArg (algebraMap B B') e`. Simplify using `only [map_mul] at e2 hb`. Take the linear combination `e2 + algebraMap B B' r * hb`.
-/
theorem gen_up (Q' : Ideal B') [hQ : Q'.IsPrime] (s : B)
    (hs : ∀ y ∈ Q'.under B, ∃ c r : B, r ∉ Q'.under B ∧ r * y = c * s) :
    ∀ y ∈ Q', ∃ c r : B', r ∉ Q' ∧ r * y = c * algebraMap B B' s := by
  intro y hy
  obtain ⟨⟨b, m⟩, hb⟩ := IsLocalization.surj M y
  obtain ⟨c, r, hr, e⟩ := hs b (by
    rw [Ideal.under_def, Ideal.mem_comap, ← hb]; exact Q'.mul_mem_right _ hy)
  refine ⟨algebraMap B B' c, algebraMap B B' r * algebraMap B B' m, fun h => (hQ.mem_or_mem h).elim hr fun hm => ?_, ?_⟩
  · exact hQ.ne_top (Q'.eq_top_of_isUnit_mem hm (IsLocalization.map_units B' m))
  · have e2 := congrArg (algebraMap B B') e
    simp only [map_mul] at e2 hb
    linear_combination e2 + algebraMap B B' r * hb

include M in

/- English proof (translation)
Take `⟨⟨r0, m1⟩, h1⟩` from `IsLocalization.surj M r`. Take `⟨⟨c0, m2⟩, h2⟩` from `IsLocalization.surj M c`. Establish `hu : ∀ m : M, algebraMap B B' m ∉ Q'` using `fun m hm => hQ.ne_top (Q'.eq_top_of_isUnit_mem hm (IsLocalization.map_units B' m))`. Use `⟨c0 * m1, r0 * m2, fun hm => ?_, ?_⟩` and prove the remaining obligations. Rewrite `hm` using `[Ideal.under_def, Ideal.mem_comap, map_mul, ← h1]`.

Conclude with `(hQ.mem_or_mem hm).elim (fun h' => (hQ.mem_or_mem h').elim hr (hu m1)) (hu m2)`. Establish `e1` using `congrArg (algebraMap B' K) h1`. Establish `e2` using `congrArg (algebraMap B' K) h2`. Simplify using `only [map_mul, ← IsScalarTower.algebraMap_apply] at e1 e2 ⊢`. Take the linear combination `(algebraMap B K m1 * algebraMap B K m2) * h - (algebraMap B K m2 * w) * e1 + algebraMap B K m1 * e2`.
-/
theorem loc_down {K : Type} [CommRing K] [Algebra B K] [Algebra B' K] [IsScalarTower B B' K] (Q' : Ideal B')
    [hQ : Q'.IsPrime] (w : K) (c r : B') (hr : r ∉ Q') (h : algebraMap B' K r * w = algebraMap B' K c) :
    ∃ c r : B, r ∉ Q'.under B ∧ algebraMap B K r * w = algebraMap B K c := by
  obtain ⟨⟨r0, m1⟩, h1⟩ := IsLocalization.surj M r
  obtain ⟨⟨c0, m2⟩, h2⟩ := IsLocalization.surj M c
  have hu : ∀ m : M, algebraMap B B' m ∉ Q' := fun m hm =>
    hQ.ne_top (Q'.eq_top_of_isUnit_mem hm (IsLocalization.map_units B' m))
  refine ⟨c0 * m1, r0 * m2, fun hm => ?_, ?_⟩
  · rw [Ideal.under_def, Ideal.mem_comap, map_mul, ← h1] at hm
    exact (hQ.mem_or_mem hm).elim (fun h' => (hQ.mem_or_mem h').elim hr (hu m1)) (hu m2)
  · have e1 := congrArg (algebraMap B' K) h1
    have e2 := congrArg (algebraMap B' K) h2
    simp only [map_mul, ← IsScalarTower.algebraMap_apply] at e1 e2 ⊢
    linear_combination (algebraMap B K m1 * algebraMap B K m2) * h - (algebraMap B K m2 * w) * e1
      + algebraMap B K m1 * e2

end Transfer

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`. Take `⟨⟨c, r⟩, h⟩` from `IsLocalization.surj p.primeCompl y`. Use `⟨r, c, r.2, ?_⟩` and prove the remaining obligations. Establish `e` using `congrArg (algebraMap A' F) h`.

Simplify using `only [map_mul, ← IsScalarTower.algebraMap_apply] at e`. Rewrite using `[mul_comm, e]`. Introduce and unpack `⟨r, c, hr, h⟩`. Take `⟨v, hv⟩` from `(IsLocalization.map_units A' (⟨r, hr⟩ : p.primeCompl)).exists_left_inv`. Use `⟨v * algebraMap A A' c, ?_⟩` and prove the remaining obligations.

Establish `e` using `congrArg (algebraMap A' F) hv`. Simplify using `only [map_mul, map_one, ← IsScalarTower.algebraMap_apply] at e ⊢`. Take the linear combination `(-algebraMap A' F v) * h + x * e`.
-/
theorem mem_range_iff {A F A' : Type} [CommRing A] [CommRing A'] [Field F] [Algebra A F] [IsFractionRing A F]
    [Algebra A A'] [Algebra A' F] [IsScalarTower A A' F] (p : Ideal A) [p.IsPrime] [IsLocalization.AtPrime A' p] (x : F) :
    x ∈ (algebraMap A' F).range ↔ ∃ r c : A, r ∉ p ∧ algebraMap A F r * x = algebraMap A F c := by
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨⟨c, r⟩, h⟩ := IsLocalization.surj p.primeCompl y
    refine ⟨r, c, r.2, ?_⟩
    have e := congrArg (algebraMap A' F) h
    simp only [map_mul, ← IsScalarTower.algebraMap_apply] at e
    rw [mul_comm, e]
  · rintro ⟨r, c, hr, h⟩
    obtain ⟨v, hv⟩ := (IsLocalization.map_units A' (⟨r, hr⟩ : p.primeCompl)).exists_left_inv
    refine ⟨v * algebraMap A A' c, ?_⟩
    have e := congrArg (algebraMap A' F) hv
    simp only [map_mul, map_one, ← IsScalarTower.algebraMap_apply] at e ⊢
    linear_combination (-algebraMap A' F v) * h + x * e

/- English proof (translation)
Set `Ap` to `Localization.subalgebra.ofField F p.primeCompl p.primeCompl_le_nonZeroDivisors`. Use `haveI : IsLocalization.AtPrime Ap p := inferInstance`. Use `haveI : IsDiscreteValuationRing Ap := GlobalTheory.isDiscreteValuationRing_of_height_eq_one p hp1 Ap`. Use `haveI : CharZero (IsLocalRing.ResidueField Ap) := charZero_of_inj_zero fun n hn => by`. Assume the negation of the conclusion as `h`.

Use `((hchar n h).map ((IsLocalRing.residue Ap).comp (algebraMap A Ap))).ne_zero` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Conclude with `this hn`. Set `B` to `integralClosure A K`. Set `Bp` to `integralClosure Ap K`.

Use `haveI : IsDedekindDomain Bp := integralClosure.isDedekindDomain Ap F K`. Use `haveI : Module.Finite Ap Bp := IsIntegralClosure.finite Ap F K Bp`. Use `haveI : IsFractionRing Bp K := integralClosure.isFractionRing_of_finite_extension F K`. Establish `hinj : Function.Injective (algebraMap Ap K)`. Rewrite using `[IsScalarTower.algebraMap_eq Ap F K]`.

Conclude with `(algebraMap F K).injective.comp (IsFractionRing.injective Ap F)`. Use `haveI : FaithfulSMul Ap Bp := (faithfulSMul_iff_algebraMap_injective Ap Bp).2 fun x y h => hinj (congrArg (fun w : Bp => (w : K)) h)`. Use `haveI : Module.IsTorsionFree Ap Bp := inferInstance`. Use `letI : Algebra B Bp := (RingHom.codRestrict B.val.toRingHom Bp fun b => IsIntegral.tower_top (A := Ap) b.2).toAlgebra`. Use `haveI : IsScalarTower B Bp K := IsScalarTower.of_algebraMap_eq fun _ => rfl`.

Use `haveI : IsScalarTower A B Bp := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Use `haveI : IsLocalization (Algebra.algebraMapSubmonoid K p.primeCompl) K := IsLocalization.self (by`. Introduce and unpack `_ ⟨a, ha, rfl⟩`. Rewrite using `[IsUnit.mem_submonoid_iff, IsScalarTower.algebraMap_apply A Ap K]`. Conclude with `(IsLocalization.map_units Ap (⟨a, ha⟩ : p.primeCompl)).map _)`.

Set `M` to `Algebra.algebraMapSubmonoid B p.primeCompl`. Use `haveI : IsLocalization M Bp := IsLocalization.integralClosure (R := A) (S := K) (Rf := Ap) (Sf := K) p.primeCompl`. Establish `hπ : IsLocalRing.maximalIdeal Ap = Ideal.span {algebraMap A Ap t}`. Rewrite using `[← IsLocalization.AtPrime.map_eq_maximalIdeal p Ap]`. Use `conv_lhs => rw [hpt]`.

Rewrite using `[Ideal.map_span, Set.image_singleton]`. Establish `hrel : ∀ (s a r : B) (e : ℕ), r * algebraMap A B t = a * s ^ e → algebraMap B Bp r * algebraMap Ap Bp (algebraMap A Ap t) = algebraMap B Bp a * algebraMap B Bp s ^ e`. Introduce `s a r e h`. Rewrite using `[← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A B Bp, ← map_mul, h, map_mul, map_pow]`. Prove the components needed by the constructor for the conclusion.

Introduce `hL Q hQ hQp s e he hsQ hs ⟨a, r, ha, hr, h⟩`. Establish `hz : ∀ b : Bp, Algebra.trace F K (z * algebraMap Bp K b) ∈ (algebraMap Ap F).range`. Introduce `b`. Take `⟨⟨b0, _, m, hm, rfl⟩, hb⟩` from `IsLocalization.surj M b`. Take `⟨r, c, hr, h⟩` from `hL b0`.

Use `(mem_range_iff p _).2 ⟨r * m, c, fun h' => (hp.mem_or_mem h').elim hr hm, ?_⟩` and prove the remaining obligations. Establish `e1 : (b0 : K) = (b : K) * algebraMap A K m` using `(congrArg (fun w : Bp => (w : K)) hb).symm`. Establish `e2 : z * (b0 : K) = algebraMap A F m • (z * algebraMap Bp K b)`. Rewrite using `[e1, Algebra.smul_def, ← IsScalarTower.algebraMap_apply]`. Express the relevant statement in the definitionally equal form `_ = _ * (z * (b : K))`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← h, e2, map_smul, map_mul, smul_eq_mul, mul_assoc]`. Establish `hdis : Disjoint (M : Set B) (Q : Set B)`. Rewrite using `[Set.disjoint_left]`. Introduce and unpack `_ ⟨m, hm, rfl⟩ hmQ`.

Conclude with `hm (hQp ▸ hmQ : m ∈ p)`. Use `haveI := IsLocalization.isPrime_of_isPrime_disjoint M Bp Q hQ hdis`. Establish `hu` using `IsLocalization.under_map_of_isPrime_disjoint M Bp hQ hdis`. Generalize the expression as in `Ideal.map (algebraMap B Bp) Q = Q' at *`. Substitute `hu` using the available equality.

Take `⟨c', r', hr', h'⟩` from `core_mp F K _ hπ z hz Q' (algebraMap B Bp s) e he hsQ (gen_up M Q' s hs) _ _ ha hr (hrel s a r e h)`. Conclude with `loc_down M Q' _ c' r' hr' h'`. Introduce `hR b`. Use `(mem_range_iff (A' := Ap) p _).1 (core_mpr F K _ hπ z (fun Q' hQ' => ?_) (algebraMap B Bp b))` and prove the remaining obligations. Establish `hQp : (Q'.under B).under A = p`.

Establish `h1 : Q'.under Ap = IsLocalRing.maximalIdeal Ap` using `IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q')`. Rewrite using `[Ideal.under_under, ← Ideal.under_under (B := Ap), h1]`. Use extensionality with `x`. Conclude with `IsLocalization.AtPrime.to_map_mem_maximal_iff Ap p x`. Take `⟨s, e, he, hsQ, hs, a, r, ha, hr, h⟩` from `hdata (Q'.under B) inferInstance hQp`.

Take `⟨c, r', hr', h'⟩` from `hR (Q'.under B) inferInstance hQp s e he hsQ hs ⟨a, r, ha, hr, h⟩`. Conclude with `⟨algebraMap B Bp s, e, he, hsQ, gen_up M Q' s hs, ⟨_, _, ha, hr, hrel s a r e h⟩, algebraMap B Bp c, algebraMap B Bp r', hr', h'⟩`.
-/
theorem trace_mem_localization_iff (A F K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [Field F] [Field K] [Algebra A F] [IsFractionRing A F] [Algebra F K] [Algebra A K] [IsScalarTower A F K]
    [FiniteDimensional F K] [Algebra.IsSeparable F K] (hchar : ∀ n : ℕ, n ≠ 0 → IsUnit (n : A))
    (p : Ideal A) [hp : p.IsPrime] (hp1 : p.height = 1) (t : A) (hpt : p = Ideal.span {t})
    (hdata : ∀ Q : Ideal (integralClosure A K), Q.IsPrime → Q.under A = p →
      ∃ (s : integralClosure A K) (e : ℕ), 1 ≤ e ∧ s ∈ Q ∧ (∀ y ∈ Q, ∃ c r, r ∉ Q ∧ r * y = c * s) ∧
        (∃ a r : integralClosure A K, a ∉ Q ∧ r ∉ Q ∧ r * algebraMap A _ t = a * s ^ e)) (z : K) :
    (∀ b : integralClosure A K, ∃ r c : A, r ∉ p ∧ algebraMap A F r * Algebra.trace F K (z * b) = algebraMap A F c) ↔
      ∀ Q : Ideal (integralClosure A K), Q.IsPrime → Q.under A = p →
        ∀ (s : integralClosure A K) (e : ℕ), 1 ≤ e → s ∈ Q → (∀ y ∈ Q, ∃ c r, r ∉ Q ∧ r * y = c * s) →
          (∃ a r : integralClosure A K, a ∉ Q ∧ r ∉ Q ∧ r * algebraMap A _ t = a * s ^ e) →
          ∃ c r : integralClosure A K, r ∉ Q ∧ (r : K) * ((s : K) ^ (e - 1) * z) = c := by
  let Ap := Localization.subalgebra.ofField F p.primeCompl p.primeCompl_le_nonZeroDivisors
  haveI : IsLocalization.AtPrime Ap p := inferInstance
  haveI : IsDiscreteValuationRing Ap := GlobalTheory.isDiscreteValuationRing_of_height_eq_one p hp1 Ap
  haveI : CharZero (IsLocalRing.ResidueField Ap) := charZero_of_inj_zero fun n hn => by
    by_contra h
    have := ((hchar n h).map ((IsLocalRing.residue Ap).comp (algebraMap A Ap))).ne_zero
    rw [map_natCast] at this
    exact this hn
  let B := integralClosure A K
  let Bp := integralClosure Ap K
  haveI : IsDedekindDomain Bp := integralClosure.isDedekindDomain Ap F K
  haveI : Module.Finite Ap Bp := IsIntegralClosure.finite Ap F K Bp
  haveI : IsFractionRing Bp K := integralClosure.isFractionRing_of_finite_extension F K
  have hinj : Function.Injective (algebraMap Ap K) := by
    rw [IsScalarTower.algebraMap_eq Ap F K]
    exact (algebraMap F K).injective.comp (IsFractionRing.injective Ap F)
  haveI : FaithfulSMul Ap Bp := (faithfulSMul_iff_algebraMap_injective Ap Bp).2 fun x y h =>
    hinj (congrArg (fun w : Bp => (w : K)) h)
  haveI : Module.IsTorsionFree Ap Bp := inferInstance
  letI : Algebra B Bp := (RingHom.codRestrict B.val.toRingHom Bp fun b => IsIntegral.tower_top (A := Ap) b.2).toAlgebra
  haveI : IsScalarTower B Bp K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower A B Bp := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsLocalization (Algebra.algebraMapSubmonoid K p.primeCompl) K := IsLocalization.self (by
    rintro _ ⟨a, ha, rfl⟩
    rw [IsUnit.mem_submonoid_iff, IsScalarTower.algebraMap_apply A Ap K]
    exact (IsLocalization.map_units Ap (⟨a, ha⟩ : p.primeCompl)).map _)
  let M := Algebra.algebraMapSubmonoid B p.primeCompl
  haveI : IsLocalization M Bp := IsLocalization.integralClosure (R := A) (S := K) (Rf := Ap) (Sf := K) p.primeCompl
  have hπ : IsLocalRing.maximalIdeal Ap = Ideal.span {algebraMap A Ap t} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p Ap]
    conv_lhs => rw [hpt]
    rw [Ideal.map_span, Set.image_singleton]
  have hrel : ∀ (s a r : B) (e : ℕ), r * algebraMap A B t = a * s ^ e →
      algebraMap B Bp r * algebraMap Ap Bp (algebraMap A Ap t) = algebraMap B Bp a * algebraMap B Bp s ^ e := by
    intro s a r e h
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A B Bp, ← map_mul, h, map_mul, map_pow]
  constructor
  · intro hL Q hQ hQp s e he hsQ hs ⟨a, r, ha, hr, h⟩
    have hz : ∀ b : Bp, Algebra.trace F K (z * algebraMap Bp K b) ∈ (algebraMap Ap F).range := by
      intro b
      obtain ⟨⟨b0, _, m, hm, rfl⟩, hb⟩ := IsLocalization.surj M b
      obtain ⟨r, c, hr, h⟩ := hL b0
      refine (mem_range_iff p _).2 ⟨r * m, c, fun h' => (hp.mem_or_mem h').elim hr hm, ?_⟩
      have e1 : (b0 : K) = (b : K) * algebraMap A K m := (congrArg (fun w : Bp => (w : K)) hb).symm
      have e2 : z * (b0 : K) = algebraMap A F m • (z * algebraMap Bp K b) := by
        rw [e1, Algebra.smul_def, ← IsScalarTower.algebraMap_apply]
        change _ = _ * (z * (b : K))
        ring
      rw [← h, e2, map_smul, map_mul, smul_eq_mul, mul_assoc]
    have hdis : Disjoint (M : Set B) (Q : Set B) := by
      rw [Set.disjoint_left]
      rintro _ ⟨m, hm, rfl⟩ hmQ
      exact hm (hQp ▸ hmQ : m ∈ p)
    haveI := IsLocalization.isPrime_of_isPrime_disjoint M Bp Q hQ hdis
    have hu := IsLocalization.under_map_of_isPrime_disjoint M Bp hQ hdis
    generalize Ideal.map (algebraMap B Bp) Q = Q' at *
    subst hu
    obtain ⟨c', r', hr', h'⟩ := core_mp F K _ hπ z hz Q' (algebraMap B Bp s) e he hsQ (gen_up M Q' s hs) _ _ ha hr
      (hrel s a r e h)
    exact loc_down M Q' _ c' r' hr' h'
  · intro hR b
    refine (mem_range_iff (A' := Ap) p _).1 (core_mpr F K _ hπ z (fun Q' hQ' => ?_) (algebraMap B Bp b))
    have hQp : (Q'.under B).under A = p := by
      have h1 : Q'.under Ap = IsLocalRing.maximalIdeal Ap :=
        IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q')
      rw [Ideal.under_under, ← Ideal.under_under (B := Ap), h1]
      ext x
      exact IsLocalization.AtPrime.to_map_mem_maximal_iff Ap p x
    obtain ⟨s, e, he, hsQ, hs, a, r, ha, hr, h⟩ := hdata (Q'.under B) inferInstance hQp
    obtain ⟨c, r', hr', h'⟩ := hR (Q'.under B) inferInstance hQp s e he hsQ hs ⟨a, r, ha, hr, h⟩
    exact ⟨algebraMap B Bp s, e, he, hsQ, gen_up M Q' s hs, ⟨_, _, ha, hr, hrel s a r e h⟩,
      algebraMap B Bp c, algebraMap B Bp r', hr', h'⟩

/- English proof (translation)
Introduce `k F K _ _ _ _ _ _ _ _ _ d u hu A _ hA B hB p hp hp1 t _ hpt _ hdata z`. Use `haveI : IsNoetherianRing A := by`. Substitute `hA` using the available equality. Conclude with `isNoetherianRing_of_ringEquiv _ hu.aevalEquiv.toRingEquiv`. Use `haveI : IsIntegrallyClosed A := by`.

Substitute `hA` using the available equality. Conclude with `IsIntegrallyClosed.of_equiv hu.aevalEquiv.toRingEquiv`. Use `haveI : CharZero F := charZero_of_injective_ringHom (algebraMap k F).injective`. Establish `hchar : ∀ n : ℕ, n ≠ 0 → IsUnit (n : A)` using `fun n hn => by`. Simplify using `using (IsUnit.mk0 (n : k) (Nat.cast_ne_zero.2 hn)).map (algebraMap k A)`.

Substitute `hB` using the available equality. Establish `hover : ∀ Q : Ideal (integralClosure A K), Q.under A = p ↔ ∀ a : A, ∀ b : integralClosure A K, (b : K) = algebraMap F K a → (b ∈ Q ↔ a ∈ p)`. Introduce `Q`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl a b hb`.

Establish `: b = algebraMap A _ a` using `Subtype.ext hb`. Rewrite using `[this]`. Both sides reduce to the same expression. Introduce `h`. Use extensionality with `a`.

Conclude with `h a (algebraMap A _ a) rfl`. Establish `hrel : ∀ (s a r : integralClosure A K) (e : ℕ), r * algebraMap A _ t = a * s ^ e ↔ (r : K) * algebraMap F K t = a * s ^ e` using `fun s a r e => Subtype.ext_iff`. Establish `key` using `trace_mem_localization_iff A F K hchar p hp1 t hpt (by`. Simplify using `only [hover, hrel]`. Conclude with `hdata) z`.

Simplify using `only [hover, hrel, ← mul_assoc] at key`. Conclude with `key`.
-/
theorem trace_mem_localization_iff_forall_prime :
    ∀ (k F K : Type) [Field k] [CharZero k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] [FiniteDimensional F K] (d : ℕ) (u : Fin d → F), AlgebraicIndependent k u → ∀ (A : Subalgebra k F) [IsFractionRing A F], A = Algebra.adjoin k (Set.range u) → ∀ (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → ∀ (p : Ideal A), p.IsPrime → p.height = 1 → ∀ t : A, Irreducible t → p = Ideal.span {t} → (∀ Q : Ideal B, Q.IsPrime → (∀ a : A, ∀ b : B, (b : K) = algebraMap F K a → (b ∈ Q ↔ a ∈ p)) → Q.height = 1) → (∀ Q : Ideal B, Q.IsPrime → (∀ a : A, ∀ b : B, (b : K) = algebraMap F K a → (b ∈ Q ↔ a ∈ p)) → ∃ (s : B) (e : ℕ), 1 ≤ e ∧ s ∈ Q ∧ (∀ y ∈ Q, ∃ c r : B, r ∉ Q ∧ r * y = c * s) ∧ (∃ a r : B, a ∉ Q ∧ r ∉ Q ∧ (r : K) * algebraMap F K t = a * s ^ e)) → ∀ z : K, (∀ b : B, ∃ r c : A, r ∉ p ∧ (r : F) * Algebra.trace F K (z * b) = c) ↔ ∀ Q : Ideal B, Q.IsPrime → (∀ a : A, ∀ b : B, (b : K) = algebraMap F K a → (b ∈ Q ↔ a ∈ p)) → ∀ (s : B) (e : ℕ), 1 ≤ e → s ∈ Q → (∀ y ∈ Q, ∃ c r : B, r ∉ Q ∧ r * y = c * s) → (∃ a r : B, a ∉ Q ∧ r ∉ Q ∧ (r : K) * algebraMap F K t = a * s ^ e) → ∃ c r : B, r ∉ Q ∧ (r : K) * s ^ (e - 1) * z = c := by
  intro k F K _ _ _ _ _ _ _ _ _ d u hu A _ hA B hB p hp hp1 t _ hpt _ hdata z
  haveI : IsNoetherianRing A := by
    subst hA
    exact isNoetherianRing_of_ringEquiv _ hu.aevalEquiv.toRingEquiv
  haveI : IsIntegrallyClosed A := by
    subst hA
    exact IsIntegrallyClosed.of_equiv hu.aevalEquiv.toRingEquiv
  haveI : CharZero F := charZero_of_injective_ringHom (algebraMap k F).injective
  have hchar : ∀ n : ℕ, n ≠ 0 → IsUnit (n : A) := fun n hn => by
    simpa using (IsUnit.mk0 (n : k) (Nat.cast_ne_zero.2 hn)).map (algebraMap k A)
  subst hB
  have hover : ∀ Q : Ideal (integralClosure A K), Q.under A = p ↔
      ∀ a : A, ∀ b : integralClosure A K, (b : K) = algebraMap F K a → (b ∈ Q ↔ a ∈ p) := by
    intro Q
    constructor
    · rintro rfl a b hb
      have : b = algebraMap A _ a := Subtype.ext hb
      rw [this]; rfl
    · intro h
      ext a
      exact h a (algebraMap A _ a) rfl
  have hrel : ∀ (s a r : integralClosure A K) (e : ℕ), r * algebraMap A _ t = a * s ^ e ↔
      (r : K) * algebraMap F K t = a * s ^ e := fun s a r e => Subtype.ext_iff
  have key := trace_mem_localization_iff A F K hchar p hp1 t hpt (by
    simp only [hover, hrel]; exact hdata) z
  simp only [hover, hrel, ← mul_assoc] at key
  exact key

end GlobalTheory.CodimDual
