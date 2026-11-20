import Mathlib
open scoped NNReal

namespace GlobalTheory.ValCompletion

section General
variable {R : Type} [CommRing R] {I : Ideal R} {a : R}

/- English proof (translation)
Establish `hfg : I.FG` using `⟨{a}, by simp [h]⟩`. Establish `e : (I ^ n).map (algebraMap R (AdicCompletion I R)) = Ideal.span {algebraMap R (AdicCompletion I R) a ^ n}`. Establish `: I ^ n = Ideal.span {a ^ n}` using `by rw [h, Ideal.span_singleton_pow]`. Rewrite using `[this, Ideal.map_span, Set.image_singleton, map_pow]`. Rewrite using `[← Ideal.mem_span_singleton, ← e, ← Submodule.restrictScalars_mem R, ← Ideal.smul_top_eq_map, AdicCompletion.pow_smul_top_eq_ker_eval hfg, LinearMap.mem_ker]`.

Establish `h' : (I ^ n • ⊤ : Ideal R) = I ^ n` using `by ext x; simp`. Conclude with `map_eq_zero_iff _ (Ideal.quotientEquivAlgOfEq R h').injective`.
-/
theorem evalₐ_eq_zero_iff (h : I = Ideal.span {a}) (n : ℕ) (y : AdicCompletion I R) :
    AdicCompletion.evalₐ I n y = 0 ↔ algebraMap R (AdicCompletion I R) a ^ n ∣ y := by
  have hfg : I.FG := ⟨{a}, by simp [h]⟩
  have e : (I ^ n).map (algebraMap R (AdicCompletion I R)) =
      Ideal.span {algebraMap R (AdicCompletion I R) a ^ n} := by
    have : I ^ n = Ideal.span {a ^ n} := by rw [h, Ideal.span_singleton_pow]
    rw [this, Ideal.map_span, Set.image_singleton, map_pow]
  rw [← Ideal.mem_span_singleton, ← e, ← Submodule.restrictScalars_mem R,
    ← Ideal.smul_top_eq_map, AdicCompletion.pow_smul_top_eq_ker_eval hfg, LinearMap.mem_ker]
  have h' : (I ^ n • ⊤ : Ideal R) = I ^ n := by ext x; simp
  exact map_eq_zero_iff _ (Ideal.quotientEquivAlgOfEq R h').injective

/- English proof (translation)
Rewrite using `[AlgHom.commutes]`. Both sides reduce to the same expression.
-/
theorem evalₐ_algebraMap (n : ℕ) (r : R) :
    AdicCompletion.evalₐ I n (algebraMap R (AdicCompletion I R) r) = Ideal.Quotient.mk _ r := by
  rw [AlgHom.commutes]; rfl

/- English proof (translation)
Proceed by induction on `y using AdicCompletion.induction_on with`. Consider the case `_ x`. Simplify using `only [AdicCompletion.evalₐ_mk]`. Rewrite using `[← AdicCompletion.Ideal.mk_eq_mk I h x]`. Both sides reduce to the same expression.
-/
theorem factorPow_evalₐ {m n : ℕ} (h : m ≤ n) (y : AdicCompletion I R) :
    Ideal.Quotient.factorPow I h (AdicCompletion.evalₐ I n y) = AdicCompletion.evalₐ I m y := by
  induction y using AdicCompletion.induction_on with
  | _ x =>
    simp only [AdicCompletion.evalₐ_mk]
    rw [← AdicCompletion.Ideal.mk_eq_mk I h x]
    rfl

/- English proof (translation)
Establish `key : IsUnit (AdicCompletion.evalₐ I (n + 1) y)`. Take `⟨a, ha⟩` from `Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (n + 1) y)`. Rewrite `hy` using `[← factorPow_evalₐ (show 1 ≤ n + 1 by omega), ← ha]`. Take `⟨b, hb⟩` from `hy.exists_right_inv`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective b`.

Establish `h1 : a * b - 1 ∈ I ^ 1`. Rewrite using `[← Ideal.Quotient.eq]`. Conclude with `hb`. Rewrite `h1` using `[pow_one]`. Establish `hn : IsNilpotent (Ideal.Quotient.mk (I ^ (n + 1)) (a * b - 1))` using `⟨n + 1, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.pow_mem_pow h1 _⟩`.

Establish `hu` using `hn.isUnit_add_one`. Rewrite `hu` using `[map_sub, map_one, sub_add_cancel, map_mul]`. Rewrite using `[← ha]`. Conclude with `isUnit_of_mul_isUnit_left hu`. Rewrite using `[← factorPow_evalₐ (Nat.le_succ n)]`.

Conclude with `key.map _`.
-/
theorem isUnit_evalₐ (y : AdicCompletion I R) (hy : IsUnit (AdicCompletion.evalₐ I 1 y)) (n : ℕ) :
    IsUnit (AdicCompletion.evalₐ I n y) := by
  have key : IsUnit (AdicCompletion.evalₐ I (n + 1) y) := by
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (n + 1) y)
    rw [← factorPow_evalₐ (show 1 ≤ n + 1 by omega), ← ha] at hy
    obtain ⟨b, hb⟩ := hy.exists_right_inv
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    have h1 : a * b - 1 ∈ I ^ 1 := by
      rw [← Ideal.Quotient.eq]
      exact hb
    rw [pow_one] at h1
    have hn : IsNilpotent (Ideal.Quotient.mk (I ^ (n + 1)) (a * b - 1)) :=
      ⟨n + 1, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.pow_mem_pow h1 _⟩
    have hu := hn.isUnit_add_one
    rw [map_sub, map_one, sub_add_cancel, map_mul] at hu
    rw [← ha]
    exact isUnit_of_mul_isUnit_left hu
  rw [← factorPow_evalₐ (Nat.le_succ n)]
  exact key.map _

/- English proof (translation)
Set `f : (n : ℕ) → Localization.Away y →+* R ⧸ I ^ n` to `fun n => IsLocalization.Away.lift (g := (AdicCompletion.evalₐ I n).toRingHom) y (isUnit_evalₐ y hy n)`. Establish `hf0 : ∀ n x, f n (algebraMap _ _ x) = AdicCompletion.evalₐ I n x` using `fun n x => IsLocalization.Away.lift_eq y _ x`. Establish `hf : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow I hle).comp (f n) = f m`. Introduce `m n hle`. Use `IsLocalization.ringHom_ext (Submonoid.powers y) (RingHom.ext fun x => ?_)` and prove the remaining obligations.

Simplify using `only [RingHom.comp_apply, hf0, factorPow_evalₐ]`. Establish `e : AdicCompletion.liftRingHom I f hf (algebraMap _ _ y) = y` using `AdicCompletion.ext_evalₐ fun n => by rw [AdicCompletion.evalₐ_liftRingHom, hf0]`. Rewrite using `[← e]`. Conclude with `(IsLocalization.Away.algebraMap_isUnit y).map _`.
-/
theorem isUnit_of_evalₐ (y : AdicCompletion I R) (hy : IsUnit (AdicCompletion.evalₐ I 1 y)) :
    IsUnit y := by
  let f : (n : ℕ) → Localization.Away y →+* R ⧸ I ^ n := fun n =>
    IsLocalization.Away.lift (g := (AdicCompletion.evalₐ I n).toRingHom) y (isUnit_evalₐ y hy n)
  have hf0 : ∀ n x, f n (algebraMap _ _ x) = AdicCompletion.evalₐ I n x := fun n x =>
    IsLocalization.Away.lift_eq y _ x
  have hf : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow I hle).comp (f n) = f m := by
    intro m n hle
    refine IsLocalization.ringHom_ext (Submonoid.powers y) (RingHom.ext fun x => ?_)
    simp only [RingHom.comp_apply, hf0, factorPow_evalₐ]
  have e : AdicCompletion.liftRingHom I f hf (algebraMap _ _ y) = y :=
    AdicCompletion.ext_evalₐ fun n => by rw [AdicCompletion.evalₐ_liftRingHom, hf0]
  rw [← e]
  exact (IsLocalization.Away.algebraMap_isUnit y).map _

end General

section Val
variable {V : Type} [CommRing V] [IsDomain V] [ValuationRing V] {x : V}

/- English proof (translation)
Introduce and unpack `⟨c, hc⟩`. Apply `hxu` to reduce the goal to its premises. Establish `h : x ^ m * 1 = x ^ m * (x * c)` using `by rw [mul_one]; nth_rewrite 1 [hc]; ring`. Conclude with `IsUnit.of_mul_eq_one c (mul_left_cancel₀ (pow_ne_zero m hx0) h).symm`.
-/
theorem not_pow_succ_dvd_pow (hx0 : x ≠ 0) (hxu : ¬ IsUnit x) (m : ℕ) : ¬ x ^ (m + 1) ∣ x ^ m := by
  rintro ⟨c, hc⟩
  apply hxu
  have h : x ^ m * 1 = x ^ m * (x * c) := by rw [mul_one]; nth_rewrite 1 [hc]; ring
  exact IsUnit.of_mul_eq_one c (mul_left_cancel₀ (pow_ne_zero m hx0) h).symm

/- English proof (translation)
Introduce `h`. Establish `h2` using `congrArg (AdicCompletion.evalₐ (Ideal.span {x}) (m + 1)) h`. Rewrite `h2` using `[← map_pow, evalₐ_algebraMap, map_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Conclude with `not_pow_succ_dvd_pow hx0 hxu m h2`.
-/
theorem algebraMap_pow_ne_zero (hx0 : x ≠ 0) (hxu : ¬ IsUnit x) (m : ℕ) : (algebraMap V (AdicCompletion (Ideal.span {x}) V) x) ^ m ≠ 0 := by
  intro h
  have h2 := congrArg (AdicCompletion.evalₐ (Ideal.span {x}) (m + 1)) h
  rw [← map_pow, evalₐ_algebraMap, map_zero, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h2
  exact not_pow_succ_dvd_pow hx0 hxu m h2

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨n, hn⟩ : ∃ n, AdicCompletion.evalₐ (Ideal.span {x}) n y ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `hy (AdicCompletion.ext_evalₐ fun n => by rw [hc n, map_zero])`. Take `⟨a, ha⟩` from `Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (Ideal.span {x}) (n + 1) y)`.

Establish `hna : ¬ x ^ n ∣ a`. Introduce `hd`. Apply `hn` to reduce the goal to its premises. Rewrite using `[← factorPow_evalₐ (Nat.le_succ n), ← ha, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Conclude with `hd`.

Choose the witnesses or unpack the hypotheses as in `⟨b, hb⟩ : a ∣ x ^ n := by`. Take `⟨c, hc | hc⟩` from `PreValuationRing.cond a (x ^ n)`. Conclude with `⟨c, hc.symm⟩`. Conclude with `absurd ⟨c, hc.symm⟩ hna`. Choose the witnesses or unpack the hypotheses as in `⟨z, hz⟩ : algebraMap V (AdicCompletion (Ideal.span {x}) V) x ^ (n + 1) ∣ y - algebraMap V (AdicCompletion (Ideal.span {x}) V) a := by`.

Rewrite using `[← evalₐ_eq_zero_iff rfl, map_sub, evalₐ_algebraMap, ← ha, sub_self]`. Establish `hunit : IsUnit (1 + algebraMap V (AdicCompletion (Ideal.span {x}) V) b * algebraMap V (AdicCompletion (Ideal.span {x}) V) x * z)`. Apply `isUnit_of_evalₐ` to reduce the goal to its premises. Establish `hx1 : Ideal.Quotient.mk (Ideal.span {x} ^ 1) x = 0`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem, pow_one]`.

Conclude with `Ideal.mem_span_singleton_self x`. Rewrite using `[map_add, map_one, map_mul, map_mul, evalₐ_algebraMap, evalₐ_algebraMap, hx1, mul_zero, zero_mul, add_zero]`. Conclude with `isUnit_one`. Use `⟨a, n, ⟨b, hb⟩, hunit.unit, ?_⟩` and prove the remaining obligations. Rewrite using `[IsUnit.unit_spec, mul_add, mul_one]`.

Establish `: y = algebraMap V (AdicCompletion (Ideal.span {x}) V) a + algebraMap V (AdicCompletion (Ideal.span {x}) V) x ^ (n + 1) * z` using `by rw [← hz]; ring`. Rewrite using `[this, pow_succ, ← map_pow, hb, map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_eq_mul_unit (hx0 : x ≠ 0) (hxu : ¬ IsUnit x) (y : AdicCompletion (Ideal.span {x}) V) (hy : y ≠ 0) :
    ∃ (a : V) (n : ℕ), a ∣ x ^ n ∧ ∃ u : (AdicCompletion (Ideal.span {x}) V)ˣ, y = algebraMap V (AdicCompletion (Ideal.span {x}) V) a * u := by
  obtain ⟨n, hn⟩ : ∃ n, AdicCompletion.evalₐ (Ideal.span {x}) n y ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hy (AdicCompletion.ext_evalₐ fun n => by rw [hc n, map_zero])
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (Ideal.span {x}) (n + 1) y)
  have hna : ¬ x ^ n ∣ a := by
    intro hd
    apply hn
    rw [← factorPow_evalₐ (Nat.le_succ n), ← ha, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact hd
  obtain ⟨b, hb⟩ : a ∣ x ^ n := by
    obtain ⟨c, hc | hc⟩ := PreValuationRing.cond a (x ^ n)
    · exact ⟨c, hc.symm⟩
    · exact absurd ⟨c, hc.symm⟩ hna
  obtain ⟨z, hz⟩ : algebraMap V (AdicCompletion (Ideal.span {x}) V) x ^ (n + 1) ∣ y - algebraMap V (AdicCompletion (Ideal.span {x}) V) a := by
    rw [← evalₐ_eq_zero_iff rfl, map_sub, evalₐ_algebraMap, ← ha, sub_self]
  have hunit : IsUnit (1 + algebraMap V (AdicCompletion (Ideal.span {x}) V) b * algebraMap V (AdicCompletion (Ideal.span {x}) V) x * z) := by
    apply isUnit_of_evalₐ
    have hx1 : Ideal.Quotient.mk (Ideal.span {x} ^ 1) x = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem, pow_one]; exact Ideal.mem_span_singleton_self x
    rw [map_add, map_one, map_mul, map_mul, evalₐ_algebraMap, evalₐ_algebraMap, hx1,
      mul_zero, zero_mul, add_zero]
    exact isUnit_one
  refine ⟨a, n, ⟨b, hb⟩, hunit.unit, ?_⟩
  rw [IsUnit.unit_spec, mul_add, mul_one]
  have : y = algebraMap V (AdicCompletion (Ideal.span {x}) V) a + algebraMap V (AdicCompletion (Ideal.span {x}) V) x ^ (n + 1) * z := by rw [← hz]; ring
  rw [this, pow_succ, ← map_pow, hb, map_mul]
  ring

end Val

end GlobalTheory.ValCompletion

open GlobalTheory.ValCompletion in

/- English proof (translation)
Introduce `V _ _ _ x hx0 hxu`. Establish `hne : algebraMap V (AdicCompletion (Ideal.span {x}) V) x ≠ 0`. Simplify using `using algebraMap_pow_ne_zero hx0 hxu 1`. Establish `hnt : Nontrivial (AdicCompletion (Ideal.span {x}) V)` using `⟨⟨_, _, hne⟩⟩`. Establish `hdom : IsDomain (AdicCompletion (Ideal.span {x}) V)`.

Use `@NoZeroDivisors.to_isDomain _ _ hnt ⟨fun {y z} hyz => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Take `⟨a, n, ⟨c, hc1⟩, u, rfl⟩` from `exists_eq_mul_unit hx0 hxu y hc.1`. Take `⟨b, m, ⟨d, hd1⟩, w, rfl⟩` from `exists_eq_mul_unit hx0 hxu z hc.2`.

Apply `algebraMap_pow_ne_zero hx0 hxu (n + m)` to reduce the goal to its premises. Establish `h1 : algebraMap V (AdicCompletion (Ideal.span {x}) V) a * algebraMap V (AdicCompletion (Ideal.span {x}) V) b = 0`. Establish `h2 : algebraMap V (AdicCompletion (Ideal.span {x}) V) a * algebraMap V (AdicCompletion (Ideal.span {x}) V) b * ((u : AdicCompletion (Ideal.span {x}) V) * w) = 0`. Rewrite using `[← hyz]`. Expand and normalize the polynomial expressions, which then agree.

Conclude with `(Units.mul_left_eq_zero (u * w)).1 (by rw [Units.val_mul]; exact h2)`. Rewrite using `[pow_add, ← map_pow, ← map_pow, hc1, hd1]`. Simplify using `only [map_mul]`. Combine the equalities or inequalities in the displayed calculation. Use `⟨hdom, ⟨fun y z => ?_⟩, hne, ?_, ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hy : y = 0`. Conclude with `⟨0, Or.inr (by rw [hy, mul_zero])⟩`. Distinguish the cases in `hz : z = 0`. Conclude with `⟨0, Or.inl (by rw [hz, mul_zero])⟩`. Take `⟨a, n, -, u, rfl⟩` from `exists_eq_mul_unit hx0 hxu y hy`.

Take `⟨b, m, -, w, rfl⟩` from `exists_eq_mul_unit hx0 hxu z hz`. Take `⟨c, hc | hc⟩` from `PreValuationRing.cond a b`. Use `⟨algebraMap V (AdicCompletion (Ideal.span {x}) V) c * ((u⁻¹ : (AdicCompletion (Ideal.span {x}) V)ˣ) : AdicCompletion (Ideal.span {x}) V) * w, Or.inl ?_⟩` and prove the remaining obligations. Rewrite using `[← hc, map_mul]`. Combine the equalities or inequalities in the displayed calculation.

Use `⟨algebraMap V (AdicCompletion (Ideal.span {x}) V) c * ((w⁻¹ : (AdicCompletion (Ideal.span {x}) V)ˣ) : AdicCompletion (Ideal.span {x}) V) * u, Or.inr ?_⟩` and prove the remaining obligations. Rewrite using `[← hc, map_mul]`. Combine the equalities or inequalities in the displayed calculation. Introduce and unpack `⟨v, hv⟩`. Apply `hxu` to reduce the goal to its premises.

Take `⟨e, he⟩` from `isUnit_iff_exists_inv.1 (⟨v, hv⟩ : IsUnit (algebraMap V (AdicCompletion (Ideal.span {x}) V) x))`. Establish `h2` using `congrArg (AdicCompletion.evalₐ (Ideal.span {x}) 1) he`. Establish `hx1 : Ideal.Quotient.mk (Ideal.span {x} ^ 1) x = 0`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem, pow_one]`. Conclude with `Ideal.mem_span_singleton_self x`.

Rewrite `h2` using `[map_mul, evalₐ_algebraMap, hx1, zero_mul, map_one, eq_comm, ← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem, pow_one, Ideal.mem_span_singleton]`. Conclude with `isUnit_of_dvd_one h2`. Establish `e : (Ideal.span {x}).map (algebraMap V (AdicCompletion (Ideal.span {x}) V)) = Ideal.span {algebraMap V (AdicCompletion (Ideal.span {x}) V) x}`. Rewrite using `[Ideal.map_span, Set.image_singleton]`. Rewrite using `[← e, IsAdicComplete.map_algebraMap_iff]`.

Conclude with `AdicCompletion.isAdicComplete (Submodule.fg_span_singleton x)`.
-/
theorem GlobalTheory.adicCompletion_valuationRing_props : ∀ (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] (x : V), x ≠ 0 → ¬ IsUnit x → IsDomain (AdicCompletion (Ideal.span {x}) V) ∧ PreValuationRing (AdicCompletion (Ideal.span {x}) V) ∧ algebraMap V (AdicCompletion (Ideal.span {x}) V) x ≠ 0 ∧ ¬ IsUnit (algebraMap V (AdicCompletion (Ideal.span {x}) V) x) ∧ IsAdicComplete (Ideal.span {algebraMap V (AdicCompletion (Ideal.span {x}) V) x}) (AdicCompletion (Ideal.span {x}) V) := by
  intro V _ _ _ x hx0 hxu
  have hne : algebraMap V (AdicCompletion (Ideal.span {x}) V) x ≠ 0 := by
    simpa using algebraMap_pow_ne_zero hx0 hxu 1
  have hnt : Nontrivial (AdicCompletion (Ideal.span {x}) V) := ⟨⟨_, _, hne⟩⟩
  have hdom : IsDomain (AdicCompletion (Ideal.span {x}) V) := by
    refine @NoZeroDivisors.to_isDomain _ _ hnt ⟨fun {y z} hyz => ?_⟩
    by_contra hc
    push_neg at hc
    obtain ⟨a, n, ⟨c, hc1⟩, u, rfl⟩ := exists_eq_mul_unit hx0 hxu y hc.1
    obtain ⟨b, m, ⟨d, hd1⟩, w, rfl⟩ := exists_eq_mul_unit hx0 hxu z hc.2
    apply algebraMap_pow_ne_zero hx0 hxu (n + m)
    have h1 : algebraMap V (AdicCompletion (Ideal.span {x}) V) a * algebraMap V (AdicCompletion (Ideal.span {x}) V) b = 0 := by
      have h2 : algebraMap V (AdicCompletion (Ideal.span {x}) V) a * algebraMap V (AdicCompletion (Ideal.span {x}) V) b * ((u : AdicCompletion (Ideal.span {x}) V) * w) = 0 := by
        rw [← hyz]; ring
      exact (Units.mul_left_eq_zero (u * w)).1 (by rw [Units.val_mul]; exact h2)
    rw [pow_add, ← map_pow, ← map_pow, hc1, hd1]
    simp only [map_mul]
    calc _ = (algebraMap V (AdicCompletion (Ideal.span {x}) V) a * algebraMap V (AdicCompletion (Ideal.span {x}) V) b) * (algebraMap V (AdicCompletion (Ideal.span {x}) V) c * algebraMap V (AdicCompletion (Ideal.span {x}) V) d) := by ring
      _ = 0 := by rw [h1, zero_mul]
  refine ⟨hdom, ⟨fun y z => ?_⟩, hne, ?_, ?_⟩
  · by_cases hy : y = 0
    · exact ⟨0, Or.inr (by rw [hy, mul_zero])⟩
    by_cases hz : z = 0
    · exact ⟨0, Or.inl (by rw [hz, mul_zero])⟩
    obtain ⟨a, n, -, u, rfl⟩ := exists_eq_mul_unit hx0 hxu y hy
    obtain ⟨b, m, -, w, rfl⟩ := exists_eq_mul_unit hx0 hxu z hz
    obtain ⟨c, hc | hc⟩ := PreValuationRing.cond a b
    · refine ⟨algebraMap V (AdicCompletion (Ideal.span {x}) V) c * ((u⁻¹ : (AdicCompletion (Ideal.span {x}) V)ˣ) : AdicCompletion (Ideal.span {x}) V) * w, Or.inl ?_⟩
      rw [← hc, map_mul]
      calc _ = algebraMap V (AdicCompletion (Ideal.span {x}) V) a * algebraMap V (AdicCompletion (Ideal.span {x}) V) c * w * ((u : AdicCompletion (Ideal.span {x}) V) * ((u⁻¹ : (AdicCompletion (Ideal.span {x}) V)ˣ) : AdicCompletion (Ideal.span {x}) V)) := by ring
        _ = _ := by rw [Units.mul_inv, mul_one]
    · refine ⟨algebraMap V (AdicCompletion (Ideal.span {x}) V) c * ((w⁻¹ : (AdicCompletion (Ideal.span {x}) V)ˣ) : AdicCompletion (Ideal.span {x}) V) * u, Or.inr ?_⟩
      rw [← hc, map_mul]
      calc _ = algebraMap V (AdicCompletion (Ideal.span {x}) V) b * algebraMap V (AdicCompletion (Ideal.span {x}) V) c * u * ((w : AdicCompletion (Ideal.span {x}) V) * ((w⁻¹ : (AdicCompletion (Ideal.span {x}) V)ˣ) : AdicCompletion (Ideal.span {x}) V)) := by ring
        _ = _ := by rw [Units.mul_inv, mul_one]
  · rintro ⟨v, hv⟩
    apply hxu
    obtain ⟨e, he⟩ := isUnit_iff_exists_inv.1 (⟨v, hv⟩ : IsUnit (algebraMap V (AdicCompletion (Ideal.span {x}) V) x))
    have h2 := congrArg (AdicCompletion.evalₐ (Ideal.span {x}) 1) he
    have hx1 : Ideal.Quotient.mk (Ideal.span {x} ^ 1) x = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem, pow_one]; exact Ideal.mem_span_singleton_self x
    rw [map_mul, evalₐ_algebraMap, hx1, zero_mul, map_one, eq_comm, ← map_one (Ideal.Quotient.mk _),
      Ideal.Quotient.eq_zero_iff_mem, pow_one, Ideal.mem_span_singleton] at h2
    exact isUnit_of_dvd_one h2
  · have e : (Ideal.span {x}).map (algebraMap V (AdicCompletion (Ideal.span {x}) V)) = Ideal.span {algebraMap V (AdicCompletion (Ideal.span {x}) V) x} := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [← e, IsAdicComplete.map_algebraMap_iff]
    exact AdicCompletion.isAdicComplete (Submodule.fg_span_singleton x)
