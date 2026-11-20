import Mathlib
import Formalism.PeriodIntegrals.DetIdPG
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DeterminantIdentity.StNormOne

open NumberField nonZeroDivisors

namespace PI.DIP.NormOne

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
The claim follows from `(RingOfIntegers.isIntegral_coe y).map c.toIntAlgHom`.
-/
theorem map_integral (c : E →+* E) (y : 𝓞 E) : IsIntegral ℤ (c (y : E)) :=
  (RingOfIntegers.isIntegral_coe y).map c.toIntAlgHom

noncomputable def σ (c : E →+* E) (y : 𝓞 E) : 𝓞 E := ⟨c (y : E), map_integral c y⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_σ (c : E →+* E) (y : 𝓞 E) : ((σ c y : 𝓞 E) : E) = c (y : E) := rfl

/- English proof (translation)
Introduce `w hw`. Use `Submodule.mul_induction_on (C := fun w => c w ∈ Q * Q') hw ?_ ?_` and prove the remaining obligations. Introduce `p hp q hq`. Rewrite using `[map_mul]`. Conclude with `Submodule.mul_mem_mul (h p hp) (h' q hq)`.

Introduce `u v hu hv`. Rewrite using `[map_add]`. Conclude with `add_mem hu hv`.
-/
theorem map_mem_mul (c : E →+* E) {P P' Q Q' : Submodule (𝓞 E) E}
    (h : ∀ p ∈ P, c p ∈ Q) (h' : ∀ p ∈ P', c p ∈ Q') : ∀ w ∈ P * P', c w ∈ Q * Q' := by
  intro w hw
  refine Submodule.mul_induction_on (C := fun w => c w ∈ Q * Q') hw ?_ ?_
  · intro p hp q hq
    rw [map_mul]
    exact Submodule.mul_mem_mul (h p hp) (h' q hq)
  · intro u v hu hv
    rw [map_add]
    exact add_mem hu hv

/- English proof (translation)
Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Conclude with `map_mem_mul c (fun p hp => (hB p).1 hp) (fun p hp => (hB' p).1 hp) x hx`. Introduce `hx`.

Use `map_mem_mul c (fun p hp => (hB (c p)).2 (by rwa [hc])) (fun p hp => (hB' (c p)).2 (by rwa [hc])) (c x) hx` as an intermediate fact. Rewrite `this` using `[hc]`. Then use the resulting hypothesis.
-/
theorem conj_mul (c : E →+* E) (hc : ∀ x, c (c x) = x) {A A' B B' : Submodule (𝓞 E) E}
    (hB : ∀ x, x ∈ B ↔ c x ∈ A) (hB' : ∀ x, x ∈ B' ↔ c x ∈ A') :
    ∀ x, x ∈ B * B' ↔ c x ∈ A * A' := by
  intro x
  constructor
  · intro hx
    exact map_mem_mul c (fun p hp => (hB p).1 hp) (fun p hp => (hB' p).1 hp) x hx
  · intro hx
    have := map_mem_mul c (fun p hp => (hB (c p)).2 (by rwa [hc]))
      (fun p hp => (hB' (c p)).2 (by rwa [hc])) (c x) hx
    rwa [hc] at this

/- English proof (translation)
Introduce `x hx`. Take `⟨y, rfl⟩` from `Submodule.mem_one.1 hx`. Conclude with `Submodule.mem_one.2 ⟨σ c y, rfl⟩`.
-/
theorem map_mem_one (c : E →+* E) : ∀ x ∈ (1 : Submodule (𝓞 E) E), c x ∈ (1 : Submodule (𝓞 E) E) := by
  intro x hx
  obtain ⟨y, rfl⟩ := Submodule.mem_one.1 hx
  exact Submodule.mem_one.2 ⟨σ c y, rfl⟩

/- English proof (translation)
Introduce `x`. Use `⟨map_mem_one c x, fun hx => ?_⟩` and prove the remaining obligations. Use `map_mem_one c (c x) hx` as an intermediate fact. Rewrite `this` using `[hc]`. Then use the resulting hypothesis.
-/
theorem conj_one (c : E →+* E) (hc : ∀ x, c (c x) = x) :
    ∀ x, x ∈ (1 : Submodule (𝓞 E) E) ↔ c x ∈ (1 : Submodule (𝓞 E) E) := by
  intro x
  refine ⟨map_mem_one c x, fun hx => ?_⟩
  have := map_mem_one c (c x) hx
  rwa [hc] at this

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simpa only [pow_zero] using conj_one c hc`. Consider the case `succ n ih`. Simplify using `only [pow_succ]`.

Conclude with `conj_mul c hc ih hB`.
-/
theorem conj_pow (c : E →+* E) (hc : ∀ x, c (c x) = x) {A B : Submodule (𝓞 E) E}
    (hB : ∀ x, x ∈ B ↔ c x ∈ A) : ∀ n : ℕ, ∀ x, x ∈ B ^ n ↔ c x ∈ A ^ n := by
  intro n
  induction n with
  | zero => simpa only [pow_zero] using conj_one c hc
  | succ n ih =>
    simp only [pow_succ]
    exact conj_mul c hc ih hB

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[hB, Submodule.mem_span_singleton, Submodule.mem_span_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨r, hr⟩`. Use `⟨σ c r, ?_⟩` and prove the remaining obligations.

Rewrite `hr`, the goal using `[Algebra.smul_def]`. Use `congrArg c hr` as an intermediate fact. Rewrite `this` using `[hc, map_mul]`. Rewrite using `[← this]`. Both sides reduce to the same expression.

Introduce and unpack `⟨r, rfl⟩`. Use `⟨σ c r, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, Algebra.smul_def, map_mul, hc]`. Both sides reduce to the same expression.
-/
theorem conj_span (c : E →+* E) (hc : ∀ x, c (c x) = x) {B : Submodule (𝓞 E) E} (a : E)
    (hB : ∀ x, x ∈ B ↔ c x ∈ Submodule.span (𝓞 E) {a}) :
    B = Submodule.span (𝓞 E) {c a} := by
  ext x
  rw [hB, Submodule.mem_span_singleton, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨σ c r, ?_⟩
    rw [Algebra.smul_def] at hr ⊢
    have := congrArg c hr
    rw [hc, map_mul] at this
    rw [← this]
    rfl
  · rintro ⟨r, rfl⟩
    refine ⟨σ c r, ?_⟩
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, hc]
    rfl

/- English proof (translation)
Establish `hba : 𝔟 * 𝔞 = 1` using `by rw [mul_comm]; exact hab`. Establish `hfa : IsFractional (𝓞 E)⁰ 𝔞` using `FractionalIdeal.isFractional_of_fg (Submodule.fg_of_isUnit ⟨Units.mkOfMulEqOne 𝔞 𝔟 hab, rfl⟩)`. Establish `hfb : IsFractional (𝓞 E)⁰ 𝔟` using `FractionalIdeal.isFractional_of_fg (Submodule.fg_of_isUnit ⟨Units.mkOfMulEqOne 𝔟 𝔞 hba, rfl⟩)`. Set `A : FractionalIdeal (𝓞 E)⁰ E` to `⟨𝔞, hfa⟩`. Set `B : FractionalIdeal (𝓞 E)⁰ E` to `⟨𝔟, hfb⟩`.

Establish `hAB : A * B = 1`. Apply `FractionalIdeal.coeToSubmodule_injective` to reduce the goal to its premises. Use `show ((A * B : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) = ((1 : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E)`. Rewrite using `[FractionalIdeal.coe_mul, FractionalIdeal.coe_one]`. Conclude with `hab`.

Set `u : (FractionalIdeal (𝓞 E)⁰ E)ˣ` to `Units.mkOfMulEqOne A B hAB`. Set `g` to `ClassGroup.mk E u`. Establish `h1 : ClassGroup.mk E (u ^ orderOf g) = 1`. Rewrite using `[map_pow]`. Conclude with `pow_orderOf_eq_one g`.

Establish `hP` using `(ClassGroup.mk_eq_one_iff).1 h1`. Take `⟨⟨a, ha⟩⟩` from `hP`. Use `⟨orderOf g, a, orderOf_pos g, ?_⟩` and prove the remaining obligations. Rewrite using `[← ha, Units.val_pow_eq_pow_val, FractionalIdeal.coe_pow]`. Both sides reduce to the same expression.
-/
theorem pow_principal {𝔞 𝔟 : Submodule (𝓞 E) E} (hab : 𝔞 * 𝔟 = 1) :
    ∃ (h : ℕ) (a : E), 0 < h ∧ 𝔞 ^ h = Submodule.span (𝓞 E) {a} := by
  have hba : 𝔟 * 𝔞 = 1 := by rw [mul_comm]; exact hab
  have hfa : IsFractional (𝓞 E)⁰ 𝔞 :=
    FractionalIdeal.isFractional_of_fg (Submodule.fg_of_isUnit ⟨Units.mkOfMulEqOne 𝔞 𝔟 hab, rfl⟩)
  have hfb : IsFractional (𝓞 E)⁰ 𝔟 :=
    FractionalIdeal.isFractional_of_fg (Submodule.fg_of_isUnit ⟨Units.mkOfMulEqOne 𝔟 𝔞 hba, rfl⟩)
  let A : FractionalIdeal (𝓞 E)⁰ E := ⟨𝔞, hfa⟩
  let B : FractionalIdeal (𝓞 E)⁰ E := ⟨𝔟, hfb⟩
  have hAB : A * B = 1 := by
    apply FractionalIdeal.coeToSubmodule_injective
    show ((A * B : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) =
      ((1 : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E)
    rw [FractionalIdeal.coe_mul, FractionalIdeal.coe_one]
    exact hab
  let u : (FractionalIdeal (𝓞 E)⁰ E)ˣ := Units.mkOfMulEqOne A B hAB
  let g := ClassGroup.mk E u
  have h1 : ClassGroup.mk E (u ^ orderOf g) = 1 := by
    rw [map_pow]
    exact pow_orderOf_eq_one g
  have hP := (ClassGroup.mk_eq_one_iff).1 h1
  obtain ⟨⟨a, ha⟩⟩ := hP
  refine ⟨orderOf g, a, orderOf_pos g, ?_⟩
  rw [← ha, Units.val_pow_eq_pow_val, FractionalIdeal.coe_pow]
  rfl

/- English proof (translation)
Introduce `E _ _ c hc 𝔞 𝔟 hb hab`. Take `⟨h, a, hpos, ha⟩` from `pow_principal hab`. Establish `hbh : 𝔟 ^ h = Submodule.span (𝓞 E) {c a}`. Apply `conj_span c hc a` to reduce the goal to its premises. Introduce `x`.

Rewrite using `[← ha]`. Conclude with `conj_pow c hc hb h x`. Establish `hprod : Submodule.span (𝓞 E) {a} * Submodule.span (𝓞 E) {c a} = 1`. Rewrite using `[← ha, ← hbh, ← mul_pow, hab, one_pow]`. Establish `hone : (1 : E) ∈ (1 : Submodule (𝓞 E) E)` using `Submodule.mem_one.2 ⟨1, map_one _⟩`.

Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`. Rewrite `hprod` using `[Submodule.span_singleton_eq_bot.2 rfl, Submodule.bot_mul]`. Rewrite `hone` using `[← hprod, Submodule.mem_bot]`. Conclude with `one_ne_zero hone`.

Establish `hca0 : c a ≠ 0` using `(map_ne_zero c).2 ha0`. Establish `h1 : Submodule.span (𝓞 E) {c a} * Submodule.span (𝓞 E) {(c a)⁻¹} = 1`. Rewrite using `[Submodule.span_mul_span, Set.singleton_mul_singleton, mul_inv_cancel₀ hca0, ← Submodule.one_eq_span]`. Establish `hinv : Submodule.span (𝓞 E) {(c a)⁻¹} = Submodule.span (𝓞 E) {a}`. Combine the equalities or inequalities in the displayed calculation.

Use `⟨2 * h, a * (c a)⁻¹, by omega, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_inv₀, hc]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[two_mul, pow_add, ha]`. Rewrite using `[← Set.singleton_mul_singleton, ← Submodule.span_mul_span, hinv]`.
-/
theorem main : PI.DIP.StNormOne := by
  intro E _ _ c hc 𝔞 𝔟 hb hab
  obtain ⟨h, a, hpos, ha⟩ := pow_principal hab
  have hbh : 𝔟 ^ h = Submodule.span (𝓞 E) {c a} := by
    apply conj_span c hc a
    intro x
    rw [← ha]
    exact conj_pow c hc hb h x
  have hprod : Submodule.span (𝓞 E) {a} * Submodule.span (𝓞 E) {c a} = 1 := by
    rw [← ha, ← hbh, ← mul_pow, hab, one_pow]
  have hone : (1 : E) ∈ (1 : Submodule (𝓞 E) E) := Submodule.mem_one.2 ⟨1, map_one _⟩
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [Submodule.span_singleton_eq_bot.2 rfl, Submodule.bot_mul] at hprod
    rw [← hprod, Submodule.mem_bot] at hone
    exact one_ne_zero hone
  have hca0 : c a ≠ 0 := (map_ne_zero c).2 ha0
  have h1 : Submodule.span (𝓞 E) {c a} * Submodule.span (𝓞 E) {(c a)⁻¹} = 1 := by
    rw [Submodule.span_mul_span, Set.singleton_mul_singleton, mul_inv_cancel₀ hca0,
      ← Submodule.one_eq_span]
  have hinv : Submodule.span (𝓞 E) {(c a)⁻¹} = Submodule.span (𝓞 E) {a} := by
    calc Submodule.span (𝓞 E) {(c a)⁻¹}
        = (Submodule.span (𝓞 E) {a} * Submodule.span (𝓞 E) {c a}) *
            Submodule.span (𝓞 E) {(c a)⁻¹} := by rw [hprod, one_mul]
      _ = Submodule.span (𝓞 E) {a} *
            (Submodule.span (𝓞 E) {c a} * Submodule.span (𝓞 E) {(c a)⁻¹}) := mul_assoc _ _ _
      _ = Submodule.span (𝓞 E) {a} := by rw [h1, mul_one]
  refine ⟨2 * h, a * (c a)⁻¹, by omega, ?_, ?_⟩
  · rw [map_mul, map_inv₀, hc]
    field_simp
  · rw [two_mul, pow_add, ha]
    rw [← Set.singleton_mul_singleton, ← Submodule.span_mul_span, hinv]

end PI.DIP.NormOne
