import Formalism.PeriodIntegrals.NormOnePow

open NumberField nonZeroDivisors

namespace NormOnePowProof

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem map_integral (c : E →+* E) (y : 𝓞 E) : IsIntegral ℤ (c (y : E)) :=
  (RingOfIntegers.isIntegral_coe y).map c.toIntAlgHom

noncomputable def σ (c : E →+* E) (y : 𝓞 E) : 𝓞 E := ⟨c (y : E), map_integral c y⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_σ (c : E →+* E) (y : 𝓞 E) : ((σ c y : 𝓞 E) : E) = c (y : E) := rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem map_mem_one (c : E →+* E) : ∀ x ∈ (1 : Submodule (𝓞 E) E), c x ∈ (1 : Submodule (𝓞 E) E) := by
  intro x hx
  obtain ⟨y, rfl⟩ := Submodule.mem_one.1 hx
  exact Submodule.mem_one.2 ⟨σ c y, rfl⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem conj_one (c : E →+* E) (hc : ∀ x, c (c x) = x) :
    ∀ x, x ∈ (1 : Submodule (𝓞 E) E) ↔ c x ∈ (1 : Submodule (𝓞 E) E) := by
  intro x
  refine ⟨map_mem_one c x, fun hx => ?_⟩
  have := map_mem_one c (c x) hx
  rwa [hc] at this

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
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
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations.

Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
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
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Introduce a local definition for the expression. Introduce a local definition for the expression.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Introduce a local definition for the expression.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Assume the hypotheses and unpack their components. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Clear the denominators using the available nonvanishing facts. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem main : PI.NormOnePow := by
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

end NormOnePowProof
