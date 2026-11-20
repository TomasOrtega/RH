import Mathlib

open NumberField

namespace GroundTheory.Global

namespace Cyclotomic

section Frobenius

variable {m : ℕ} [NeZero m] (p : ℕ) [hp : Fact p.Prime] (K : Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {m} ℚ K]

variable (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]

omit [P.IsPrime] in
include hp in

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ne_bot_of_liesOver : P ≠ ⊥ :=
  Ideal.ne_bot_of_liesOver_of_ne_bot (p := Ideal.span {(p : ℤ)})
    (by simpa using hp.out.ne_zero) P

omit [P.IsPrime] in
include hp in

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem finite_quotient : Finite (𝓞 K ⧸ P) :=
  have : NeZero P := ⟨ne_bot_of_liesOver p K P⟩
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne P)

omit hp [NumberField K] [P.IsPrime] in

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem card_quotient_under : Nat.card (ℤ ⧸ P.under ℤ) = p := by
  rw [← Ideal.LiesOver.over (P := P) (p := Ideal.span {(p : ℤ)}),
    Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]

omit [NeZero m] hp [NumberField K] [IsCyclotomicExtension {m} ℚ K] [P.IsPrime] in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem natCast_notMem_of_not_dvd (hm : ¬ p ∣ m) : ((m : ℕ) : 𝓞 K) ∉ P := by
  intro h
  have : ((m : ℤ)) ∈ P.under ℤ := by
    rw [Ideal.under, Ideal.mem_comap]; simpa using h
  rw [← Ideal.LiesOver.over (P := P) (p := Ideal.span {(p : ℤ)}), Ideal.mem_span_singleton] at this
  exact hm (Int.natCast_dvd_natCast.mp this)

/- English proof (translation)
Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem eq_of_forall_pow_eq_one {σ τ : Gal(K/ℚ)}
    (h : ∀ x : K, x ^ m = 1 → σ x = τ x) : σ = τ := by
  have hζ := IsCyclotomicExtension.zeta_spec m ℚ K
  apply (IsCyclotomicExtension.Rat.galEquivZMod m K).injective
  have h₁ := IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq m K σ hζ.pow_eq_one
  have h₂ := IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq m K τ hζ.pow_eq_one
  rw [h _ hζ.pow_eq_one, h₂] at h₁
  rw [Units.ext_iff]
  exact ZMod.val_injective _ (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h₁.symm)

omit hp [IsCyclotomicExtension {m} ℚ K] [P.IsPrime] in

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Introduce a local definition for the expression. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem IsArithFrobAt.apply_of_pow_eq_one (hm : ¬ p ∣ m) {σ : Gal(K/ℚ)}
    (hσ : IsArithFrobAt ℤ σ P) {x : K} (hx : x ^ m = 1) : σ x = x ^ p := by
  have hxi : IsIntegral ℤ x := by
    refine ⟨Polynomial.X ^ m - 1, Polynomial.monic_X_pow_sub_C 1 (NeZero.ne m), ?_⟩
    simp [hx]
  let y : 𝓞 K := ⟨x, hxi⟩
  have hy : y ^ m = 1 := by
    apply RingOfIntegers.ext
    exact hx
  have h := AlgHom.IsArithFrobAt.apply_of_pow_eq_one hσ hy
    (natCast_notMem_of_not_dvd p K P hm)
  rw [card_quotient_under p K P] at h
  exact congrArg (fun z : 𝓞 K => (z : K)) h

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Use the resulting assumption.
-/
theorem isArithFrobAt_iff (hm : ¬ p ∣ m) (σ : Gal(K/ℚ)) :
    IsArithFrobAt ℤ σ P ↔ ∀ x : K, x ^ m = 1 → σ x = x ^ p := by
  refine ⟨fun hσ x hx => IsArithFrobAt.apply_of_pow_eq_one p K P hm hσ hx, fun h => ?_⟩
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {m} ℚ K
  have : Finite (𝓞 K ⧸ P) := finite_quotient p K P
  obtain ⟨τ, hτ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ Gal(K/ℚ) P
  have : σ = τ := eq_of_forall_pow_eq_one (m := m) K fun x hx => by
    rw [h x hx, IsArithFrobAt.apply_of_pow_eq_one p K P hm hτ hx]
  rwa [this]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem existsUnique_isArithFrobAt (hm : ¬ p ∣ m) : ∃! σ : Gal(K/ℚ), IsArithFrobAt ℤ σ P := by
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {m} ℚ K
  have : Finite (𝓞 K ⧸ P) := finite_quotient p K P
  obtain ⟨τ, hτ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ Gal(K/ℚ) P
  refine ⟨τ, hτ, fun σ hσ => eq_of_forall_pow_eq_one (m := m) K fun x hx => ?_⟩
  rw [IsArithFrobAt.apply_of_pow_eq_one p K P hm hσ hx,
    IsArithFrobAt.apply_of_pow_eq_one p K P hm hτ hx]

end Frobenius

end Cyclotomic

end GroundTheory.Global
