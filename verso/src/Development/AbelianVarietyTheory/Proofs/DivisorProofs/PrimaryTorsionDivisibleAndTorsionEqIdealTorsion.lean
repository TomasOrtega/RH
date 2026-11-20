import Mathlib
open NumberField

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact.

Assume the hypotheses and unpack their components. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Split into cases according to the possible forms of the given data. Treat this case separately.

Treat this case separately. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

A detailed English derivation is pending.
-/
theorem primaryTorsion_divisible_and_gTorsion :
    ∀ (E : Type) [Field E] [NumberField E] (M : Type) [AddCommGroup M] [Module (𝓞 E) M] (g : ℕ) (I : Ideal (𝓞 E)), g.Prime → Ideal.absNorm I = g → (g : 𝓞 E) ∉ I ^ 2 → (∀ x : M, ∃ y : M, g • y = x) → (∀ (j : ℕ) (x : M), (∀ a ∈ I ^ j, a • x = 0) → ∃ y : M, g • y = x ∧ ∀ a ∈ I ^ (j + 1), a • y = 0) ∧ (∀ (j : ℕ) (x : M), (∀ a ∈ I ^ j, a • x = 0) → g • x = 0 → ∀ a ∈ I, a • x = 0) := by
  intro E _ _ M _ _ g I hg hN hg2 hdiv
  have hgI : (g : 𝓞 E) ∈ I := by
    have := Ideal.absNorm_mem I
    rwa [hN] at this
  have hIne : I ≠ ⊥ := by
    rintro rfl
    rw [Ideal.absNorm_bot] at hN
    exact hg.ne_zero hN.symm
  have hprime : I.IsPrime := Ideal.isPrime_of_irreducible_absNorm (by rw [hN]; exact hg)
  have hmax : I.IsMaximal := hprime.isMaximal hIne
  obtain ⟨J, hJ⟩ := (Ideal.dvd_iff_le).2 ((Ideal.span_singleton_le_iff_mem I).2 hgI)
  have hJI : ¬ J ≤ I := by
    intro h
    apply hg2
    have h2 : Ideal.span {(g : 𝓞 E)} ≤ I ^ 2 := by
      rw [hJ, pow_two]; exact Ideal.mul_mono_right h
    exact h2 (Ideal.mem_span_singleton_self _)
  have hsup : I ⊔ J = ⊤ := by
    by_contra h
    exact hJI (le_sup_right.trans (le_of_eq (hmax.eq_of_le h le_sup_left).symm))
  have hpow : ∀ k : ℕ, I ^ k ⊔ J = ⊤ := fun k => Ideal.pow_sup_eq_top hsup
  refine ⟨fun j x hx => ?_, fun j x hx hgx a ha => ?_⟩
  · obtain ⟨y0, hy0⟩ := hdiv x
    have h1 : (1 : 𝓞 E) ∈ I ^ j ⊔ J := by rw [hpow j]; exact Submodule.mem_top
    obtain ⟨f, hf, e, he, hfe⟩ := Submodule.mem_sup.1 h1
    refine ⟨e • y0, ?_, ?_⟩
    · rw [← Nat.cast_smul_eq_nsmul (𝓞 E), smul_comm, Nat.cast_smul_eq_nsmul (𝓞 E), hy0]
      have : e = 1 - f := by rw [← hfe]; ring
      rw [this, sub_smul, one_smul, hx f hf, sub_zero]
    · intro a ha
      have hae : a * e ∈ I ^ j * Ideal.span {(g : 𝓞 E)} := by
        rw [hJ, ← mul_assoc, ← pow_succ]
        exact Ideal.mul_mem_mul ha he
      have hker : I ^ j * Ideal.span {(g : 𝓞 E)} ≤
          LinearMap.ker (LinearMap.toSpanSingleton (𝓞 E) M y0) := by
        rw [Ideal.mul_le]
        intro c hc s hs
        obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.1 hs
        rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, ← mul_assoc, mul_smul,
          Nat.cast_smul_eq_nsmul (𝓞 E), hy0]
        exact hx _ (Ideal.mul_mem_right _ _ hc)
      have := hker hae
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply] at this
      rw [smul_smul]; exact this
  · have hker : I ^ j ⊔ Ideal.span {(g : 𝓞 E)} ≤
        LinearMap.ker (LinearMap.toSpanSingleton (𝓞 E) M x) := by
      refine sup_le (fun b hb => ?_) ?_
      · rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]; exact hx b hb
      · refine (Ideal.span_singleton_le_iff_mem _).2 ?_
        rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, Nat.cast_smul_eq_nsmul]
        exact hgx
    have hIle : I ≤ I ^ j ⊔ Ideal.span {(g : 𝓞 E)} := by
      cases j with
      | zero => rw [pow_zero, Ideal.one_eq_top]; exact le_top.trans le_sup_left
      | succ k =>
        have h : I = I ^ (k + 1) ⊔ Ideal.span {(g : 𝓞 E)} := by
          calc I = I * (I ^ k ⊔ J) := by rw [hpow k, Ideal.mul_top]
            _ = I ^ (k + 1) ⊔ Ideal.span {(g : 𝓞 E)} := by rw [Ideal.mul_sup, hJ, pow_succ']
        exact h.le
    have := hker (hIle ha)
    rwa [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply] at this

end GlobalTheory
