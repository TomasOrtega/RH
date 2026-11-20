import Mathlib

/- English proof (translation)
Introduce `E _ _ _ hc p hp`. Use `haveI : Fact p.Prime := ⟨hp⟩`. Establish `hp0 : (Ideal.span {(p : ℤ)}) ≠ ⊥`. Simplify using `using hp.ne_zero`. Establish `hmax : (Ideal.span {(p : ℤ)}).IsMaximal` using `Ideal.IsPrime.isMaximal ((Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2 (Nat.prime_iff_prime_int.1 hp)) hp0`.

Take `⟨Q, hQm, hQo⟩` from `Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := NumberField.RingOfIntegers E) (Ideal.span {(p : ℤ)})`. Establish `hQbot : Q ≠ ⊥` using `Ideal.ne_bot_of_liesOver_of_ne_bot hp0 Q`. Use `haveI : Finite (NumberField.RingOfIntegers E ⧸ Q) := Ideal.finiteQuotientOfFreeOfNeBot Q hQbot`. Take `⟨φ, hφ⟩` from `IsArithFrobAt.exists_of_isInvariant ℤ Gal(E/ℚ) Q`. Use `⟨φ, ?_⟩` and prove the remaining obligations.

Introduce `O _ n hn hpn τ x`. Establish `hP : (n.comap τ).IsPrime` using `Ideal.comap_isPrime τ n`. Establish `hle : Ideal.span {(p : ℤ)} ≤ (n.comap τ).under ℤ`. Rewrite using `[Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap, Ideal.mem_comap]`. Simplify using `using hpn`.

Establish `hund : (n.comap τ).under ℤ = Ideal.span {(p : ℤ)}` using `(hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle).symm`. Establish `hund' : Q.under ℤ = Ideal.span {(p : ℤ)}` using `hQo.over.symm`. Take `⟨g, hg⟩` from `Algebra.IsInvariant.exists_smul_of_under_eq ℤ (NumberField.RingOfIntegers E) Gal(E/ℚ) Q (n.comap τ) (hund'.trans hund.symm)`. Establish `hcj` using `hφ.conj g`. Establish `hcomm : g * φ * g⁻¹ = φ`.

Rewrite using `[hc g φ, mul_assoc, mul_inv_cancel, mul_one]`. Rewrite `hcj` using `[hcomm, ← hg]`. Establish `hx` using `hcj x`. Rewrite `hx` using `[hund]`. Rewrite `hx` using `[Int.card_ideal_quot, Ideal.mem_comap]`.

Establish `he : (MulSemiringAction.toAlgHom ℤ (NumberField.RingOfIntegers E) φ) x = NumberField.RingOfIntegers.mapRingEquiv φ.toRingEquiv x`. Use `ext`. Both sides reduce to the same expression. Rewrite `hx` using `[he, map_sub, map_pow]`. Conclude with `hx`.
-/
theorem UpperTheory.Reformulated.B.DYda8.main :
    ∀ (E : Type) [inst : Field E] [inst_1 : NumberField E] [IsGalois ℚ E],
      (∀ (a b : Gal(E/ℚ)), a * b = b * a) →
        ∀ (p : ℕ),
          Nat.Prime p →
            ∃ (φ : Gal(E/ℚ)),
              ∀ (O : Type) [inst_3 : CommRing O] (n : Ideal O),
                n.IsPrime →
                  (↑p : O) ∈ n →
                    ∀ (τ : NumberField.RingOfIntegers E →+* O) (x : NumberField.RingOfIntegers E),
                      (τ : NumberField.RingOfIntegers E → O)
                            ((NumberField.RingOfIntegers.mapRingEquiv φ.toRingEquiv :
                                NumberField.RingOfIntegers E → NumberField.RingOfIntegers E)
                              x) -
                          (τ : NumberField.RingOfIntegers E → O) x ^ p ∈
                        n := by
  intro E _ _ _ hc p hp
  haveI : Fact p.Prime := ⟨hp⟩
  have hp0 : (Ideal.span {(p : ℤ)}) ≠ ⊥ := by
    simpa using hp.ne_zero
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    Ideal.IsPrime.isMaximal ((Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2
      (Nat.prime_iff_prime_int.1 hp)) hp0
  obtain ⟨Q, hQm, hQo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := NumberField.RingOfIntegers E) (Ideal.span {(p : ℤ)})
  have hQbot : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp0 Q
  haveI : Finite (NumberField.RingOfIntegers E ⧸ Q) := Ideal.finiteQuotientOfFreeOfNeBot Q hQbot
  obtain ⟨φ, hφ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ Gal(E/ℚ) Q
  refine ⟨φ, ?_⟩
  intro O _ n hn hpn τ x
  have hP : (n.comap τ).IsPrime := Ideal.comap_isPrime τ n
  have hle : Ideal.span {(p : ℤ)} ≤ (n.comap τ).under ℤ := by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap, Ideal.mem_comap]
    simpa using hpn
  have hund : (n.comap τ).under ℤ = Ideal.span {(p : ℤ)} :=
    (hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle).symm
  have hund' : Q.under ℤ = Ideal.span {(p : ℤ)} := hQo.over.symm
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq ℤ (NumberField.RingOfIntegers E)
    Gal(E/ℚ) Q (n.comap τ) (hund'.trans hund.symm)
  have hcj := hφ.conj g
  have hcomm : g * φ * g⁻¹ = φ := by
    rw [hc g φ, mul_assoc, mul_inv_cancel, mul_one]
  rw [hcomm, ← hg] at hcj
  have hx := hcj x
  rw [hund] at hx
  rw [Int.card_ideal_quot, Ideal.mem_comap] at hx
  have he : (MulSemiringAction.toAlgHom ℤ (NumberField.RingOfIntegers E) φ) x =
      NumberField.RingOfIntegers.mapRingEquiv φ.toRingEquiv x := by
    ext
    rfl
  rw [he, map_sub, map_pow] at hx
  exact hx
