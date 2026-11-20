import Mathlib

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
The claim follows from `o.2`.
-/
theorem isInt_O (o : 𝓞 K) : IsIntegral ℤ (algebraMap (𝓞 K) K o) := o.2

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨x, h⟩, rfl⟩`.
-/
theorem O_of_isInt {x : K} (h : IsIntegral ℤ x) : ∃ o : 𝓞 K, algebraMap (𝓞 K) K o = x := ⟨⟨x, h⟩, rfl⟩

/- English proof (translation)
Simplify using `using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ K n))`.
-/
theorem isInt_intCast (n : ℤ) : IsIntegral ℤ (n : K) := by
  simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ K n))

/- English proof (translation)
The claim follows from `h.map (starRingEnd K).toIntAlgHom`.
-/
theorem isInt_star [StarRing K] {x : K} (h : IsIntegral ℤ x) : IsIntegral ℤ (star x) :=
  h.map (starRingEnd K).toIntAlgHom

/- English proof (translation)
Take `⟨y, hy, h⟩` from `exists_integral_multiples ℤ ℚ s`. Use `⟨y.natAbs ^ 2, pow_pos (Int.natAbs_pos.2 hy) 2, fun x hx => ?_⟩` and prove the remaining obligations. Establish `e0 : ((y.natAbs ^ 2 : ℕ) : ℤ) = y ^ 2` using `by rw [Nat.cast_pow, Int.natAbs_sq]`. Establish `e1 : ((y.natAbs ^ 2 : ℕ) : K) = (y : K) ^ 2` using `by rw [← Int.cast_natCast, e0, Int.cast_pow]`. Rewrite using `[e1, pow_two, mul_assoc, ← zsmul_eq_mul x y]`.

Conclude with `(isInt_intCast y).mul (h x hx)`.
-/
theorem commonDen (s : Finset K) : ∃ d : ℕ, 0 < d ∧ ∀ x ∈ s, IsIntegral ℤ ((d : K) * x) := by
  obtain ⟨y, hy, h⟩ := exists_integral_multiples ℤ ℚ s
  refine ⟨y.natAbs ^ 2, pow_pos (Int.natAbs_pos.2 hy) 2, fun x hx => ?_⟩
  have e0 : ((y.natAbs ^ 2 : ℕ) : ℤ) = y ^ 2 := by rw [Nat.cast_pow, Int.natAbs_sq]
  have e1 : ((y.natAbs ^ 2 : ℕ) : K) = (y : K) ^ 2 := by rw [← Int.cast_natCast, e0, Int.cast_pow]
  rw [e1, pow_two, mul_assoc, ← zsmul_eq_mul x y]
  exact (isInt_intCast y).mul (h x hx)

/- English proof (translation)
Use `set I : Ideal (𝓞 K) := Ideal.span {(N : 𝓞 K)} with hI`. Establish `hIne : I ≠ ⊥`. Rewrite using `[hI, Ne, Ideal.span_singleton_eq_bot]`. Conclude with `hN.ne'` after adjusting the coercions. Use `I.finiteQuotientOfFreeOfNeBot hIne` as an intermediate fact.

Use `set σ := Function.surjInv (Ideal.Quotient.mk_surjective (I := I)) with hσ`. Use `⟨Set.range (fun q : 𝓞 K ⧸ I => algebraMap (𝓞 K) K (σ q)), Set.finite_range _, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨q, rfl⟩`. Conclude with `isInt_O _`. Introduce `o ho`.

Take `⟨oo, rfl⟩` from `O_of_isInt ho`. Use `set q := Ideal.Quotient.mk I oo`. Establish `hq : Ideal.Quotient.mk I (σ q) = q` using `Function.surjInv_eq _ q`. Establish `hmem : oo - σ q ∈ I` using `Ideal.Quotient.eq.1 hq.symm`. Take `⟨t, ht⟩` from `Ideal.mem_span_singleton'.1 hmem`.

Use `⟨algebraMap (𝓞 K) K t, algebraMap (𝓞 K) K (σ q), isInt_O _, ⟨q, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `e : oo = t * N + σ q` using `by rw [ht]; ring`. Rewrite using `[e, map_add, map_mul, map_natCast]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem reduceRep (N : ℕ) (hN : 0 < N) : ∃ Rep : Set K, Rep.Finite ∧ (∀ ρ ∈ Rep, IsIntegral ℤ ρ) ∧
    ∀ o : K, IsIntegral ℤ o → ∃ t ρ : K, IsIntegral ℤ t ∧ ρ ∈ Rep ∧ o = (N : K) * t + ρ := by
  set I : Ideal (𝓞 K) := Ideal.span {(N : 𝓞 K)} with hI
  have hIne : I ≠ ⊥ := by
    rw [hI, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN.ne'
  have := I.finiteQuotientOfFreeOfNeBot hIne
  set σ := Function.surjInv (Ideal.Quotient.mk_surjective (I := I)) with hσ
  refine ⟨Set.range (fun q : 𝓞 K ⧸ I => algebraMap (𝓞 K) K (σ q)), Set.finite_range _, ?_, ?_⟩
  · rintro _ ⟨q, rfl⟩; exact isInt_O _
  · intro o ho
    obtain ⟨oo, rfl⟩ := O_of_isInt ho
    set q := Ideal.Quotient.mk I oo
    have hq : Ideal.Quotient.mk I (σ q) = q := Function.surjInv_eq _ q
    have hmem : oo - σ q ∈ I := Ideal.Quotient.eq.1 hq.symm
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hmem
    refine ⟨algebraMap (𝓞 K) K t, algebraMap (𝓞 K) K (σ q), isInt_O _, ⟨q, rfl⟩, ?_⟩
    have e : oo = t * N + σ q := by rw [ht]; ring
    rw [e, map_add, map_mul, map_natCast]
    ring

end PI.UnitaryGroupMassFormula.CntFormula
