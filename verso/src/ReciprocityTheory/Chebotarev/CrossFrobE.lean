import Mathlib

open NumberField Polynomial

namespace ReciprocityTheory.Cheb

/- English proof (translation)
Use `set p := Ideal.absNorm q with hpdef`. Establish `hq0 : q ≠ ⊥`. Introduce `h`. Rewrite `hpdef` using `[h, Ideal.absNorm_bot]`. Conclude with `Nat.not_prime_zero (hpdef ▸ hqp)`.

Establish `hqmax : q.IsMaximal` using `hq.isMaximal hq0`. Take `⟨P, hPmax, hPq⟩` from `Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 M) q`. Establish `hPunder : P.under (𝓞 E) = q` using `hPq.over.symm`. Establish `hP0 : P ≠ ⊥`. Introduce `h`.

Apply `hq0` to reduce the goal to its premises. Rewrite using `[← hPunder, h]`. Conclude with `Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)`. Establish `hPfin : Finite (𝓞 M ⧸ P)` using `(Ideal.absNorm_ne_zero_iff P).mp (fun h => hP0 (Ideal.absNorm_eq_zero_iff.mp h))`. Take `⟨σ, hσ⟩` from `IsArithFrobAt.exists_of_isInvariant (𝓞 E) (M ≃ₐ[E] M) P`.

Establish `hqZ : q.under ℤ = Ideal.span {(p : ℤ)}`. Establish `hpr : (Ideal.span {(p : ℤ)}).IsMaximal` using `PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hqp).irreducible`. Establish `hle : Ideal.span {(p : ℤ)} ≤ q.under ℤ`. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.under_def, Ideal.mem_comap]`. Use `Ideal.absNorm_mem q` as an intermediate fact.

Rewrite `this` using `[← hpdef]`. Simplify using `using this`. Conclude with `(hpr.eq_of_le (Ideal.IsPrime.under ℤ q).ne_top hle).symm`. Establish `hPZ : P.under ℤ = Ideal.span {(p : ℤ)}`. Rewrite using `[← Ideal.under_under (B := 𝓞 E), hPunder, hqZ]`.

Establish `hcardZ : Nat.card (ℤ ⧸ P.under ℤ) = p`. Rewrite using `[hPZ, Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]`. Establish `hcardE : Nat.card (𝓞 E ⧸ P.under (𝓞 E)) = p`. Rewrite using `[hPunder, hpdef, Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Establish `hfrob : IsArithFrobAt ℤ (σ.restrictScalars ℚ) P`.

Introduce `x`. Use `hσ x` as an intermediate fact. Rewrite `this` using `[hcardE]`. Use `show (σ.restrictScalars ℚ) • x - x ^ Nat.card (ℤ ⧸ P.under ℤ) ∈ P`. Rewrite using `[hcardZ]`.

Conclude with `this`. Use `⟨P, hPmax.isPrime, σ, ⟨hPZ.symm⟩, ?_, hfrob⟩` and prove the remaining obligations. Establish `hint : IsIntegral ℤ ζ` using `hζ.isIntegral (Nat.Prime.pos Fact.out)`. Set `z : 𝓞 M` to `⟨ζ, hint⟩`. Establish `hz : z ^ l = 1`.

Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[RingOfIntegers.coe_eq_algebraMap, RingOfIntegers.coe_eq_algebraMap, map_one]`. Conclude with `(map_pow (algebraMap (𝓞 M) M) z l).trans hζ.pow_eq_one`. Establish `hl : ((l : ℕ) : 𝓞 M) ∉ P`. Introduce `h`.

Establish `h' : ((l : ℕ) : ℤ) ∈ P.under ℤ`. Rewrite using `[Ideal.mem_comap]`. Simplify using `using h`. Rewrite `h'` using `[hPZ, Ideal.mem_span_singleton]`. Establish `hdvd : p ∣ l` using `by exact_mod_cast h'`.

Conclude with `hql ((Nat.prime_dvd_prime_iff_eq hqp Fact.out).mp hdvd)`. Establish `key` using `AlgHom.IsArithFrobAt.apply_of_pow_eq_one hfrob hz hl`. Rewrite `key` using `[hcardZ]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[RingOfIntegers.coe_eq_algebraMap]`.

Conclude with `(map_pow (algebraMap (𝓞 M) M) z p).trans rfl`.
-/
theorem exists_frob_above {M : Type} [Field M] [NumberField M] (E : IntermediateField ℚ M) [IsGalois E M]
    (l : ℕ) [Fact l.Prime] {ζ : M} (hζ : IsPrimitiveRoot ζ l) (q : Ideal (𝓞 E)) (hq : q.IsPrime)
    (hqp : (Ideal.absNorm q).Prime) (hql : Ideal.absNorm q ≠ l) :
    ∃ (P : Ideal (𝓞 M)) (_ : P.IsPrime) (φ : M ≃ₐ[E] M),
      P.LiesOver (Ideal.span {((Ideal.absNorm q : ℕ) : ℤ)}) ∧ φ ζ = ζ ^ Ideal.absNorm q ∧
      IsArithFrobAt ℤ (φ.restrictScalars ℚ) P := by
  set p := Ideal.absNorm q with hpdef
  have hq0 : q ≠ ⊥ := by
    intro h
    rw [h, Ideal.absNorm_bot] at hpdef
    exact Nat.not_prime_zero (hpdef ▸ hqp)
  have hqmax : q.IsMaximal := hq.isMaximal hq0
  obtain ⟨P, hPmax, hPq⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 M) q
  have hPunder : P.under (𝓞 E) = q := hPq.over.symm
  have hP0 : P ≠ ⊥ := by
    intro h
    apply hq0
    rw [← hPunder, h]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
  have hPfin : Finite (𝓞 M ⧸ P) :=
    (Ideal.absNorm_ne_zero_iff P).mp (fun h => hP0 (Ideal.absNorm_eq_zero_iff.mp h))
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant (𝓞 E) (M ≃ₐ[E] M) P

  have hqZ : q.under ℤ = Ideal.span {(p : ℤ)} := by
    have hpr : (Ideal.span {(p : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hqp).irreducible
    have hle : Ideal.span {(p : ℤ)} ≤ q.under ℤ := by
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.under_def, Ideal.mem_comap]
      have := Ideal.absNorm_mem q
      rw [← hpdef] at this
      simpa using this
    exact (hpr.eq_of_le (Ideal.IsPrime.under ℤ q).ne_top hle).symm
  have hPZ : P.under ℤ = Ideal.span {(p : ℤ)} := by
    rw [← Ideal.under_under (B := 𝓞 E), hPunder, hqZ]
  have hcardZ : Nat.card (ℤ ⧸ P.under ℤ) = p := by
    rw [hPZ, Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]
  have hcardE : Nat.card (𝓞 E ⧸ P.under (𝓞 E)) = p := by
    rw [hPunder, hpdef, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hfrob : IsArithFrobAt ℤ (σ.restrictScalars ℚ) P := by
    intro x
    have := hσ x
    rw [hcardE] at this
    show (σ.restrictScalars ℚ) • x - x ^ Nat.card (ℤ ⧸ P.under ℤ) ∈ P
    rw [hcardZ]
    exact this
  refine ⟨P, hPmax.isPrime, σ, ⟨hPZ.symm⟩, ?_, hfrob⟩

  have hint : IsIntegral ℤ ζ := hζ.isIntegral (Nat.Prime.pos Fact.out)
  let z : 𝓞 M := ⟨ζ, hint⟩
  have hz : z ^ l = 1 := by
    apply RingOfIntegers.ext
    rw [RingOfIntegers.coe_eq_algebraMap, RingOfIntegers.coe_eq_algebraMap, map_one]
    exact (map_pow (algebraMap (𝓞 M) M) z l).trans hζ.pow_eq_one
  have hl : ((l : ℕ) : 𝓞 M) ∉ P := by
    intro h
    have h' : ((l : ℕ) : ℤ) ∈ P.under ℤ := by
      rw [Ideal.mem_comap]; simpa using h
    rw [hPZ, Ideal.mem_span_singleton] at h'
    have hdvd : p ∣ l := by exact_mod_cast h'
    exact hql ((Nat.prime_dvd_prime_iff_eq hqp Fact.out).mp hdvd)
  have key := AlgHom.IsArithFrobAt.apply_of_pow_eq_one hfrob hz hl
  rw [hcardZ] at key
  calc σ ζ = (((σ.restrictScalars ℚ) • z : 𝓞 M) : M) := rfl
    _ = ((z ^ p : 𝓞 M) : M) := congrArg (fun y : 𝓞 M => (y : M)) key
    _ = ζ ^ p := by
      rw [RingOfIntegers.coe_eq_algebraMap]
      exact (map_pow (algebraMap (𝓞 M) M) z p).trans rfl

end ReciprocityTheory.Cheb
