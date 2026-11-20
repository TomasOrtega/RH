import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzPinA
import Development.DiscreteGroups.GlobalIrreducibility.DzStickTeich

noncomputable section

set_option linter.style.haveILetI false

open NumberField IsDedekindDomain Polynomial

namespace DiscreteGroups.sglob.DzPin

/- English proof (translation)
Establish `hpZ : Prime (p : ℤ)` using `Nat.prime_iff_prime_int.mp hp.out`. Establish `hmax : (Ideal.span {(p : ℤ)}).IsMaximal` using `PrincipalIdealRing.isMaximal_of_irreducible hpZ.irreducible`. Establish `hker : RingHom.ker (algebraMap ℤ (𝓞 L)) ≤ Ideal.span {(p : ℤ)}`. Rewrite using `[(RingHom.injective_iff_ker_eq_bot _).mp (algebraMap ℤ (𝓞 L)).injective_int]`. Conclude with `bot_le`.

Take `⟨Q, hQ, hQc⟩` from `Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 L) _ hker`. Use `⟨Q, hQ, ?_⟩` and prove the remaining obligations. Establish `h : (p : ℤ) ∈ Ideal.comap (algebraMap ℤ (𝓞 L)) Q` using `hQc ▸ Ideal.subset_span rfl`. Simplify using `using h`.
-/
theorem exists_maximal_above (L : Type) [Field L] [NumberField L] (p : ℕ) [hp : Fact p.Prime] :
    ∃ Q : Ideal (𝓞 L), Q.IsMaximal ∧ (p : 𝓞 L) ∈ Q := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hpZ.irreducible
  have hker : RingHom.ker (algebraMap ℤ (𝓞 L)) ≤ Ideal.span {(p : ℤ)} := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (algebraMap ℤ (𝓞 L)).injective_int]
    exact bot_le
  obtain ⟨Q, hQ, hQc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 L) _ hker
  refine ⟨Q, hQ, ?_⟩
  have h : (p : ℤ) ∈ Ideal.comap (algebraMap ℤ (𝓞 L)) Q := hQc ▸ Ideal.subset_span rfl
  simpa using h

/- English proof (translation)
Use `letI : Field (𝓞 L ⧸ Q) := Ideal.Quotient.field Q`. Establish `hpz : ((p : ℕ) : 𝓞 L ⧸ Q) = 0`. Rewrite using `[← map_natCast (Ideal.Quotient.mk Q), Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hpQ`. Use `haveI : CharP (𝓞 L ⧸ Q) p := ringChar.of_eq (CharP.ringChar_of_prime_eq_zero hp.out hpz)`.

Use `letI : Algebra (ZMod p) (𝓞 L ⧸ Q) := ZMod.algebra _ p`. Use `haveI := FiniteField.isSplittingField_sub K (ZMod p)`. Establish `hμ' : IsPrimitiveRoot (Ideal.Quotient.mk Q μ) N` using `Stick.isPrimitiveRoot_mk Q hNQ hμ`. Establish `hs : (map (algebraMap (ZMod p) (𝓞 L ⧸ Q)) (X ^ Fintype.card K - X)).Splits`. Establish `e : (X ^ Fintype.card K - X : (𝓞 L ⧸ Q)[X]) = X * (X ^ N - C 1)`.

Rewrite using `[hK, C_1]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Polynomial.map_sub, Polynomial.map_pow, map_X, e]`. Conclude with `Splits.X.mul (X_pow_sub_one_splits hμ')`. Conclude with `⟨(IsSplittingField.lift K (X ^ Fintype.card K - X) hs).toRingHom⟩`.
-/
theorem exists_iota (L : Type) [Field L] [NumberField L] (p : ℕ) [hp : Fact p.Prime]
    (Q : Ideal (𝓞 L)) [hQ : Q.IsMaximal] (hpQ : (p : 𝓞 L) ∈ Q) {N : ℕ} {μ : 𝓞 L}
    (hμ : IsPrimitiveRoot μ N) (hNQ : (N : 𝓞 L) ∉ Q) (K : Type) [Field K] [Fintype K]
    [Algebra (ZMod p) K] (hK : Fintype.card K = N + 1) : Nonempty (K →+* 𝓞 L ⧸ Q) := by
  letI : Field (𝓞 L ⧸ Q) := Ideal.Quotient.field Q
  have hpz : ((p : ℕ) : 𝓞 L ⧸ Q) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk Q), Ideal.Quotient.eq_zero_iff_mem]
    exact hpQ
  haveI : CharP (𝓞 L ⧸ Q) p := ringChar.of_eq (CharP.ringChar_of_prime_eq_zero hp.out hpz)
  letI : Algebra (ZMod p) (𝓞 L ⧸ Q) := ZMod.algebra _ p
  haveI := FiniteField.isSplittingField_sub K (ZMod p)
  have hμ' : IsPrimitiveRoot (Ideal.Quotient.mk Q μ) N := Stick.isPrimitiveRoot_mk Q hNQ hμ
  have hs : (map (algebraMap (ZMod p) (𝓞 L ⧸ Q)) (X ^ Fintype.card K - X)).Splits := by
    have e : (X ^ Fintype.card K - X : (𝓞 L ⧸ Q)[X]) = X * (X ^ N - C 1) := by
      rw [hK, C_1]; ring
    rw [Polynomial.map_sub, Polynomial.map_pow, map_X, e]
    exact Splits.X.mul (X_pow_sub_one_splits hμ')
  exact ⟨(IsSplittingField.lift K (X ^ Fintype.card K - X) hs).toRingHom⟩

/- English proof (translation)
Establish `hirr` using `Polynomial.cyclotomic.irreducible_rat (NeZero.pos m)`. Set `x : primitiveRoots m ℂ` to `⟨c, (mem_primitiveRoots (NeZero.pos m)).2 hc⟩`. Use `⟨((hζ.embeddingsEquivPrimitiveRoots ℂ hirr).symm x).toRingHom, ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg Subtype.val ((hζ.embeddingsEquivPrimitiveRoots ℂ hirr).apply_symm_apply x)`. Rewrite `h` using `[IsPrimitiveRoot.embeddingsEquivPrimitiveRoots_apply_coe]`.

Conclude with `h`.
-/
theorem exists_emb (m : ℕ) [NeZero m] (L : Type) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {m} ℚ L] {ζ : L} (hζ : IsPrimitiveRoot ζ m) (c : ℂ)
    (hc : IsPrimitiveRoot c m) : ∃ φ : L →+* ℂ, φ ζ = c := by
  have hirr := Polynomial.cyclotomic.irreducible_rat (NeZero.pos m)
  let x : primitiveRoots m ℂ := ⟨c, (mem_primitiveRoots (NeZero.pos m)).2 hc⟩
  refine ⟨((hζ.embeddingsEquivPrimitiveRoots ℂ hirr).symm x).toRingHom, ?_⟩
  have h := congrArg Subtype.val ((hζ.embeddingsEquivPrimitiveRoots ℂ hirr).apply_symm_apply x)
  rw [IsPrimitiveRoot.embeddingsEquivPrimitiveRoots_apply_coe] at h
  exact h

/- English proof (translation)
Establish `hp2` using `hp.out.two_le`. Establish `hpn : p ≤ p ^ n` using `Nat.le_self_pow (by omega) p`. Use `set N := p ^ n - 1 with hNdef`. Establish `hN1 : N + 1 = p ^ n` using `by omega`. Establish `hN0 : 0 < N` using `by omega`.

Use `haveI : NeZero N := ⟨by omega⟩`. Use `haveI : NeZero (p * N) := ⟨Nat.mul_ne_zero hp.out.ne_zero (by omega)⟩`. Use `haveI : NeZero (((p * N : ℕ)) : ℚ) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne _)⟩`. Use `haveI : IsCyclotomicExtension {p * N} ℚ (CyclotomicField (p * N) ℚ) := by`. Use `CyclotomicField.isCyclotomicExtension (p * N) ℚ` and compare the differences between its conclusion and the goal.

Apply the tactic sequence `all_goals rfl`. Establish `hζL` using `IsCyclotomicExtension.zeta_spec (p * N) ℚ (CyclotomicField (p * N) ℚ)`. Set `z : 𝓞 (CyclotomicField (p * N) ℚ)` to `hζL.toInteger`. Establish `hzL : algebraMap (𝓞 (CyclotomicField (p * N) ℚ)) (CyclotomicField (p * N) ℚ) z = IsCyclotomicExtension.zeta (p * N) ℚ (CyclotomicField (p * N) ℚ)` using `rfl`. Establish `hz : IsPrimitiveRoot z (p * N)` using `hζL.toInteger_isPrimitiveRoot`.

Establish `hμ : IsPrimitiveRoot (z ^ p) N` using `hz.pow (NeZero.pos _) rfl`. Take `⟨Q0, hQmax, hpQ⟩` from `exists_maximal_above (CyclotomicField (p * N) ℚ) p`. Establish `hNQ : (N : 𝓞 (CyclotomicField (p * N) ℚ)) ∉ Q0`. Introduce `h`. Establish `h1 : (p : 𝓞 (CyclotomicField (p * N) ℚ)) ^ n ∈ Q0` using `Ideal.pow_mem_of_mem _ hpQ n (by omega)`.

Establish `h2 : (1 : 𝓞 (CyclotomicField (p * N) ℚ)) = (p : 𝓞 (CyclotomicField (p * N) ℚ)) ^ n - N`. Establish `e : ((N + 1 : ℕ) : 𝓞 (CyclotomicField (p * N) ℚ)) = ((p ^ n : ℕ) : 𝓞 (CyclotomicField (p * N) ℚ))` using `by rw [hN1]`. Move the coercions through the operations in `at e`. Rewrite using `[← e]`. Expand and normalize the polynomial expressions, which then agree.

Conclude with `hQmax.ne_top ((Ideal.eq_top_iff_one _).2 (h2 ▸ Q0.sub_mem h1 h))`. Take `⟨ι⟩` from `exists_iota (CyclotomicField (p * N) ℚ) p Q0 hpQ hμ hNQ K (by omega)`. Establish `hne : Q0 ≠ ⊥`. Introduce and unpack `rfl`. Conclude with `(Nat.cast_ne_zero.mpr hp.out.ne_zero) ((Submodule.mem_bot _).1 hpQ)`.

Set `Q : HeightOneSpectrum (𝓞 (CyclotomicField (p * N) ℚ))` to `⟨Q0, hQmax.isPrime, hne⟩`. Take `⟨ω, hω1, hωN⟩` from `Stick.exists_powResChar Q0 ι (n := N) (by rw [hK]) hμ`. Establish `hdiv : (Fintype.card K - 1) / N = 1` using `by rw [hK, ← hNdef, Nat.div_self hN0]`. Establish `mk_ω : ∀ x, Ideal.Quotient.mk Q.asIdeal (ω x) = ι x`. Introduce `x`.

Establish `h` using `hω1 x`. Rewrite `h` using `[hdiv, pow_one]`. Conclude with `h`. Establish `hωu : ∀ y : Kˣ, ω y ^ N = 1`. Introduce `y`.

Rewrite using `[← MulChar.pow_apply_coe, hωN, MulChar.one_apply_coe]`. Set `c : ℂ` to `Complex.exp (2 * Real.pi * Complex.I / ((p * N : ℕ) : ℂ))`. Establish `hc : IsPrimitiveRoot c (p * N)` using `Complex.isPrimitiveRoot_exp _ (NeZero.ne _)`. Establish `hemb : ∀ t : ℕ, t.Coprime (p * N) → ∃ Φ : 𝓞 (CyclotomicField (p * N) ℚ) →+* ℂ, Function.Injective Φ ∧ Φ z = c ^ t`. Introduce `t ht`.

Take `⟨φ, hφ⟩` from `exists_emb (p * N) (CyclotomicField (p * N) ℚ) hζL (c ^ t) (hc.pow_of_coprime t ht)`. Conclude with `⟨φ.comp (algebraMap (𝓞 (CyclotomicField (p * N) ℚ)) (CyclotomicField (p * N) ℚ)), φ.injective.comp (IsFractionRing.injective (𝓞 (CyclotomicField (p * N) ℚ)) (CyclotomicField (p * N) ℚ)), by rw [RingHom.comp_apply, hzL, hφ]⟩`. Take `⟨Φ1, hΦ1i, hΦ1z⟩` from `hemb 1 (Nat.coprime_one_left _)`. Set `Ω : Kˣ →* ℂˣ` to `(Units.map Φ1.toMonoidHom).comp ω.toUnitHom`. Establish `hΩ : ∀ y : Kˣ, ((Ω y : ℂˣ) : ℂ) = Φ1 (ω y)` using `fun y => rfl`.

Use `⟨Q, ω, Ω, ?_, ?_⟩` and prove the remaining obligations. Introduce `y₁ y₂ h`. Establish `h1 : Φ1 (ω y₁) = Φ1 (ω y₂)` using `by rw [← hΩ, ← hΩ, h]`. Establish `h2` using `congrArg (Ideal.Quotient.mk Q.asIdeal) (hΦ1i h1)`. Rewrite `h2` using `[mk_ω, mk_ω]`.

Conclude with `Units.ext (ι.injective h2)`. Introduce `t ht`. Take `⟨Φ, hΦi, hΦz⟩` from `hemb t ht`. Establish `hpow : ∀ x : 𝓞 (CyclotomicField (p * N) ℚ), x ^ N = 1 → Φ x = Φ1 x ^ t`. Introduce `x hx`.

Take `⟨j, -, rfl⟩` from `hμ.eq_pow_of_pow_eq_one hx`. Simplify using `only [map_pow, hΦz, hΦ1z, pow_one]`. Expand and normalize the polynomial expressions, which then agree. Establish `hw : IsPrimitiveRoot ((ψ₀ 1 : Circle) : ℂ) p`. Establish `h1 : ((ψ₀ 1 : Circle) : ℂ) ^ p = 1`.

Rewrite using `[← Circle.coe_pow, ← AddChar.map_nsmul_eq_pow, nsmul_one, ZMod.natCast_self, AddChar.map_zero_eq_one, Circle.coe_one]`. Establish `h2 : ((ψ₀ 1 : Circle) : ℂ) ≠ 1`. Introduce `h`. Apply `hψ₀` to reduce the goal to its premises. Use `AddChar.ext_iff.2 fun y => Circle.coe_injective ?_` and prove the remaining obligations.

Rewrite using `[addChar_apply_eq_pow, h, one_pow, AddChar.one_apply, Circle.coe_one]`. Establish `h3` using `IsPrimitiveRoot.orderOf ((ψ₀ 1 : Circle) : ℂ)`. Rewrite `h3` using `[orderOf_eq_prime h1 h2]`. Then use the resulting hypothesis. Establish `hzN : IsPrimitiveRoot (Φ (z ^ N)) p`. Rewrite using `[map_pow, hΦz]`.

Conclude with `(hc.pow_of_coprime t ht).pow (NeZero.pos _) (by ring)`. Take `⟨j, -, hj⟩` from `hzN.eq_pow_of_pow_eq_one hw.pow_eq_one`. Establish `hΦζ : Φ ((z ^ N) ^ j) = ((ψ₀ 1 : Circle) : ℂ)` using `by rw [map_pow, hj]`. Establish `hprim : IsPrimitiveRoot ((z ^ N) ^ j) p` using `IsPrimitiveRoot.of_map_of_injective (f := Φ) (by rw [hΦζ]; exact hw) hΦi`. Set `D : Stick.GSDatum p n K (𝓞 (CyclotomicField (p * N) ℚ)) Q` to `{ card_eq := hK, ι := ι, ω := ω, mk_ω := mk_ω, ζ := (z ^ N) ^ j, prim := hprim }`.

Use `⟨Φ, D, hΦi, rfl, hΦζ, fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[hpow _ (hωu y), hΩ]`.
-/
theorem exists_setup (p : ℕ) [hp : Fact p.Prime] (n : ℕ) (hn : 1 ≤ n) (K : Type) [Field K]
    [Fintype K] [Algebra (ZMod p) K] (hK : Fintype.card K = p ^ n) (ψ₀ : AddChar (ZMod p) Circle)
    (hψ₀ : ψ₀ ≠ 1) :
    ∃ (Q : HeightOneSpectrum (𝓞 (CyclotomicField (p * (p ^ n - 1)) ℚ)))
      (ω : MulChar K (𝓞 (CyclotomicField (p * (p ^ n - 1)) ℚ))) (Ω : Kˣ →* ℂˣ),
      Function.Injective Ω ∧
      ∀ t : ℕ, t.Coprime (p * (p ^ n - 1)) →
        ∃ (Φ : 𝓞 (CyclotomicField (p * (p ^ n - 1)) ℚ) →+* ℂ) (D : Stick.GSDatum p n K _ Q),
          Function.Injective Φ ∧ D.ω = ω ∧ Φ D.ζ = ((ψ₀ 1 : Circle) : ℂ) ∧
          ∀ z : Kˣ, Φ (ω z) = ((Ω z : ℂˣ) : ℂ) ^ t := by
  classical
  have hp2 := hp.out.two_le
  have hpn : p ≤ p ^ n := Nat.le_self_pow (by omega) p
  set N := p ^ n - 1 with hNdef
  have hN1 : N + 1 = p ^ n := by omega
  have hN0 : 0 < N := by omega
  haveI : NeZero N := ⟨by omega⟩
  haveI : NeZero (p * N) := ⟨Nat.mul_ne_zero hp.out.ne_zero (by omega)⟩
  haveI : NeZero (((p * N : ℕ)) : ℚ) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne _)⟩
  haveI : IsCyclotomicExtension {p * N} ℚ (CyclotomicField (p * N) ℚ) := by
    convert CyclotomicField.isCyclotomicExtension (p * N) ℚ
    all_goals rfl
  have hζL := IsCyclotomicExtension.zeta_spec (p * N) ℚ (CyclotomicField (p * N) ℚ)
  let z : 𝓞 (CyclotomicField (p * N) ℚ) := hζL.toInteger
  have hzL : algebraMap (𝓞 (CyclotomicField (p * N) ℚ)) (CyclotomicField (p * N) ℚ) z = IsCyclotomicExtension.zeta (p * N) ℚ (CyclotomicField (p * N) ℚ) := rfl
  have hz : IsPrimitiveRoot z (p * N) := hζL.toInteger_isPrimitiveRoot
  have hμ : IsPrimitiveRoot (z ^ p) N := hz.pow (NeZero.pos _) rfl
  obtain ⟨Q0, hQmax, hpQ⟩ := exists_maximal_above (CyclotomicField (p * N) ℚ) p
  have hNQ : (N : 𝓞 (CyclotomicField (p * N) ℚ)) ∉ Q0 := by
    intro h
    have h1 : (p : 𝓞 (CyclotomicField (p * N) ℚ)) ^ n ∈ Q0 := Ideal.pow_mem_of_mem _ hpQ n (by omega)
    have h2 : (1 : 𝓞 (CyclotomicField (p * N) ℚ)) = (p : 𝓞 (CyclotomicField (p * N) ℚ)) ^ n - N := by
      have e : ((N + 1 : ℕ) : 𝓞 (CyclotomicField (p * N) ℚ)) = ((p ^ n : ℕ) : 𝓞 (CyclotomicField (p * N) ℚ)) := by rw [hN1]
      push_cast at e
      rw [← e]; ring
    exact hQmax.ne_top ((Ideal.eq_top_iff_one _).2 (h2 ▸ Q0.sub_mem h1 h))
  obtain ⟨ι⟩ := exists_iota (CyclotomicField (p * N) ℚ) p Q0 hpQ hμ hNQ K (by omega)
  have hne : Q0 ≠ ⊥ := by
    rintro rfl
    exact (Nat.cast_ne_zero.mpr hp.out.ne_zero) ((Submodule.mem_bot _).1 hpQ)
  let Q : HeightOneSpectrum (𝓞 (CyclotomicField (p * N) ℚ)) := ⟨Q0, hQmax.isPrime, hne⟩
  obtain ⟨ω, hω1, hωN⟩ := Stick.exists_powResChar Q0 ι (n := N) (by rw [hK]) hμ
  have hdiv : (Fintype.card K - 1) / N = 1 := by rw [hK, ← hNdef, Nat.div_self hN0]
  have mk_ω : ∀ x, Ideal.Quotient.mk Q.asIdeal (ω x) = ι x := by
    intro x
    have h := hω1 x
    rw [hdiv, pow_one] at h
    exact h
  have hωu : ∀ y : Kˣ, ω y ^ N = 1 := by
    intro y; rw [← MulChar.pow_apply_coe, hωN, MulChar.one_apply_coe]

  let c : ℂ := Complex.exp (2 * Real.pi * Complex.I / ((p * N : ℕ) : ℂ))
  have hc : IsPrimitiveRoot c (p * N) := Complex.isPrimitiveRoot_exp _ (NeZero.ne _)
  have hemb : ∀ t : ℕ, t.Coprime (p * N) →
      ∃ Φ : 𝓞 (CyclotomicField (p * N) ℚ) →+* ℂ, Function.Injective Φ ∧ Φ z = c ^ t := by
    intro t ht
    obtain ⟨φ, hφ⟩ := exists_emb (p * N) (CyclotomicField (p * N) ℚ) hζL (c ^ t) (hc.pow_of_coprime t ht)
    exact ⟨φ.comp (algebraMap (𝓞 (CyclotomicField (p * N) ℚ)) (CyclotomicField (p * N) ℚ)), φ.injective.comp (IsFractionRing.injective (𝓞 (CyclotomicField (p * N) ℚ)) (CyclotomicField (p * N) ℚ)),
      by rw [RingHom.comp_apply, hzL, hφ]⟩
  obtain ⟨Φ1, hΦ1i, hΦ1z⟩ := hemb 1 (Nat.coprime_one_left _)

  let Ω : Kˣ →* ℂˣ := (Units.map Φ1.toMonoidHom).comp ω.toUnitHom
  have hΩ : ∀ y : Kˣ, ((Ω y : ℂˣ) : ℂ) = Φ1 (ω y) := fun y => rfl
  refine ⟨Q, ω, Ω, ?_, ?_⟩
  · intro y₁ y₂ h
    have h1 : Φ1 (ω y₁) = Φ1 (ω y₂) := by rw [← hΩ, ← hΩ, h]
    have h2 := congrArg (Ideal.Quotient.mk Q.asIdeal) (hΦ1i h1)
    rw [mk_ω, mk_ω] at h2
    exact Units.ext (ι.injective h2)
  · intro t ht
    obtain ⟨Φ, hΦi, hΦz⟩ := hemb t ht

    have hpow : ∀ x : 𝓞 (CyclotomicField (p * N) ℚ), x ^ N = 1 → Φ x = Φ1 x ^ t := by
      intro x hx
      obtain ⟨j, -, rfl⟩ := hμ.eq_pow_of_pow_eq_one hx
      simp only [map_pow, hΦz, hΦ1z, pow_one]
      ring

    have hw : IsPrimitiveRoot ((ψ₀ 1 : Circle) : ℂ) p := by
      have h1 : ((ψ₀ 1 : Circle) : ℂ) ^ p = 1 := by
        rw [← Circle.coe_pow, ← AddChar.map_nsmul_eq_pow, nsmul_one, ZMod.natCast_self,
          AddChar.map_zero_eq_one, Circle.coe_one]
      have h2 : ((ψ₀ 1 : Circle) : ℂ) ≠ 1 := by
        intro h
        apply hψ₀
        refine AddChar.ext_iff.2 fun y => Circle.coe_injective ?_
        rw [addChar_apply_eq_pow, h, one_pow, AddChar.one_apply, Circle.coe_one]
      have h3 := IsPrimitiveRoot.orderOf ((ψ₀ 1 : Circle) : ℂ)
      rwa [orderOf_eq_prime h1 h2] at h3
    have hzN : IsPrimitiveRoot (Φ (z ^ N)) p := by
      rw [map_pow, hΦz]
      exact (hc.pow_of_coprime t ht).pow (NeZero.pos _) (by ring)
    obtain ⟨j, -, hj⟩ := hzN.eq_pow_of_pow_eq_one hw.pow_eq_one
    have hΦζ : Φ ((z ^ N) ^ j) = ((ψ₀ 1 : Circle) : ℂ) := by rw [map_pow, hj]
    have hprim : IsPrimitiveRoot ((z ^ N) ^ j) p :=
      IsPrimitiveRoot.of_map_of_injective (f := Φ) (by rw [hΦζ]; exact hw) hΦi
    let D : Stick.GSDatum p n K (𝓞 (CyclotomicField (p * N) ℚ)) Q :=
      { card_eq := hK, ι := ι, ω := ω, mk_ω := mk_ω, ζ := (z ^ N) ^ j, prim := hprim }
    refine ⟨Φ, D, hΦi, rfl, hΦζ, fun y => ?_⟩
    rw [hpow _ (hωu y), hΩ]

/- English proof (translation)
Establish `hg2` using `hg.out.two_le`. Establish `hfin : Module.finrank (ZMod g) K = n`. Establish `h` using `Module.card_eq_pow_finrank (K := ZMod g) (V := K)`. Rewrite `h` using `[ZMod.card, hK]`. Conclude with `(Nat.pow_right_injective hg2 h).symm`.

Use `MonoidHom.ext fun z => ?_` and prove the remaining obligations. Establish `hz : Units.map (algebraMap (ZMod g) K).toMonoidHom (Units.map (Algebra.norm (ZMod g) : K →* ZMod g) z) = z ^ ((g ^ n - 1) / (g - 1))`. Use `Units.ext ?_` and prove the remaining obligations. Simplify using `only [Units.coe_map, Units.val_pow_eq_pow_val, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]`. Rewrite using `[FiniteField.algebraMap_norm_eq_prod_pow, Finset.prod_pow_eq_pow_sum, Nat.card_zmod, hfin, Nat.geomSum_eq hg2]`.

Rewrite using `[MonoidHom.comp_apply, MonoidHom.pow_apply, MonoidHom.comp_apply, hz, map_pow, ← pow_mul, MonoidHom.pow_apply]`.
-/
theorem nm_eq {g : ℕ} [hg : Fact g.Prime] {n : ℕ} {K : Type} [Field K] [Fintype K]
    [Algebra (ZMod g) K] (hK : Fintype.card K = g ^ n) (Ω : Kˣ →* ℂˣ) (m : ℕ) :
    ((Ω.comp (Units.map (algebraMap (ZMod g) K).toMonoidHom)) ^ m).comp
        (Units.map (Algebra.norm (ZMod g) : K →* ZMod g)) = Ω ^ ((g ^ n - 1) / (g - 1) * m) := by
  have hg2 := hg.out.two_le
  have hfin : Module.finrank (ZMod g) K = n := by
    have h := Module.card_eq_pow_finrank (K := ZMod g) (V := K)
    rw [ZMod.card, hK] at h
    exact (Nat.pow_right_injective hg2 h).symm
  refine MonoidHom.ext fun z => ?_
  have hz : Units.map (algebraMap (ZMod g) K).toMonoidHom
      (Units.map (Algebra.norm (ZMod g) : K →* ZMod g) z) = z ^ ((g ^ n - 1) / (g - 1)) := by
    refine Units.ext ?_
    simp only [Units.coe_map, Units.val_pow_eq_pow_val, MonoidHom.coe_coe,
      RingHom.toMonoidHom_eq_coe]
    rw [FiniteField.algebraMap_norm_eq_prod_pow, Finset.prod_pow_eq_pow_sum, Nat.card_zmod, hfin,
      Nat.geomSum_eq hg2]
  rw [MonoidHom.comp_apply, MonoidHom.pow_apply, MonoidHom.comp_apply, hz, map_pow, ← pow_mul,
    MonoidHom.pow_apply]

end DiscreteGroups.sglob.DzPin
