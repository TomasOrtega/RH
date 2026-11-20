import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.LargePrimeDivisors

set_option autoImplicit false

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
open Polynomial

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.P6.LargePrimeDivisors.GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.exists_large_prime_dvd_eval f hf N`.
-/
theorem exists_large_prime_dvd_eval (f : ℤ[X]) (hf : 0 < f.natDegree) (N : ℕ) :
    ∃ (p : ℕ) (m : ℤ), p.Prime ∧ N < p ∧ (p : ℤ) ∣ f.eval m :=
  _root_.UpperTheory.Reformulated.B.P6.LargePrimeDivisors.GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.exists_large_prime_dvd_eval f hf N

/- English proof (translation)
Take `⟨α, hα⟩` from `Field.exists_primitive_element ℚ F`. Take `⟨y, hy, hint⟩` from `IsAlgebraic.exists_integral_multiple (R := ℤ) ((IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic α))`. Take `⟨θ, hθ⟩` from `(IsIntegralClosure.isIntegral_iff (A := 𝓞 F)).1 hint`. Use `⟨θ, ?_⟩` and prove the remaining obligations. Establish `hθ' : (θ : F) = y • α` using `hθ`.

Establish `hprim : IntermediateField.adjoin ℚ {(θ : F)} = ⊤`. Rewrite using `[eq_top_iff, ← hα, IntermediateField.adjoin_simple_le_iff]`. Establish `h : (θ : F) ∈ IntermediateField.adjoin ℚ {(θ : F)}` using `IntermediateField.mem_adjoin_simple_self ℚ _`. Establish `hyF : (y : F) ≠ 0` using `by exact_mod_cast hy`. Establish `e : α = ((y : ℚ)⁻¹) • (θ : F)`.

Rewrite using `[hθ', Algebra.smul_def, zsmul_eq_mul]`. Simplify using `[hyF]`. Rewrite using `[e]`. Conclude with `(IntermediateField.adjoin ℚ {(θ : F)}).smul_mem h`. Establish `hintZ : IsIntegral ℤ (θ : F)` using `RingOfIntegers.isIntegral_coe θ`.

Establish `hintQ : IsIntegral ℚ (θ : F)` using `Algebra.IsIntegral.isIntegral _`. Establish `htop : Algebra.adjoin ℚ {(θ : F)} = ⊤`. Rewrite using `[← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hintQ.isAlgebraic, hprim, IntermediateField.top_toSubalgebra]`. Set `B` to `PowerBasis.ofAdjoinEqTop hintQ htop`. Establish `hgen : B.gen = θ` using `PowerBasis.ofAdjoinEqTop_gen hintQ htop`.

Establish `hintB : IsIntegral ℤ B.gen` using `hgen ▸ hintZ`. Establish `hdi : IsIntegral ℤ (Algebra.discr ℚ B.basis)` using `Algebra.discr_isIntegral ℚ (fun i => by`. Rewrite using `[PowerBasis.coe_basis]`. Conclude with `hintB.pow _)`. Take `⟨n, hn⟩` from `IsIntegrallyClosed.isIntegral_iff.1 hdi`.

Establish `hn0 : n ≠ 0`. Introduce and unpack `rfl`. Conclude with `Algebra.discr_not_zero_of_basis ℚ B.basis (by simpa using hn.symm)`. Establish `hcond : (n : 𝓞 F) ∈ conductor ℤ θ`. Rewrite using `[mem_conductor_iff]`.

Introduce `b`. Establish `h1` using `Algebra.discr_mul_isIntegral_mem_adjoin ℚ hintB (RingOfIntegers.isIntegral_coe b)`. Rewrite `h1` using `[hgen, ← hn]`. Establish `h2 : ((n : F) * (b : F)) ∈ Algebra.adjoin ℤ {(θ : F)}`. Simplify `h1` using `[Algebra.smul_def]`.

Establish `h3 : Algebra.adjoin ℤ {(θ : F)} = (Algebra.adjoin ℤ {θ}).map (IsScalarTower.toAlgHom ℤ (𝓞 F) F)`. Rewrite using `[AlgHom.map_adjoin, Set.image_singleton]`. Both sides reduce to the same expression. Rewrite `h2` using `[h3]`. Take `⟨u, hu, hue⟩` from `h2`.

Establish `hub : u = (n : 𝓞 F) * b` using `RingOfIntegers.coe_injective (by simpa using hue)`. Conclude with `hub ▸ hu`. Introduce `h0`. Rewrite `h0` using `[RingOfIntegers.exponent, Ideal.absNorm_eq_zero_iff]`. Establish `hm : n ∈ Ideal.under ℤ (conductor ℤ θ)`.

Rewrite using `[Ideal.under_def, Ideal.mem_comap]`. Simplify using `using hcond`. Rewrite `hm` using `[h0]`. Conclude with `hn0 (by simpa using hm)`.
-/
theorem exists_exponent_ne_zero (F : Type) [Field F] [NumberField F] :
    ∃ θ : 𝓞 F, RingOfIntegers.exponent θ ≠ 0 := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ F
  obtain ⟨y, hy, hint⟩ := IsAlgebraic.exists_integral_multiple (R := ℤ)
    ((IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic α))
  obtain ⟨θ, hθ⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 F)).1 hint
  refine ⟨θ, ?_⟩
  have hθ' : (θ : F) = y • α := hθ
  have hprim : IntermediateField.adjoin ℚ {(θ : F)} = ⊤ := by
    rw [eq_top_iff, ← hα, IntermediateField.adjoin_simple_le_iff]
    have h : (θ : F) ∈ IntermediateField.adjoin ℚ {(θ : F)} :=
      IntermediateField.mem_adjoin_simple_self ℚ _
    have hyF : (y : F) ≠ 0 := by exact_mod_cast hy
    have e : α = ((y : ℚ)⁻¹) • (θ : F) := by
      rw [hθ', Algebra.smul_def, zsmul_eq_mul]
      simp [hyF]
    rw [e]
    exact (IntermediateField.adjoin ℚ {(θ : F)}).smul_mem h
  have hintZ : IsIntegral ℤ (θ : F) := RingOfIntegers.isIntegral_coe θ
  have hintQ : IsIntegral ℚ (θ : F) := Algebra.IsIntegral.isIntegral _
  have htop : Algebra.adjoin ℚ {(θ : F)} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hintQ.isAlgebraic, hprim,
      IntermediateField.top_toSubalgebra]
  let B := PowerBasis.ofAdjoinEqTop hintQ htop
  have hgen : B.gen = θ := PowerBasis.ofAdjoinEqTop_gen hintQ htop
  have hintB : IsIntegral ℤ B.gen := hgen ▸ hintZ
  have hdi : IsIntegral ℤ (Algebra.discr ℚ B.basis) := Algebra.discr_isIntegral ℚ (fun i => by
    rw [PowerBasis.coe_basis]
    exact hintB.pow _)
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 hdi
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact Algebra.discr_not_zero_of_basis ℚ B.basis (by simpa using hn.symm)
  have hcond : (n : 𝓞 F) ∈ conductor ℤ θ := by
    rw [mem_conductor_iff]
    intro b
    have h1 := Algebra.discr_mul_isIntegral_mem_adjoin ℚ hintB (RingOfIntegers.isIntegral_coe b)
    rw [hgen, ← hn] at h1
    have h2 : ((n : F) * (b : F)) ∈ Algebra.adjoin ℤ {(θ : F)} := by
      simpa [Algebra.smul_def] using h1
    have h3 : Algebra.adjoin ℤ {(θ : F)} =
        (Algebra.adjoin ℤ {θ}).map (IsScalarTower.toAlgHom ℤ (𝓞 F) F) := by
      rw [AlgHom.map_adjoin, Set.image_singleton]
      rfl
    rw [h3] at h2
    obtain ⟨u, hu, hue⟩ := h2
    have hub : u = (n : 𝓞 F) * b := RingOfIntegers.coe_injective (by simpa using hue)
    exact hub ▸ hu
  intro h0
  rw [RingOfIntegers.exponent, Ideal.absNorm_eq_zero_iff] at h0
  have hm : n ∈ Ideal.under ℤ (conductor ℤ θ) := by
    rw [Ideal.under_def, Ideal.mem_comap]
    simpa using hcond
  rw [h0] at hm
  exact hn0 (by simpa using hm)

/- English proof (translation)
Establish `h₀ : map (Int.castRingHom (ZMod p)) (minpoly ℤ θ) ≠ 0` using `map_monic_ne_zero (minpoly.monic θ.isIntegral)`. Establish `hQ : (X - C ((m : ℤ) : ZMod p)) ∈ RingOfIntegers.monicFactorsMod θ p`. Rewrite using `[Multiset.mem_toFinset, Polynomial.mem_normalizedFactors_iff h₀]`. Use `⟨irreducible_X_sub_C _, monic_X_sub_C _, dvd_iff_isRoot.2 ?_⟩` and prove the remaining obligations. Rewrite using `[IsRoot.def, eval_intCast_map]`.

Conclude with `(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hm`. Set `P` to `(NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hp).symm ⟨_, hQ⟩`. Establish `hf` using `NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply' hp hQ`. Establish `hPp : (P : Ideal (𝓞 F)).IsPrime` using `P.2.1`. Establish `hPl : (P : Ideal (𝓞 F)).LiesOver (Ideal.span {(p : ℤ)})` using `P.2.2`.

Use `⟨P, hPp, ?_⟩` and prove the remaining obligations. Rewrite using `[← Ideal.pow_inertiaDeg p (P : Ideal (𝓞 F)), hf, natDegree_X_sub_C, pow_one]`.
-/
theorem exists_isPrime_absNorm_eq {F : Type} [Field F] [NumberField F] (θ : 𝓞 F) (p : ℕ) [Fact p.Prime]
    (hp : ¬ p ∣ RingOfIntegers.exponent θ) (m : ℤ) (hm : (p : ℤ) ∣ (minpoly ℤ θ).eval m) :
    ∃ 𝔠 : Ideal (𝓞 F), 𝔠.IsPrime ∧ Ideal.absNorm 𝔠 = p := by
  have h₀ : map (Int.castRingHom (ZMod p)) (minpoly ℤ θ) ≠ 0 :=
    map_monic_ne_zero (minpoly.monic θ.isIntegral)
  have hQ : (X - C ((m : ℤ) : ZMod p)) ∈ RingOfIntegers.monicFactorsMod θ p := by
    rw [Multiset.mem_toFinset, Polynomial.mem_normalizedFactors_iff h₀]
    refine ⟨irreducible_X_sub_C _, monic_X_sub_C _, dvd_iff_isRoot.2 ?_⟩
    rw [IsRoot.def, eval_intCast_map]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hm
  let P := (NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hp).symm ⟨_, hQ⟩
  have hf := NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply' hp hQ
  have hPp : (P : Ideal (𝓞 F)).IsPrime := P.2.1
  have hPl : (P : Ideal (𝓞 F)).LiesOver (Ideal.span {(p : ℤ)}) := P.2.2
  refine ⟨P, hPp, ?_⟩
  rw [← Ideal.pow_inertiaDeg p (P : Ideal (𝓞 F)), hf, natDegree_X_sub_C, pow_one]

/- English proof (translation)
Introduce `F _ _ 𝔣 h𝔣 W B hW`. Take `⟨θ, hθ⟩` from `exists_exponent_ne_zero F`. Take `⟨p, m, hp, hN, hdvd⟩` from `exists_large_prime_dvd_eval (minpoly ℤ θ) (minpoly.natDegree_pos θ.isIntegral) (B + RingOfIntegers.exponent θ + Ideal.absNorm 𝔣 + ∑ x ∈ W, Ideal.absNorm (Ideal.span {x}))`. Use `Fact.mk hp` as an intermediate fact. Establish `hexp : ¬ p ∣ RingOfIntegers.exponent θ` using `fun h => by`.

Use `Nat.le_of_dvd (Nat.pos_of_ne_zero hθ) h` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Take `⟨𝔠, hprime, hnorm⟩` from `exists_isPrime_absNorm_eq θ p hexp m hdvd`. Establish `small : ∀ I : Ideal (𝓞 F), I ≠ ⊥ → Ideal.absNorm I < p → ¬ I ≤ 𝔠` using `fun I hI hlt hle => by`. Establish `h0 : Ideal.absNorm I ≠ 0` using `fun h => hI (Ideal.absNorm_eq_zero_iff.1 h)`.

Use `Nat.le_of_dvd (Nat.pos_of_ne_zero h0) (Ideal.absNorm_dvd_absNorm_of_le hle)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hbot : 𝔠 ≠ ⊥`. Introduce and unpack `rfl`. Rewrite `hnorm` using `[Ideal.absNorm_bot]`.

Conclude with `hp.ne_zero hnorm.symm`. Establish `hmax : 𝔠.IsMaximal` using `hprime.isMaximal hbot`. Use `⟨𝔠, hprime, hnorm ▸ hp, by omega, ?_, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Conclude with `small 𝔣 h𝔣 (by omega) (sup_eq_left.1 (hmax.eq_of_le h le_sup_left).symm)`.

Introduce `x hx hxc`. Establish `hle : Ideal.absNorm (Ideal.span {x}) ≤ ∑ x ∈ W, Ideal.absNorm (Ideal.span {x})` using `Finset.single_le_sum (f := fun x => Ideal.absNorm (Ideal.span {x})) (fun _ _ => Nat.zero_le _) hx`. Conclude with `small (Ideal.span {x}) (by simpa using hW x hx) (by omega) ((Ideal.span_singleton_le_iff_mem _).2 hxc)`.
-/
theorem exists_prime_absNorm_avoiding : ∀ (F : Type) [Field F] [NumberField F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ →
    ∀ (W : Finset (𝓞 F)) (B : ℕ), (∀ x ∈ W, x ≠ 0) →
    ∃ 𝔠 : Ideal (𝓞 F), 𝔠.IsPrime ∧ (Ideal.absNorm 𝔠).Prime ∧ B < Ideal.absNorm 𝔠 ∧ 𝔠 ⊔ 𝔣 = ⊤ ∧ ∀ x ∈ W, x ∉ 𝔠 := by
  intro F _ _ 𝔣 h𝔣 W B hW
  obtain ⟨θ, hθ⟩ := exists_exponent_ne_zero F
  obtain ⟨p, m, hp, hN, hdvd⟩ := exists_large_prime_dvd_eval (minpoly ℤ θ)
    (minpoly.natDegree_pos θ.isIntegral)
    (B + RingOfIntegers.exponent θ + Ideal.absNorm 𝔣 + ∑ x ∈ W, Ideal.absNorm (Ideal.span {x}))
  have := Fact.mk hp
  have hexp : ¬ p ∣ RingOfIntegers.exponent θ := fun h => by
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hθ) h
    omega
  obtain ⟨𝔠, hprime, hnorm⟩ := exists_isPrime_absNorm_eq θ p hexp m hdvd
  have small : ∀ I : Ideal (𝓞 F), I ≠ ⊥ → Ideal.absNorm I < p → ¬ I ≤ 𝔠 := fun I hI hlt hle => by
    have h0 : Ideal.absNorm I ≠ 0 := fun h => hI (Ideal.absNorm_eq_zero_iff.1 h)
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero h0) (Ideal.absNorm_dvd_absNorm_of_le hle)
    omega
  have hbot : 𝔠 ≠ ⊥ := by
    rintro rfl
    rw [Ideal.absNorm_bot] at hnorm
    exact hp.ne_zero hnorm.symm
  have hmax : 𝔠.IsMaximal := hprime.isMaximal hbot
  refine ⟨𝔠, hprime, hnorm ▸ hp, by omega, ?_, ?_⟩
  · by_contra h
    exact small 𝔣 h𝔣 (by omega) (sup_eq_left.1 (hmax.eq_of_le h le_sup_left).symm)
  · intro x hx hxc
    have hle : Ideal.absNorm (Ideal.span {x}) ≤ ∑ x ∈ W, Ideal.absNorm (Ideal.span {x}) :=
      Finset.single_le_sum (f := fun x => Ideal.absNorm (Ideal.span {x})) (fun _ _ => Nat.zero_le _) hx
    exact small (Ideal.span {x}) (by simpa using hW x hx) (by omega)
      ((Ideal.span_singleton_le_iff_mem _).2 hxc)

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
