import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerTowerQqPowLevelEqQ
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompletedLaurentIsDVRStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntPrimeDivRootOfUnitySubOnePowStatement
open GlobalTheory.K5 GlobalTheory.KumDlog

namespace GlobalTheory.K5

/- English proof (translation)
Introduce `p hp hp2 Ω _ _ _ T j hj y hy`. Use `set A := integralClosure (O0 p) Ω`. Establish `hpj : 1 < p ^ j` using `Nat.one_lt_pow (by omega) hp.out.one_lt`. Establish `hζ1 : T.ζ j ≠ 1` using `(T.prim j).ne_one hpj`. Establish `hτ0 : T.ζ j - 1 ≠ 0` using `sub_ne_zero.2 hζ1`.

Establish `hζint : IsIntegral (O0 p) (T.ζ j)`. Use `IsIntegral.of_pow (n := p ^ j) (by omega) ?_` and prove the remaining obligations. Rewrite using `[(T.prim j).pow_eq_one]`. Conclude with `isIntegral_one`. Establish `htot : 2 ≤ Nat.totient (p ^ j)`.

Rewrite using `[Nat.totient_prime_pow hp.out (by omega)]`. Establish `: 3 ≤ p` using `by have := hp.out.two_le; omega`. Establish `h1 : 1 ≤ p ^ (j - 1)` using `Nat.one_le_pow _ _ hp.out.pos`. Combine the equalities or inequalities in the displayed calculation. Establish `hw : IsIntegral (O0 p) ((p : Ω) / (T.ζ j - 1) ^ 2 * y)` using `(GlobalTheory.T.isInt_prime_div_rootOfUnity_sub_one_pow p Ω T j 2 hj htot).mul hy`.

Set `ζ' : A` to `⟨T.ζ j, hζint⟩`. Set `τ : A` to `ζ' - 1`. Set `w : A` to `⟨_, hw⟩`. Set `u : A` to `1 - τ * w`. Establish `hu : (u : Ω) = 1 - (p : Ω) / (T.ζ j - 1) * y`.

Simplify using `only [u, τ, w, ζ', Subalgebra.coe_sub, Subalgebra.coe_mul, Subalgebra.coe_one]`. Clear the denominators using the available nonvanishing facts. Take `⟨hdom, hdvr, hirr⟩` from `completed_laurent_isDVR p`. Establish `hmax : IsLocalRing.maximalIdeal (O0 p) = Ideal.span {(p : O0 p)}` using `(IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hirr`. Establish `hτM : ∀ M : Ideal A, M.IsMaximal → τ ∈ M`.

Introduce `M hM`. Establish `hc : (M.comap (algebraMap (O0 p) A)).IsMaximal` using `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M`. Establish `hpM : (p : A) ∈ M`. Establish `h1 : M.comap (algebraMap (O0 p) A) = IsLocalRing.maximalIdeal (O0 p)` using `IsLocalRing.eq_maximalIdeal hc`. Establish `h2 : (p : O0 p) ∈ M.comap (algebraMap (O0 p) A)`.

Rewrite using `[h1, hmax]`. Conclude with `Ideal.mem_span_singleton_self _`. Simplify using `using h2`. Use `haveI : M.IsPrime := hM.isPrime`. Use `haveI : Nontrivial (A ⧸ M) := Ideal.Quotient.nontrivial_iff.2 hM.ne_top`.

Use `haveI : CharP (A ⧸ M) p := by`. Rewrite using `[CharP.charP_iff_prime_eq_zero hp.out]`. Rewrite using `[← map_natCast (Ideal.Quotient.mk M), Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hpM`. Establish `hζp : ζ' ^ (p ^ j) = 1` using `Subtype.ext (by simp [ζ', (T.prim j).pow_eq_one])`.

Establish `h3 : (Ideal.Quotient.mk M τ) ^ (p ^ j) = 0`. Simplify using `only [τ, map_sub, map_one]`. Rewrite using `[sub_pow_char_pow, ← map_pow, hζp, map_one, one_pow, sub_self]`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `pow_eq_zero_iff (by omega) |>.1 h3`.

Establish `hunit : IsUnit u`. Assume the negation of the conclusion as `h`. Take `⟨M, hM, hle⟩` from `Ideal.exists_le_maximal (Ideal.span {u}) (by rwa [Ne, Ideal.span_singleton_eq_top])`. Establish `h1 : u ∈ M` using `hle (Ideal.mem_span_singleton_self _)`. Establish `h2 : τ * w ∈ M` using `M.mul_mem_right _ (hτM M hM)`.

Establish `: (1 : A) ∈ M`. Use `M.add_mem h1 h2` as an intermediate fact. Simplify `this` using `[u]`. Conclude with `hM.ne_top ((Ideal.eq_top_iff_one _).2 this)`. Take `⟨v, hv⟩` from `hunit`.

Establish `hval : (u : Ω) * (((v⁻¹ : Aˣ) : A) : Ω) = 1`. Rewrite using `[← hv, ← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one]`. Rewrite using `[← hu]`. Use `⟨left_ne_zero_of_mul_eq_one hval, ?_⟩` and prove the remaining obligations. Rewrite using `[← eq_inv_of_mul_eq_one_right hval]`.

Conclude with `((v⁻¹ : Aˣ) : A).2`.
-/
theorem one_sub_p_div_zeta_mul_isUnit : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (j : ℕ), 1 ≤ j → ∀ y : Ω, IsInt p y →
  1 - (p : Ω) / (T.ζ j - 1) * y ≠ 0 ∧ IsInt p (1 - (p : Ω) / (T.ζ j - 1) * y)⁻¹ := by
  intro p hp hp2 Ω _ _ _ T j hj y hy
  classical
  set A := integralClosure (O0 p) Ω
  have hpj : 1 < p ^ j := Nat.one_lt_pow (by omega) hp.out.one_lt
  have hζ1 : T.ζ j ≠ 1 := (T.prim j).ne_one hpj
  have hτ0 : T.ζ j - 1 ≠ 0 := sub_ne_zero.2 hζ1
  have hζint : IsIntegral (O0 p) (T.ζ j) := by
    refine IsIntegral.of_pow (n := p ^ j) (by omega) ?_
    rw [(T.prim j).pow_eq_one]; exact isIntegral_one
  have htot : 2 ≤ Nat.totient (p ^ j) := by
    rw [Nat.totient_prime_pow hp.out (by omega)]
    have : 3 ≤ p := by have := hp.out.two_le; omega
    have h1 : 1 ≤ p ^ (j - 1) := Nat.one_le_pow _ _ hp.out.pos
    calc 2 = 1 * 2 := by ring
      _ ≤ p ^ (j - 1) * (p - 1) := Nat.mul_le_mul h1 (by omega)
  have hw : IsIntegral (O0 p) ((p : Ω) / (T.ζ j - 1) ^ 2 * y) :=
    (GlobalTheory.T.isInt_prime_div_rootOfUnity_sub_one_pow p Ω T j 2 hj htot).mul hy
  let ζ' : A := ⟨T.ζ j, hζint⟩
  let τ : A := ζ' - 1
  let w : A := ⟨_, hw⟩
  let u : A := 1 - τ * w
  have hu : (u : Ω) = 1 - (p : Ω) / (T.ζ j - 1) * y := by
    simp only [u, τ, w, ζ', Subalgebra.coe_sub, Subalgebra.coe_mul, Subalgebra.coe_one]
    field_simp
  obtain ⟨hdom, hdvr, hirr⟩ := completed_laurent_isDVR p
  have hmax : IsLocalRing.maximalIdeal (O0 p) = Ideal.span {(p : O0 p)} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hirr

  have hτM : ∀ M : Ideal A, M.IsMaximal → τ ∈ M := by
    intro M hM
    have hc : (M.comap (algebraMap (O0 p) A)).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M
    have hpM : (p : A) ∈ M := by
      have h1 : M.comap (algebraMap (O0 p) A) = IsLocalRing.maximalIdeal (O0 p) :=
        IsLocalRing.eq_maximalIdeal hc
      have h2 : (p : O0 p) ∈ M.comap (algebraMap (O0 p) A) := by
        rw [h1, hmax]; exact Ideal.mem_span_singleton_self _
      simpa using h2
    haveI : M.IsPrime := hM.isPrime
    haveI : Nontrivial (A ⧸ M) := Ideal.Quotient.nontrivial_iff.2 hM.ne_top
    haveI : CharP (A ⧸ M) p := by
      rw [CharP.charP_iff_prime_eq_zero hp.out]
      rw [← map_natCast (Ideal.Quotient.mk M), Ideal.Quotient.eq_zero_iff_mem]; exact hpM
    have hζp : ζ' ^ (p ^ j) = 1 := Subtype.ext (by simp [ζ', (T.prim j).pow_eq_one])
    have h3 : (Ideal.Quotient.mk M τ) ^ (p ^ j) = 0 := by
      simp only [τ, map_sub, map_one]
      rw [sub_pow_char_pow, ← map_pow, hζp, map_one, one_pow, sub_self]
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact pow_eq_zero_iff (by omega) |>.1 h3
  have hunit : IsUnit u := by
    by_contra h
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (Ideal.span {u})
      (by rwa [Ne, Ideal.span_singleton_eq_top])
    have h1 : u ∈ M := hle (Ideal.mem_span_singleton_self _)
    have h2 : τ * w ∈ M := M.mul_mem_right _ (hτM M hM)
    have : (1 : A) ∈ M := by
      have := M.add_mem h1 h2; simpa [u] using this
    exact hM.ne_top ((Ideal.eq_top_iff_one _).2 this)
  obtain ⟨v, hv⟩ := hunit
  have hval : (u : Ω) * (((v⁻¹ : Aˣ) : A) : Ω) = 1 := by
    rw [← hv, ← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one]
  rw [← hu]
  refine ⟨left_ne_zero_of_mul_eq_one hval, ?_⟩
  rw [← eq_inv_of_mul_eq_one_right hval]
  exact ((v⁻¹ : Aˣ) : A).2

end GlobalTheory.K5
