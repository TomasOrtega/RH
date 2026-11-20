import Mathlib

open Polynomial

namespace GlobalTheory.ResiduePowerFixed

/- English proof (translation)
Set `F` to `IntermediateField.adjoin (ZMod l) {y}`. Use `haveI : FiniteDimensional (ZMod l) F := IntermediateField.adjoin.finiteDimensional hy.isIntegral`. Use `haveI : Finite F := Module.finite_of_finite (ZMod l)`. Use `letI := Fintype.ofFinite F`. Use `haveI : CharP F l := charP_of_injective_algebraMap (algebraMap (ZMod l) F).injective l`.

Take `⟨n, -, hcard⟩` from `FiniteField.card F l`. Use `⟨n, n.pos, ?_⟩` and prove the remaining obligations. Establish `h` using `FiniteField.pow_card (⟨y, IntermediateField.mem_adjoin_simple_self _ y⟩ : F)`. Rewrite `h` using `[hcard]`. Simplify using `using congrArg Subtype.val h`.
-/
theorem pow_fixed_of_algebraic (l : ℕ) [Fact (Nat.Prime l)] {k : Type} [Field k]
    [Algebra (ZMod l) k] (y : k) (hy : IsAlgebraic (ZMod l) y) :
    ∃ N : ℕ, 0 < N ∧ y ^ l ^ N = y := by
  let F := IntermediateField.adjoin (ZMod l) {y}
  haveI : FiniteDimensional (ZMod l) F := IntermediateField.adjoin.finiteDimensional hy.isIntegral
  haveI : Finite F := Module.finite_of_finite (ZMod l)
  letI := Fintype.ofFinite F
  haveI : CharP F l := charP_of_injective_algebraMap (algebraMap (ZMod l) F).injective l
  obtain ⟨n, -, hcard⟩ := FiniteField.card F l
  refine ⟨n, n.pos, ?_⟩
  have h := FiniteField.pow_card (⟨y, IntermediateField.mem_adjoin_simple_self _ y⟩ : F)
  rw [hcard] at h
  simpa using congrArg Subtype.val h

/- English proof (translation)
Establish `hx' : IsAlgebraic ℤ x` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).mpr hx`. Take `⟨p, hp0, hp⟩` from `hx'`. Use `⟨p.primPart, p.isPrimitive_primPart, ?_⟩` and prove the remaining obligations. Establish `hc : algebraMap ℤ Ω p.content ≠ 0`. Rewrite using `[IsScalarTower.algebraMap_apply ℤ ℚ Ω]`.

Use `(_root_.map_ne_zero _).mpr ?_` and prove the remaining obligations. Establish `: p.content ≠ 0` using `Polynomial.content_eq_zero_iff.not.mpr hp0`. Rewrite using `[algebraMap_int_eq, eq_intCast]`. Conclude with `this` after adjusting the coercions. Rewrite `hp` using `[Polynomial.eq_C_content_mul_primPart p, map_mul, aeval_C]`.

Conclude with `(mul_eq_zero.mp hp).resolve_left hc`.
-/
theorem exists_primitive {Ω : Type} [Field Ω] [Algebra ℚ Ω] (x : Ω) (hx : IsAlgebraic ℚ x) :
    ∃ p : ℤ[X], p.IsPrimitive ∧ aeval x p = 0 := by
  have hx' : IsAlgebraic ℤ x := (IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).mpr hx
  obtain ⟨p, hp0, hp⟩ := hx'
  refine ⟨p.primPart, p.isPrimitive_primPart, ?_⟩
  have hc : algebraMap ℤ Ω p.content ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply ℤ ℚ Ω]
    refine (_root_.map_ne_zero _).mpr ?_
    have : p.content ≠ 0 := Polynomial.content_eq_zero_iff.not.mpr hp0
    rw [algebraMap_int_eq, eq_intCast]
    exact_mod_cast this
  rw [Polynomial.eq_C_content_mul_primPart p, map_mul, aeval_C] at hp
  exact (mul_eq_zero.mp hp).resolve_left hc

/- English proof (translation)
Establish `hlm : (l : A) ∈ IsLocalRing.maximalIdeal A`. Rewrite using `[ValuationSubring.valuation_lt_one_iff]`. Simplify using `using hl`. Establish `hl0 : ((l : ℕ) : IsLocalRing.ResidueField A) = 0`. Rewrite using `[← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff]`.

Conclude with `hlm`. Use `haveI hchar : CharP (IsLocalRing.ResidueField A) l := by`. Take `⟨q, hq⟩` from `CharP.exists (IsLocalRing.ResidueField A)`. Use `haveI := hq`. Establish `hdvd : q ∣ l` using `(CharP.cast_eq_zero_iff _ q l).mp hl0`.

Break down `(Fact.out : l.Prime).eq_one_or_self_of_dvd q hdvd with h1 | h1` into its components or cases. It suffices to derive a contradiction. Substitute `h1` using the available equality. Establish `h` using `(CharP.cast_eq_zero_iff (IsLocalRing.ResidueField A) 1 1).mpr dvd_rfl`. Establish `h' : (1 : IsLocalRing.ResidueField A) = 0`.

Rewrite using `[← Nat.cast_one]`. Conclude with `h`. Conclude with `one_ne_zero h'`. Substitute `h1` using the available equality. Conclude with `hq`.

Use `letI : Algebra (ZMod l) (IsLocalRing.ResidueField A) := ZMod.algebra _ l`. Apply `pow_fixed_of_algebraic l` to reduce the goal to its premises. Establish `hxalg : IsAlgebraic ℚ (xA : Ω)` using `Algebra.IsAlgebraic.isAlgebraic _`. Take `⟨p, hprim, hp⟩` from `exists_primitive (xA : Ω) hxalg`. Use `⟨p.map (Int.castRingHom (ZMod l)), ?_, ?_⟩` and prove the remaining obligations.

Introduce `h0`. Establish `hdvd : ∀ n, (l : ℤ) ∣ p.coeff n` using `fun n => by`. Establish `h` using `congrArg (fun q => Polynomial.coeff q n) h0`. Simplify using `only [Polynomial.coeff_map, Polynomial.coeff_zero, eq_intCast] at h`. Conclude with `(ZMod.intCast_zmod_eq_zero_iff_dvd _ l).mp h`.

Establish `hC : Polynomial.C (l : ℤ) ∣ p` using `(Polynomial.C_dvd_iff_dvd_coeff _ _).mpr hdvd`. Establish `hcont` using `Polynomial.dvd_content_iff_C_dvd.mpr hC`. Rewrite `hcont` using `[hprim.content_eq_one]`. Establish `h1` using `Int.eq_one_of_dvd_one (by positivity) hcont`. Conclude with `(Fact.out : l.Prime).one_lt.ne' (by exact_mod_cast h1)`.

Establish `hA : aeval xA p = 0`. Establish `h` using `Polynomial.aeval_algHom_apply (A.subtype.toIntAlgHom) xA p`. Establish `h2 : A.subtype.toIntAlgHom (aeval xA p) = 0`. Rewrite using `[← h]`. Conclude with `hp`.

Conclude with `Subtype.ext h2`. Establish `e : aeval (IsLocalRing.residue A xA) (p.map (Int.castRingHom (ZMod l))) = aeval (IsLocalRing.residue A xA) p`. Rewrite using `[Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_map]`. Use `congr 1`. Conclude with `RingHom.ext_int _ _`.

Rewrite using `[e]`. Rewrite using `[show IsLocalRing.residue A xA = (IsLocalRing.residue A).toIntAlgHom xA from rfl, Polynomial.aeval_algHom_apply, hA, map_zero]`.
-/
theorem residue_pow_fixed (l : ℕ) [Fact (Nat.Prime l)] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (hl : A.valuation (l : Ω) < 1) (xA : A) :
    ∃ N : ℕ, 0 < N ∧ IsLocalRing.residue A xA ^ l ^ N = IsLocalRing.residue A xA := by
  classical

  have hlm : (l : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [ValuationSubring.valuation_lt_one_iff]
    simpa using hl
  have hl0 : ((l : ℕ) : IsLocalRing.ResidueField A) = 0 := by
    rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff]
    exact hlm
  haveI hchar : CharP (IsLocalRing.ResidueField A) l := by
    obtain ⟨q, hq⟩ := CharP.exists (IsLocalRing.ResidueField A)
    haveI := hq
    have hdvd : q ∣ l := (CharP.cast_eq_zero_iff _ q l).mp hl0
    rcases (Fact.out : l.Prime).eq_one_or_self_of_dvd q hdvd with h1 | h1
    · exfalso
      subst h1
      have h := (CharP.cast_eq_zero_iff (IsLocalRing.ResidueField A) 1 1).mpr dvd_rfl
      have h' : (1 : IsLocalRing.ResidueField A) = 0 := by
        rw [← Nat.cast_one]
        exact h
      exact one_ne_zero h'
    · subst h1
      exact hq
  letI : Algebra (ZMod l) (IsLocalRing.ResidueField A) := ZMod.algebra _ l
  apply pow_fixed_of_algebraic l

  have hxalg : IsAlgebraic ℚ (xA : Ω) := Algebra.IsAlgebraic.isAlgebraic _
  obtain ⟨p, hprim, hp⟩ := exists_primitive (xA : Ω) hxalg
  refine ⟨p.map (Int.castRingHom (ZMod l)), ?_, ?_⟩
  · intro h0
    have hdvd : ∀ n, (l : ℤ) ∣ p.coeff n := fun n => by
      have h := congrArg (fun q => Polynomial.coeff q n) h0
      simp only [Polynomial.coeff_map, Polynomial.coeff_zero, eq_intCast] at h
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ l).mp h
    have hC : Polynomial.C (l : ℤ) ∣ p := (Polynomial.C_dvd_iff_dvd_coeff _ _).mpr hdvd
    have hcont := Polynomial.dvd_content_iff_C_dvd.mpr hC
    rw [hprim.content_eq_one] at hcont
    have h1 := Int.eq_one_of_dvd_one (by positivity) hcont
    exact (Fact.out : l.Prime).one_lt.ne' (by exact_mod_cast h1)
  · have hA : aeval xA p = 0 := by
      have h := Polynomial.aeval_algHom_apply (A.subtype.toIntAlgHom) xA p
      have h2 : A.subtype.toIntAlgHom (aeval xA p) = 0 := by
        rw [← h]
        exact hp
      exact Subtype.ext h2
    have e : aeval (IsLocalRing.residue A xA) (p.map (Int.castRingHom (ZMod l))) =
        aeval (IsLocalRing.residue A xA) p := by
      rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_map]
      congr 1
      exact RingHom.ext_int _ _
    rw [e]
    rw [show IsLocalRing.residue A xA = (IsLocalRing.residue A).toIntAlgHom xA from rfl,
      Polynomial.aeval_algHom_apply, hA, map_zero]

end GlobalTheory.ResiduePowerFixed
