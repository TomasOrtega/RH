import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExpTwoPiIRatInFieldRootsOfUnityPropertiesStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.ZetaExp

/- English proof (translation)
Use `conv_rhs => rw [← Nat.mod_add_div a N, pow_add, pow_mul, h, one_pow, mul_one]`.
-/
theorem pow_mod_eq {M : Type*} [Monoid M] {w : M} {N : ℕ} (h : w ^ N = 1) (a : ℕ) : w ^ (a % N) = w ^ a := by
  conv_rhs => rw [← Nat.mod_add_div a N, pow_add, pow_mul, h, one_pow, mul_one]

/- English proof (translation)
Rewrite using `[ch, ← Complex.exp_nat_mul]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ch_eq_pow (N : ℕ) (j : ZMod N) :
    ch N j = Complex.exp (2 * Real.pi * Complex.I * (((1 : ℚ) / N : ℚ) : ℂ)) ^ j.val := by
  rw [ch, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/- English proof (translation)
Introduce `Ω _ _ _ ε s N hN`. Use `haveI : NeZero N := ⟨hN.ne'⟩`. Take `⟨_, hval, _, _, hprim, _⟩` from `GlobalTheory.T.expTwoPiIRatInField_roots_of_unity_properties Ω ε`. Use `set ζ := eOm ε (1 / N) with hζ`. Establish `hp : IsPrimitiveRoot ζ N` using `hprim N hN`.

Establish `hsp : IsPrimitiveRoot (s ζ) N` using `hp.map_of_injective s.injective`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Take `⟨i, -, hi⟩` from `hp.eq_pow_of_pow_eq_one hsp.pow_eq_one`. Conclude with `⟨i, by rw [← hi, zpow_natCast]⟩`. Introduce `d hd set i : ℕ := (d % (N : ℤ)).toNat with hi`.

Establish `hnn : 0 ≤ d % (N : ℤ)` using `Int.emod_nonneg _ (by exact_mod_cast hN.ne')`. Establish `hic : (i : ℤ) = d % (N : ℤ)` using `Int.toNat_of_nonneg hnn`. Establish `hζi : ζ ^ d = ζ ^ i`. Rewrite using `[← zpow_natCast, hic]`. Establish `hz : ζ ≠ 0` using `hp.ne_zero hN.ne'`.

Use `conv_lhs => rw [← Int.mul_ediv_add_emod d N, zpow_add₀ hz, zpow_mul, zpow_natCast, hp.pow_eq_one, one_zpow, one_mul]`. Establish `hsi : s ζ = ζ ^ i` using `hd.trans hζi`. Establish `hcop : i.Coprime N` using `(hp.pow_iff_coprime hN i).1 (hsi ▸ hsp)`. Establish `hdi : ((d : ZMod N)) = (i : ZMod N)`. Rewrite using `[← Int.cast_natCast, hic, ZMod.intCast_mod]`.

Establish `hu : IsUnit (i : ZMod N)` using `(ZMod.isUnit_iff_coprime i N).2 hcop`. Use `⟨hu.unit, by rw [IsUnit.unit_spec, hdi], ?_⟩` and prove the remaining obligations. Introduce `g hg j`. Establish `hεζ : ε ζ = Complex.exp (2 * Real.pi * Complex.I * (((1 : ℚ) / N : ℚ) : ℂ))` using `hval _`. Establish `hηN : (ε ζ) ^ N = 1` using `by rw [← map_pow, hp.pow_eq_one, map_one]`.

Establish `hl : g ((ε ζ) ^ j.val) = (ε ζ) ^ (i * j.val)`. Rewrite using `[map_pow, hg, hsi, map_pow, ← pow_mul]`. Establish `hr : ((i : ZMod N) * j).val = (i * j.val) % N`. Rewrite using `[ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod]`. Rewrite using `[ch_eq_pow, ch_eq_pow, ← hεζ, hl, IsUnit.unit_spec, hr, pow_mod_eq hηN]`.
-/
theorem main : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (s : Ω ≃ₐ[ℚ] Ω) (N : ℕ), 0 < N → (∃ d : ℤ, s (eOm ε (1 / N)) = eOm ε (1 / N) ^ d) ∧ ∀ d : ℤ, s (eOm ε (1 / N)) = eOm ε (1 / N) ^ d → ∃ u : (ZMod N)ˣ, (u : ZMod N) = d ∧ ∀ g : ℂ ≃+* ℂ, (∀ x, g (ε x) = ε (s x)) → ZetaAct g N u := by
  intro Ω _ _ _ ε s N hN
  haveI : NeZero N := ⟨hN.ne'⟩
  obtain ⟨_, hval, _, _, hprim, _⟩ := GlobalTheory.T.expTwoPiIRatInField_roots_of_unity_properties Ω ε
  set ζ := eOm ε (1 / N) with hζ
  have hp : IsPrimitiveRoot ζ N := hprim N hN
  have hsp : IsPrimitiveRoot (s ζ) N := hp.map_of_injective s.injective
  refine ⟨?_, ?_⟩
  · obtain ⟨i, -, hi⟩ := hp.eq_pow_of_pow_eq_one hsp.pow_eq_one
    exact ⟨i, by rw [← hi, zpow_natCast]⟩
  · intro d hd
    set i : ℕ := (d % (N : ℤ)).toNat with hi
    have hnn : 0 ≤ d % (N : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hN.ne')
    have hic : (i : ℤ) = d % (N : ℤ) := Int.toNat_of_nonneg hnn
    have hζi : ζ ^ d = ζ ^ i := by
      rw [← zpow_natCast, hic]
      have hz : ζ ≠ 0 := hp.ne_zero hN.ne'
      conv_lhs => rw [← Int.mul_ediv_add_emod d N, zpow_add₀ hz, zpow_mul, zpow_natCast, hp.pow_eq_one, one_zpow, one_mul]
    have hsi : s ζ = ζ ^ i := hd.trans hζi
    have hcop : i.Coprime N := (hp.pow_iff_coprime hN i).1 (hsi ▸ hsp)
    have hdi : ((d : ZMod N)) = (i : ZMod N) := by
      rw [← Int.cast_natCast, hic, ZMod.intCast_mod]
    have hu : IsUnit (i : ZMod N) := (ZMod.isUnit_iff_coprime i N).2 hcop
    refine ⟨hu.unit, by rw [IsUnit.unit_spec, hdi], ?_⟩
    intro g hg j
    have hεζ : ε ζ = Complex.exp (2 * Real.pi * Complex.I * (((1 : ℚ) / N : ℚ) : ℂ)) := hval _
    have hηN : (ε ζ) ^ N = 1 := by rw [← map_pow, hp.pow_eq_one, map_one]
    have hl : g ((ε ζ) ^ j.val) = (ε ζ) ^ (i * j.val) := by
      rw [map_pow, hg, hsi, map_pow, ← pow_mul]
    have hr : ((i : ZMod N) * j).val = (i * j.val) % N := by
      rw [ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod]
    rw [ch_eq_pow, ch_eq_pow, ← hεζ, hl, IsUnit.unit_spec, hr, pow_mod_eq hηN]

end GlobalTheory.ZetaExp
