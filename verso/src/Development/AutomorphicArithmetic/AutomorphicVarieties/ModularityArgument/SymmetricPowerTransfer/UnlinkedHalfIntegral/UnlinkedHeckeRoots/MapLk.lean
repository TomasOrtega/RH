import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnitFormC
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.EisCoef

open UpperTheory.V.Af UpperTheory.V.Sd

namespace UpperTheory.V.Z.Sym.Unl

/- English proof (translation)
Unfold `Lk`. Rewrite using `[map_div₀, map_pow, map_sub, map_one]`. Use `congr 1`. Conclude with `(Polynomial.aeval_algHom_apply (σ.toRingHom.toIntAlgHom) x (numL k)).symm`.
-/
private lemma map_Lk (σ : ℂ ≃+* ℂ) (k : ℕ) (x : ℂ) : σ (Lk k x) = Lk k (σ x) := by
  unfold Lk
  rw [map_div₀, map_pow, map_sub, map_one]
  congr 1
  exact (Polynomial.aeval_algHom_apply (σ.toRingHom.toIntAlgHom) x (numL k)).symm

/- English proof (translation)
Establish `hN : 0 < N` using `Nat.pos_of_ne_zero (NeZero.ne N)`. Establish `hpow : ∀ (m : ℕ) (c : ZMod N), (ZMod.stdAddChar ((m : ZMod N) * c) : ℂ) = (ZMod.stdAddChar c : ℂ) ^ m`. Introduce `m c`. Rewrite using `[← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]`. Establish `hone : (ZMod.stdAddChar (1 : ZMod N) : ℂ) ^ N = 1`.

Rewrite using `[← hpow, ZMod.natCast_self, zero_mul, AddChar.map_zero_eq_one]`. Establish `hz : IsPrimitiveRoot (ZMod.stdAddChar (1 : ZMod N) : ℂ) N`. Use `IsPrimitiveRoot.mk_of_lt _ hN hone fun l hl hlN h => ?_` and prove the remaining obligations. Establish `h1 : (ZMod.stdAddChar ((l : ZMod N) * 1) : ℂ) = ZMod.stdAddChar (0 : ZMod N)`. Rewrite using `[hpow, h, AddChar.map_zero_eq_one]`.

Establish `h2` using `ZMod.injective_stdAddChar h1`. Rewrite `h2` using `[mul_one, ZMod.natCast_eq_zero_iff]`. Conclude with `absurd (Nat.le_of_dvd hl h2) (by omega)`. Establish `hz'` using `hz.map_of_injective (f := σ) σ.injective`. Take `⟨i, -, hi⟩` from `hz.eq_pow_of_pow_eq_one hz'.pow_eq_one`.

Establish `hc : i.Coprime N`. Rewrite using `[← hz.pow_iff_coprime hN, hi]`. Conclude with `hz'`. Use `⟨ZMod.unitOfCoprime i hc, fun b => ?_⟩` and prove the remaining obligations. Take `⟨m, rfl⟩ : ∃ m : ℕ, (m : ZMod N) = b` from `⟨b.val, ZMod.natCast_zmod_val b⟩`.

Establish `e1 : (ZMod.stdAddChar (m : ZMod N) : ℂ) = (ZMod.stdAddChar (1 : ZMod N) : ℂ) ^ m`. Rewrite using `[← hpow, mul_one]`. Establish `e2 : (ZMod.stdAddChar ((i : ZMod N) * (m : ZMod N)) : ℂ) = (ZMod.stdAddChar (1 : ZMod N) : ℂ) ^ (i * m)`. Rewrite using `[← Nat.cast_mul, ← hpow, mul_one]`. Rewrite using `[ZMod.coe_unitOfCoprime, e1, e2, map_pow, ← hi, pow_mul]`.
-/
private lemma exists_unit (N : ℕ) [NeZero N] (σ : ℂ ≃+* ℂ) :
    ∃ s : (ZMod N)ˣ, ∀ b : ZMod N, σ (ZMod.stdAddChar b : ℂ) = (ZMod.stdAddChar ((s : ZMod N) * b) : ℂ) := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hpow : ∀ (m : ℕ) (c : ZMod N), (ZMod.stdAddChar ((m : ZMod N) * c) : ℂ) = (ZMod.stdAddChar c : ℂ) ^ m := by
    intro m c
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]
  have hone : (ZMod.stdAddChar (1 : ZMod N) : ℂ) ^ N = 1 := by
    rw [← hpow, ZMod.natCast_self, zero_mul, AddChar.map_zero_eq_one]
  have hz : IsPrimitiveRoot (ZMod.stdAddChar (1 : ZMod N) : ℂ) N := by
    refine IsPrimitiveRoot.mk_of_lt _ hN hone fun l hl hlN h => ?_
    have h1 : (ZMod.stdAddChar ((l : ZMod N) * 1) : ℂ) = ZMod.stdAddChar (0 : ZMod N) := by
      rw [hpow, h, AddChar.map_zero_eq_one]
    have h2 := ZMod.injective_stdAddChar h1
    rw [mul_one, ZMod.natCast_eq_zero_iff] at h2
    exact absurd (Nat.le_of_dvd hl h2) (by omega)
  have hz' := hz.map_of_injective (f := σ) σ.injective
  obtain ⟨i, -, hi⟩ := hz.eq_pow_of_pow_eq_one hz'.pow_eq_one
  have hc : i.Coprime N := by
    rw [← hz.pow_iff_coprime hN, hi]
    exact hz'
  refine ⟨ZMod.unitOfCoprime i hc, fun b => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, (m : ZMod N) = b := ⟨b.val, ZMod.natCast_zmod_val b⟩
  have e1 : (ZMod.stdAddChar (m : ZMod N) : ℂ) = (ZMod.stdAddChar (1 : ZMod N) : ℂ) ^ m := by
    rw [← hpow, mul_one]
  have e2 : (ZMod.stdAddChar ((i : ZMod N) * (m : ZMod N)) : ℂ) = (ZMod.stdAddChar (1 : ZMod N) : ℂ) ^ (i * m) := by
    rw [← Nat.cast_mul, ← hpow, mul_one]
  rw [ZMod.coe_unitOfCoprime, e1, e2, map_pow, ← hi, pow_mul]

end UpperTheory.V.Z.Sym.Unl

open UpperTheory.V.Af UpperTheory.V.Sd in
/- English proof (translation)
Introduce `N _ hN σ`. Take `⟨s, hs⟩` from `UpperTheory.V.Z.Sym.Unl.exists_unit N σ`. Use `⟨s, hs, fun k hk a n => ?_⟩` and prove the remaining obligations. Use `haveI : Fact (1 < N) := ⟨hN⟩`. Establish `ha : ((a : (ZMod N)ˣ) : ZMod N) ≠ 0` using `a.ne_zero`.

Establish `hsa : (((s * a : (ZMod N)ˣ)) : ZMod N) ≠ 0` using `(s * a).ne_zero`. Establish `hu : (((s * a : (ZMod N)ˣ)) : ZMod N) = (s : ZMod N) * a` using `Units.val_mul s a`. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Rewrite using `[(eisCoef N k hk _ hsa).1, (eisCoef N k hk _ ha).1, UpperTheory.V.Z.Sym.Unl.map_Lk, hs, hu]`. Rewrite using `[(eisCoef N k hk _ hsa).2 n hn, (eisCoef N k hk _ ha).2 n hn, map_sum]`.

Use `Finset.sum_congr rfl fun e _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul σ, map_pow σ, map_natCast σ, map_add σ, map_mul σ, map_pow σ, map_neg σ, map_one σ, hs, hs, hu]`. Simplify using `only [mul_assoc, mul_neg]`.
-/
theorem UpperTheory.V.Z.Sym.Unl.eisCj : UpperTheory.V.Z.Sym.Unl.EisCj := by
  intro N _ hN σ
  obtain ⟨s, hs⟩ := UpperTheory.V.Z.Sym.Unl.exists_unit N σ
  refine ⟨s, hs, fun k hk a n => ?_⟩
  haveI : Fact (1 < N) := ⟨hN⟩
  have ha : ((a : (ZMod N)ˣ) : ZMod N) ≠ 0 := a.ne_zero
  have hsa : (((s * a : (ZMod N)ˣ)) : ZMod N) ≠ 0 := (s * a).ne_zero
  have hu : (((s * a : (ZMod N)ˣ)) : ZMod N) = (s : ZMod N) * a := Units.val_mul s a
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [(eisCoef N k hk _ hsa).1, (eisCoef N k hk _ ha).1, UpperTheory.V.Z.Sym.Unl.map_Lk, hs, hu]
  · rw [(eisCoef N k hk _ hsa).2 n hn, (eisCoef N k hk _ ha).2 n hn, map_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [map_mul σ, map_pow σ, map_natCast σ, map_add σ, map_mul σ, map_pow σ, map_neg σ, map_one σ, hs, hs, hu]
    simp only [mul_assoc, mul_neg]
