import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IsClassFieldHilbert
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.Basic

open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

/- English proof (translation)
Use `haveI : NeZero d := ⟨hd.out.ne_zero⟩`. Establish `hζd : ζ ^ d = 1` using `hζ.pow_eq_one`. Set `χ : MulChar (ZMod d) K` to `(quadraticChar (ZMod d)).ringHomComp (Int.castRingHom K)`. Set `ψ : AddChar (ZMod d) K` to `AddChar.zmodChar d hζd`. Establish `hψp : ψ.IsPrimitive` using `AddChar.zmodChar_primitive_of_primitive_root d hζ`.

Establish `hchar : ringChar (ZMod d) ≠ 2` using `by rw [ZMod.ringChar_zmod_n]; exact hd2`. Establish `hχ1 : χ ≠ 1` using `(MulChar.ringHomComp_ne_one_iff (f := Int.castRingHom K) Int.cast_injective).2 (quadraticChar_ne_one hchar)`. Establish `hχq : χ.IsQuadratic` using `(quadraticChar_isQuadratic (ZMod d)).comp _`. Establish `hχa : ∀ a : ZMod d, χ a = ((quadraticChar (ZMod d) a : ℤ) : K)` using `fun a => by`. Simplify using `[χ, MulChar.ringHomComp_apply]`.

Establish `hψa : ∀ n : ℕ, ψ (n : ZMod d) = ζ ^ n` using `fun n => AddChar.zmodChar_apply' hζd n`. Use `⟨gaussSum χ ψ, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[gaussSum_sq hχ1 hχq hψp, hχa, ZMod.card]`. Establish `h1 : quadraticChar (ZMod d) (-1) = legendreSym d (-1)`. Simplify using `[legendreSym]`.

Rewrite using `[h1, legendreSym.at_neg_one hd2, ZMod.χ₄_nat_eq_if_mod_four, pStar]`. Establish `hodd : d % 2 = 1` using `hd.out.eq_two_or_odd.resolve_left hd2`. Establish `h4 : d % 4 = 1 ∨ d % 4 = 3` using `by omega`. Break down `h4 with h4 | h4` into its components or cases. Establish `he : Even (d / 2)` using `by rw [Nat.even_iff]; omega`.

Simplify using `[hodd, h4, he.neg_one_pow]`. Establish `ho : Odd (d / 2)` using `by rw [Nat.odd_iff]; omega`. Simplify using `[hodd, h4, ho.neg_one_pow]`. Unfold `gaussSum`. Use `IntermediateField.sum_mem _ fun a _ => IntermediateField.mul_mem _ ?_ ?_` and prove the remaining obligations.

Rewrite using `[hχa]`. Conclude with `IntermediateField.intCast_mem _ _`. Rewrite using `[← ZMod.natCast_zmod_val a, hψa]`. Conclude with `pow_mem (IntermediateField.mem_adjoin_simple_self ℚ ζ) _`. Introduce `σ b hσ`.

Establish `hG : σ (gaussSum χ ψ) = gaussSum χ (ψ.mulShift (b : ZMod d))`. Unfold `gaussSum`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, hχa, map_intCast, AddChar.mulShift_apply]`.

Use `congr 1`. Rewrite using `[← ZMod.natCast_zmod_val a, hψa, map_pow, hσ, ← pow_mul, ← Nat.cast_mul, hψa]`. Establish `hb : (b : ZMod d) ≠ 0`. Introduce `h0`. Establish `h1 : σ ζ = 1`.

Rewrite using `[hσ]`. Rewrite `h0` using `[ZMod.natCast_eq_zero_iff]`. Take `⟨k, rfl⟩` from `h0`. Rewrite using `[pow_mul, hζd, one_pow]`. Establish `h2 : ζ = 1` using `σ.injective (by rw [h1, map_one])`.

Conclude with `hζ.ne_one hd.out.one_lt h2`. Establish `hmul : χ (b : ZMod d) * gaussSum χ (ψ.mulShift (b : ZMod d)) = gaussSum χ ψ` using `gaussSum_mulShift χ ψ (Units.mk0 _ hb)`. Establish `hu2 : χ (b : ZMod d) * χ (b : ZMod d) = 1`. Rewrite using `[hχa, ← Int.cast_mul, ← sq, quadraticChar_sq_one hb, Int.cast_one]`. Establish `hleg : ((legendreSym d b : ℤ) : K) = χ (b : ZMod d)`.

Rewrite using `[hχa]`. Simplify using `[legendreSym]`. Rewrite using `[hG, hleg, ← hmul, ← mul_assoc, hu2, one_mul]`.
-/
private theorem UpperTheory.V.CF.exists_quadratic_gauss_sum {K : Type} [Field K] [CharZero K] {d : ℕ} [hd : Fact d.Prime]
    (hd2 : d ≠ 2) {ζ : K} (hζ : IsPrimitiveRoot ζ d) :
    ∃ G : K, G ^ 2 = (pStar d : ℤ) ∧ G ∈ ℚ⟮ζ⟯ ∧ ∀ (σ : K →+* K) (a : ℕ), σ ζ = ζ ^ a →
      σ G = (legendreSym d a : ℤ) * G := by
  classical
  haveI : NeZero d := ⟨hd.out.ne_zero⟩
  have hζd : ζ ^ d = 1 := hζ.pow_eq_one
  let χ : MulChar (ZMod d) K := (quadraticChar (ZMod d)).ringHomComp (Int.castRingHom K)
  let ψ : AddChar (ZMod d) K := AddChar.zmodChar d hζd
  have hψp : ψ.IsPrimitive := AddChar.zmodChar_primitive_of_primitive_root d hζ
  have hchar : ringChar (ZMod d) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hd2
  have hχ1 : χ ≠ 1 :=
    (MulChar.ringHomComp_ne_one_iff (f := Int.castRingHom K) Int.cast_injective).2
      (quadraticChar_ne_one hchar)
  have hχq : χ.IsQuadratic := (quadraticChar_isQuadratic (ZMod d)).comp _
  have hχa : ∀ a : ZMod d, χ a = ((quadraticChar (ZMod d) a : ℤ) : K) := fun a => by
    simp [χ, MulChar.ringHomComp_apply]
  have hψa : ∀ n : ℕ, ψ (n : ZMod d) = ζ ^ n := fun n => AddChar.zmodChar_apply' hζd n
  refine ⟨gaussSum χ ψ, ?_, ?_, ?_⟩
  · rw [gaussSum_sq hχ1 hχq hψp, hχa, ZMod.card]
    have h1 : quadraticChar (ZMod d) (-1) = legendreSym d (-1) := by
      simp [legendreSym]
    rw [h1, legendreSym.at_neg_one hd2, ZMod.χ₄_nat_eq_if_mod_four, pStar]
    have hodd : d % 2 = 1 := hd.out.eq_two_or_odd.resolve_left hd2
    have h4 : d % 4 = 1 ∨ d % 4 = 3 := by omega
    rcases h4 with h4 | h4
    · have he : Even (d / 2) := by rw [Nat.even_iff]; omega
      simp [hodd, h4, he.neg_one_pow]
    · have ho : Odd (d / 2) := by rw [Nat.odd_iff]; omega
      simp [hodd, h4, ho.neg_one_pow]
  · unfold gaussSum
    refine IntermediateField.sum_mem _ fun a _ => IntermediateField.mul_mem _ ?_ ?_
    · rw [hχa]; exact IntermediateField.intCast_mem _ _
    · rw [← ZMod.natCast_zmod_val a, hψa]
      exact pow_mem (IntermediateField.mem_adjoin_simple_self ℚ ζ) _
  · intro σ b hσ
    have hG : σ (gaussSum χ ψ) = gaussSum χ (ψ.mulShift (b : ZMod d)) := by
      unfold gaussSum
      rw [map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_mul, hχa, map_intCast, AddChar.mulShift_apply]
      congr 1
      rw [← ZMod.natCast_zmod_val a, hψa, map_pow, hσ, ← pow_mul, ← Nat.cast_mul, hψa]
    have hb : (b : ZMod d) ≠ 0 := by
      intro h0
      have h1 : σ ζ = 1 := by
        rw [hσ]
        rw [ZMod.natCast_eq_zero_iff] at h0
        obtain ⟨k, rfl⟩ := h0
        rw [pow_mul, hζd, one_pow]
      have h2 : ζ = 1 := σ.injective (by rw [h1, map_one])
      exact hζ.ne_one hd.out.one_lt h2
    have hmul : χ (b : ZMod d) * gaussSum χ (ψ.mulShift (b : ZMod d)) = gaussSum χ ψ :=
      gaussSum_mulShift χ ψ (Units.mk0 _ hb)
    have hu2 : χ (b : ZMod d) * χ (b : ZMod d) = 1 := by
      rw [hχa, ← Int.cast_mul, ← sq, quadraticChar_sq_one hb, Int.cast_one]
    have hleg : ((legendreSym d b : ℤ) : K) = χ (b : ZMod d) := by
      rw [hχa]; simp [legendreSym]
    rw [hG, hleg, ← hmul, ← mul_assoc, hu2, one_mul]

/- English proof (translation)
Introduce `K _ _ p _ ζ hp hζ`. Take `⟨G, hG, hmem, hσ⟩` from `UpperTheory.V.CF.exists_quadratic_gauss_sum hp hζ`. Use `⟨⟨G, hG⟩, fun x hx => ?_⟩` and prove the remaining obligations. Break down `sq_eq_sq_iff_eq_or_eq_neg.mp (hx.trans hG.symm) with rfl | rfl` into its components or cases. Conclude with `⟨hmem, hσ⟩`.

Use `⟨neg_mem hmem, fun σ b h => ?_⟩` and prove the remaining obligations. Rewrite using `[map_neg, hσ σ b h, mul_neg]`.
-/
theorem UpperTheory.V.CF.gauss :
    ∀ (K : Type) [Field K] [CharZero K] (p : ℕ) [Fact p.Prime] (ζ : K), p ≠ 2 → IsPrimitiveRoot ζ p → (∃ x : K, x ^ 2 = (pStar p : ℤ)) ∧ ∀ x : K, x ^ 2 = (pStar p : ℤ) → x ∈ ℚ⟮ζ⟯ ∧ ∀ (σ : K →+* K) (b : ℕ), σ ζ = ζ ^ b → σ x = (legendreSym p b : ℤ) * x := by
  intro K _ _ p _ ζ hp hζ
  obtain ⟨G, hG, hmem, hσ⟩ := UpperTheory.V.CF.exists_quadratic_gauss_sum hp hζ
  refine ⟨⟨G, hG⟩, fun x hx => ?_⟩
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hx.trans hG.symm) with rfl | rfl
  · exact ⟨hmem, hσ⟩
  · refine ⟨neg_mem hmem, fun σ b h => ?_⟩
    rw [map_neg, hσ σ b h, mul_neg]
