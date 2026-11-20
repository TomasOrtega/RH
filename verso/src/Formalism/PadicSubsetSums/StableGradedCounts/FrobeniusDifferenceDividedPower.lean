import Formalism.PadicSubsetSums.CentralIdempotents.ArchimedeanComponents
import Formalism.PadicSubsetSums.StableGradedCounts.ARCReuse

namespace Formalism.IrreducibleCountingLemmas.WindowSums

open Polynomial

/- English proof (translation)
Introduce `l hl h4 F _ ζ hζ`. Use `Fact.mk hl` as an intermediate fact. Distinguish the cases in `h2 : (2 : F) = 0`. Establish `h1 : (l : F) = 1`. Take `⟨k, hk⟩ : ∃ k, l = 2 * k + 1` from `⟨l / 2, by omega⟩`.

Rewrite using `[hk]`. Use `push_cast`. Rewrite using `[h2]`. Expand and normalize the polynomial expressions, which then agree. Establish `hneg : (-1 : F) = 1` using `by linear_combination -h2`.

Rewrite using `[h1, hneg]`. Conclude with `IsSquare.one`. Establish `hchar : ringChar (ZMod l) ≠ 2` using `by rw [ZMod.ringChar_zmod_n]; omega`. Establish `hm1 : quadraticChar (ZMod l) (-1) = -1`. Rewrite using `[quadraticChar_neg_one hchar, ZMod.card, ZMod.χ₄_nat_three_mod_four h4]`.

Establish `hχm1 : ((quadraticChar (ZMod l)).ringHomComp (Int.castRingHom F)) (-1) = -1`. Simplify using `[MulChar.ringHomComp_apply, hm1]`. Establish `hχ1 : (quadraticChar (ZMod l)).ringHomComp (Int.castRingHom F) ≠ 1`. Introduce `h`. Rewrite `hχm1` using `[h, MulChar.one_apply (isUnit_one.neg)]`.

Apply `h2` to reduce the goal to its premises. Take the linear combination `hχm1`. Establish `hq : ((quadraticChar (ZMod l)).ringHomComp (Int.castRingHom F)).IsQuadratic` using `(quadraticChar_isQuadratic (ZMod l)).comp _`. Establish `hψ` using `AddChar.zmodChar_primitive_of_primitive_root l hζ`. Establish `hsq` using `gaussSum_sq hχ1 hq hψ`.

Rewrite `hsq` using `[hχm1, ZMod.card]`. Conclude with `⟨gaussSum _ _, by rw [← sq, hsq]; ring⟩`.
-/
theorem sqrt_neg_in_cyclotomic_field : SqrtNegInCyclotomic := by
  intro l hl h4 F _ ζ hζ
  have := Fact.mk hl
  by_cases h2 : (2 : F) = 0
  · have h1 : (l : F) = 1 := by
      obtain ⟨k, hk⟩ : ∃ k, l = 2 * k + 1 := ⟨l / 2, by omega⟩
      rw [hk]; push_cast; rw [h2]; ring
    have hneg : (-1 : F) = 1 := by linear_combination -h2
    rw [h1, hneg]; exact IsSquare.one
  · have hchar : ringChar (ZMod l) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
    have hm1 : quadraticChar (ZMod l) (-1) = -1 := by
      rw [quadraticChar_neg_one hchar, ZMod.card, ZMod.χ₄_nat_three_mod_four h4]
    have hχm1 : ((quadraticChar (ZMod l)).ringHomComp (Int.castRingHom F)) (-1) = -1 := by
      simp [MulChar.ringHomComp_apply, hm1]
    have hχ1 : (quadraticChar (ZMod l)).ringHomComp (Int.castRingHom F) ≠ 1 := by
      intro h
      rw [h, MulChar.one_apply (isUnit_one.neg)] at hχm1
      apply h2; linear_combination hχm1
    have hq : ((quadraticChar (ZMod l)).ringHomComp (Int.castRingHom F)).IsQuadratic :=
      (quadraticChar_isQuadratic (ZMod l)).comp _
    have hψ := AddChar.zmodChar_primitive_of_primitive_root l hζ
    have hsq := gaussSum_sq hχ1 hq hψ
    rw [hχm1, ZMod.card] at hsq
    exact ⟨gaussSum _ _, by rw [← sq, hsq]; ring⟩

end Formalism.IrreducibleCountingLemmas.WindowSums
