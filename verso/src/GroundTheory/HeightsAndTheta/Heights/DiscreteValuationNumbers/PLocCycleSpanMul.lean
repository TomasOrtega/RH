import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsLocalCoeffLocal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.MemDivSuppOfDivCycleNeZero
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MemMinimalPrimesIff
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1

noncomputable section

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Yhd1.mem_minimalPrimes_iff hz W`.
-/
theorem LocCycleSpanMul.mem_minimalPrimes_iff {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    {z : A} (hz : z ≠ 0) (W : Ideal A) :
    W ∈ (Ideal.span {z}).minimalPrimes ↔ W.IsPrime ∧ W.height = 1 ∧ z ∈ W :=
  _root_.UpperTheory.Reformulated.B.Yhd1.mem_minimalPrimes_iff hz W

/- English proof (translation)
Introduce `A _ _ _ x y hx hy W`. Distinguish the cases in `hP : W.IsPrime ∧ W.height = 1`. Take `⟨hp, h1⟩` from `hP`. Establish `key : ∀ z : A, z ≠ 0 → locCycle (Ideal.span {z}) W = ((locLen (A ⧸ Ideal.span {z}) ⟨W, hp⟩).toNat : ℤ) ∧ locLen (A ⧸ Ideal.span {z}) ⟨W, hp⟩ ≠ ⊤`. Introduce `z hz`.

Distinguish the cases in `hzW : z ∈ W`. Establish `hm : W ∈ (Ideal.span {z}).minimalPrimes` using `(LocCycleSpanMul.mem_minimalPrimes_iff hz W).mpr ⟨hp, h1, hzW⟩`. Use `⟨?_, locLen_ne_top hm⟩` and prove the remaining obligations. Unfold `locCycle`. Rewrite using `[dif_pos hm]`.

Both sides reduce to the same expression. Establish `hm : W ∉ (Ideal.span {z}).minimalPrimes` using `fun h => hzW ((LocCycleSpanMul.mem_minimalPrimes_iff hz W).mp h).2.2`. Establish `h0 : locLen (A ⧸ Ideal.span {z}) ⟨W, hp⟩ = 0`. Use `locLen_quot_eq_zero (V := (⊥ : Ideal A)) (g := z) ⟨W, hp⟩ hzW` as an intermediate fact. Rewrite `this` using `[bot_sup_eq]`. Then use the resulting hypothesis.

Use `⟨?_, by rw [h0]; exact ENat.zero_ne_top⟩` and prove the remaining obligations. Unfold `locCycle`. Rewrite using `[dif_neg hm, h0]`. Simplify using the standard rewrite rules. Take `⟨ex, fx⟩` from `key x hx`.

Take `⟨ey, fy⟩` from `key y hy`. Take `⟨exy, -⟩` from `key (x * y) (mul_ne_zero hx hy)`. Establish `hmul` using `locLen_mul (V := (⊥ : Ideal A)) Ideal.isPrime_bot (f := x) (by rw [Ideal.mem_bot]; exact hx) y ⟨W, hp⟩`. Rewrite `hmul` using `[bot_sup_eq, bot_sup_eq, bot_sup_eq]`. Rewrite using `[exy, ex, ey, hmul, ENat.toNat_add fy fx]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hz : ∀ z : A, z ≠ 0 → locCycle (Ideal.span {z}) W = 0`. Introduce `z hz`. Unfold `locCycle`.

Rewrite using `[dif_neg]`. Introduce `hm`. Establish `h` using `(LocCycleSpanMul.mem_minimalPrimes_iff hz W).mp hm`. Conclude with `hP ⟨h.1, h.2.1⟩`. Rewrite using `[hz _ (mul_ne_zero hx hy), hz x hx, hz y hy]`.

Simplify using the standard rewrite rules.
-/
theorem LocCycleSpanMul.proof : LocCycleSpanMul.Statement := by
  intro A _ _ _ x y hx hy W
  by_cases hP : W.IsPrime ∧ W.height = 1
  · obtain ⟨hp, h1⟩ := hP
    have key : ∀ z : A, z ≠ 0 →
        locCycle (Ideal.span {z}) W = ((locLen (A ⧸ Ideal.span {z}) ⟨W, hp⟩).toNat : ℤ) ∧
          locLen (A ⧸ Ideal.span {z}) ⟨W, hp⟩ ≠ ⊤ := by
      intro z hz
      by_cases hzW : z ∈ W
      · have hm : W ∈ (Ideal.span {z}).minimalPrimes :=
          (LocCycleSpanMul.mem_minimalPrimes_iff hz W).mpr ⟨hp, h1, hzW⟩
        refine ⟨?_, locLen_ne_top hm⟩
        unfold locCycle
        rw [dif_pos hm]
        rfl
      · have hm : W ∉ (Ideal.span {z}).minimalPrimes := fun h =>
          hzW ((LocCycleSpanMul.mem_minimalPrimes_iff hz W).mp h).2.2
        have h0 : locLen (A ⧸ Ideal.span {z}) ⟨W, hp⟩ = 0 := by
          have := locLen_quot_eq_zero (V := (⊥ : Ideal A)) (g := z) ⟨W, hp⟩ hzW
          rwa [bot_sup_eq] at this
        refine ⟨?_, by rw [h0]; exact ENat.zero_ne_top⟩
        unfold locCycle
        rw [dif_neg hm, h0]
        simp
    obtain ⟨ex, fx⟩ := key x hx
    obtain ⟨ey, fy⟩ := key y hy
    obtain ⟨exy, -⟩ := key (x * y) (mul_ne_zero hx hy)
    have hmul := locLen_mul (V := (⊥ : Ideal A)) Ideal.isPrime_bot (f := x)
      (by rw [Ideal.mem_bot]; exact hx) y ⟨W, hp⟩
    rw [bot_sup_eq, bot_sup_eq, bot_sup_eq] at hmul
    rw [exy, ex, ey, hmul, ENat.toNat_add fy fx]
    push_cast
    ring
  · have hz : ∀ z : A, z ≠ 0 → locCycle (Ideal.span {z}) W = 0 := by
      intro z hz
      unfold locCycle
      rw [dif_neg]
      intro hm
      have h := (LocCycleSpanMul.mem_minimalPrimes_iff hz W).mp hm
      exact hP ⟨h.1, h.2.1⟩
    rw [hz _ (mul_ne_zero hx hy), hz x hx, hz y hy]
    simp

end

end GroundTheory.Heights₂.Heights.NumbersDVR
