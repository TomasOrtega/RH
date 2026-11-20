import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory

/- English proof (translation)
Take `⟨c, hc⟩ : ∃ c : k, c ^ l = w.coeff 0` from `⟨_, frobeniusEquiv_symm_pow_p k l _⟩`. Use `set a : WittVector l k := WittVector.teichmuller l c with ha`. Establish `h0 : ∀ i < 1, (w - a ^ l).coeff i = 0`. Introduce `i hi`. Take `rfl : i = 0` from `Nat.lt_one_iff.mp hi`.

Express the relevant statement in the definitionally equal form `WittVector.constantCoeff (w - a ^ l) = 0`. Rewrite using `[map_sub, map_pow]`. Express the relevant statement in the definitionally equal form `w.coeff 0 - (WittVector.teichmuller l c).coeff 0 ^ l = 0`. Rewrite using `[WittVector.teichmuller_coeff_zero, hc, sub_self]`. Establish `hV : w - a ^ l = WittVector.verschiebung ((w - a ^ l).shift 1)` using `WittVector.eq_iterate_verschiebung h0`.

Use `set y := (w - a ^ l).shift 1 with hy`. Use `set b := (WittVector.frobeniusEquiv l k).symm y with hb`. Establish `hFb : WittVector.frobenius b = y` using `(WittVector.frobeniusEquiv l k).apply_symm_apply y`. Use `⟨a, b, ?_⟩` and prove the remaining obligations. Establish `hVb : WittVector.verschiebung y = b * (l : WittVector l k)`.

Rewrite using `[← hFb, WittVector.verschiebung_frobenius]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem wittVector_exists_eq_pow_add_natCast_mul (l : ℕ) [Fact l.Prime] (k : Type) [CommRing k]
    [CharP k l] [PerfectRing k l] (w : WittVector l k) :
    ∃ a b : WittVector l k, w = a ^ l + (l : WittVector l k) * b := by

  obtain ⟨c, hc⟩ : ∃ c : k, c ^ l = w.coeff 0 := ⟨_, frobeniusEquiv_symm_pow_p k l _⟩
  set a : WittVector l k := WittVector.teichmuller l c with ha

  have h0 : ∀ i < 1, (w - a ^ l).coeff i = 0 := by
    intro i hi
    obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
    change WittVector.constantCoeff (w - a ^ l) = 0
    rw [map_sub, map_pow]
    change w.coeff 0 - (WittVector.teichmuller l c).coeff 0 ^ l = 0
    rw [WittVector.teichmuller_coeff_zero, hc, sub_self]
  have hV : w - a ^ l = WittVector.verschiebung ((w - a ^ l).shift 1) :=
    WittVector.eq_iterate_verschiebung h0

  set y := (w - a ^ l).shift 1 with hy
  set b := (WittVector.frobeniusEquiv l k).symm y with hb
  have hFb : WittVector.frobenius b = y := (WittVector.frobeniusEquiv l k).apply_symm_apply y
  refine ⟨a, b, ?_⟩
  have hVb : WittVector.verschiebung y = b * (l : WittVector l k) := by
    rw [← hFb, WittVector.verschiebung_frobenius]
  calc w = (w - a ^ l) + a ^ l := by ring
    _ = b * (l : WittVector l k) + a ^ l := by rw [hV, hVb]
    _ = a ^ l + (l : WittVector l k) * b := by ring

/- English proof (translation)
Introduce `l _ k _ _ _ C _ J hl hJ ω ω' h`. Establish `key : ∀ n : ℕ, ∀ w, ω w - ω' w ∈ J ^ (n + 1)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro w`.

Simplify using `using h w`. Consider the case `succ n ih`. Introduce `w`. Take `⟨a, b, rfl⟩` from `wittVector_exists_eq_pow_add_natCast_mul l k w`. Take `⟨d, hdJ, hda⟩ : ∃ d, d ∈ J ^ (n + 1) ∧ ω a = ω' a + d` from `⟨_, ih a, by ring⟩`.

Take `⟨r, hr⟩` from `exists_add_pow_prime_eq (Fact.out : l.Prime) (ω' a) d`. Establish `e : ω (a ^ l + (l : WittVector l k) * b) - ω' (a ^ l + (l : WittVector l k) * b) = d ^ l + (l : C) * (ω' a * d * r) + (l : C) * (ω b - ω' b)`. Simplify using `only [map_add, map_mul, map_pow, map_natCast]`. Rewrite using `[hda, hr]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Establish `hl2 : 2 ≤ l` using `(Fact.out : l.Prime).two_le`. Use `Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_` and prove the remaining obligations. Establish `hpow : d ^ l ∈ J ^ ((n + 1) * l)`. Rewrite using `[pow_mul]`.

Conclude with `Ideal.pow_mem_pow hdJ l`. Conclude with `Ideal.pow_le_pow_right (by nlinarith) hpow`. Rewrite using `[pow_succ']`. Conclude with `Ideal.mul_mem_mul hl (Ideal.mul_mem_right r _ (Ideal.mul_mem_left _ (ω' a) hdJ))`. Rewrite using `[pow_succ']`.

Conclude with `Ideal.mul_mem_mul hl (ih b)`. Use `RingHom.ext fun w => ?_` and prove the remaining obligations. Rewrite using `[← sub_eq_zero]`. Use `hJ.haus _ fun n => ?_` and prove the remaining obligations. Rewrite using `[SModEq.zero]`.

Establish `hn : ω w - ω' w ∈ J ^ n`. Consider the cases of `n with`. Consider the case `zero => simp`. Consider the case `succ n => exact key n w`. Simplify using `using Submodule.smul_mem_smul hn (Submodule.mem_top : (1 : C) ∈ ⊤)`.
-/
theorem wittVector_ringHom_eq_of_sub_mem : ∀ (l : ℕ) [Fact l.Prime] (k : Type) [CommRing k] [CharP k l] [PerfectRing k l] (C : Type) [CommRing C] (J : Ideal C), (l : C) ∈ J → IsHausdorff J C → ∀ ω ω' : WittVector l k →+* C, (∀ w, ω w - ω' w ∈ J) → ω = ω' := by
  intro l _ k _ _ _ C _ J hl hJ ω ω' h

  have key : ∀ n : ℕ, ∀ w, ω w - ω' w ∈ J ^ (n + 1) := by
    intro n
    induction n with
    | zero => intro w; simpa using h w
    | succ n ih =>
      intro w
      obtain ⟨a, b, rfl⟩ := wittVector_exists_eq_pow_add_natCast_mul l k w
      obtain ⟨d, hdJ, hda⟩ : ∃ d, d ∈ J ^ (n + 1) ∧ ω a = ω' a + d := ⟨_, ih a, by ring⟩
      obtain ⟨r, hr⟩ := exists_add_pow_prime_eq (Fact.out : l.Prime) (ω' a) d
      have e : ω (a ^ l + (l : WittVector l k) * b) - ω' (a ^ l + (l : WittVector l k) * b) =
          d ^ l + (l : C) * (ω' a * d * r) + (l : C) * (ω b - ω' b) := by
        simp only [map_add, map_mul, map_pow, map_natCast]
        rw [hda, hr]
        ring
      rw [e]
      have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
      refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_
      ·
        have hpow : d ^ l ∈ J ^ ((n + 1) * l) := by
          rw [pow_mul]
          exact Ideal.pow_mem_pow hdJ l
        exact Ideal.pow_le_pow_right (by nlinarith) hpow
      · rw [pow_succ']
        exact Ideal.mul_mem_mul hl (Ideal.mul_mem_right r _ (Ideal.mul_mem_left _ (ω' a) hdJ))
      · rw [pow_succ']
        exact Ideal.mul_mem_mul hl (ih b)

  refine RingHom.ext fun w => ?_
  rw [← sub_eq_zero]
  refine hJ.haus _ fun n => ?_
  rw [SModEq.zero]
  have hn : ω w - ω' w ∈ J ^ n := by
    cases n with
    | zero => simp
    | succ n => exact key n w
  simpa using Submodule.smul_mem_smul hn (Submodule.mem_top : (1 : C) ∈ ⊤)

end GlobalTheory
