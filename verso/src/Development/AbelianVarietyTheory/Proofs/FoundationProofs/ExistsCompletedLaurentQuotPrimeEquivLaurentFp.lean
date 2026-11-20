import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IntegralLocallyConstCochainModPow
open GlobalTheory.K5

namespace GlobalTheory.K5

noncomputable def lauRed (p : ℕ) [Fact p.Prime] : Lau p →+* LaurentSeries (ZMod p) where
  toFun x := HahnSeries.map x (PadicInt.toZMod (p := p))
  map_one' := HahnSeries.map_one (PadicInt.toZMod (p := p)).toMonoidWithZeroHom
  map_mul' x y := HahnSeries.map_mul (PadicInt.toZMod (p := p)).toNonUnitalRingHom
  map_zero' := by ext n; simp
  map_add' x y := by ext n; simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lauRed_coeff (p : ℕ) [Fact p.Prime] (x : Lau p) (n : ℤ) :
    (lauRed p x).coeff n = PadicInt.toZMod (x.coeff n) := rfl

/- English proof (translation)
Introduce `y`. Use `⟨HahnSeries.map y (⟨fun a => ((ZMod.val a : ℕ) : ℤ_[p]), by simp⟩ : ZeroHom (ZMod p) ℤ_[p]), ?_⟩` and prove the remaining obligations. Use extensionality with `n`. Rewrite using `[lauRed_coeff]`. Use `show PadicInt.toZMod ((ZMod.val (y.coeff n) : ℕ) : ℤ_[p]) = _`.

Simplify using the standard rewrite rules.
-/
theorem lauRed_surjective (p : ℕ) [Fact p.Prime] : Function.Surjective (lauRed p) := by
  intro y
  refine ⟨HahnSeries.map y (⟨fun a => ((ZMod.val a : ℕ) : ℤ_[p]), by simp⟩ : ZeroHom (ZMod p) ℤ_[p]), ?_⟩
  ext n
  rw [lauRed_coeff]
  show PadicInt.toZMod ((ZMod.val (y.coeff n) : ℕ) : ℤ_[p]) = _
  simp

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`. Rewrite `hx` using `[RingHom.mem_ker]`. Establish `h : ∀ n, ∃ c : ℤ_[p], x.coeff n = (p : ℤ_[p]) * c`. Introduce `n`.

Establish `h1 : x.coeff n ∈ RingHom.ker (PadicInt.toZMod (p` using `p)) := by`. Rewrite using `[RingHom.mem_ker, ← lauRed_coeff, hx]`. Both sides reduce to the same expression. Rewrite `h1` using `[PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]`. Conclude with `h1`.

Use `choose c hc using h`. Establish `hp : (p : ℤ_[p]) ≠ 0` using `by exact_mod_cast (Fact.out : p.Prime).ne_zero`. Use `Ideal.mem_span_singleton.2 ⟨⟨c, x.isPWO_support.mono ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `n hn`. Rewrite using `[HahnSeries.mem_support, hc n]`.

Conclude with `mul_ne_zero hp hn`. Use extensionality with `n`. Rewrite using `[← nsmul_eq_mul, HahnSeries.coeff_nsmul, hc n]`. Simplify using the standard rewrite rules. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff] show lauRed p _ = 0`.

Rewrite using `[map_natCast]`. Use extensionality with `n`. Rewrite using `[← Nat.smul_one_eq_cast, HahnSeries.coeff_nsmul]`. Simplify using the standard rewrite rules.
-/
theorem ker_lauRed (p : ℕ) [Fact p.Prime] : RingHom.ker (lauRed p) = pI p := by
  apply le_antisymm
  · intro x hx
    rw [RingHom.mem_ker] at hx
    have h : ∀ n, ∃ c : ℤ_[p], x.coeff n = (p : ℤ_[p]) * c := by
      intro n
      have h1 : x.coeff n ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
        rw [RingHom.mem_ker, ← lauRed_coeff, hx]; rfl
      rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h1
      exact h1
    choose c hc using h
    have hp : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    refine Ideal.mem_span_singleton.2 ⟨⟨c, x.isPWO_support.mono ?_⟩, ?_⟩
    · intro n hn
      rw [HahnSeries.mem_support, hc n]
      exact mul_ne_zero hp hn
    · ext n
      rw [← nsmul_eq_mul, HahnSeries.coeff_nsmul, hc n]
      simp
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    show lauRed p _ = 0
    rw [map_natCast]
    ext n
    rw [← Nat.smul_one_eq_cast, HahnSeries.coeff_nsmul]
    simp

/- English proof (translation)
Establish `fg : (pI p).FG` using `Submodule.fg_span_singleton _`. Establish `hker` using `AdicCompletion.ker_evalOneₐ_eq_map (pI p) fg`. Establish `hsurj : Function.Surjective (AdicCompletion.evalOneₐ (pI p))`. Introduce `y`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective y`.

Conclude with `⟨algebraMap _ _ a, (AdicCompletion.evalOneₐ (pI p)).commutes a⟩`. Establish `hmap : (pI p).map (algebraMap (Lau p) (O0 p)) = Ideal.span {(p : O0 p)}`. Rewrite using `[Ideal.map_span, Set.image_singleton, map_natCast]`. Establish `h1 : Ideal.span {(p : O0 p)} = RingHom.ker (AdicCompletion.evalOneₐ (pI p)).toRingHom`. Rewrite using `[← hmap]`.

Conclude with `hker.symm`. Use `⟨(Ideal.quotEquivOfEq h1).trans ((RingHom.quotientKerEquivOfSurjective (f := (AdicCompletion.evalOneₐ (pI p)).toRingHom) hsurj).trans ((Ideal.quotEquivOfEq (ker_lauRed p).symm).trans (RingHom.quotientKerEquivOfSurjective (lauRed_surjective p)))), ?_⟩` and prove the remaining obligations. Simplify using `only [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]`. Establish `hq : (AdicCompletion.evalOneₐ (pI p)).toRingHom (qO p) = Ideal.Quotient.mk (pI p) (HahnSeries.single (1 : ℤ) (1 : ℤ_[p]))` using `(AdicCompletion.evalOneₐ (pI p)).commutes _`. Rewrite using `[hq, Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]`.

Use extensionality with `n`. Rewrite using `[lauRed_coeff]`. Distinguish the cases in `hn : n = 1`. Substitute `hn` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[HahnSeries.coeff_single_of_ne hn]`.
-/
theorem exists_completedLaurent_quot_prime_equiv_laurentFp (p : ℕ) [Fact p.Prime] : ∃ e : (O0 p ⧸ Ideal.span {(p : O0 p)}) ≃+* LaurentSeries (ZMod p),
    e (Ideal.Quotient.mk _ (qO p)) = HahnSeries.single (1 : ℤ) (1 : ZMod p) := by
  have fg : (pI p).FG := Submodule.fg_span_singleton _
  have hker := AdicCompletion.ker_evalOneₐ_eq_map (pI p) fg
  have hsurj : Function.Surjective (AdicCompletion.evalOneₐ (pI p)) := by
    intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨algebraMap _ _ a, (AdicCompletion.evalOneₐ (pI p)).commutes a⟩
  have hmap : (pI p).map (algebraMap (Lau p) (O0 p)) = Ideal.span {(p : O0 p)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have h1 : Ideal.span {(p : O0 p)} = RingHom.ker (AdicCompletion.evalOneₐ (pI p)).toRingHom := by
    rw [← hmap]; exact hker.symm
  refine ⟨(Ideal.quotEquivOfEq h1).trans
    ((RingHom.quotientKerEquivOfSurjective (f := (AdicCompletion.evalOneₐ (pI p)).toRingHom) hsurj).trans
      ((Ideal.quotEquivOfEq (ker_lauRed p).symm).trans
        (RingHom.quotientKerEquivOfSurjective (lauRed_surjective p)))), ?_⟩
  simp only [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]
  have hq : (AdicCompletion.evalOneₐ (pI p)).toRingHom (qO p) =
      Ideal.Quotient.mk (pI p) (HahnSeries.single (1 : ℤ) (1 : ℤ_[p])) :=
    (AdicCompletion.evalOneₐ (pI p)).commutes _
  rw [hq, Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]
  ext n
  rw [lauRed_coeff]
  by_cases hn : n = 1
  · subst hn; simp
  · simp [HahnSeries.coeff_single_of_ne hn]

end GlobalTheory.K5
