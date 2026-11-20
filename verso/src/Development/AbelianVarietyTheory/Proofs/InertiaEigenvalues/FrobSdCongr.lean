import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CstSApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusMapsDividedPowerSeriesGeneratorSetStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittTiltFrobeniusEqPowAddMulStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DividedPowerMonomialFrobeniusCongrPowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DividedPowerSeriesGeneratorSetEqSumAddMulStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DividedPowerSeriesSubringEqGeneratorSet

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

/- English proof (translation)
Introduce `l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t w`. Prove the components needed by the constructor for the conclusion. Use `⟨fun n => if n = 0 then w else 0, fun r => ?_, fun τ n => ?_⟩` and prove the remaining obligations. Use `(Set.finite_singleton 0).subset fun n hn => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `h0`.

Conclude with `hn (by simp [show n ≠ 0 from h0])`. Rewrite using `[cstS_apply, coeff_C]`. Distinguish the cases in `hn : n = 0`. Substitute `hn` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[hn]`. Use function extensionality and compare the values at `τ`. Express the relevant statement in the definitionally equal form `frob K l (cstS t K w (τ - 1)) = cstS t K (sigma l a w) τ`. Rewrite using `[cstS_apply, cstS_apply, emb_sigma, ← PowerSeries.algebraMap_eq (R := K)]`. Conclude with `(frob K l).commutes _`.
-/
theorem cstS_mem_frob : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ w : Wq l a, cstS t K w ∈ SdSet t K e ∧ frobTot K a l (cstS t K w) = cstS t K (sigma l a w) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t w
  constructor
  · refine ⟨fun n => if n = 0 then w else 0, fun r => ?_, fun τ n => ?_⟩
    · refine (Set.finite_singleton 0).subset fun n hn => ?_
      by_contra h0
      exact hn (by simp [show n ≠ 0 from h0])
    · rw [cstS_apply, coeff_C]
      by_cases hn : n = 0
      · subst hn; simp
      · simp [hn]
  · funext τ
    change frob K l (cstS t K w (τ - 1)) = cstS t K (sigma l a w) τ
    rw [cstS_apply, cstS_apply, emb_sigma, ← PowerSeries.algebraMap_eq (R := K)]
    exact (frob K l).commutes _

/- English proof (translation)
Introduce `l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t`. Establish `hclosed : ∀ F ∈ Sd t K e, F ∈ SdSet t K e` using `sdSet_closed l a e O K t`. Establish `memS : ∀ {F}, F ∈ SdSet t K e → F ∈ Sd t K e` using `fun h => Subring.subset_closure h`. Establish `hl0 : l ≠ 0` using `(Fact.out : l.Prime).ne_zero`. Set `G : (ZMod a → K⟦X⟧) → Prop` to `fun z => z ∈ Sd t K e ∧ ∃ B ∈ Sd t K e, frobTot K a l z = z ^ l + (l : ZMod a → K⟦X⟧) * B`.

Establish `gadd : ∀ x y, G x → G y → G (x + y)`. Introduce and unpack `x y ⟨hx, Bx, hBx, ex⟩ ⟨hy, By, hBy, ey⟩`. Take `⟨r, hr⟩` from `exists_add_pow_prime_eq (Fact.out : l.Prime) (⟨x, hx⟩ : Sd t K e) ⟨y, hy⟩`. Establish `hr'` using `congrArg Subtype.val hr`. Move the coercions through the operations in `at hr'`.

Use `⟨(Sd t K e).add_mem hx hy, Bx + By - x * y * r, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(Sd t K e).sub_mem ((Sd t K e).add_mem hBx hBy) ((Sd t K e).mul_mem ((Sd t K e).mul_mem hx hy) r.2)`. Rewrite using `[map_add, ex, ey, hr']`. Expand and normalize the polynomial expressions, which then agree. Establish `gmul : ∀ x y, G x → G y → G (x * y)`.

Introduce and unpack `x y ⟨hx, Bx, hBx, ex⟩ ⟨hy, By, hBy, ey⟩`. Use `⟨(Sd t K e).mul_mem hx hy, Bx * y ^ l + x ^ l * By + (l : ZMod a → K⟦X⟧) * Bx * By, ?_, ?_⟩` and prove the remaining obligations. Establish `hlS : (l : ZMod a → K⟦X⟧) ∈ Sd t K e` using `natCast_mem (Sd t K e) l`. Conclude with `(Sd t K e).add_mem ((Sd t K e).add_mem ((Sd t K e).mul_mem hBx ((Sd t K e).pow_mem hy l)) ((Sd t K e).mul_mem ((Sd t K e).pow_mem hx l) hBy)) ((Sd t K e).mul_mem ((Sd t K e).mul_mem hlS hBx) hBy)`. Rewrite using `[map_mul, ex, ey]`.

Expand and normalize the polynomial expressions, which then agree. Establish `gcst : ∀ w, G (cstS t K w)`. Introduce `w`. Take `⟨hm, hf⟩` from `cstS_mem_frob l a e O K t w`. Take `⟨x, hx⟩` from `GlobalTheory.T.wittTiltFrobenius_eq_pow_add_mul l a w`.

Use `⟨memS hm, cstS t K x, memS (cstS_mem_frob l a e O K t x).1, ?_⟩` and prove the remaining obligations. Rewrite using `[hf, hx, map_add, map_pow, map_mul, map_natCast]`. Establish `gdp : ∀ n, G (dpS a e n)`. Introduce `n`. Take `⟨hm, B, hB, eB⟩` from `GlobalTheory.T.dividedPowerMonomial_frobenius_congr_pow l a e O K t n`.

Conclude with `⟨memS hm, B, memS hB, eB⟩`. Establish `gsum : ∀ (N : ℕ) (v : ℕ → Wq l a), G (∑ n ∈ Finset.range N, cstS t K (v n) * dpS a e n)`. Introduce `N v`. Use `Finset.sum_induction _ G gadd ⟨(Sd t K e).zero_mem, 0, (Sd t K e).zero_mem, ?_⟩ fun n _ => gmul _ _ (gcst _) (gdp n)` and prove the remaining obligations. Rewrite using `[map_zero, zero_pow hl0, mul_zero, add_zero]`.

Introduce `F hF`. Use `⟨GlobalTheory.T.frobenius_maps_dividedPowerSeriesGeneratorSet l a e O K t F hF, ?_⟩` and prove the remaining obligations. Take `⟨N, v, y, hy, hFe⟩` from `GlobalTheory.T.dividedPowerSeriesGeneratorSet_eq_sum_add_mul l a e O K t F hF`. Take `⟨hg, Bg, hBg, eg⟩` from `gsum N v`. Use `set g := ∑ n ∈ Finset.range N, cstS t K (v n) * dpS a e n`.

Use `set L : ZMod a → K⟦X⟧ := (l : ZMod a → K⟦X⟧)`. Use `set Q := ∑ i ∈ Finset.range l, (g + L * y) ^ i * g ^ (l - 1 - i)`. Establish `hQ : Q ∈ Sd t K e` using `(Sd t K e).sum_mem fun i _ => (Sd t K e).mul_mem ((Sd t K e).pow_mem ((Sd t K e).add_mem hg ((Sd t K e).mul_mem (natCast_mem (Sd t K e) l) (memS hy))) i) ((Sd t K e).pow_mem hg _)`. Establish `geo : (g + L * y) ^ l = g ^ l + L * (y * Q)`. Establish `h` using `geom_sum₂_mul (g + L * y) g l`.

Take the linear combination `-h`. Use `⟨Bg + frobTot K a l y - y * Q, hclosed _ ((Sd t K e).sub_mem ((Sd t K e).add_mem hBg (memS (GlobalTheory.T.frobenius_maps_dividedPowerSeriesGeneratorSet l a e O K t y hy))) ((Sd t K e).mul_mem (memS hy) hQ)), ?_⟩` and prove the remaining obligations. Rewrite using `[hFe, map_add, map_mul, map_natCast]`. Take the linear combination `eg - geo`.
-/
theorem frob_sd_congr : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ F ∈ SdSet t K e, (frobTot K a l) F ∈ SdSet t K e ∧ ∃ B ∈ SdSet t K e, (frobTot K a l) F = F ^ l + (l : ZMod a → K⟦X⟧) * B := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t
  have hclosed : ∀ F ∈ Sd t K e, F ∈ SdSet t K e := sdSet_closed l a e O K t
  have memS : ∀ {F}, F ∈ SdSet t K e → F ∈ Sd t K e := fun h => Subring.subset_closure h
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  let G : (ZMod a → K⟦X⟧) → Prop := fun z => z ∈ Sd t K e ∧
    ∃ B ∈ Sd t K e, frobTot K a l z = z ^ l + (l : ZMod a → K⟦X⟧) * B
  have gadd : ∀ x y, G x → G y → G (x + y) := by
    rintro x y ⟨hx, Bx, hBx, ex⟩ ⟨hy, By, hBy, ey⟩
    obtain ⟨r, hr⟩ := exists_add_pow_prime_eq (Fact.out : l.Prime) (⟨x, hx⟩ : Sd t K e) ⟨y, hy⟩
    have hr' := congrArg Subtype.val hr
    push_cast at hr'
    refine ⟨(Sd t K e).add_mem hx hy, Bx + By - x * y * r, ?_, ?_⟩
    · exact (Sd t K e).sub_mem ((Sd t K e).add_mem hBx hBy) ((Sd t K e).mul_mem ((Sd t K e).mul_mem hx hy) r.2)
    · rw [map_add, ex, ey, hr']; ring
  have gmul : ∀ x y, G x → G y → G (x * y) := by
    rintro x y ⟨hx, Bx, hBx, ex⟩ ⟨hy, By, hBy, ey⟩
    refine ⟨(Sd t K e).mul_mem hx hy, Bx * y ^ l + x ^ l * By + (l : ZMod a → K⟦X⟧) * Bx * By, ?_, ?_⟩
    · have hlS : (l : ZMod a → K⟦X⟧) ∈ Sd t K e := natCast_mem (Sd t K e) l
      exact (Sd t K e).add_mem ((Sd t K e).add_mem ((Sd t K e).mul_mem hBx ((Sd t K e).pow_mem hy l))
        ((Sd t K e).mul_mem ((Sd t K e).pow_mem hx l) hBy)) ((Sd t K e).mul_mem ((Sd t K e).mul_mem hlS hBx) hBy)
    · rw [map_mul, ex, ey]; ring
  have gcst : ∀ w, G (cstS t K w) := by
    intro w
    obtain ⟨hm, hf⟩ := cstS_mem_frob l a e O K t w
    obtain ⟨x, hx⟩ := GlobalTheory.T.wittTiltFrobenius_eq_pow_add_mul l a w
    refine ⟨memS hm, cstS t K x, memS (cstS_mem_frob l a e O K t x).1, ?_⟩
    rw [hf, hx, map_add, map_pow, map_mul, map_natCast]
  have gdp : ∀ n, G (dpS a e n) := by
    intro n
    obtain ⟨hm, B, hB, eB⟩ := GlobalTheory.T.dividedPowerMonomial_frobenius_congr_pow l a e O K t n
    exact ⟨memS hm, B, memS hB, eB⟩
  have gsum : ∀ (N : ℕ) (v : ℕ → Wq l a), G (∑ n ∈ Finset.range N, cstS t K (v n) * dpS a e n) := by
    intro N v
    refine Finset.sum_induction _ G gadd ⟨(Sd t K e).zero_mem, 0, (Sd t K e).zero_mem, ?_⟩ fun n _ => gmul _ _ (gcst _) (gdp n)
    rw [map_zero, zero_pow hl0, mul_zero, add_zero]
  intro F hF
  refine ⟨GlobalTheory.T.frobenius_maps_dividedPowerSeriesGeneratorSet l a e O K t F hF, ?_⟩
  obtain ⟨N, v, y, hy, hFe⟩ := GlobalTheory.T.dividedPowerSeriesGeneratorSet_eq_sum_add_mul l a e O K t F hF
  obtain ⟨hg, Bg, hBg, eg⟩ := gsum N v
  set g := ∑ n ∈ Finset.range N, cstS t K (v n) * dpS a e n
  set L : ZMod a → K⟦X⟧ := (l : ZMod a → K⟦X⟧)
  set Q := ∑ i ∈ Finset.range l, (g + L * y) ^ i * g ^ (l - 1 - i)
  have hQ : Q ∈ Sd t K e := (Sd t K e).sum_mem fun i _ => (Sd t K e).mul_mem
    ((Sd t K e).pow_mem ((Sd t K e).add_mem hg ((Sd t K e).mul_mem (natCast_mem (Sd t K e) l) (memS hy))) i)
    ((Sd t K e).pow_mem hg _)
  have geo : (g + L * y) ^ l = g ^ l + L * (y * Q) := by
    have h := geom_sum₂_mul (g + L * y) g l
    linear_combination -h
  refine ⟨Bg + frobTot K a l y - y * Q, hclosed _ ((Sd t K e).sub_mem ((Sd t K e).add_mem hBg
    (memS (GlobalTheory.T.frobenius_maps_dividedPowerSeriesGeneratorSet l a e O K t y hy))) ((Sd t K e).mul_mem (memS hy) hQ)), ?_⟩
  rw [hFe, map_add, map_mul, map_natCast]
  linear_combination eg - geo

end GlobalTheory.CrysPrism
