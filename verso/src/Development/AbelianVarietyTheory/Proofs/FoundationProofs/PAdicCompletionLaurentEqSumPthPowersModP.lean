import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LaurentSeriesPadicExistsPthPowerCombinationStatement
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.K5

/- English proof (translation)
Rewrite using `[qO, ← map_pow, HahnSeries.single_pow]`. Simplify using the standard rewrite rules.
-/
theorem qO_pow_eq (p : ℕ) [Fact p.Prime] (j : ℕ) :
    qO p ^ j = algebraMap (Lau p) (O0 p) (HahnSeries.single (j : ℤ) (1 : ℤ_[p])) := by
  rw [qO, ← map_pow, HahnSeries.single_pow]
  simp

/- English proof (translation)
Establish `fg : (pI p).FG` using `Submodule.fg_span_singleton _`. Establish `hker` using `AdicCompletion.ker_evalOneₐ_eq_map (pI p) fg`. Take `⟨a, ha⟩` from `Ideal.Quotient.mk_surjective (AdicCompletion.evalOneₐ (pI p) x)`. Establish `hmem : x - algebraMap (Lau p) (O0 p) a ∈ RingHom.ker (AdicCompletion.evalOneₐ (pI p)).toRingHom`. Rewrite using `[RingHom.mem_ker]`.

Use `show AdicCompletion.evalOneₐ (pI p) (x - algebraMap (Lau p) (O0 p) a) = 0`. Rewrite using `[map_sub, (AdicCompletion.evalOneₐ (pI p)).commutes a]`. Use `show _ - Ideal.Quotient.mk (pI p) a = 0`. Rewrite using `[ha, sub_self]`. Establish `hmap : (pI p).map (algebraMap (Lau p) (O0 p)) = Ideal.span {(p : O0 p)}`.

Rewrite using `[Ideal.map_span, Set.image_singleton, map_natCast]`. Rewrite `hmem` using `[hker, hmap, Ideal.mem_span_singleton]`. Take `⟨z, hz⟩` from `hmem`. Conclude with `⟨a, z, by rw [← hz]; ring⟩`.
-/
theorem exists_lau_add_p_mul (p : ℕ) [Fact p.Prime] (x : O0 p) :
    ∃ (f : Lau p) (z : O0 p), x = algebraMap (Lau p) (O0 p) f + (p : O0 p) * z := by
  have fg : (pI p).FG := Submodule.fg_span_singleton _
  have hker := AdicCompletion.ker_evalOneₐ_eq_map (pI p) fg
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalOneₐ (pI p) x)
  have hmem : x - algebraMap (Lau p) (O0 p) a ∈
      RingHom.ker (AdicCompletion.evalOneₐ (pI p)).toRingHom := by
    rw [RingHom.mem_ker]
    show AdicCompletion.evalOneₐ (pI p) (x - algebraMap (Lau p) (O0 p) a) = 0
    rw [map_sub, (AdicCompletion.evalOneₐ (pI p)).commutes a]
    show _ - Ideal.Quotient.mk (pI p) a = 0
    rw [ha, sub_self]
  have hmap : (pI p).map (algebraMap (Lau p) (O0 p)) = Ideal.span {(p : O0 p)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  rw [hker, hmap, Ideal.mem_span_singleton] at hmem
  obtain ⟨z, hz⟩ := hmem
  exact ⟨a, z, by rw [← hz]; ring⟩

/- English proof (translation)
Take `⟨f, z, rfl⟩` from `exists_lau_add_p_mul p x`. Take `⟨g, h, hf⟩` from `GlobalTheory.T.laurentSeriesPadic_exists_pthPower_combination p f`. Use `⟨fun j => algebraMap (Lau p) (O0 p) (g j), algebraMap (Lau p) (O0 p) h + z, ?_⟩` and prove the remaining obligations. Rewrite using `[hf, map_add, map_sum, map_mul, map_natCast]`. Simplify using `only [map_mul, map_pow, qO_pow_eq]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_eq_sum_qO_pow_mul_pow_add_mul (p : ℕ) [Fact p.Prime] (x : O0 p) :
    ∃ (g : Fin p → O0 p) (h : O0 p), x = ∑ j : Fin p, qO p ^ (j : ℕ) * g j ^ p + (p : O0 p) * h := by
  obtain ⟨f, z, rfl⟩ := exists_lau_add_p_mul p x
  obtain ⟨g, h, hf⟩ := GlobalTheory.T.laurentSeriesPadic_exists_pthPower_combination p f
  refine ⟨fun j => algebraMap (Lau p) (O0 p) (g j), algebraMap (Lau p) (O0 p) h + z, ?_⟩
  rw [hf, map_add, map_sum, map_mul, map_natCast]
  simp only [map_mul, map_pow, qO_pow_eq]
  ring

end GlobalTheory.K5
