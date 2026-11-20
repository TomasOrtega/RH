import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsAvoidOne
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum

set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

/- English proof (translation)
Proceed by induction on `cs with`. Consider the case `nil => exact hg`. Consider the case `cons c cs ih`. Introduce `m`. Take `⟨z1, h1⟩` from `ih (m + Pi.single c 1)`.

Take `⟨z2, h2⟩` from `ih m`. Use `⟨z1 - z2, ?_⟩` and prove the remaining obligations. Use `show DL cs g (m + Pi.single c 1) - DL cs g m = ((z1 - z2 : ℤ) : ℂ)`. Rewrite using `[h1, h2]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem DL_int_valued {r : ℕ} (g : (Fin r → ℕ) → ℂ) (hg : ∀ m, ∃ z : ℤ, g m = (z : ℂ))
    (cs : List (Fin r)) : ∀ m, ∃ z : ℤ, DL cs g m = (z : ℂ) := by
  induction cs with
  | nil => exact hg
  | cons c cs ih =>
    intro m
    obtain ⟨z1, h1⟩ := ih (m + Pi.single c 1)
    obtain ⟨z2, h2⟩ := ih m
    refine ⟨z1 - z2, ?_⟩
    show DL cs g (m + Pi.single c 1) - DL cs g m = ((z1 - z2 : ℤ) : ℂ)
    rw [h1, h2]
    push_cast
    ring

/- English proof (translation)
Unfold `coneTerm`. Rewrite using `[Complex.ofReal_prod]`. Use `Finset.prod_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[neg_neg, Complex.cpow_natCast, Complex.ofReal_pow]`.
-/
theorem coneTerm_neg_nat {ι : Type} [Fintype ι] {r : ℕ} (a : ι → Fin r → ℝ) (b : ι → ℝ) (p : ℕ)
    (m : Fin r → ℕ) :
    coneTerm a b (-(p : ℂ)) m = ((∏ j, (b j + ∑ i, a j i * (m i : ℝ)) ^ p : ℝ) : ℂ) := by
  unfold coneTerm
  rw [Complex.ofReal_prod]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [neg_neg, Complex.cpow_natCast, Complex.ofReal_pow]

/- English proof (translation)
Establish `hmem : ((l : ℂ) ^ K) * ∑' m, f m ∈ Set.range (Int.cast : ℤ → ℂ)`. Distinguish the cases in `hs : Summable f`. Rewrite using `[← tsum_mul_left]`. Establish `hs' : Summable (fun m => (l : ℂ) ^ K * f m)` using `hs.mul_left _`. Apply `Complex.isClosed_range_intCast.mem_of_tendsto hs'.hasSum` to reduce the goal to its premises.

Use `Filter.Eventually.of_forall (fun S => ?_)` and prove the remaining obligations. Use `choose x hx using hf`. Conclude with `⟨∑ b ∈ S, x b, by push_cast; exact Finset.sum_congr rfl (fun b _ => (hx b).symm)⟩`. Rewrite using `[tsum_eq_zero_of_not_summable hs, mul_zero]`. Conclude with `⟨0, by simp⟩`.

Take `⟨z, hz⟩` from `hmem`. Establish `hlC : ((l : ℂ) ^ K) ≠ 0` using `pow_ne_zero _ (Nat.cast_ne_zero.mpr hl.ne')`. Establish `hlQ : ((l : ℚ) ^ K) ≠ 0` using `pow_ne_zero _ (Nat.cast_ne_zero.mpr hl.ne')`. Use `⟨(z : ℚ) / (l : ℚ) ^ K, z, ?_, ?_⟩` and prove the remaining obligations. Use `push_cast`.

Rewrite using `[hz]`. Conclude with `(mul_div_cancel_left₀ (∑' m, f m) hlC).symm`. Rewrite using `[mul_div_assoc']`. Conclude with `mul_div_cancel_left₀ _ hlQ`.
-/
theorem tsum_mem_of_denominator {α : Type} (f : α → ℂ) (K l : ℕ) (hl : 0 < l)
    (hf : ∀ m, ∃ x : ℤ, ((l : ℂ) ^ K) * f m = (x : ℂ)) :
    ∃ (q : ℚ) (z : ℤ), ∑' m, f m = (q : ℂ) ∧ (l : ℚ) ^ K * q = z := by
  have hmem : ((l : ℂ) ^ K) * ∑' m, f m ∈ Set.range (Int.cast : ℤ → ℂ) := by
    by_cases hs : Summable f
    · rw [← tsum_mul_left]
      have hs' : Summable (fun m => (l : ℂ) ^ K * f m) := hs.mul_left _
      apply Complex.isClosed_range_intCast.mem_of_tendsto hs'.hasSum
      refine Filter.Eventually.of_forall (fun S => ?_)
      choose x hx using hf
      exact ⟨∑ b ∈ S, x b, by push_cast; exact Finset.sum_congr rfl (fun b _ => (hx b).symm)⟩
    · rw [tsum_eq_zero_of_not_summable hs, mul_zero]
      exact ⟨0, by simp⟩
  obtain ⟨z, hz⟩ := hmem
  have hlC : ((l : ℂ) ^ K) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hl.ne')
  have hlQ : ((l : ℚ) ^ K) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hl.ne')
  refine ⟨(z : ℚ) / (l : ℚ) ^ K, z, ?_, ?_⟩
  · push_cast
    rw [hz]
    exact (mul_div_cancel_left₀ (∑' m, f m) hlC).symm
  · rw [mul_div_assoc']
    exact mul_div_cancel_left₀ _ hlQ

/- English proof (translation)
Introduce `ι _ r a b u cs p K l hl hu hprod`. Apply `tsum_mem_of_denominator _ K l hl` to reduce the goal to its premises. Introduce `m`. Take `⟨z2, h2⟩` from `DL_int_valued (coneTerm a b (-(p : ℂ))) (fun m' => by`. Take `⟨z, hz⟩` from `hprod m'`.

Conclude with `⟨z, by rw [coneTerm_neg_nat, hz, Complex.ofReal_intCast]⟩) cs m`. Take `⟨z1, h1⟩` from `hu m`. Use `⟨z1 * z2, ?_⟩` and prove the remaining obligations. Rewrite using `[h2, ← mul_assoc]`. Establish `h1' : ((l : ℂ) ^ K) * (u m : ℂ) = (z1 : ℂ)` using `by exact_mod_cast h1`.

Rewrite using `[h1']`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem value_neg_nat_mem : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (u : (Fin r → ℕ) → ℚ) (cs : List (Fin r)) (p K l : ℕ), 0 < l → (∀ m, ∃ z : ℤ, (l : ℚ) ^ K * u m = z) → (∀ m : Fin r → ℕ, ∃ z : ℤ, ∏ j, (b j + ∑ i, a j i * (m i : ℝ)) ^ p = (z : ℝ)) → ∃ (q : ℚ) (z : ℤ), ∑' m, (u m : ℂ) * DL cs (coneTerm a b (-(p : ℂ))) m = (q : ℂ) ∧ (l : ℚ) ^ K * q = z := by
  intro ι _ r a b u cs p K l hl hu hprod
  apply tsum_mem_of_denominator _ K l hl
  intro m
  obtain ⟨z2, h2⟩ := DL_int_valued (coneTerm a b (-(p : ℂ))) (fun m' => by
      obtain ⟨z, hz⟩ := hprod m'
      exact ⟨z, by rw [coneTerm_neg_nat, hz, Complex.ofReal_intCast]⟩) cs m
  obtain ⟨z1, h1⟩ := hu m
  refine ⟨z1 * z2, ?_⟩
  rw [h2, ← mul_assoc]
  have h1' : ((l : ℂ) ^ K) * (u m : ℂ) = (z1 : ℂ) := by exact_mod_cast h1
  rw [h1']
  push_cast
  ring

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
