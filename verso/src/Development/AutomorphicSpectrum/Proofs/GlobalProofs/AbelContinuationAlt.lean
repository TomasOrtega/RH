import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.TendstoTailInfiniteProductOneStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.WeightSumAsFiniteDifferencesStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConeSeriesSummableRightHalfPlaneStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SummationDecompositionFiniteDifferencesStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.RealDifferenceConeBoundStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PeriodicWeightBoundedStatement

set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

/- English proof (translation)
Take `⟨Q, x, cs, u, hu, hcs, hsum⟩` from `GlobalTheory.T.weight_sum_as_finite_differences r l (Fintype.card ι * k + 2) w hl hw`. Use `⟨fun s => ∑ q, ∑' m, (u q m : ℂ) * DL (cs q) (coneTerm a b s) m, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `h : ∀ q ∈ (Finset.univ : Finset Q), DifferentiableOn ℂ (fun s => ∑' m, (u q m : ℂ) * DL (cs q) (coneTerm a b s) m) {s : ℂ | -(k : ℝ) < s.re}` using `fun q _ => GlobalTheory.T.cone_series_differentiable_left_strip ι r a b ha hb k (Fintype.card ι * k + 2) (cs q) (u q) le_rfl (hu q) (hcs q)`. Establish `h2` using `DifferentiableOn.sum h`. Establish `h3 : (fun s : ℂ => ∑ q, ∑' m, (u q m : ℂ) * DL (cs q) (coneTerm a b s) m) = ∑ q, fun s : ℂ => ∑' m, (u q m : ℂ) * DL (cs q) (coneTerm a b s) m`.

Use function extensionality and compare the values at `s`. Simplify using `[Finset.sum_apply]`. Rewrite using `[h3]`. Conclude with `h2`. Introduce `s hs`.

Conclude with `(hsum (coneTerm a b s) (GlobalTheory.T.cone_series_summable_right_half_plane ι r a b hr ha hb s hs)).symm`. Introduce `p hp hrat`. Establish `hN : Fintype.card ι * p < Fintype.card ι * k + 2`. Use `Nat.mul_le_mul_left (Fintype.card ι) hp.le` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Use `choose q hq using fun t => GlobalTheory.T.shintani_values_negative_integers_rational ι r a b (u t) (cs t) (Fintype.card ι * k + 2) p hN (hcs t) hrat`. Use `⟨∑ t, q t, ?_⟩` and prove the remaining obligations. Simplify using `only [Rat.cast_sum]`. Conclude with `Finset.sum_congr rfl fun t _ => hq t`.
-/
theorem stage (ι : Type) [Fintype ι] (r l : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (w : (Fin r → ℕ) → ℚ)
    (hr : r ≤ Fintype.card ι) (hl : 0 < l) (ha : ∀ j i, 0 < a j i) (hb : ∀ j, 0 < b j) (hw : GoodWeight l w) (k : ℕ) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s | -(k : ℝ) < s.re} ∧
      (∀ s : ℂ, 1 < s.re → G s = ∑' m, (w m : ℂ) * coneTerm a b s m) ∧
      ∀ p : ℕ, p < k → (∀ m : Fin r → ℕ, ∃ q : ℚ, ∏ j, (b j + ∑ i, a j i * (m i : ℝ)) ^ p = (q : ℝ)) →
        ∃ q : ℚ, G (-(p : ℂ)) = (q : ℂ) := by
  classical
  obtain ⟨Q, x, cs, u, hu, hcs, hsum⟩ := GlobalTheory.T.weight_sum_as_finite_differences r l (Fintype.card ι * k + 2) w hl hw
  refine ⟨fun s => ∑ q, ∑' m, (u q m : ℂ) * DL (cs q) (coneTerm a b s) m, ?_, ?_, ?_⟩
  · have h : ∀ q ∈ (Finset.univ : Finset Q), DifferentiableOn ℂ
        (fun s => ∑' m, (u q m : ℂ) * DL (cs q) (coneTerm a b s) m) {s : ℂ | -(k : ℝ) < s.re} :=
      fun q _ => GlobalTheory.T.cone_series_differentiable_left_strip ι r a b ha hb k (Fintype.card ι * k + 2) (cs q) (u q) le_rfl (hu q) (hcs q)
    have h2 := DifferentiableOn.sum h
    have h3 : (fun s : ℂ => ∑ q, ∑' m, (u q m : ℂ) * DL (cs q) (coneTerm a b s) m) =
        ∑ q, fun s : ℂ => ∑' m, (u q m : ℂ) * DL (cs q) (coneTerm a b s) m := by
      funext s
      simp [Finset.sum_apply]
    rw [h3]
    exact h2
  · intro s hs
    exact (hsum (coneTerm a b s) (GlobalTheory.T.cone_series_summable_right_half_plane ι r a b hr ha hb s hs)).symm
  · intro p hp hrat
    have hN : Fintype.card ι * p < Fintype.card ι * k + 2 := by
      have := Nat.mul_le_mul_left (Fintype.card ι) hp.le
      omega
    choose q hq using fun t => GlobalTheory.T.shintani_values_negative_integers_rational ι r a b (u t) (cs t) (Fintype.card ι * k + 2) p hN (hcs t) hrat
    refine ⟨∑ t, q t, ?_⟩
    simp only [Rat.cast_sum]
    exact Finset.sum_congr rfl fun t _ => hq t

/- English proof (translation)
Introduce `ι _ r l a b w hr hl ha hb hw`. Use `choose G hG hGeq hGrat using fun k : ℕ => stage ι r l a b w hr hl ha hb hw k`. Take `⟨T, hT, hTG⟩` from `GlobalTheory.T.analytic_continuation_from_strips (fun s => ∑' m, (w m : ℂ) * coneTerm a b s m) G hG hGeq`. Use `⟨T, hT, ?_, ?_⟩` and prove the remaining obligations. Introduce `s hs`.

Establish `hs0 : -((0 : ℕ) : ℝ) < s.re`. Rewrite using `[Nat.cast_zero, neg_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hTG 0 s hs0, hGeq 0 s hs]`. Establish `hper : ∀ (i : Fin r) (m : Fin r → ℕ), w (m + Pi.single i l) = w m`.

Take `⟨h1, -⟩` from `hw`. Conclude with `fun i m => h1 m i`. Take `⟨C, hC⟩` from `GlobalTheory.T.periodic_weight_bounded r l w hl hper`. Establish `hcone` using `GlobalTheory.T.cone_series_summable_right_half_plane ι r a b hr ha hb s hs`. Use `Summable.hasSum (Summable.of_norm ?_)` and prove the remaining obligations.

Use `Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) (hcone.norm.mul_left C)` and prove the remaining obligations. Establish `hwm : ‖(w m : ℂ)‖ ≤ C` using `by simpa using hC m`. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul_of_nonneg_right hwm (norm_nonneg _)`. Introduce `p hrat`.

Establish `hp : -((p + 1 : ℕ) : ℝ) < (-(p : ℂ)).re` using `by norm_num`. Rewrite using `[hTG (p + 1) _ hp]`. Conclude with `hGrat (p + 1) p (Nat.lt_succ_self p) hrat`.
-/
theorem abelContinuation : AbelContinuation := by
  intro ι _ r l a b w hr hl ha hb hw
  choose G hG hGeq hGrat using fun k : ℕ => stage ι r l a b w hr hl ha hb hw k
  obtain ⟨T, hT, hTG⟩ := GlobalTheory.T.analytic_continuation_from_strips (fun s => ∑' m, (w m : ℂ) * coneTerm a b s m) G hG hGeq
  refine ⟨T, hT, ?_, ?_⟩
  · intro s hs
    have hs0 : -((0 : ℕ) : ℝ) < s.re := by
      rw [Nat.cast_zero, neg_zero]
      linarith
    rw [hTG 0 s hs0, hGeq 0 s hs]
    have hper : ∀ (i : Fin r) (m : Fin r → ℕ), w (m + Pi.single i l) = w m := by
      obtain ⟨h1, -⟩ := hw
      exact fun i m => h1 m i
    obtain ⟨C, hC⟩ := GlobalTheory.T.periodic_weight_bounded r l w hl hper
    have hcone := GlobalTheory.T.cone_series_summable_right_half_plane ι r a b hr ha hb s hs
    refine Summable.hasSum (Summable.of_norm ?_)
    refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) (hcone.norm.mul_left C)
    have hwm : ‖(w m : ℂ)‖ ≤ C := by simpa using hC m
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hwm (norm_nonneg _)
  · intro p hrat
    have hp : -((p + 1 : ℕ) : ℝ) < (-(p : ℂ)).re := by norm_num
    rw [hTG (p + 1) _ hp]
    exact hGrat (p + 1) p (Nat.lt_succ_self p) hrat

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
