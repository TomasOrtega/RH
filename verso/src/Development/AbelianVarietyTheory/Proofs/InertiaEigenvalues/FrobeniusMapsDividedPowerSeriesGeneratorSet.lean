import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CstSApply

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

/- English proof (translation)
Introduce `l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t F hF`. Take `⟨w, hw, hF⟩` from `hF`. Establish `hpos : 0 < l` using `(Fact.out : l.Prime).pos`. Use `⟨fun n => if l ∣ n then ((((n / e).factorial / ((n / l) / e).factorial : ℕ) : Wq l a) * sigma l a (w (n / l))) else 0, ?_, ?_⟩` and prove the remaining obligations. Introduce `r`.

Establish `h` using `hw r`. Rewrite `h`, the goal using `[Filter.eventually_cofinite]`. Use `(h.image fun m => l * m).subset ?_` and prove the remaining obligations. Introduce `n hn`. Simplify using `only [Set.mem_setOf_eq] at hn`.

Use `split_ifs at hn with hd`. Use `⟨n / l, ?_, Nat.mul_div_cancel' hd⟩` and prove the remaining obligations. Introduce `hr`. Apply `hn` to reduce the goal to its premises. Take `⟨c, hc⟩` from `hr`.

Conclude with `Dvd.dvd.mul_left ⟨sigma l a c, by rw [hc, map_mul, map_pow, map_natCast]⟩ _`. Conclude with `absurd (dvd_zero _) hn`. Introduce `τ n show _ = algebraMap O K (emb t τ (if l ∣ n then _ else 0))`. Rewrite using `[frobTot_apply, coeff_frob]`. Distinguish the cases in `hd : l ∣ n`.

Rewrite using `[if_pos hd, if_pos hd]`. Take `⟨m, rfl⟩` from `hd`. Rewrite using `[Nat.mul_div_cancel_left m hpos]`. Establish `hdiv : (m / e).factorial ∣ (l * m / e).factorial` using `Nat.factorial_dvd_factorial (Nat.div_le_div_right (Nat.le_mul_of_pos_left m hpos))`. Rewrite using `[map_mul, map_natCast, emb_sigma, map_mul, map_natCast, ← hF (τ - 1) m, ← mul_assoc, ← Nat.cast_mul, Nat.div_mul_cancel hdiv]`.

Rewrite using `[if_neg hd, if_neg hd]`. Simplify using the standard rewrite rules.
-/
theorem frobTot_mem_SdSet : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O),
    ∀ F ∈ SdSet t K e, frobTot K a l F ∈ SdSet t K e := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t F hF
  obtain ⟨w, hw, hF⟩ := hF
  have hpos : 0 < l := (Fact.out : l.Prime).pos
  refine ⟨fun n => if l ∣ n then
      ((((n / e).factorial / ((n / l) / e).factorial : ℕ) : Wq l a) * sigma l a (w (n / l))) else 0, ?_, ?_⟩
  · intro r
    have h := hw r
    rw [Filter.eventually_cofinite] at h ⊢
    refine (h.image fun m => l * m).subset ?_
    intro n hn
    simp only [Set.mem_setOf_eq] at hn
    split_ifs at hn with hd
    · refine ⟨n / l, ?_, Nat.mul_div_cancel' hd⟩
      intro hr
      apply hn
      obtain ⟨c, hc⟩ := hr
      exact Dvd.dvd.mul_left ⟨sigma l a c, by rw [hc, map_mul, map_pow, map_natCast]⟩ _
    · exact absurd (dvd_zero _) hn
  · intro τ n
    show _ = algebraMap O K (emb t τ (if l ∣ n then _ else 0))
    rw [frobTot_apply, coeff_frob]
    by_cases hd : l ∣ n
    · rw [if_pos hd, if_pos hd]
      obtain ⟨m, rfl⟩ := hd
      rw [Nat.mul_div_cancel_left m hpos]
      have hdiv : (m / e).factorial ∣ (l * m / e).factorial :=
        Nat.factorial_dvd_factorial (Nat.div_le_div_right (Nat.le_mul_of_pos_left m hpos))
      rw [map_mul, map_natCast, emb_sigma, map_mul, map_natCast, ← hF (τ - 1) m, ← mul_assoc, ← Nat.cast_mul,
        Nat.div_mul_cancel hdiv]
    · rw [if_neg hd, if_neg hd]; simp

end GlobalTheory.CrysPrism
