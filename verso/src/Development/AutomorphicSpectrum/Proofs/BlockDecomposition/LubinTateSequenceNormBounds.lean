import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMod
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationLtOneOfEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalEmbeddingRangeEqField
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniformizerGaloisAction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormSubLeOfNear
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt

namespace GlobalTheory.CompanionTheory.LTPer.Tilt.Normz

/- English proof (translation)
Take `⟨k, rfl⟩ : ∃ k, q = k + 2` from `⟨q - 2, by omega⟩`. Establish `hmax : ∀ x y : F, ‖x + y‖ ≤ max ‖x‖ ‖y‖` using `fun x y => IsUltrametricDist.norm_add_le_max x y`. Establish `hp0 : 0 ≤ ‖p‖` using `norm_nonneg p`. Establish `hlt : ∀ n, ‖w n‖ < 1`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero => simp [h0]`. Consider the case `succ n ih`. Assume the negation of the conclusion as `hge`. Rewrite `hge` using `[not_lt]`.

Establish `hapos : 0 < ‖w (n + 1)‖` using `lt_of_lt_of_le one_pos hge`. Establish `hq1 : ‖w (n + 1)‖ ≤ ‖w (n + 1)‖ ^ (k + 2)`. Combine the equalities or inequalities in the displayed calculation. Establish `key : w (n + 1) ^ (k + 2) = w n + -(p * w (n + 1))` using `by linear_combination hr n`. Establish `h2 : ‖w (n + 1) ^ (k + 2)‖ ≤ max ‖w n‖ ‖-(p * w (n + 1))‖`.

Rewrite using `[key]`. Conclude with `hmax _ _`. Rewrite `h2` using `[norm_pow, norm_neg, norm_mul]`. Establish `h3 : ‖p‖ * ‖w (n + 1)‖ < ‖w (n + 1)‖ ^ (k + 2)`. Combine the equalities or inequalities in the displayed calculation.

Establish `h4 : ‖w n‖ < ‖w (n + 1)‖ ^ (k + 2)` using `lt_of_lt_of_le ih (le_trans hge hq1)`. Conclude with `absurd h2 (not_le.mpr (max_lt h4 h3))`. Establish `hrec1 : w 1 ^ (k + 2) + p * w 1 = 0`. Use `hr 0` as an intermediate fact. Rewrite `this` using `[h0]`.

Conclude with `this`. Establish `hpw : w 1 ^ (k + 1) = -p`. Establish `e : w 1 * (w 1 ^ (k + 1) + p) = 0` using `by linear_combination hrec1`. Break down `mul_eq_zero.mp e with h | h` into its components or cases. Conclude with `absurd h h1`.

Take the linear combination `h`. Establish `hnorm1 : ‖w 1‖ ^ (k + 1) = ‖p‖` using `by rw [← norm_pow, hpw, norm_neg]`. Establish `hp_pos : 0 < ‖p‖`. Rewrite using `[← hnorm1]`. Conclude with `pow_pos (norm_pos_iff.mpr h1) _`.

Establish `hw1 : ‖p‖ ≤ ‖w 1‖`. Rewrite using `[← hnorm1]`. Combine the equalities or inequalities in the displayed calculation. Establish `hsmall : ∀ a : F, ‖a‖ ≤ ‖p‖ → ‖a ^ (k + 2) + p * a‖ ≤ ‖p‖ ^ 2`. Introduce `a ha`.

Establish `ha0 : 0 ≤ ‖a‖` using `norm_nonneg a`. Use `le_trans (hmax _ _) (max_le ?_ ?_)` and prove the remaining obligations. Rewrite using `[norm_pow]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_mul, sq]`.

Conclude with `mul_le_mul_of_nonneg_left ha hp0`. Establish `hstep : ∀ n, ‖p‖ ≤ ‖w n‖ → ‖p‖ < ‖w (n + 1)‖`. Introduce `n hn`. Assume the negation of the conclusion as `hc`. Rewrite `hc` using `[not_lt]`.

Establish `hb` using `hsmall (w (n + 1)) hc`. Rewrite `hb` using `[hr n]`. Establish `hp2 : ‖p‖ ^ 2 < ‖p‖`. Rewrite using `[sq]`. Combine the equalities or inequalities in the displayed calculation.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hge : ∀ n, ‖p‖ ≤ ‖w (n + 1)‖`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => exact hw1`.

Consider the case `succ n ih => exact (hstep _ ih).le`. Use `⟨hlt, fun n hn => ?_⟩` and prove the remaining obligations. Take `⟨m, rfl⟩ : ∃ m, n = m + 2` from `⟨n - 2, by omega⟩`. Conclude with `hstep (m + 1) (hge m)`.
-/
theorem norm_bounds_of_rec {F : Type*} [NormedField F] [IsUltrametricDist F] (w : ℕ → F) (p : F)
    (q : ℕ) (hq : 2 ≤ q) (hp : ‖p‖ < 1) (h0 : w 0 = 0) (h1 : w 1 ≠ 0)
    (hr : ∀ n, w (n + 1) ^ q + p * w (n + 1) = w n) :
    (∀ n, ‖w n‖ < 1) ∧ ∀ n, 2 ≤ n → ‖p‖ < ‖w n‖ := by
  obtain ⟨k, rfl⟩ : ∃ k, q = k + 2 := ⟨q - 2, by omega⟩
  have hmax : ∀ x y : F, ‖x + y‖ ≤ max ‖x‖ ‖y‖ := fun x y => IsUltrametricDist.norm_add_le_max x y
  have hp0 : 0 ≤ ‖p‖ := norm_nonneg p
  have hlt : ∀ n, ‖w n‖ < 1 := by
    intro n
    induction n with
    | zero => simp [h0]
    | succ n ih =>
      by_contra hge
      rw [not_lt] at hge
      have hapos : 0 < ‖w (n + 1)‖ := lt_of_lt_of_le one_pos hge
      have hq1 : ‖w (n + 1)‖ ≤ ‖w (n + 1)‖ ^ (k + 2) := by
        calc ‖w (n + 1)‖ = ‖w (n + 1)‖ ^ 1 := (pow_one _).symm
          _ ≤ ‖w (n + 1)‖ ^ (k + 2) := pow_le_pow_right₀ hge (by omega)
      have key : w (n + 1) ^ (k + 2) = w n + -(p * w (n + 1)) := by linear_combination hr n
      have h2 : ‖w (n + 1) ^ (k + 2)‖ ≤ max ‖w n‖ ‖-(p * w (n + 1))‖ := by
        rw [key]; exact hmax _ _
      rw [norm_pow, norm_neg, norm_mul] at h2
      have h3 : ‖p‖ * ‖w (n + 1)‖ < ‖w (n + 1)‖ ^ (k + 2) := by
        calc ‖p‖ * ‖w (n + 1)‖ < 1 * ‖w (n + 1)‖ := mul_lt_mul_of_pos_right hp hapos
          _ = ‖w (n + 1)‖ := one_mul _
          _ ≤ ‖w (n + 1)‖ ^ (k + 2) := hq1
      have h4 : ‖w n‖ < ‖w (n + 1)‖ ^ (k + 2) := lt_of_lt_of_le ih (le_trans hge hq1)
      exact absurd h2 (not_le.mpr (max_lt h4 h3))
  have hrec1 : w 1 ^ (k + 2) + p * w 1 = 0 := by
    have := hr 0
    rw [h0] at this
    exact this
  have hpw : w 1 ^ (k + 1) = -p := by
    have e : w 1 * (w 1 ^ (k + 1) + p) = 0 := by linear_combination hrec1
    rcases mul_eq_zero.mp e with h | h
    · exact absurd h h1
    · linear_combination h
  have hnorm1 : ‖w 1‖ ^ (k + 1) = ‖p‖ := by rw [← norm_pow, hpw, norm_neg]
  have hp_pos : 0 < ‖p‖ := by
    rw [← hnorm1]
    exact pow_pos (norm_pos_iff.mpr h1) _
  have hw1 : ‖p‖ ≤ ‖w 1‖ := by
    rw [← hnorm1]
    calc ‖w 1‖ ^ (k + 1) ≤ ‖w 1‖ ^ 1 := pow_le_pow_of_le_one (norm_nonneg _) (hlt 1).le (by omega)
      _ = ‖w 1‖ := pow_one _
  have hsmall : ∀ a : F, ‖a‖ ≤ ‖p‖ → ‖a ^ (k + 2) + p * a‖ ≤ ‖p‖ ^ 2 := by
    intro a ha
    have ha0 : 0 ≤ ‖a‖ := norm_nonneg a
    refine le_trans (hmax _ _) (max_le ?_ ?_)
    · rw [norm_pow]
      calc ‖a‖ ^ (k + 2) ≤ ‖a‖ ^ 2 := pow_le_pow_of_le_one ha0 (ha.trans hp.le) (by omega)
        _ ≤ ‖p‖ ^ 2 := by gcongr
    · rw [norm_mul, sq]
      exact mul_le_mul_of_nonneg_left ha hp0
  have hstep : ∀ n, ‖p‖ ≤ ‖w n‖ → ‖p‖ < ‖w (n + 1)‖ := by
    intro n hn
    by_contra hc
    rw [not_lt] at hc
    have hb := hsmall (w (n + 1)) hc
    rw [hr n] at hb
    have hp2 : ‖p‖ ^ 2 < ‖p‖ := by
      rw [sq]
      calc ‖p‖ * ‖p‖ < 1 * ‖p‖ := mul_lt_mul_of_pos_right hp hp_pos
        _ = ‖p‖ := one_mul _
    linarith
  have hge : ∀ n, ‖p‖ ≤ ‖w (n + 1)‖ := by
    intro n
    induction n with
    | zero => exact hw1
    | succ n ih => exact (hstep _ ih).le
  refine ⟨hlt, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  exact hstep (m + 1) (hge m)

/- English proof (translation)
Introduce `l _ K χ π z hz hq hp`. Take `⟨_, h0, h1, hr, _⟩` from `hz`. Establish `e : GlobalTheory.CompanionTheory.LTPer.Tilt.omC (((π : ↥K.1) : Om l)) = GlobalTheory.CompanionTheory.LTPer.Tilt.oc K π`. Rewrite using `[GlobalTheory.CompanionTheory.LTPer.Tilt.omC_apply, GlobalTheory.CompanionTheory.LTPer.Tilt.oc_apply]`. Use `norm_bounds_of_rec (fun n => GlobalTheory.CompanionTheory.LTPer.Tilt.omC (z n)) (GlobalTheory.CompanionTheory.LTPer.Tilt.oc K π) (qOf π) hq hp (by simp [h0]) ?_ ?_` and prove the remaining obligations.

Use `show GlobalTheory.CompanionTheory.LTPer.Tilt.omC (z 1) ≠ 0`. Introduce `h`. Establish `hn` using `congrArg norm h`. Rewrite `hn` using `[GlobalTheory.CompanionTheory.LTPer.Tilt.norm_omC, norm_zero]`. Conclude with `h1 (norm_eq_zero.mp hn)`.

Introduce `n show GlobalTheory.CompanionTheory.LTPer.Tilt.omC (z (n + 1)) ^ qOf π + GlobalTheory.CompanionTheory.LTPer.Tilt.oc K π * GlobalTheory.CompanionTheory.LTPer.Tilt.omC (z (n + 1)) = GlobalTheory.CompanionTheory.LTPer.Tilt.omC (z n)`. Establish `hr' : z (n + 1) ^ qOf π + ((π : ↥K.1) : Om l) * z (n + 1) = z n` using `hr n`. Rewrite using `[← e, ← map_pow, ← map_mul, ← map_add, hr']`.
-/
theorem norm_z_bounds : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) (π : ↥(OL K)) (z : ℕ → Om l),
    LTData K χ π z → 2 ≤ qOf π → ‖oc K π‖ < 1 →
    (∀ n, ‖omC (z n)‖ < 1) ∧ ∀ n, 2 ≤ n → ‖oc K π‖ < ‖omC (z n)‖ := by
  intro l _ K χ π z hz hq hp
  obtain ⟨_, h0, h1, hr, _⟩ := hz
  have e : GlobalTheory.CompanionTheory.LTPer.Tilt.omC (((π : ↥K.1) : Om l)) = GlobalTheory.CompanionTheory.LTPer.Tilt.oc K π := by
    rw [GlobalTheory.CompanionTheory.LTPer.Tilt.omC_apply, GlobalTheory.CompanionTheory.LTPer.Tilt.oc_apply]
  refine norm_bounds_of_rec (fun n => GlobalTheory.CompanionTheory.LTPer.Tilt.omC (z n)) (GlobalTheory.CompanionTheory.LTPer.Tilt.oc K π) (qOf π) hq hp
    (by simp [h0]) ?_ ?_
  · show GlobalTheory.CompanionTheory.LTPer.Tilt.omC (z 1) ≠ 0
    intro h
    have hn := congrArg norm h
    rw [GlobalTheory.CompanionTheory.LTPer.Tilt.norm_omC, norm_zero] at hn
    exact h1 (norm_eq_zero.mp hn)
  · intro n
    show GlobalTheory.CompanionTheory.LTPer.Tilt.omC (z (n + 1)) ^ qOf π + GlobalTheory.CompanionTheory.LTPer.Tilt.oc K π * GlobalTheory.CompanionTheory.LTPer.Tilt.omC (z (n + 1))
      = GlobalTheory.CompanionTheory.LTPer.Tilt.omC (z n)
    have hr' : z (n + 1) ^ qOf π + ((π : ↥K.1) : Om l) * z (n + 1) = z n := hr n
    rw [← e, ← map_pow, ← map_mul, ← map_add, hr']

end GlobalTheory.CompanionTheory.LTPer.Tilt.Normz
