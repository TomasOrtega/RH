import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SumRangeMulOfPeriodic
open NumberField IsDedekindDomain Formalism.L2.Col

namespace GlobalTheory

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.PeriodicSumShift.sum_range_mul_of_periodic`. Consider the case `exact _root_.GlobalTheory.PeriodicSumShift.sum_range_mul_of_periodic`. Consider the case `(apply _root_.GlobalTheory.PeriodicSumShift.sum_range_mul_of_periodic <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.PeriodicSumShift.sum_range_mul_of_periodic <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.PeriodicSumShift.sum_range_mul_of_periodic <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.PeriodicSumShift.sum_range_mul_of_periodic ..)`.
-/
theorem sum_range_mul_of_periodic {K : Type} [Field K] (g : ℕ → K) (N : ℕ)
    (hg : ∀ i, g (N + i) = g i) (k : ℕ) :
    ∑ i ∈ Finset.range (N * k), g i = (k : K) * ∑ i ∈ Finset.range N, g i := by
  first
  | exact @_root_.GlobalTheory.PeriodicSumShift.sum_range_mul_of_periodic
  | exact _root_.GlobalTheory.PeriodicSumShift.sum_range_mul_of_periodic
  | (apply _root_.GlobalTheory.PeriodicSumShift.sum_range_mul_of_periodic <;> assumption)
  | (intros; apply _root_.GlobalTheory.PeriodicSumShift.sum_range_mul_of_periodic <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PeriodicSumShift.sum_range_mul_of_periodic <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PeriodicSumShift.sum_range_mul_of_periodic ..)

/- English proof (translation)
Establish `hq : (qOf P : E) ≠ 0`. Establish `: qOf P ≠ 0`. Unfold `qOf`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `P.ne_bot`.

Conclude with `this` after adjusting the coercions. Establish `key : ∀ C : ℕ, ∑ a ∈ LocE.valsQ E (qOf P) A C, f a = ∑ i ∈ Finset.range (qOf P ^ (A + C)), f ((i : E) / (qOf P : E) ^ A)`. Introduce `C`. Unfold `LocE.valsQ`. Rewrite using `[Finset.sum_image]`.

Introduce `i _ j _ hij`. Use `(div_left_inj' (pow_ne_zero A hq)).1 hij` as an intermediate fact. Conclude with `this` after adjusting the coercions. Rewrite using `[key, key]`. Establish `e : qOf P ^ (A + B) = qOf P ^ (A + B₀) * qOf P ^ (B - B₀)`.

Rewrite using `[← pow_add]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Rewrite using `[e, sum_range_mul_of_periodic (fun i : ℕ => f ((i : E) / (qOf P : E) ^ A))]`. Use `push_cast`.

Both sides reduce to the same expression. Introduce `i`. Establish `h1 : IntAt P (1 : E)` using `by simpa using IntAt.coe P 1`. Use `hf ((i : E) / (qOf P : E) ^ A) 1 h1` as an intermediate fact. Rewrite using `[← this]`.

Use `congr 1`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_valsQ_of_invariant (E : Type) [Field E] [NumberField E]
    (P : HeightOneSpectrum (𝓞 E)) (K : Type) [Field K] (f : E → K) (B₀ : ℕ)
    (hf : ∀ a u, IntAt P u → f (a + (qOf P : E) ^ B₀ * u) = f a) (A B : ℕ) (hB : B₀ ≤ B) :
    ∑ a ∈ LocE.valsQ E (qOf P) A B, f a
      = (qOf P : K) ^ (B - B₀) * ∑ a ∈ LocE.valsQ E (qOf P) A B₀, f a := by
  classical
  have hq : (qOf P : E) ≠ 0 := by
    have : qOf P ≠ 0 := by
      unfold qOf
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact P.ne_bot
    exact_mod_cast this
  have key : ∀ C : ℕ, ∑ a ∈ LocE.valsQ E (qOf P) A C, f a
      = ∑ i ∈ Finset.range (qOf P ^ (A + C)), f ((i : E) / (qOf P : E) ^ A) := by
    intro C
    unfold LocE.valsQ
    rw [Finset.sum_image]
    intro i _ j _ hij
    have := (div_left_inj' (pow_ne_zero A hq)).1 hij
    exact_mod_cast this
  rw [key, key]
  have e : qOf P ^ (A + B) = qOf P ^ (A + B₀) * qOf P ^ (B - B₀) := by
    rw [← pow_add]; congr 1; omega
  rw [e, sum_range_mul_of_periodic (fun i : ℕ => f ((i : E) / (qOf P : E) ^ A))]
  · push_cast; rfl
  · intro i
    have h1 : IntAt P (1 : E) := by simpa using IntAt.coe P 1
    have := hf ((i : E) / (qOf P : E) ^ A) 1 h1
    rw [← this]
    congr 1
    push_cast
    field_simp
    ring

end GlobalTheory
