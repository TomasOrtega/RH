import Mathlib

namespace GlobalTheory

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero => intro g _ hg`. Simplify using `using hg`. Consider the case `succ N ih`. Introduce `g hg hgN`.

Apply `ih g hg` to reduce the goal to its premises. Apply `h _ (O.mul_mem hg (O.pow_mem ht N))` to reduce the goal to its premises. Rewrite using `[mul_assoc, ← pow_succ]` and apply the resulting hypothesis.
-/
theorem div_mem_of_mul_pow_div_mem_of_regularPair (K : Type) [Field K] (O : Subring K) (s t : K)
    (ht : t ∈ O) (h : ∀ g ∈ O, g * t / s ∈ O → g / s ∈ O) (N : ℕ) :
    ∀ g ∈ O, g * t ^ N / s ∈ O → g / s ∈ O := by
  induction N with
  | zero => intro g _ hg; simpa using hg
  | succ N ih =>
    intro g hg hgN
    apply ih g hg
    apply h _ (O.mul_mem hg (O.pow_mem ht N))
    rwa [mul_assoc, ← pow_succ]

/- English proof (translation)
Introduce `K _ O s t hs ht hs0 h m N`. Proceed by induction on `m with`. Consider the case `zero => intro g hg _`. Simplify using `using hg`. Consider the case `succ m ih`.

Introduce `g hg hgN`. Establish `h1 : g * t ^ N / s ∈ O`. Establish `h2` using `O.mul_mem hgN (O.pow_mem hs m)`. Establish `e : g * t ^ N / s ^ (m + 1) * s ^ m = g * t ^ N / s`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Rewrite `h2` using `[e]`. Then use the resulting hypothesis. Establish `h3` using `div_mem_of_mul_pow_div_mem_of_regularPair K O s t ht h N g hg h1`. Establish `e1 : g / s * t ^ N / s ^ m = g * t ^ N / s ^ (m + 1)`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Establish `e2 : g / s / s ^ m = g / s ^ (m + 1)`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← e2]`.

Conclude with `ih _ h3 (by rwa [e1])`.
-/
theorem regularPair_pow : ∀ (K : Type) [Field K] (O : Subring K) (s t : K), s ∈ O → t ∈ O → s ≠ 0 → (∀ g ∈ O, g * t / s ∈ O → g / s ∈ O) → ∀ (m N : ℕ), ∀ g ∈ O, g * t ^ N / s ^ m ∈ O → g / s ^ m ∈ O := by
  intro K _ O s t hs ht hs0 h m N
  induction m with
  | zero => intro g hg _; simpa using hg
  | succ m ih =>
    intro g hg hgN
    have h1 : g * t ^ N / s ∈ O := by
      have h2 := O.mul_mem hgN (O.pow_mem hs m)
      have e : g * t ^ N / s ^ (m + 1) * s ^ m = g * t ^ N / s := by
        field_simp
        ring
      rwa [e] at h2
    have h3 := div_mem_of_mul_pow_div_mem_of_regularPair K O s t ht h N g hg h1
    have e1 : g / s * t ^ N / s ^ m = g * t ^ N / s ^ (m + 1) := by
      field_simp
      ring
    have e2 : g / s / s ^ m = g / s ^ (m + 1) := by
      field_simp
      ring
    rw [← e2]
    exact ih _ h3 (by rwa [e1])

end GlobalTheory
