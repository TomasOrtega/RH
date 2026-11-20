import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HasQExpansionModularForm

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

namespace GlobalTheory.QFam

/- English proof (translation)
Establish `toSeries : ∀ c : ℕ → ℂ, HasQ N f c → GlobalTheory.HasQExpansion (N : ℝ) f (PowerSeries.mk c)`. Introduce `c hc τ`. Establish `hs` using `(hasQ_iff N f c).1 hc τ`. Simplify `hs` using `[PowerSeries.coeff_mk, Function.Periodic.qParam]`. Establish `hN' : (0 : ℝ) < N` using `by exact_mod_cast hN`.

Establish `hab` using `GlobalTheory.HasQExpansion.unique hN' (toSeries a ha) (toSeries b hb)`. Use function extensionality and compare the values at `n`. Simplify using `using congrArg (PowerSeries.coeff n) hab`.
-/
theorem HasQ.coeff_unique {N : ℕ} {f : ℍ → ℂ} {a b : ℕ → ℂ} (hN : 0 < N) (ha : HasQ N f a)
    (hb : HasQ N f b) : a = b := by
  have toSeries : ∀ c : ℕ → ℂ, HasQ N f c → GlobalTheory.HasQExpansion (N : ℝ) f (PowerSeries.mk c) := by
    intro c hc τ
    have hs := (hasQ_iff N f c).1 hc τ
    simpa [PowerSeries.coeff_mk, Function.Periodic.qParam] using hs
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hab := GlobalTheory.HasQExpansion.unique hN' (toSeries a ha) (toSeries b hb)
  funext n
  simpa using congrArg (PowerSeries.coeff n) hab

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Conclude with `(hf τ).unique (hg τ)`.
-/
theorem HasQ.fun_unique {N : ℕ} {f g : ℍ → ℂ} {a : ℕ → ℂ} (hf : HasQ N f a) (hg : HasQ N g a) :
    f = g := by
  funext τ
  exact (hf τ).unique (hg τ)

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ _ _ _ hN ha hb => HasQ.coeff_unique hN ha hb, fun _ _ _ _ hf hg => HasQ.fun_unique hf hg⟩`.
-/
theorem hasQ_unique_both :
    (∀ (N : ℕ) (f : ℍ → ℂ) (a b : ℕ → ℂ), 0 < N → HasQ N f a → HasQ N f b → a = b) ∧
    (∀ (N : ℕ) (f g : ℍ → ℂ) (a : ℕ → ℂ), HasQ N f a → HasQ N g a → f = g) :=
  ⟨fun _ _ _ _ hN ha hb => HasQ.coeff_unique hN ha hb, fun _ _ _ _ hf hg => HasQ.fun_unique hf hg⟩

end GlobalTheory.QFam
