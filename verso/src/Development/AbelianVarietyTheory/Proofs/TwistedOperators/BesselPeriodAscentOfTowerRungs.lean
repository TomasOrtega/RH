import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.Asc

/- English proof (translation)
Introduce `hT h0 hB hJ D hq T L μ0 hL sc G W M hM v Ψ hΨ u hu hper`. Take `⟨F, hE, ΓL, hG⟩` from `hT D hq T L μ0 hL sc G W M hM v`. Establish `key : ∀ k (h : 2 * k + 2 ≤ D.R.m), NZB W M v F Ψ u k h`. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero`. Introduce `h`. Conclude with `hB D hq T L μ0 hL sc G W M hM v F ΓL hE hG Ψ hΨ u hu 0 h (h0 D hq T L μ0 hL sc G W M hM v F ΓL hE hG Ψ hΨ u hu hper h)`. Consider the case `succ k ih`. Introduce `h`.

Establish `h' : 2 * k + 2 ≤ D.R.m` using `by omega`. Conclude with `hB D hq T L μ0 hL sc G W M hM v F ΓL hE hG Ψ hΨ u hu (k + 1) h (hJ D hq T L μ0 hL sc G W M hM v F ΓL hE hG Ψ hΨ u hu k h h' (ih h'))`. Take `⟨r, hr⟩` from `D.R.m_even`. Establish `h2` using `D.R.two_le_m`. Establish `hk : 2 * (r - 1) + 2 ≤ D.R.m` using `by omega`.

Establish `hk' : 2 * (r - 1) + 2 = D.R.m` using `by omega`. Take `⟨ρ, Φ, hne⟩` from `key (r - 1) hk`. Use `⟨ρ, Φ, ?_⟩` and prove the remaining obligations. Set `f : ∀ i, Fn G (.grid i 0)` to `fun i => if hi : i ≤ D.R.m then part W M ρ Φ u i hi else 0`. Establish `hf : f D.R.m = thetaChi W M ρ Φ u`.

Simplify using `only [f, dif_pos le_rfl]`. Both sides reduce to the same expression. Use `hE.top (r - 1) hk hk' Ψ f (hΨ.1 _ le_rfl) (by rw [hf, ← part_m]; exact hu ρ Φ _ le_rfl) (by` as an intermediate fact. Simplify using `only [f, dif_pos hk]`. Conclude with `hne)`.

Rewrite `this` using `[hf]`. Then use the resulting hypothesis.
-/
theorem ascent_of_rungs : TowerEx → Rung0 → RungB → RungJ → Ascent := by
  intro hT h0 hB hJ D hq T L μ0 hL sc G W M hM v Ψ hΨ u hu hper
  obtain ⟨F, hE, ΓL, hG⟩ := hT D hq T L μ0 hL sc G W M hM v
  have key : ∀ k (h : 2 * k + 2 ≤ D.R.m), NZB W M v F Ψ u k h := by
    intro k
    induction k with
    | zero =>
      intro h
      exact hB D hq T L μ0 hL sc G W M hM v F ΓL hE hG Ψ hΨ u hu 0 h
        (h0 D hq T L μ0 hL sc G W M hM v F ΓL hE hG Ψ hΨ u hu hper h)
    | succ k ih =>
      intro h
      have h' : 2 * k + 2 ≤ D.R.m := by omega
      exact hB D hq T L μ0 hL sc G W M hM v F ΓL hE hG Ψ hΨ u hu (k + 1) h
        (hJ D hq T L μ0 hL sc G W M hM v F ΓL hE hG Ψ hΨ u hu k h h' (ih h'))
  obtain ⟨r, hr⟩ := D.R.m_even
  have h2 := D.R.two_le_m
  have hk : 2 * (r - 1) + 2 ≤ D.R.m := by omega
  have hk' : 2 * (r - 1) + 2 = D.R.m := by omega
  obtain ⟨ρ, Φ, hne⟩ := key (r - 1) hk
  refine ⟨ρ, Φ, ?_⟩
  let f : ∀ i, Fn G (.grid i 0) := fun i => if hi : i ≤ D.R.m then part W M ρ Φ u i hi else 0
  have hf : f D.R.m = thetaChi W M ρ Φ u := by
    simp only [f, dif_pos le_rfl]; rfl
  have := hE.top (r - 1) hk hk' Ψ f (hΨ.1 _ le_rfl) (by rw [hf, ← part_m]; exact hu ρ Φ _ le_rfl) (by
    simp only [f, dif_pos hk]; exact hne)
  rwa [hf] at this

end GlobalTheory.Asc
