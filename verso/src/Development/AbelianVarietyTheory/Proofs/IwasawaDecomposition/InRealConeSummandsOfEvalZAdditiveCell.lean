import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkValEqZeroOrOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfToRealRel

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

noncomputable section

namespace GlobalTheory.PolFan.Mark

/- English proof (translation)
Take `⟨N, ℓ, hN, h1, h2, h3⟩` from `hγ.strict`. Take `⟨c, hc, e⟩` from `hs`. Establish `hsum : ψ.evalZ (∑ j, u j) = ∑ i, c i * ψ.evalZ (γ i)`. Rewrite using `[← hγ.linear c hc]`. Unfold `InvFun.evalZ`.

Use `congr 1`. Use function extensionality and compare the values at `a b`. Use `LinearMap.congr_fun₂ e a b` as an intermediate fact. Simplify `this` using `[LinearMap.sum_apply]`. Establish `hℓ : (ℓ (∑ j, u j) : ℝ) = N * ψ.evalZ (∑ j, u j)`.

Rewrite using `[apply_eq_of_toReal_eq e ℓ, hsum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[h1 i]`. Expand and normalize the polynomial expressions, which then agree. Establish `hd : ∀ j, 0 ≤ (ℓ (u j) : ℝ) - N * ψ.evalZ (u j)` using `fun j => sub_nonneg.2 (h2 _ (hu j) (hp j))`.

Establish `hz : ∑ j, ((ℓ (u j) : ℝ) - N * ψ.evalZ (u j)) = 0`. Use `le_antisymm ?_ (Finset.sum_nonneg fun j _ => hd j)` and prove the remaining obligations. Rewrite using `[Finset.sum_sub_distrib, ← Finset.mul_sum]`. Establish `e1 : (∑ j, (ℓ (u j) : ℝ)) = ℓ (∑ j, u j)` using `by rw [map_sum]; push_cast; rfl`. Rewrite using `[e1, hℓ]`.

Establish `h0 : (0 : ℝ) ≤ N` using `Nat.cast_nonneg N`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hle h0]`. Introduce `j`. Establish `hj` using `(Finset.sum_eq_zero_iff_of_nonneg fun j _ => hd j).1 hz j (Finset.mem_univ _)`. Take `⟨n, c', hn, hc'⟩` from `h3 _ (hu j) (hp j) (by linarith)`.

Establish `hn' : (n : ℝ) ≠ 0` using `by exact_mod_cast hn.ne'`. Use `⟨fun i => (c' i : ℝ) / n, fun i => by positivity, LinearMap.ext₂ fun a b => ?_⟩` and prove the remaining obligations. Establish `h4` using `LinearMap.congr_fun₂ hc' a b`. Simplify using `only [LinearMap.sum_apply, LinearMap.smul_apply, nsmul_eq_mul] at h4`. Establish `h5 : (n : ℝ) * u j a b = ∑ i, (c' i : ℝ) * γ i a b` using `by exact_mod_cast h4`.

Simplify using `only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]`. Rewrite using `[show ∑ i, (c' i : ℝ) / n * (γ i a b : ℝ) = (∑ i, (c' i : ℝ) * γ i a b) / n by`. Rewrite using `[Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring, ← h5]`. Clear the denominators using the available nonvanishing facts.
-/
theorem inRCone_of_evalZ_sum_le (O : Type) [CommRing O] (bar : O → O) (ψ : InvFun O) (X : Type) [AddCommGroup X]
    [Module O X] [Module.Finite O X] (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (hγ : IsCell bar ψ γ) (k : ℕ)
    (u : Fin k → LinearMap.BilinForm ℤ X) (hu : ∀ j, u j ∈ balForms bar X) (hp : ∀ j y, 0 ≤ u j y y)
    (hs : InRCone γ (∑ j, u j)) (hle : ψ.evalZ (∑ j, u j) ≤ ∑ j, ψ.evalZ (u j)) : ∀ j, InRCone γ (u j) := by
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hγ.strict
  obtain ⟨c, hc, e⟩ := hs
  have hsum : ψ.evalZ (∑ j, u j) = ∑ i, c i * ψ.evalZ (γ i) := by
    rw [← hγ.linear c hc]
    unfold InvFun.evalZ
    congr 1
    funext a b
    have := LinearMap.congr_fun₂ e a b
    simpa [LinearMap.sum_apply] using this
  have hℓ : (ℓ (∑ j, u j) : ℝ) = N * ψ.evalZ (∑ j, u j) := by
    rw [apply_eq_of_toReal_eq e ℓ, hsum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h1 i]; ring
  have hd : ∀ j, 0 ≤ (ℓ (u j) : ℝ) - N * ψ.evalZ (u j) := fun j => sub_nonneg.2 (h2 _ (hu j) (hp j))
  have hz : ∑ j, ((ℓ (u j) : ℝ) - N * ψ.evalZ (u j)) = 0 := by
    refine le_antisymm ?_ (Finset.sum_nonneg fun j _ => hd j)
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    have e1 : (∑ j, (ℓ (u j) : ℝ)) = ℓ (∑ j, u j) := by rw [map_sum]; push_cast; rfl
    rw [e1, hℓ]
    have h0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith [mul_le_mul_of_nonneg_left hle h0]
  intro j
  have hj := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hd j).1 hz j (Finset.mem_univ _)
  obtain ⟨n, c', hn, hc'⟩ := h3 _ (hu j) (hp j) (by linarith)
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  refine ⟨fun i => (c' i : ℝ) / n, fun i => by positivity, LinearMap.ext₂ fun a b => ?_⟩
  have h4 := LinearMap.congr_fun₂ hc' a b
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, nsmul_eq_mul] at h4
  have h5 : (n : ℝ) * u j a b = ∑ i, (c' i : ℝ) * γ i a b := by exact_mod_cast h4
  simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [show ∑ i, (c' i : ℝ) / n * (γ i a b : ℝ) = (∑ i, (c' i : ℝ) * γ i a b) / n by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring, ← h5]
  field_simp

end GlobalTheory.PolFan.Mark
