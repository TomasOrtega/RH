import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace Katz

/- English proof (translation)
Introduce `p _ k _ _ _ σ τ _ u u' hu0 hu`. Establish `hinj : Function.Injective (algebraMap (WittVector p k) (Fr p k))` using `IsFractionRing.injective _ _`. Establish `hu1 : ∀ i (α : τ →₀ ℕ), ∃ w : WittVector p k, coeff α (u i) = algebraMap _ (Fr p k) w ∧ WittVector.constantCoeff w = coeff α (u' i)` using `hu`. Use `choose U hU using hu1`. Set `V : σ → MvPowerSeries τ (WittVector p k)` to `U`.

Establish `hV : ∀ i α, coeff α (V i) = U i α` using `fun _ _ => rfl`. Establish `hmap : u = fun i => map (algebraMap (WittVector p k) (Fr p k)) (V i)`. Use function extensionality and compare the values at `i`. Use extensionality with `α`. Rewrite using `[coeff_map, hV, (hU i α).1]`.

Establish `hmap' : u' = fun i => map (WittVector.constantCoeff (p` using `p) (R := k)) (V i) := by`. Use function extensionality and compare the values at `i`. Use extensionality with `α`. Rewrite using `[coeff_map, hV, (hU i α).2]`. Establish `hV0 : ∀ i, constantCoeff (V i) = 0`.

Introduce `i`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_zero, ← hu0 i, ← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply, hV, (hU i 0).1]`. Establish `hVs : HasSubst V` using `hasSubst_of_constantCoeff_zero hV0`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Introduce `f f' hf`. Establish `hf1 : ∀ α, ∃ w : WittVector p k, coeff α f = algebraMap _ (Fr p k) w ∧ WittVector.constantCoeff w = coeff α f'` using `hf`. Use `choose F hF using hf1`. Set `G : MvPowerSeries σ (WittVector p k)` to `F`. Establish `e1 : f = map (algebraMap (WittVector p k) (Fr p k)) G`.

Use extensionality with `α`. Rewrite using `[coeff_map]`. Conclude with `(hF α).1`. Establish `e2 : f' = map (WittVector.constantCoeff (p` using `p) (R := k)) G := by`. Use extensionality with `α`.

Rewrite using `[coeff_map]`. Conclude with `(hF α).2.symm`. Rewrite using `[e1, e2, hmap, hmap', ← map_subst hVs, ← map_subst hVs]`. Introduce `α`. Conclude with `⟨coeff α (subst V G), by rw [coeff_map], by rw [coeff_map]⟩`.

Introduce `c f hf`. Establish `hf1 : ∀ α, ∃ w : WittVector p k, coeff α f = algebraMap _ (Fr p k) (c * w)` using `hf`. Use `choose F hF using hf1`. Set `G : MvPowerSeries σ (WittVector p k)` to `F`. Establish `e1 : f = algebraMap (WittVector p k) (Fr p k) c • map (algebraMap (WittVector p k) (Fr p k)) G`.

Use extensionality with `α`. Rewrite using `[coeff_smul, coeff_map, hF α, map_mul]`. Both sides reduce to the same expression. Rewrite using `[e1, hmap, subst_smul (hVs.map _), ← map_subst hVs]`. Introduce `α`.

Conclude with `⟨coeff α (subst V G), by rw [coeff_smul, coeff_map, map_mul]⟩`.
-/
theorem red_subst : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p]
    (σ τ : Type) [Finite σ] (u : σ → MvPowerSeries (τ) (Fr p k)) (u' : σ → MvPowerSeries τ k),
    (∀ i, constantCoeff (u i) = 0) → (∀ i, Red p (u i) (u' i)) →
    (∀ (f : MvPowerSeries (σ) (Fr p k)) f', Red p f f' → Red p (subst u f) (subst u' f')) ∧
    ∀ (c : WittVector p k) (f : MvPowerSeries (σ) (Fr p k)), f ∈ intBy p k σ c →
      subst u f ∈ intBy p k τ c := by
  intro p _ k _ _ _ σ τ _ u u' hu0 hu
  have hinj : Function.Injective (algebraMap (WittVector p k) (Fr p k)) :=
    IsFractionRing.injective _ _
  have hu1 : ∀ i (α : τ →₀ ℕ), ∃ w : WittVector p k, coeff α (u i) = algebraMap _ (Fr p k) w ∧
      WittVector.constantCoeff w = coeff α (u' i) := hu
  choose U hU using hu1
  let V : σ → MvPowerSeries τ (WittVector p k) := U
  have hV : ∀ i α, coeff α (V i) = U i α := fun _ _ => rfl
  have hmap : u = fun i => map (algebraMap (WittVector p k) (Fr p k)) (V i) := by
    funext i; ext α; rw [coeff_map, hV, (hU i α).1]
  have hmap' : u' = fun i => map (WittVector.constantCoeff (p := p) (R := k)) (V i) := by
    funext i; ext α; rw [coeff_map, hV, (hU i α).2]
  have hV0 : ∀ i, constantCoeff (V i) = 0 := by
    intro i
    apply hinj
    rw [map_zero, ← hu0 i, ← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply,
      hV, (hU i 0).1]
  have hVs : HasSubst V := hasSubst_of_constantCoeff_zero hV0
  refine ⟨?_, ?_⟩
  · intro f f' hf
    have hf1 : ∀ α, ∃ w : WittVector p k, coeff α f = algebraMap _ (Fr p k) w ∧
        WittVector.constantCoeff w = coeff α f' := hf
    choose F hF using hf1
    let G : MvPowerSeries σ (WittVector p k) := F
    have e1 : f = map (algebraMap (WittVector p k) (Fr p k)) G := by
      ext α; rw [coeff_map]; exact (hF α).1
    have e2 : f' = map (WittVector.constantCoeff (p := p) (R := k)) G := by
      ext α; rw [coeff_map]; exact (hF α).2.symm
    rw [e1, e2, hmap, hmap', ← map_subst hVs, ← map_subst hVs]
    intro α
    exact ⟨coeff α (subst V G), by rw [coeff_map], by rw [coeff_map]⟩
  · intro c f hf
    have hf1 : ∀ α, ∃ w : WittVector p k, coeff α f = algebraMap _ (Fr p k) (c * w) := hf
    choose F hF using hf1
    let G : MvPowerSeries σ (WittVector p k) := F
    have e1 : f = algebraMap (WittVector p k) (Fr p k) c •
        map (algebraMap (WittVector p k) (Fr p k)) G := by
      ext α; rw [coeff_smul, coeff_map, hF α, map_mul]; rfl
    rw [e1, hmap, subst_smul (hVs.map _), ← map_subst hVs]
    intro α
    exact ⟨coeff α (subst V G), by rw [coeff_smul, coeff_map, map_mul]⟩

end Katz

end GlobalTheory
